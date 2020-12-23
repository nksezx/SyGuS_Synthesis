from z3 import *

Type = {}
Productions = {}
SynFunExpr=[]
VarDecMap={}
Constraints=[]
FunDefMap={}
VarTable={}
FunDefineStr = ''

def extractBmExpr(bmExpr):
    for expr in bmExpr:
        if len(expr)==0:
            continue
        elif expr[0]=='synth-fun':
            SynFunExpr=expr
        elif expr[0]=='declare-var':
            VarDecMap[expr[1]]=expr
        elif expr[0]=='constraint':
            Constraints.append(expr)
        elif expr[0]=='define-fun':
            FunDefMap[expr[1]]=expr
    
    # TODO: discuss the way to unify names
    # unify the vairable names for function calls in constraints and specification
    for c in Constraints:
        varListInConstraints = dfsFindFunCall(SynFunExpr[1], c[1])
        if varListInConstraints != None:
            varNameReplaceMap = {}
            # change in Fun parameters
            for i in range(len(SynFunExpr[2])):
                varNameReplaceMap[SynFunExpr[2][i][0]] = varListInConstraints[i]
                SynFunExpr[2][i][0] = varListInConstraints[i]
            # change in productions
            for productions in SynFunExpr[4]:
                for i in range(len(productions[2])):
                    if productions[2][i] in varNameReplaceMap.keys():
                        productions[2][i] = varNameReplaceMap[productions[2][i]]
            break
    
    for NonTerm in SynFunExpr[4]: #SynFunExpr[4] is the production rules
        NTName = NonTerm[0]
        NTType = NonTerm[1]
        Type[NTName] = NTType
        #Productions[NTName] = NonTerm[2]
        Productions[NTName] = []
        for NT in NonTerm[2]:
            if type(NT) == tuple:
                Productions[NTName].append(str(NT[1])) # deal with ('Int',0). You can also utilize type information, but you will suffer from these tuples.
            else:
                Productions[NTName].append(NT)

    # Declare Var
    for var in VarDecMap:
        VarTable[var]=DeclareVar(VarDecMap[var][2],var)

    global FuncDefineStr
    FuncDefine = ['define-fun']+SynFunExpr[1:4] #copy function signature
    FuncDefineStr = toString(FuncDefine,ForceBracket = True) # use Force Bracket = True on function definition. MAGIC CODE. DO NOT MODIFY THE ARGUMENT ForceBracket = True.


# Check if the expression set satisfies constraints
# ExprStr: [['+', 'x', 'x'], 'x']
def checkExpr(ExprSet):

    specList = []
    solver = Solver()

    # Add constraints
    for constraint in Constraints:
        specList.append('(assert %s)'%(toString(constraint[1:])))
    
    for expr in ExprSet:
        FunDefStr = FuncDefineStr[:-1]+' '+expr+FuncDefineStr[-1]
        specList.insert(0, FunDefStr)

        spec='\n'.join(specList)
        spec = parse_smt2_string(spec,decls=dict(VarTable))
        solver.add(Not(And(spec)))

        specList.pop(0)

    # check
    res = solver.check()
    if res==unsat:
        return None
    else:
        return solver.model()


def checkCondsforExpr(condsforExp, expr):

    solver = Solver()
    spec = []

    # Add constraints
    # Add Function Definition
    FunDefStr = FuncDefineStr[:-1]+' '+expr+FuncDefineStr[-1]
    spec.append(FunDefStr)

    # Add Constraints
    for constraint in Constraints:
        spec.append('(assert %s)'%(toString(constraint[1:])))

    spec='\n'.join(spec)
    spec = parse_smt2_string(spec,decls=dict(VarTable))
    solver.add(And(spec))
    
    # Add Condition for Expr
    for cond in condsforExp:
        if cond != []:
            condSpec = []

            for orCond in cond:
                condOrSpec = []

                if orCond != []:
                    for andCond in orCond:
                        condOrSpec.append('(assert %s)'%(toString(andCond)))

                    condOrSpec = '\n'.join(condOrSpec)
                    condOrSpec = parse_smt2_string(condOrSpec, decls=dict(VarTable))
                    condSpec.append(And(condOrSpec))

                if condSpec != []:
                    solver.add(Not(Or(*condSpec)))
    
    # Check
    res = solver.check()
    if res==unsat:
        return None
    else:
        return solver.model()


def checkGuardForCounterExample(guard, variableMap):

    #print(guard, model)
    #print(variableMap.keys())
    if guard[1] in variableMap.keys():
        num1 = variableMap[guard[1]]
    else:
        num1 = int(guard[1])
    
    if guard[2] in variableMap.keys():
        num2 = variableMap[guard[2]]
    else:
        num2 = int(guard[2])
    tmp = guard[0]
    if tmp == '=':
        tmp = '=='
    return eval(str(num1) + tmp + str(num2))


# CE: counter-example
def checkGuardSet(guardsForCE, expr, condSpecs):

    solver = Solver()
    spec = []
    
    # Add Constraints
    for guard in guardsForCE:
        spec.append('(assert %s)'%(toString(guard)))
    spec = '\n'.join(spec)
    spec = parse_smt2_string(spec, decls=dict(VarTable))
    solver.add(And(spec))

    spec = []
    FunDefStr = FuncDefineStr[:-1]+' '+expr+FuncDefineStr[-1]
    spec.append(FunDefStr)

    for constraint in Constraints:
        spec.append('(assert %s)'%(toString(constraint[1:])))

    spec ='\n'.join(spec)
    spec = parse_smt2_string(spec,decls=dict(VarTable))
    solver.add(Not(And(spec)))

    solver.add(*condSpecs)

    # Check
    res = solver.check()
    if res == unsat:
        return None
    else:
        return solver.model()


def synAndCond(conds):
    if len(conds) == 1:
            return conds
    else:
        res = conds[0]
        for cond in conds[1:]:
            res = ['and'] + [cond] + [res]
        return res


def synOrCond(conds):
    if conds == []:
        return None
    elif len(conds) == 1:
        return conds[0]
    else:
        res = conds[0]
        for cond in conds[1:]:
            res = ['or'] + [cond] + [res]
        return res


def synCondForOutputExpr(exprs, conds):

    # synthesis from last expr
    ans = exprs[-1]
    for i in range(len(exprs)-1, -1, -1):
        C = []

        for orCond in conds[i]:
            C.append(synAndCond(orCond))

        cond = synOrCond(C)
        if cond == None:
            ans = exprs[i]
        else: ans = ['ite', cond, exprs[i], ans]

    # check Answer
    FunDefStr = FuncDefineStr[:-1]+' '+toString(ans)+FuncDefineStr[-1]
    spec=[FunDefStr]

    for constraint in Constraints:
        spec.append('(assert %s)'%(toString(constraint[1:])))

    spec='\n'.join(spec)
    spec = parse_smt2_string(spec,decls=dict(VarTable))
    spec = And(spec)

    solver = Solver()
    solver.add(Not(spec))

    res=solver.check()
    if res == unsat:
        return FunDefStr
    else:
        return 'Failed.'


# binary search a smallest satisfied guards set
def getSatGuardSet(waitS, finalS, expr, conds):
    if checkGuardSet(finalS, expr, conds) == None:
        return []
    else:
        if len(waitS) == 1:
            return waitS

        mid = len(waitS) / 2
        leftS = waitS[:mid]
        rightS = waitS[mid:]

        leftResult = getSatGuardSet(leftS, finalS + rightS, expr, conds)
        rightResult = getSatGuardSet(rightS, finalS + leftResult, expr, conds)
        return leftResult + rightResult

# Ex: example
def canCover(condsForNewEx, condsForPriorEx):

    solver = Solver()
    priorExSpec = []

    for guard in condsForPriorEx:
        priorExSpec.append('(assert %s)'%(toString(guard)))

    priorExSpec = '\n'.join(priorExSpec)
    priorExSpec = parse_smt2_string(priorExSpec,decls=dict(VarTable))
    priorExSpec = And(priorExSpec)

    newExSpec = []

    for guard in condsForNewEx:
        newExSpec.append('(assert %s)'%(toString(guard)))

    newExSpec = '\n'.join(newExSpec)
    newExSpec = parse_smt2_string(newExSpec,decls=dict(VarTable))
    newExSpec = Not(And(newExSpec))

    solver.add(priorExSpec)
    solver.add(newExSpec)

    res = solver.check()
    if res == unsat:
        return True
    else: 
        return False


def dfsFindFunCall(funName, constraintClause):
    if type(constraintClause) == list:
        if constraintClause[0] == funName:
            return constraintClause[1:]
        else:
            lres = dfsFindFunCall(funName, constraintClause[1])
            if lres != None:
                return lres
            else: 
                rres = dfsFindFunCall(funName, constraintClause[2])
                return rres


def toString(Expr,Bracket=True,ForceBracket=False):
    if type(Expr)==str:
        return Expr
    if type(Expr)==tuple:
        return (str(Expr[1])) # todo: immediate 
    subexpr=[]
    for expr in Expr:
        if type(expr)==list:
            subexpr.append(toString(expr, ForceBracket=ForceBracket))
        elif type(expr)==tuple:
            subexpr.append(str(expr[1]))
        else:
            subexpr.append(expr)


    if not Bracket:
        #print subexpr
        return "%s"%(' '.join(subexpr))
    # Avoid Redundant Brackets
    if ForceBracket:
        return "(%s)"%(' '.join(subexpr))
    if len(subexpr)==1:
        return "%s"%(' '.join(subexpr))
    else:
        return "(%s)"%(' '.join(subexpr))

def DeclareVar(sort,name):
    if sort=="Int":
        return Int(name)
    if sort=='Bool':
        return Bool(name)
from translator import *

Type = {}
Productions = {}
SynFunExpr=[]
VarDecMap={}
Constraints=[]
FunDefMap={}
VarTable={}
FunDefineStr = ''

def dfsFindFunCall(funName, c):
    if type(c) == list:
        if c[0] == funName:
            return c[1:]
        else:
            lres = dfsFindFunCall(funName, c[1])
            if lres != None:
                return lres
            else: 
                return dfsFindFunCall(funName, c[2])

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
    
    # unify the vairable name for function calls in constraint and in specification
    for c in Constraints:
        varList = dfsFindFunCall(SynFunExpr[1], c[1])
        if varList != None:
            replaceMap = {}
            for i in range(len(SynFunExpr[2])):
                replaceMap[SynFunExpr[2][i][0]] = varList[i]
                SynFunExpr[2][i][0] = varList[i]
            for productions in SynFunExpr[4]:
                for i in range(len(productions[2])):
                    if productions[2][i] in replaceMap.keys():
                        productions[2][i] = replaceMap[productions[2][i]]
    
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


# Check whether the expression set satisfies constraints
# ExprStr: [['+', 'x', 'x'], 'x']
def checkExpr(ExprSet):

    spec_smt2 = []
    # Add constraints
    for constraint in Constraints:
        spec_smt2.append('(assert %s)'%(toString(constraint[1:])))
    
    solver = Solver()

    for expr in ExprSet:
        FunDefStr = FuncDefineStr[:-1]+' '+expr+FuncDefineStr[-1]
        spec_smt2.insert(0, FunDefStr)
        spec_smt2_join='\n'.join(spec_smt2)
        spec = parse_smt2_string(spec_smt2_join,decls=dict(VarTable))
        solver.add(Not(And(spec)))
        spec_smt2.pop(0)

    # check
    res = solver.check()
    if res==unsat:
        return None
    else:
        model=solver.model()
        return model


def checkCondsforExpr(conds, expr):

    solver = Solver()
    spec_smt2 = []

    FunDefStr = FuncDefineStr[:-1]+' '+expr+FuncDefineStr[-1]
    spec_smt2.append(FunDefStr)

    for constraint in Constraints:
        spec_smt2.append('(assert %s)'%(toString(constraint[1:])))
    spec_smt2_join='\n'.join(spec_smt2)
    spec = parse_smt2_string(spec_smt2_join,decls=dict(VarTable))
    solver.add(And(spec))
    
    for cond in conds:
        if cond != []:
            cond_smt2 = []
            for orCond in cond:
                cond_or_smt2 = []
                if orCond != []:
                    for andCond in orCond:
                        if andCond[0] == 'T':
                            continue
                        cond_or_smt2.append('(assert %s)'%(toString(andCond)))
                    cond_or_smt2 = '\n'.join(cond_or_smt2)
                    cond_or_smt2 = parse_smt2_string(cond_or_smt2, decls=dict(VarTable))
                    cond_smt2.append(And(cond_or_smt2))
                if cond_smt2 != []:
                    solver.add(Not(Or(*cond_smt2)))
    
    res = solver.check()
    if res==unsat:
        return None
    else:
        model=solver.model()
        return model

def checkGuardForCounterExample(guard, model):
    solver = Solver()
    spec_smt2 = []
    spec_smt2.append('(assert %s)'%(toString(guard)))
    for d in model.decls():
        constraint = ['=', d.name(), str(model[d])]
        spec_smt2.append('(assert %s)'%(toString(constraint)))
    spec_smt2_join = '\n'.join(spec_smt2)
    spec = parse_smt2_string(spec_smt2_join,decls=dict(VarTable))
    solver.add(And(spec))

    res = solver.check()
    if res==unsat:
        return False
    else:
        return True

def checkGuardSet(P, expr, conds):
    solver = Solver()
    spec_P = []
    
    for guard in P:
        spec_P.append('(assert %s)'%(toString(guard)))
    spec_P = '\n'.join(spec_P)
    spec_P = parse_smt2_string(spec_P, decls=dict(VarTable))
    solver.add(And(spec_P))

    spec_smt2 = []
    FunDefStr = FuncDefineStr[:-1]+' '+expr+FuncDefineStr[-1]
    spec_smt2.append(FunDefStr)

    for constraint in Constraints:
        spec_smt2.append('(assert %s)'%(toString(constraint[1:])))
    spec_smt2 ='\n'.join(spec_smt2)
    spec_smt2 = parse_smt2_string(spec_smt2,decls=dict(VarTable))
    solver.add(Not(And(spec_smt2)))

    for cond in conds:
        if cond != []:
            cond_smt2 = []
            for orCond in cond:
                cond_or_smt2 = []
                if orCond != []:
                    for andCond in orCond:
                        if andCond[0] == 'T':
                            continue
                        cond_or_smt2.append('(assert %s)'%(toString(andCond)))
                    cond_or_smt2 = '\n'.join(cond_or_smt2)
                    cond_or_smt2 = parse_smt2_string(cond_or_smt2, decls=dict(VarTable))
                    cond_smt2.append(And(cond_or_smt2))
                if cond_smt2 != []:
                    solver.add(Not(Or(*cond_smt2)))

    res = solver.check()
    if res == unsat:
        return None
    else:
        return solver.model()

def synAndCond(conds):
    if len(conds) == 1:
        if conds[0][0] == 'T':
            return None
        else: 
            return conds
    else:
        res = conds[0]
        for cond in conds[1:]:
            if cond[0] == 'T':
                continue
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

def synthesis(exprs, conds):
    ans = exprs[-1]
    for i in range(len(exprs)-1, -1, -1):
        C = []
        for orCond in conds[i]:
            C.append(synAndCond(orCond))
        cond = synOrCond(C)
        if cond == None:
            ans = exprs[i]
        else: ans = ['ite', cond, exprs[i], ans]

    FunDefStr = FuncDefineStr[:-1]+' '+toString(ans)+FuncDefineStr[-1]
    spec_smt2=[FunDefStr]
    for constraint in Constraints:
        spec_smt2.append('(assert %s)'%(toString(constraint[1:])))
    spec_smt2='\n'.join(spec_smt2)
    spec = parse_smt2_string(spec_smt2,decls=dict(VarTable))
    spec = And(spec)
    
    solver = Solver()
    solver.add(Not(spec))

    res=solver.check()
    if res == unsat:
        return FunDefStr
    else:
        return 'Failed.'

def getSatGuardSet(S, finalS, expr, guards):
    if checkGuardSet(finalS, expr, guards) == None:
        return []
    else:
        if len(S) == 1:
            return S

        mid = len(S) / 2
        leftS = S[:mid]
        rightS = S[mid:]

        leftResult = getSatGuardSet(leftS, finalS + rightS, expr, guards)
        rightResult = getSatGuardSet(rightS, finalS + leftResult, expr, guards)
        return leftResult + rightResult

def canCover(P, prior):
    solver = Solver()

    prior_spec = []
    for g in prior:
        prior_spec.append('(assert %s)'%(toString(g)))
    prior_spec = '\n'.join(prior_spec)
    prior_spec = parse_smt2_string(prior_spec,decls=dict(VarTable))
    prior_spec = And(prior_spec)

    P_spec = []
    for g in P:
        P_spec.append('(assert %s)'%(toString(g)))
    P_spec = '\n'.join(P_spec)
    P_spec = parse_smt2_string(P_spec,decls=dict(VarTable))
    P_spec = Not(And(P_spec))

    solver.add(prior_spec)
    solver.add(P_spec)

    res = solver.check()
    if res == unsat:
        return True
    else: 
        return False
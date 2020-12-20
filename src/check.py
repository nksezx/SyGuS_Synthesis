from translator import *

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

    # Add constraints
    for constraint in Constraints:
        spec_smt2.append('(assert %s)'%(toString(constraint[1:])))
    spec_smt2_join='\n'.join(spec_smt2)
    spec = parse_smt2_string(spec_smt2_join,decls=dict(VarTable))
    solver.add(And(spec))
    
    for cond in conds:
        cond_smt2 = []
        for c in cond:
            cond_smt2.append('(assert %s)'%(toString(c)))
        cond_smt2_join='\n'.join(cond_smt2)
        cond_smt2_spec=parse_smt2_string(cond_smt2_join, decls=dict(VarTable))
        solver.add(Not(And(cond_smt2_spec)))
    
    # for c in solver.assertions():
    #     print(c)
    # input()
    
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
import sys
import sexp
import copy
import pprint

import check
import gen_guard
import output_expr
import optimization

def stripComments(bmFile):
    noComments = '('
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + ')'

if __name__ == '__main__':
    benchmarkFile = open(sys.argv[1])
    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0] #Parse string to python list
    # pprint.pprint(bmExpr)

    Type = {}
    Productions = {}
    SynFunExpr = []

    for expr in bmExpr:
        if len(expr)==0:
            continue
        elif expr[0]=='synth-fun':
            SynFunExpr=expr
    
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

    check.extractBmExpr(bmExpr)    
    exprs = output_expr.getExpr(Type, Productions)
    guardGenerator = gen_guard.genGuard(Type, Productions)
    conds = []
    while True:
        guards = guardGenerator.next()
        for expr in exprs:
            conds.append([])
            while True:
                counterExample = check.checkCondsforExpr(conds, expr)
                if counterExample == None:
                    break
                S = []
                for guard in guards:
                    if check.checkGuardForCounterExample(guard, counterExample):
                        S.append(guard)
                P = check.getSatGuardSet(S, [], expr, conds)
                if P == []:
                    break
                flag = []
                conds_ = []
                for cond in conds[-1]:
                    if check.canCover(P, cond) == False:
                        conds_.append(cond)
                conds[-1] = copy.deepcopy(conds_)
                conds[-1].append(P)
        print(check.synthesis(exprs, conds))
        exit()
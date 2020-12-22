import sys
import sexp
import copy
import time
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

    start = time.time()
    check.extractBmExpr(bmExpr)    
    exprs = output_expr.getExpr(check.Type, check.Productions)
    guardGenerator = gen_guard.genGuard(check.Type, check.Productions)
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
        print(time.time()-start)
        exit()
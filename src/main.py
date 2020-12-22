import sys
import sexp
import copy
import time
import check
import pprint
import gen_guard
import output_expr

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
    
                satGuards = []
                for guard in guards:
                    if check.checkGuardForCounterExample(guard, counterExample):
                        satGuards.append(guard)

                filteredGuards = check.getSatGuardSet(satGuards, [], expr, conds)

                if filteredGuards == []: # Conds are satisfied already
                    break

                conds_ = []
                for cond in conds[-1]:
                    if check.canCover(filteredGuards, cond) == False:
                        conds_.append(cond)

                conds[-1] = copy.deepcopy(conds_)
                conds[-1].append(filteredGuards)

        print(check.synCondForOutputExpr(exprs, conds))
        print(time.time()-start)
        exit()
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
        tot1 = tot2 = tot3 = tot4 = 0
        totNum = 0
        for expr in exprs:
            print('synthesis for', expr)
            CESet = []
            CEGuardsSet = []
            conds.append([])

            while True:
                totNum += 1
                t1 = time.time()
                counterExample = check.checkCondsforExpr(conds, expr)
                t2 = time.time()
                if counterExample == None:
                    break
    
                satGuardsForNewCE = []
                variableMap = {}
                for d in counterExample.decls():
                    variableMap[d.name()] = counterExample[d]
                for guard in guards:
                    if check.checkGuardForCounterExample(guard, variableMap):
                        satGuardsForNewCE.append(guard)
                t3 = time.time()
                if check.checkGuardSet([], expr, conds) == None:
                    break
                if CESet == []:
                    filteredGuards = check.getSatGuardSet(satGuardsForNewCE, [], expr, conds)
                    CESet.append([counterExample])
                    CEGuardsSet.append(filteredGuards)
                    conds[-1].append(filteredGuards)
                else:
                    canCombine = 0
                    for i in range(len(CESet)):
                        ceset = CESet[i]
                        satGuards = []
                        ceset.append(counterExample)
                        for guard in CEGuardsSet[i]:
                            if check.checkGuardForCounterExample(guard, variableMap):
                                satGuards.append(guard)
                        if satGuards != []:
                            if check.checkGuardSet(satGuards, expr, conds) == None:
                                conds[-1][i] = satGuards
                                canCombine = 1
                                CEGuardsSet[i] = satGuards
                                break
                        ceset = ceset[:-1]
                    if canCombine == 0:
                        filteredGuards = check.getSatGuardSet(satGuardsForNewCE, [], expr, conds)
                        CESet.append([counterExample])
                        CEGuardsSet.append(filteredGuards)
                        conds[-1].append(filteredGuards)               
                t4 = time.time()
                tot1 += t2 - t1
                tot2 += t3 - t2
                tot3 += t4 - t3
        print(check.synCondForOutputExpr(exprs, conds))
        print(time.time()-start)
        print(tot1, tot2, tot3, totNum)
        exit()
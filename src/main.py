import sys
import sexp
import copy
import time
import check
import pprint
import gen_guard
import output_expr

from z3 import *

def stripComments(bmFile):
    noComments = '('
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + ')'


def condsToSpec(conds):
    spec = []
    for cond in conds:
        if cond != []:
            condSpec = []

            for orCond in cond:
                condOrSpec = []

                if orCond != []:
                    for andCond in orCond:
                        condOrSpec.append('(assert %s)'%(check.toString(andCond)))

                    condOrSpec = '\n'.join(condOrSpec)
                    condOrSpec = parse_smt2_string(condOrSpec, decls=dict(check.VarTable))

                    condSpec.append(And(condOrSpec))

                if condSpec != []:
                    spec.append(Not(Or(*condSpec)))
    
    return spec


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
                condSpecs = condsToSpec(conds)
                if check.checkGuardSet([], expr, condSpecs) == None:
                    break

                if CESet == []:
                    filteredGuards = check.getSatGuardSet(satGuardsForNewCE, [], expr, condSpecs)
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
                            if check.checkGuardSet(satGuards, expr, condSpecs) == None:
                                filtered = check.getSatGuardSet(satGuards, [], expr, condSpecs)
                                conds[-1][i] = filtered
                                canCombine = 1
                                CEGuardsSet[i] = satGuards
                                print('combine success!')
                                break
                        ceset = ceset[:-1]
                    if canCombine == 0:
                        filteredGuards = check.getSatGuardSet(satGuardsForNewCE, [], expr, condSpecs)
                        CESet.append([counterExample])
                        CEGuardsSet.append(satGuardsForNewCE)
                        conds[-1].append(filteredGuards)               
                t4 = time.time()
                tot1 += t2 - t1
                tot2 += t3 - t2
                tot3 += t4 - t3
        print(check.synCondForOutputExpr(exprs, conds))
        print(time.time()-start)
        print(tot1, tot2, tot3, totNum)
        exit()
import sys
import sexp
import pprint

import check
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
            model = check.checkCondsforExpr(conds, expr)
            
            P = []
            for guard in guards:
                res = check.checkGuardForCounterExample(guard, model)
                if res:
                    

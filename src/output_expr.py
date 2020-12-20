import translator

exprWithDiffNumOp = {}
atomicExpr = []
arithExpr = []

def classifyProductions(Type, Productions):
    body = []
    for key in Productions:
        if Type[key] == 'Int':
            body = Productions[key]
    
    if body != []:
        for elm in body:
            if type(elm) != list:
                atomicExpr.append(elm)
            elif elm[0] != 'ite':
                arithExpr.append(elm)

def genExpr():
    numOfOp = 0
    while numOfOp < 100:
        if numOfOp != 0:
            for expr in arithExpr:
                for i in range(numOfOp):
                    for left in exprWithDiffNumOp[i]:
                        for right in exprWithDiffNumOp[numOfOp - i - 1]:
                            # TODO: Addition and multiplication do not remove repeated expressions
                            exprWithDiffNumOp[numOfOp].append([expr[0]] + [left] + [right])
        yield exprWithDiffNumOp[numOfOp]
        numOfOp += 1
        exprWithDiffNumOp[numOfOp] = []


def biSearch(R, finalR, bmExpr):
    if translator.checkExpr(R + finalR, bmExpr) == None:
        if translator.checkExpr(finalR, bmExpr) != None:
            if len(R) == 1:
                return R

            mid = len(R) / 2
            leftR = R[:mid]
            rightR = R[mid:]

            leftResult = biSearch(leftR, finalR + rightR, bmExpr)
            rightResult = biSearch(rightR, finalR + leftResult, bmExpr)
            if translator.checkExpr(rightResult, bmExpr) == None:
                return rightResult
            return leftResult + rightResult
        else:
            return finalR


def getExpr(Type, Productions, bmExpr):

    classifyProductions(Type, Productions)
    exprWithDiffNumOp[0] = atomicExpr
    exprGenerator = genExpr()
    exprSet = []

    while True:
        exprSet.extend(exprGenerator.next())
        finalExprSet = biSearch(exprSet, [], bmExpr)
        l = len(finalExprSet)
        print(finalExprSet)
        if finalExprSet != []:
            break

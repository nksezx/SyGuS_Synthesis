import check

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
    return (atomicExpr, arithExpr)


def genExpr(Type, Productions):
    classifyProductions(Type, Productions)
    exprWithDiffNumOp[0] = atomicExpr

    numOfOp = 0
    while numOfOp < 100:
        if numOfOp != 0:
            for expr in arithExpr:
                for i in range(numOfOp):

                    for left in exprWithDiffNumOp[i]:
                        for right in exprWithDiffNumOp[numOfOp - i - 1]:
                            exprWithDiffNumOp[numOfOp].append([expr[0]] + [left] + [right])

        yield exprWithDiffNumOp[numOfOp]
        numOfOp += 1
        exprWithDiffNumOp[numOfOp] = []


def biSearch(R, finalR):
    if not check.checkExpr(finalR):
        if len(R) == 1:
            return R

        mid = len(R) / 2
        leftR = R[:mid]
        rightR = R[mid:]

        leftResult = biSearch(leftR, finalR + rightR)
        rightResult = biSearch(rightR, finalR + leftResult)
        return leftResult + rightResult
    else:
        return []


def getExpr(Type, Productions):

    exprGenerator = genExpr(Type, Productions)
    exprSet = []

    while True:
        exprSet.extend(exprGenerator.next())
        if not check.checkExpr(exprSet):
            continue
        finalExprSet = biSearch(exprSet, [])
        return finalExprSet
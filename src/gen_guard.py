import output_expr

def genGuard(Type, Productions):
    boolProds = []
    compProds = []

    for key in Productions:
        if Type[key] == 'Bool':
            boolProds = Productions[key]
    
    compOp = []
    for prod in boolProds:
        if not prod[0] in ['<=', '<', '=', '>', '>=']:
            continue
        else:
            if prod[0] == '<=' and '>=' in compOp:
                continue
            elif prod[0] == '<' and '>' in compOp:
                continue
            elif prod[0] == '>=' and '<=' in compOp:
                continue
            elif prod[0] == '>' and '<' in compOp:
                continue
            compOp.append(prod[0])
            compProds.append(prod)

    guards = []
    numOfOp = 0
    arithExpr = output_expr.exprWithDiffNumOp[numOfOp]

    while numOfOp < 30:
        if numOfOp != 0:
            arithExpr.extend(output_expr.exprWithDiffNumOp[numOfOp])

        for i in range(len(arithExpr)):
            for expr in arithExpr[i+1:]:
                for prod in compProds:
                    guards.append([prod[0]]+[arithExpr[i]]+[expr])
                    if prod[0] != '=':
                        guards.append([prod[0]]+[expr]+[arithExpr[i]])

        yield guards
        numOfOp += 1
        guards = []


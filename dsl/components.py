from collections import namedtuple

def execHead(inputs):
    out = []
    for val in inputs:
        ret = None
        if len(val)>0:
            ret = val[0]
        out.append(ret)
    return tuple(out)

def execLast(inputs):
    out = []
    for val in inputs:
        ret = None
        if len(val)>0:
            ret = val[-1]
        out.append(ret)
    return tuple(out)

def execTake(inputs):
    return tuple(tuple(val[1])[:val[0]] for val in inputs)

def execDrop(inputs):
    return tuple(tuple(val[1])[val[0]:] for val in inputs)

def execAccess(inputs):
    out = []
    for val in inputs:
        a = val[0]
        b = val[1]
        if a is None:
            ret = None
        elif ((a>=0 and len(b)>a) or (a<0 and len(b)>=-a)):
            ret = b[a]
        else:
            ret = None
        out.append(ret)
    return tuple(out)

def execMinimum(inputs):
    out = []
    for val in inputs:
        ret = None
        if len(val)>0:
            ret = min(val)
        out.append(ret)
    return tuple(out)

def execMaximum(inputs):
    out = []
    for val in inputs:
        ret = None
        if len(val)>0:
            ret = max(val)
        out.append(ret)
    return tuple(out)

def execSort(inputs):
    return tuple(tuple(sorted(val)) for val in inputs)

def execReverse(inputs):
    return tuple(tuple(val[::-1]) for val in inputs)

def execFilter(inputs, option):
    return tuple(tuple(filter(option, val)) for val in inputs)

def execCount(inputs, option):
    return tuple(len(tuple(filter(option, val))) for val in inputs)

def execSum(inputs):
    out = []
    for val in inputs:
        out.append(sum(val))
    return tuple(out)

def execMap(inputs, option):
    return tuple(tuple(map(option,val)) for val in inputs)

def execZipwith(inputs, option):
    return tuple(tuple(option(x,y) for (x,y) in zip(val[0],val[1])) for val in inputs)

def execScanL1(inputs, option):
    out = []
    for val in inputs:
        ret = []
        if len(val) > 0:
            y = val[0]
            ret.append(y)
            for x in val[1:]:
                y = option(y, x)
                ret.append(y)
        out.append(tuple(ret))
    return tuple(out)

Function = namedtuple('Function', ['options', 'inputTypes', 'outputType', 'execute'])

boolOpts = {
    '<0': Function(None, 'I', 'B', lambda i: i < 0),
    '>0': Function(None, 'I', 'B', lambda i: i > 0),
    '%2==0': Function(None, 'I', 'B', lambda i: i%2==0),
    '%2==1': Function(None, 'I', 'B', lambda i: i%2==1),
}

intOpts = {
    '+1': Function(None, 'I', 'I', lambda i: i+1),
    '-1': Function(None, 'I', 'I', lambda i: i-1),
    '*2': Function(None, 'I', 'I', lambda i: i*2),
    '/2': Function(None, 'I', 'I', lambda i: i//2),
    '*(-1)': Function(None, 'I', 'I', lambda i: i*(-1)),
    '**2': Function(None, 'I', 'I', lambda i: i**2),
    '*3': Function(None, 'I', 'I', lambda i: i*3),
    '/3': Function(None, 'I', 'I', lambda i: i//3),
    '*4': Function(None, 'I', 'I', lambda i: i*4),
    '/4': Function(None, 'I', 'I', lambda i: i//4),
}

pairOpts = {
   '+': Function(None, 'II', 'I', lambda i,j: i+j),
   '-': Function(None, 'II', 'I', lambda i,j: i-j),
   '*': Function(None, 'II', 'I', lambda i,j: i*j),
   'MIN': Function(None, 'II', 'I', lambda i,j: min(i,j)),
   'MAX': Function(None, 'II', 'I', lambda i,j: max(i,j)),
}

functions = {
    'HEAD': Function(None, (list,), int, execHead),
    'LAST': Function(None, (list,), int, execLast),
    'MINIMUM': Function(None, (list,), int, execMinimum),
    'MAXIMUM': Function(None, (list,), int, execMaximum),
    'SORT': Function(None, (list,), list, execSort),
    'REVERSE': Function(None, (list,), list, execReverse),
    'FILTER': Function(boolOpts, (list,), list, execFilter),
    'COUNT': Function(boolOpts, (list,), int, execCount),
    'SUM': Function(None, (list,), int, execSum),
    'MAP': Function(intOpts, (list,), list, execMap),
    'SCANL1': Function(pairOpts, (list,), list, execScanL1),
    'TAKE': Function(None, (int,list), list, execTake),
    'DROP': Function(None, (int,list), list, execDrop),
    'ACCESS': Function(None, (int,list), int, execAccess),
    'ZIPWITH': Function(pairOpts, (list,list), list, execZipwith),
}

def getCompositeFunctionKeys():
    return list(getCompositeFunctions().keys())

def getCompositeFunctions():
    # loop thru functions and pair with options to get the full list
    compositeFunctions = {}
    for fk, f in functions.items():
        opts = f.options
        if opts:
            for ok, o in opts.items():
                id = fk+','+ok
                compositeFunctions[id] = Function(None, f.inputTypes, f.outputType, lambda inputs: f.execute(inputs, o.execute))
        else:
            compositeFunctions[fk] = f
    return compositeFunctions

def getAllFunctionsAndOptionsList():
    return list(functions.keys()) + list(boolOpts.keys()) + list(intOpts.keys()) + list(pairOpts.keys())

def getOptionsList(functionId):
    return list(functions[functionId].options.keys())

def getFunctionKeysWithLambda():
    hasLambda = []
    for fk, f in functions.items():
        opts = f.options
        if opts:
            hasLambda.append(fk)
    return hasLambda

def evaluate(functionId, inputValues, optionId = None):
    option = None
    f = functions[functionId]
    if optionId:
        option = f.options[optionId].execute
        out = f.execute(inputValues, option)
    else:
        out = f.execute(inputValues)
    return out

def getFunctionOutput(functionId):
    try:
        out = functions[functionId].outputType
    except:
        cfuncs = getCompositeFunctions()
        out = cfuncs[functionId].outputType
    return out

def getFunctionInputs(functionId):
    try:
        intypes = functions[functionId].inputTypes
    except:
        cfuncs = getCompositeFunctions()
        intypes = cfuncs[functionId].inputTypes
    return intypes

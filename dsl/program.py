import ast
from collections import namedtuple
from dsl import components

class ProgramLine:
    def __init__(self, function = '', inputRefs = [], option = None):
        self.function = function
        self.option = option
        self.inputRefs = inputRefs

    @classmethod
    def fromString(cls, progLineString, progInputs):
        newLine = cls()
        line = progLineString.split(',')
        newLine.function = line[0]
        newLine.option = None
        if line[1]: newLine.option = line[1]
        newLine.inputRefs = []
        # program strings use slightly more readable refs for line inputs
        # this returns us to simple int references
        for inStr in line[2].split():
            if inStr[0] == 'X':
                newLine.inputRefs.append(int(inStr[1:]) - 1)
            else:
                for i, progIn in enumerate(progInputs):
                    if progIn.name == inStr:
                        # because first prog input will be in pos -1 in line output list when running the program
                        # and more generally ith input at pos -i
                        newLine.inputRefs.append(-i - 1)
                        break
        return newLine

    def toString(self, inputMapping):
        lineInputStrings = []
        for lineIn in self.inputRefs:
            if lineIn < 0:
                lineInputStrings.append(inputMapping[-lineIn-1].name)
            else:
                lineInputStrings.append('X'+str(lineIn+1))
        if self.option == None: o = ''
        else: o = str(self.option)
        return self.function+','+o+','+' '.join(lineInputStrings)

    def evaluateLine(self, values):
        return self.evaluateLineMany([values])[0]

    def evaluateLineMany(self, allValues):
        allData = []
        for values in allValues:
            actualData = []
            for d in self.inputRefs:
                actualData.append(values[d])
            if len(self.inputRefs) > 1:
                allData.append(actualData)
            else: allData += actualData
        return components.evaluate(self.function, allData, self.option)

class Program:
    def __init__(self, inputTypes = [], lineFunctions = [], lineInputRefs = []):
        ProgramInput = namedtuple('Input', ['name', 'type'])
        self.inputs = []
        i = 1
        for t in inputTypes:
            # nicer name for string output
            name = 'I'+str(i)
            self.inputs.append(ProgramInput(name, t))
            i += 1
        self.lines = []
        for fn in lineFunctions:
            fnParts = fn.split(',')
            f = fnParts[0]
            o = None
            if len(fnParts) == 2: o = fnParts[1]
            n = len(components.getFunctionInputs(f))
            self.lines.append(ProgramLine(f, lineInputRefs[:n], o))
            del lineInputRefs[:n]

    def getNumberOfListInputs(self):
        return len([x for x in self.inputs if x.type is list])

    def getNumberOfInputs(self):
        return len(self.inputs)

    def getOutputType(self):
       return components.getFunctionOutput(self.lines[-1].function)

    # order of inputs in programInputValues must match program.inputs
    def runFullOutput(self, programInputValues):
        lineOutputValues = [None]*len(self.lines) + list(programInputValues[::-1])
        for i, line in enumerate(self.lines):
            lineOutputValues[i] = line.evaluateLine(lineOutputValues)
        return lineOutputValues

    # order of inputs in programInputValues must match program.inputs
    # to use input names instead, first create a dictionary of input names: values
    # and run this through program.parseInputDict()
    def run(self, programInputValues):
        return self.runFullOutput(programInputValues)[len(self.lines)-1]

    # evaluate program on several input sets at once
    # order of inputs within a set must match program.inputs
    def runMany(self, programInputValues):
        lineOutputValues = []
        for progIns in programInputValues:
            lineOutputValues.append([None]*len(self.lines) + list(progIns[::-1]))
        for i, line in enumerate(self.lines):
            fullOut = line.evaluateLineMany(lineOutputValues)
            for j, lineOut in enumerate(lineOutputValues):
                lineOutputValues[j][i] = fullOut[j]
        return tuple(x[len(self.lines)-1] for x in lineOutputValues)

    # ensures that the inputs given do not go outside the range [-255, 256]
    def runWithChecks(self, programInputValues, outputNotEmpty = True):
        lineOutputValues = self.runFullOutput(programInputValues)

        for lineOut in lineOutputValues:
            if isinstance(lineOut, (tuple, list)):
                for list_val in lineOut:
                    if list_val < -255 or list_val > 256:
                        return False
            else:
                if lineOut is not None:
                    if lineOut < -255 or lineOut > 256:
                        return False

        progOutput = lineOutputValues[len(self.lines)-1]
        if outputNotEmpty:
            if progOutput is None or progOutput == ():
                return False

        return progOutput

    def runAndCollectStats(self, programInputValues):
        lineOutputValues = self.runFullOutput(programInputValues)

        indicators = []
        for i, progLine in enumerate(self.lines):
            for lineInput in progLine.inputRefs:
                # first list input is considered "main" input
                if self.inputs[abs(lineInput)-1].type is list:
                    initial = lineOutputValues[lineInput]
                    break
                else:
                    # or if there's no list just take the first input
                    initial = lineOutputValues[progLine.inputRefs[0]]
            final = lineOutputValues[i]
            indicators.append(tuple(self.compareLines(initial, final)))

        return lineOutputValues[len(self.lines)-1], tuple(indicators)

    def compareLines(self, initial, final):
        indicatorList = [0] * 5

        if isinstance(initial, int):
            initial = [initial]
        if isinstance(final, int):
            final = [final]
        if initial is None:
            initial = []
        if final is None:
            final  = []

        if len(initial) == 0 and len(final) == 0:
            # nothing has changed
            pass
        elif len(initial) == 0 and len(final) != 0:
            # all features have changed
            indicatorList = [1,1,1,1,1]
        elif len(initial) != 0 and len(final) == 0:
            # all features have changed
            indicatorList = [1,1,1,1,1]
        else:
            # non trivial case that both inputs non empty
            # first list item
            if initial[0] != final[0]:
                indicatorList[0] = 1
            # last list item
            if initial[-1] != final[-1]:
                indicatorList[1] = 1
            # max element
            if max(initial) != max(final):
                indicatorList[2] = 1
            # min element
            if min(initial) != min(final):
                indicatorList[3] = 1
            # length
            if len(initial) != len(final):
                indicatorList[4] = 1

        return indicatorList

    def parseInputString(self, inputString):
        return self.parseInputDict(ast.literal_eval(inputString))

    # takes a dictionary of 'inputName': inputValue
    # returns a list of inputs in same order as program.inputs
    # which is suitable for passing to program.run()
    def parseInputDict(self, inputDict):
        inNames = [x.name for  x in self.inputs]
        inTypes = [x.type for x in self.inputs]
        valList = [inputDict[s] for s in inNames]
        checkVals = [type(valList[i]) is inTypes[i] or (valList[i] is None and inTypes[i] is int) for i in range(len(valList))]
        if checkVals.count(False) != 0:
            # one of the input types isn't as expected
            raise Exception('unexpected input type: {} {}'.format(inputString, self.inputs))
        return valList

    def generateInputString(self, inputValues):
        return str(self.generateInputDict(inputValues))

    # internally the order of inputs is used to identify them
    # but for readability they are given names in the string output
    def generateInputDict(self, inputValues):
        inNames = [x.name for x in self.inputs]
        inTypes = [x.type for x in self.inputs]
        checkVals = [type(inputValues[i]) is inTypes[i] or (inputValues[i] is None and inTypes[i] is int) for i in range(len(inputValues))]
        if checkVals.count(False) != 0:
            # one of the input types isn't as expected
            raise Exception('unexpected input type: {} {}'.format(str(inputValues), self.inputs))
        inputDict = {}
        for i, inputName in enumerate(inNames):
            inputDict[inputName] = inputValues[i]
        return inputDict

    @classmethod
    def fromString(cls, progString):
        ProgramInput = namedtuple('Input', ['name', 'type'])
        p = cls()
        # clean input
        if progString[-1] == '\n':
            progString = progString[:-1]
        if progString[0] != '{':
            lines = progString.split('\\')[1:]
        else:
            lines = progString.split('\\')
        for inName, inType in ast.literal_eval(lines[0]).items():
            assert(inType in ('list', 'int'))
            t = list if inType == 'list' else int
            p.inputs.append(ProgramInput(inName, t))
        for l in lines[1:]:
            p.lines.append(ProgramLine.fromString(l, p.inputs))
        return p

    def toString(self):
        inputDict = {}
        lines = []
        for progIn in self.inputs:
            inputDict[progIn.name] = progIn.type.__name__
        for progLine in self.lines:
            lines.append(progLine.toString(self.inputs))
        return str(inputDict)+'\\'+'\\'.join(lines)

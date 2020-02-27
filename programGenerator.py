import dsl
import itertools

class programGenerator:
    # rough check for equivalent programs
    class EquivalenceChecker:
        testInputs = {
            'list1': [[-2,-3,-1,-1,-4,-2,-5], [1,2,4,3,1,1], [-1,0,2,0,-1], [7,2,-6,2,9,-4,1,6,1],[10,-2,6,2,222,-1,1,-8,-4,4,6]],
            'list2': [[-2,2,-3,0,1,4], [-1,8,0,-2,3,-1], [1,3,7], [4,-8,2,6,-3,-1,2,8,8,0], [-1,1,-2,-3,7,-3]],
            'int': [3, 2, 0, -1, 2]
        }

        def __init__(self):
            self.testOutputs = {
                ((-2, -3, -1, -1, -4, -2, -5), (1, 2, 4, 3, 1, 1), (-1, 0, 2, 0, -1), (7, 2, -6, 2, 9, -4, 1, 6, 1), (10, -2, 6, 2, 222, -1, 1, -8, -4, 4, 6)):0,
                ((-2, 2, -3, 0, 1, 4), (-1, 8, 0, -2, 3, -1), (1, 3, 7), (4, -8, 2, 6, -3, -1, 2, 8, 8, 0), (-1, 1, -2, -3, 7, -3)):0,
                (3, 2, 0, -1, 2):0
            }

        def acceptProgram(self, program, id, inputTypes):
            if inputTypes == [list]:
                out = program.runMany(zip(self.testInputs['list1']))
            elif inputTypes == [list, list]:
                out = program.runMany(zip(self.testInputs['list1'], self.testInputs['list2']))
            elif inputTypes == [list, int]:
                out = program.runMany(zip(self.testInputs['list1'], self.testInputs['int']))
            # lookup id of equivalent programs
            equiv = self.testOutputs.get(out, None)
            if equiv is not None:
                # don't add this program
                return False, equiv
            # passed - add to output sets
            self.testOutputs[out] = id
            return True, None

    # for simplicity all programs will have either one or two inputs
    progInputs = [[list], [list, int], [list, list]]

    def __init__(self):
        self.checker = self.EquivalenceChecker()

    # all the ways for the program input slots to be filled
    def getLineInputs(self, pIns, skeletonProgram, n):
        # what ints and lists are given and calulated during the program
        availableInputs = {int: [], list: []}
        for i, progInType in enumerate(pIns):
            availableInputs[progInType].append(-(i+1))
        for i in range(n):
            lineOutputType = dsl.getFunctionOutput(skeletonProgram[i])
            availableInputs[lineOutputType].append(i)

        allInputsOptions = []
        for i in range(n):
            lineOpts = []
            # line expects fixed var types in fixed order
            requiredInputs = dsl.getFunctionInputs(skeletonProgram[i])
            for lineInputType in requiredInputs:
                # we can use program inputs plus line outputs from earlier lines provided type matches
                lineOpts.append(list(filter(lambda x: x<i, availableInputs[lineInputType])))
            # it is almost never interesting to have a line take the same input twice
            filteredLineOpts = list(filter(lambda x: len(set(x)) == len(x), list(itertools.product(*lineOpts))))
            allInputsOptions.append(filteredLineOpts)

        finalLineInputs = list(itertools.product(*allInputsOptions))
        # flatten out the options so each possibility is a single list of inputs in the order they can be used
        finalLineInputs = [[x for y in b for x in y] for b in finalLineInputs]
        # required to use all input and calculated values in a program -- but not the final output
        all = (set(availableInputs[int]) | set(availableInputs[list])) - {n-1}
        return list(filter(lambda x: set(x) == all, finalLineInputs))

    def getAllUpToMLines(self, m, folderName):
        progId = 1
        for n in range(1,m+1):
            accepted = []
            failed = []
            for inputs in self.progInputs:
                lineFunctions = [dsl.getCompositeFunctionKeys()]*n
                # skeleton programs created by taking all the combinations of funcs at each line
                for skeletonProg in itertools.product(*lineFunctions):
                    # fill in the possible inputs for each line in the proposed program
                    # and contruct the full programs
                    for inputChoice in self.getLineInputs(inputs, skeletonProg, n):
                        # create program and hand to equivalence checker to decide whether to keep it
                        candidate = dsl.Program(inputs, skeletonProg, list(inputChoice))
                        acceptProg, clash = self.checker.acceptProgram(candidate, progId, inputs)
                        if acceptProg:
                            accepted.append(str(progId)+'\\'+candidate.toString()+'\n')
                        else:
                            failed.append(str(progId)+'\\'+candidate.toString()+'\\'+str(clash)+'\n')
                        progId += 1
            # write out generated programs
            fileName = folderName+'/'+str(n)+'Progs.txt'
            failedFileName = folderName+'/'+str(n)+'Failed.txt'
            with open(fileName, 'w', encoding='utf-8') as f:
                for acc in accepted:
                    f.write(acc)
            with open(failedFileName, 'w', encoding='utf-8') as f1:
                for fail in failed:
                    f1.write(fail)

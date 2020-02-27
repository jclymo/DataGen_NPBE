import z3InputsOracle
import dsl
import numpy as np
import multiprocessing as mp
from collections import namedtuple

class exampleGenerator:
    def factory(self, mode, output_file_name, program_list, number_per_program = 25, max_list_length = 10, examples_per_set = 5):
        assert(mode in ['restricted', 'exp', 'constraint', 'varied'])
        if mode == 'restricted':
            return IOGeneratorRestrictedDomain(output_file_name, program_list, number_per_program, max_list_length, examples_per_set)
        elif mode == 'exp':
            return IOGeneratorExpSampling(output_file_name, program_list, number_per_program, max_list_length, examples_per_set)
        elif mode == 'constraint':
            return IOGeneratorConstraintBased(output_file_name, program_list, number_per_program, max_list_length, examples_per_set)
        elif mode == 'varied':
            return IOGeneratorVaried(output_file_name, program_list, number_per_program, max_list_length, examples_per_set)

class IOGeneratorBase():
    def __init__(self, output_file_name, program_list, number_per_program, max_list_length, examples_per_set):
        self.output_file_name = output_file_name
        self.program_list = program_list
        self.number_per_program = number_per_program
        self.max_list_length = max_list_length
        self.examples_per_set = examples_per_set

    def run(self):
        n_cpus = mp.cpu_count()
        pool = mp.Pool(processes = n_cpus)
        with open(self.output_file_name, 'a', encoding='utf-8') as outFile:
            for program, listOfExamples in pool.imap_unordered(self.getFormattedExamples, self.program_list):
                for j in range(0, self.number_per_program, self.examples_per_set):
                    outFile.write(program)
                    count_examples = 0
                    for ex in listOfExamples[j:j+self.examples_per_set]:
                        count_examples += 1
                        outFile.write(ex)
                    for defecit in range(self.examples_per_set - count_examples):
                        outFile.write('Could not find Example\n')

    def getFormattedExamples(self, progString):
        program = dsl.Program.fromString(progString)
        exampleSet = self.getExamples(program)
        exampleSetStrings = []
        for ex in exampleSet:
            exampleSetStrings.append(program.generateInputString(ex[0])+'|'+str(ex[1])+'\n')
        return progString, exampleSetStrings

    def outIsSuitable(self, out, tries):
        if type(out) is int:
            if out == 0 and tries >= int(self.patience*0.9):
                return True
            elif out in range(-255, 256):
                return True
        elif type(out) is list and len(out) > 0:
            if (max(out) <= 256) and (min(out) >= -255):
                return True
        elif type(out) is list and len(out) == 0 and tries >= int(self.patience*0.9):
            return True
        return False

    def getExamplesfromZ3(self, program, required, exclude_set = [], specifications = [], returnNullResults = False):
        resultSet = []
        noRepeatedIn = True
        noRepeatedOut = True

        codifiedProgram = []
        for l in program.lines:
            thisLine = (l.function, l.option)+tuple(l.inputRefs)
            if len(l.inputRefs) == 1:
                thisLine += (None,)
            codifiedProgram.append(thisLine)

        integerInputIndices = [i for i in range(len(program.inputs)) if program.inputs[i].type is int]

        if specifications == []:
            z3interface = z3InputsOracle.z3InputsOracle(self.max_list_length)
            z3interface.setProgram(len(program.inputs), integerInputIndices, codifiedProgram, 'basic')
        else:
            z3interface = z3InputsOracle.z3InputsOracle(self.max_list_length, timeout=1000)
            z3interface.setProgram(len(program.inputs), integerInputIndices, codifiedProgram, 'varied')

        z3interface.inputsNotNone()
        z3interface.distinctInandOut()

        failedExclusions = set()
        failedFeatures = set()
        for example_num in range(required):
            # any additional constraints to be used?
            try: spec = specifications[i]
            except: spec = None

            z3interface.beginAddConstraints()

            # random length is a minimum, not exact length
            random_lengths = {}
            for i, in_data in enumerate(program.inputs):
                if in_data.type == list:
                    # first (0th) input takes position -1 in line output list, next at pos -2 etc.
                    random_lengths[-(i+1)] = np.random.randint(1, self.max_list_length//2 + 1)
                else:
                    random_lengths[-(i+1)] = 0
            z3interface.setInputMinimumLengths(random_lengths)

            if program.getOutputType() is int:
                z3interface.outputNotNone()

            R = resultSet[example_num - (example_num % self.examples_per_set):example_num]
            try:
                R.append(exclude_set[example_num])
            except: pass
            I = [x[0] for x in R if x is not None]
            recentInputs = [y for x in I for y in x]
            recentOutputs = [x[1] for x in R if x is not None]
            if noRepeatedIn:
                for val in recentInputs:
                    z3interface.excludeInputConstraint(val)
            if noRepeatedOut:
                for val in recentOutputs:
                    z3interface.excludeOutputs(val)

            if spec and spec.notNull: z3interface.excludeNullBehaviours()

            if spec and spec.behaviours and spec.behaviours not in failedExclusions:
                z3interface.excludeBehaviours(spec.behaviours)

            if spec and spec.updateFeature not in failedFeatures:
                if spec.updateFeature == "min":
                    z3interface.setOutMin(-50)
                if spec.updateFeature == "max":
                    z3interface.setOutMax(50)
                if spec.updateFeature == "len":
                    z3interface.setOutputMinimumLength(4)

            res = z3interface.evalSatAndUpdateModel().removeAddedConstraints().getLastInputsAndOutputs()

            if res is None:
                # this is useful when calling code wants to know which queries were successful
                if returnNullResults: resultSet.append(res)
                # not able to find IO example - relax conditions so don't try a bad query again
                if spec and spec.behaviours: failedExclusions = failedExclusions | {spec.behaviours}
                if spec and spec.updateFeature: failedFeatures = failedFeatures | {spec.updateFeature}
                if not spec:
                    if noRepeatedOut: noRepeatedOut = False
                    else: noRepeatedIn = False
            else:
                allInputs = res[1:][::-1]
                for i, progIn in enumerate(program.inputs):
                    if progIn.type is int:
                        if allInputs[i] == []: allInputs[i] = None
                        else: allInputs[i] = allInputs[i][0]
                if program.getOutputType() is int:
                    if not res[0]: out = None
                    else: out = res[0][0]
                else: out = res[0]
                resultSet.append((allInputs, out))

        return resultSet

class IOGeneratorRestrictedDomain(IOGeneratorBase):
    def backPropagateValues(self, program, listLength):
        bounds = [None] * (len(program.lines)+2)
        # initiate program output bounds i.e. output of final line
        bounds[len(program.lines)-1] = (-255,256)
        # loop starts at final line and works backwards thru program
        for index in reversed(range(len(program.lines))):
            lineOutputBound = bounds[index]
            assert(lineOutputBound is not None)
            programLine = program.lines[index]
            func = programLine.function
            opt = programLine.option
            lineInputs = programLine.inputRefs
            if func in ['HEAD', 'LAST']:
                existingBound = bounds[lineInputs[0]]
                if existingBound:
                    bounds[lineInputs[0]] = (max(existingBound[0], lineOutputBound[0]), min(existingBound[1], lineOutputBound[1]))
                else:
                    bounds[lineInputs[0]] = lineOutputBound
            elif func in ['TAKE', 'DROP', 'ACCESS']:
                existingBoundInt = bounds[lineInputs[0]]
                existingBoundList = bounds[lineInputs[1]]
                if existingBoundInt:
                    pass
                else:
                    bounds[lineInputs[0]] = (-255, 256)
                if existingBoundList:
                    bounds[lineInputs[1]] = (max(existingBoundList[0], lineOutputBound[0]), min(existingBoundList[1], lineOutputBound[1]))
                else:
                    bounds[lineInputs[1]] = lineOutputBound
            elif func in ['MAXIMUM', 'MINIMUM', 'SORT', 'REVERSE']:
                existingBound = bounds[lineInputs[0]]
                if existingBound:
                    bounds[lineInputs[0]] = (max(existingBound[0], lineOutputBound[0]), min(existingBound[1], lineOutputBound[1]))
                else:
                    bounds[lineInputs[0]] = lineOutputBound
            elif func == 'FILTER':
                if opt == '<0':
                    lb = 0
                    ub = 256
                    if lineOutputBound[0] < 0: lb = lineOutputBound[0]
                    if lineOutputBound[1] < 0: ub = lineOutputBound[1]
                    existingBound = bounds[lineInputs[0]]
                    if existingBound:
                        bounds[lineInputs[0]] = (max(existingBound[0],lb), min(existingBound[1],ub))
                    else:
                        bounds[lineInputs[0]] = (lb, ub)
                elif opt == '>0':
                    lb = -255
                    ub = 0
                    if lineOutputBound[0] > 0: lb = lineOutputBound[0]
                    if lineOutputBound[1] > 0: ub = lineOutputBound[1]
                    existingBound = bounds[lineInputs[0]]
                    if existingBound:
                        bounds[lineInputs[0]] = (max(existingBound[0],lb), min(existingBound[1],ub))
                    else:
                        bounds[lineInputs[0]] = (lb, ub)
                elif opt in ['%2==0', '%2==1']:
                    try:
                        existingBound = bounds[lineInputs[0]]
                        bounds[lineInputs[0]] = (max(existingBound[0], lineOutputBound[0]), min(existingBound[1], lineOutputBound[1]))
                    except:
                        bounds[lineInputs[0]] = lineOutputBound
            elif func == 'COUNT':
                # this one's tricky
                # the length of input matters, not the range
                existingBound = bounds[lineInputs[0]]
                if existingBound: pass
                else: bounds[lineInputs[0]] = (-255, 256)
            elif func == 'SUM':
                lb = int(np.ceil(lineOutputBound[0] / listLength))
                ub = int(np.floor(lineOutputBound[1] / listLength))
                existingBound = bounds[lineInputs[0]]
                if existingBound:
                    bounds[lineInputs[0]] = (max(existingBound[0], lb), min(existingBound[1], ub))
                else:
                    bounds[lineInputs[0]] = (lb, ub)
            elif func == 'MAP':
                if opt == '+1':
                    lb = max(lineOutputBound[0]-1, -255)
                    ub = min(lineOutputBound[1]-1, 256)
                elif opt == '-1':
                    lb = max(lineOutputBound[0]+1, -255)
                    ub = min(lineOutputBound[1]+1, 256)
                elif opt == '/2':
                    lb = max(lineOutputBound[0]*2, -255)
                    ub = min(lineOutputBound[1]*2, 256)
                elif opt == '*2':
                    if lineOutputBound[0] < 0:
                        lb = (lineOutputBound[0]//2)+1
                    else:
                        lb = (lineOutputBound[0]//2)
                    if lineOutputBound[1] < 0:
                        ub = (lineOutputBound[1]//2)+1
                    else:
                        ub = lineOutputBound[1]//2
                elif opt == '/3':
                    lb = max(lineOutputBound[0]*3, -255)
                    ub = min(lineOutputBound[1]*3, 256)
                elif opt == '*3':
                    if lineOutputBound[0] < 0:
                        lb = (lineOutputBound[0]//3)+1
                    else:
                        lb = (lineOutputBound[0]//3)
                    if lineOutputBound[1] < 0:
                        ub = (lineOutputBound[1]//3)+1
                    else:
                        ub = lineOutputBound[1]//3
                elif opt == '/4':
                    lb = max(lineOutputBound[0]*4, -255)
                    ub = min(lineOutputBound[1]*4, 256)
                elif opt == '*4':
                    if lineOutputBound[0] < 0:
                        lb = (lineOutputBound[0]//4)+1
                    else:
                        lb = (lineOutputBound[0]//4)
                    if lineOutputBound[1] < 0:
                        ub = (lineOutputBound[1]//4)+1
                    else:
                        ub = lineOutputBound[1]//4
                elif opt == '**2':
                    if lineOutputBound[1] < 0:
                        # impossible, so give empty range
                        lb = 1
                        ub = 0
                    else:
                        ub = int(np.sqrt(lineOutputBound[1]))
                        lb = -ub
                        if lineOutputBound[0] > 0:
                            # e.g. output at least 4, although -2 is fine, -1, 0 and 1 are not
                            # so have to take lower bound as +2
                            lb = int(np.ceil(np.sqrt(lineOutputBound[0])))
                elif opt == '*(-1)':
                    lb = -lineOutputBound[1]
                    ub = -lineOutputBound[0]
                existingBound = bounds[lineInputs[0]]
                if existingBound:
                    bounds[lineInputs[0]] = (max(existingBound[0], lb), min(existingBound[1], ub))
                else:
                    bounds[lineInputs[0]] = (lb, ub)
            elif func == 'ZIPWITH':
                if opt == '+':
                    lb = int(lineOutputBound[0]/2)
                    ub = int(lineOutputBound[1]/2)
                    if lineOutputBound[0] > 0:
                        lb = int(np.ceil(lineOutputBound[0]/2))
                    if lineOutputBound[1] < 0:
                        ub = int(np.floor(lineOutputBound[0]/2))
                elif opt == '-':
                    if lineOutputBound[0] > 0 or lineOutputBound[1] < 0:
                        # no safe range
                        lb = 1
                        ub = 0
                    else:
                        val = int(min(abs(lineOutputBound[0]), lineOutputBound[1])/2)
                        lb = -val
                        ub = val
                elif opt == '*':
                    if lineOutputBound[1] < 0:
                        # no safe range
                        lb = 1
                        ub = 0
                    else:
                        upper = int(np.sqrt(lineOutputBound[1]))
                        lower = int(np.ceil(np.sqrt(abs(lineOutputBound[0]))))
                        val = min(upper, lower)
                        lb = -val
                        ub = val
                elif opt in ['MAX', 'MIN']:
                    lb = lineOutputBound[0]
                    ub = lineOutputBound[1]
                bounds[lineInputs[0]] = (lb, ub)
                bounds[lineInputs[1]] = (lb, ub)
                existingBound1 = bounds[lineInputs[0]]
                existingBound2 = bounds[lineInputs[1]]
                if existingBound1:
                    bounds[lineInputs[0]] = (max(existingBound1[0], lb), min(existingBound1[1], ub))
                if existingBound2:
                    bounds[lineInputs[1]] = (max(existingBound2[0], lb), min(existingBound2[1], ub))
            elif func == 'SCANL1':
                if opt == '*':
                    if lineOutputBound[1] < 0:
                        # no safe range
                        lb = 1
                        ub = 0
                    else:
                        absbound = min(abs(lineOutputBound[0]), lineOutputBound[1])
                        val = int(absbound**(1/float(listLength)))
                        lb = -val
                        ub = val
                elif opt == '+':
                    if lineOutputBound[0] <= 0:
                        lb = int(lineOutputBound[0]/listLength)
                    else:
                        lb = int(np.ceil(lineOutputBound[0]/listLength))
                    if lineOutputBound[1] >= 0:
                        ub = int(lineOutputBound[1]/listLength)
                    else:
                        ub = int(np.floor(lineOutputBound[1]/listLength))
                elif opt == '-':
                    if lineOutputBound[0] > 0 or lineOutputBound[1] < 0:
                        # no safe range
                        lb = 1
                        ub = 0
                    else:
                        val = int(min(abs(lineOutputBound[0]), lineOutputBound[1])/listLength)
                        lb = -val
                        ub = val
                elif opt in ['MAX', 'MIN']:
                    lb = lineOutputBound[0]
                    ub = lineOutputBound[1]
                try:
                    existingBound = bounds[lineInputs[0]]
                    bounds[lineInputs[0]] = (max(existingBound[0], lb), min(existingBound[1], ub))
                except: bounds[lineInputs[0]] = (lb, ub)

        # check whether program inputs have been given empty range
        for b in bounds[-2:]:
            if b == None: continue
            if b[0] >= b[1]: return False

        return bounds[-2:][::-1]

    def getExamples(self, program):
        self.patience = 20
        resultSet = []

        for __ in range(self.number_per_program):
            tries = 0
            acceptExample = False
            programBounds = {}
            while tries < self.patience and not acceptExample:
                out = None

                listLengths = []
                for i in range(program.getNumberOfListInputs()):
                    listLengths.append(np.random.randint(1, high=self.max_list_length))

                # find safe range for each input
                # but don't recalculate if we've had this length before
                if programBounds.get(max(listLengths)) is None:
                    programBounds[max(listLengths)] = self.backPropagateValues(program, max(listLengths))
                bounds = programBounds[max(listLengths)]
                if not bounds:
                    tries += 1
                    continue

                # generate input values uniformly at random from safe range
                allInputs = []
                i = 0
                for n, programInput in enumerate(program.inputs):
                    if programInput.type is list:
                        inputLength = listLengths[i]
                        numbers = np.random.randint(bounds[n][0], high=bounds[n][1]+1, size=inputLength)
                        allInputs.append([int(val) for val in numbers])
                        i += 1
                    else:
                        allInputs.append(int(np.random.randint(bounds[n][0], high=bounds[n][1]+1)))

                # checks
                out = program.runWithChecks(allInputs, False)
                if isinstance(out, tuple):
                    out = list(out)
                if self.outIsSuitable(out, tries):
                    acceptExample = True
                tries += 1

            if acceptExample:
                resultSet.append((allInputs, out))

        return resultSet

class IOGeneratorExpSampling(IOGeneratorBase):
    def getExamples(self, program):
        self.patience = 500
        resultSet = []
        lamd = 0.0001

        probsTemp = [lamd*np.power(np.e, -k*lamd) for k in range(256)]
        probsum = sum(probsTemp)
        probsExp = [x/probsum for x in probsTemp]

        for __ in range(self.number_per_program):
            tries = 0
            acceptExample = False
            while (tries < self.patience) and not acceptExample:
                # to prevent harder problems only finding short list examples
                if tries % 100 == 0 or max(listLengths) < 3:
                    listLengths = []
                    for progIn in program.inputs:
                        if progIn.type == list:
                            listLengths.append(np.random.randint(1, high=self.max_list_length))

                maxVal = np.random.choice(256,p=probsExp)

                # generate input values uniformly at random from chosen range
                allInputs = []
                max_len = max(listLengths)
                i = 0
                for programInput in program.inputs:
                    if programInput.type is list:
                        inputLength = listLengths[i]
                        signs = [2*x - 1 for x in np.random.randint(2, size=inputLength)]
                        numbers = np.random.choice(maxVal+1, inputLength, p=None)
                        signedInput = np.multiply(signs, numbers)
                        allInputs.append([int(val) for val in signedInput])
                        i += 1
                    else:
                        allInputs.append(int(np.random.randint(-max_len, max_len)))

                out = program.runWithChecks(allInputs, False)
                if isinstance(out, tuple):
                    out = list(out)
                if self.outIsSuitable(out, tries):
                    acceptExample = True
                    resultSet.append((allInputs, out))
                tries += 1

        return resultSet

class IOGeneratorConstraintBased(IOGeneratorBase):
    def getExamples(self, program):
        return self.getExamplesfromZ3(program, self.number_per_program)

class IOGeneratorVaried(IOGeneratorBase):
    def getSampledIO(self, program, required):
        resultSet = []
        self.patience = 50
        maxVal = 256
        rateOfChange = np.ceil(self.patience/45)

        def updateSamplingRange(maxVal):
            if maxVal < 2: return maxVal
            if maxVal < 20: rangeStep = 1
            else: rangeStep = int((0.9)*maxVal)
            return maxVal - rangeStep

        # fix list length first
        listLengths = []
        for i, in_data in enumerate(program.inputs):
            if in_data.type == list:
                listLengths.append(np.random.randint(1, high=self.max_list_length))

        for __ in range(required):
            tries = 0
            acceptExample = False
            while (tries < self.patience) and not acceptExample:
                if tries > 0 and tries % rateOfChange == 0: maxVal = updateSamplingRange(maxVal)

                allInputs = []
                i=0
                for in_data in program.inputs:
                    if in_data.type == list:
                        inputLength = listLengths[i]
                        signs = np.random.randint(2, size=inputLength)
                        numbers = np.random.choice(maxVal+1, inputLength)
                        signedInput = np.multiply(np.multiply(signs, 2)-1, numbers)
                        allInputs.append([int(val) for val in signedInput])
                        i+=1
                    else:
                        allInputs.append(int(np.random.randint(-self.max_list_length, self.max_list_length)))

                # checks
                out = program.runWithChecks(allInputs, False)
                if isinstance(out, tuple):
                    out = list(out)
                if self.outIsSuitable(out, tries):
                    acceptExample = True
                tries += 1

            if acceptExample:
                resultSet.append((allInputs, out))

        return resultSet

    def equalInAndOut(self, example):
        same = False
        for ex_in in example[0]:
            if example[1] == ex_in:
                same = True
        return same

    def getExamples(self, program):
        condition = namedtuple('Condition', ['notNull', 'behaviours', 'updateFeature'])
        # sampledSet = self.getSampledIO(program, self.number_per_program)
        number_of_sets = self.number_per_program // self.examples_per_set
        sampledResults = [[]]*number_of_sets
        consRequired = [[]]*number_of_sets
        resultSets = [[]]*number_of_sets
        consResults = [[]]*number_of_sets

        for i in range(number_of_sets):
            # we get 3 examples because we're looking for sets of 5
            # should make this able to vary depending on size of exmaple sets
            sampledResults[i] = self.getSampledIO(program, 3)
            required = []
            allBehaviours = set()
            getNotNullExample = False
            allSame = True
            for ex in sampledResults[i]:
                output, behaviours = program.runAndCollectStats(ex[0])
                if len([1 for x in behaviours if x == [0,0,0,0,0]]) > 0:
                    getNotNullExample = True
                if self.equalInAndOut(ex) == False: allSame = False
                allBehaviours = allBehaviours | {behaviours}
            if getNotNullExample:
                required.append(condition(True, None, None))
            if allSame:
                required.append(None)
                # the sampled examples are really useless so get rid of one
                sampledResults[i] = sampledResults[i][:2]
            required.append(condition(False, tuple(allBehaviours), None))
            # TODO should we check max/min for int outputs also?
            update_feature = None
            if program.getOutputType() == list:
                max_out = -255
                min_out = 256
                max_len = 0
                for ex in sampledResults[i]:
                    if ex[1] != []:
                        if max(ex[1]) > max_out: max_out = max(ex[1])
                        if min(ex[1]) < min_out: min_out = min(ex[1])
                        if len(ex[1]) > max_len: max_len = len(ex[1])
                if max_out < 50 or min_out > -50:
                    if 255 - max_out > 255 + min_out: update_feature = "max"
                    else: update_feature = "min"
                if max_len < 4: update_feature = "len"
                required.append(condition(False, None, update_feature))
            if len(required) < 2:
                required.append(None)
            consRequired[i] = required

        allRequirements = [x for y in consRequired for x in y]
        excludeSet = [x for y in sampledResults for x in y][:len(allRequirements)]
        allConsResults = self.getExamplesfromZ3(program, len(allRequirements), excludeSet, allRequirements, True)

        extraRequiredCount = 0
        extraResults = []
        startIndex = 0
        for i in range(number_of_sets):
            endIndex = startIndex + len(consRequired[i])
            consResults[i] = [x for x in allConsResults[startIndex:endIndex] if x is not None]
            deficit = self.examples_per_set - (len(sampledResults[i]) + len(consResults[i]))
            extraRequiredCount += max(deficit, 0)
            if deficit >= 0:
                resultSets[i] = sampledResults[i] + consResults[i]
            else:
                num_cons = self.examples_per_set - len(sampledResults[i])
                resultSets[i] = sampledResults[i] + consResults[i][:num_cons]
                extraRequiredCount -= len(consResults[i][num_cons:])
                extraResults.append(consResults[i][num_cons:])
            startIndex = endIndex

        if extraRequiredCount > 0:
            extraResults = self.getExamplesfromZ3(program, extraRequiredCount, allConsResults)

        for i in range(number_of_sets):
            j = 0
            while len(resultSets[i]) < 5:
                try:
                    next = extraResults[j]
                    j += 1
                except:
                    # run out of results
                    next = self.getSampledIO(program, 1)
                resultSets[i].append(next)
            np.random.shuffle(resultSets[i])

        return [x for y in resultSets for x in y]

from z3 import *
import time
from z3Interface import z3BaseOracle

class z3InputsOracle(z3BaseOracle):
    def __init__(self, max_list_length, timeout = None):
        self.solver = Then(
            'propagate-values',
            'simplify',
            'reduce-bv-size',
            'solve-eqs',
            'bit-blast',
            'smt').solver()
        if timeout is not None:
            self.setTimeout(timeout)
        self.max_list_length = max_list_length

    def unsetProgram(self):
        self.solver.pop()

    def setOutput(self, output):
        if isinstance(output, int):
            self.solver.add(self.lineOutputs[self.outputIndex][0] == output)
        else:
            for i in range(len(output)):
                self.solver.add(self.lineOutputs[self.outputIndex][i] == output[i])
            self.solver.add(self.lineOutputLengths[self.outputIndex] == len(output))

    # program lines is a list of tuples (func, opt, input1Id, input2Id)
    # mode is 'none', 'basic', 'varied'
    def setProgram(self, numberOfInputs, intInputs, programLines, mode):
        self.numberOfLines = len(programLines)
        self.numberOfInputs = numberOfInputs
        self.outputIndex = self.numberOfLines - 1
        self.mode = mode
        self.solver.push()
        self.lineOutputs = []
        self.lineOutputLengths = []
        if (mode == 'varied'):
            self.linePreds = []
            self.watchedPreds = []

        for i in range(self.numberOfLines + self.numberOfInputs):
            self.lineOutputs.append(self.BitVectorVector('line'+str(i)+'Outputs', self.max_list_length))
            self.solver.add(self.bound_intvector(self.lineOutputs[i]))
            self.lineOutputLengths.append(BitVec('line'+str(i)+'OutLength', 32))
            self.solver.add(self.bound_int(self.lineOutputLengths[i], 0, self.max_list_length))

        # integer inputs are only useful for referencing list indices
        for ind in intInputs:
            self.solver.add(self.bound_int(self.lineOutputs[ind][0], -self.max_list_length, self.max_list_length))

        for i, line in enumerate(programLines):
            if (mode == 'varied'):
                temp_preds = []
                tp_2 = []
                for j in range(5):
                    name = 'p_'+str(i)+'_'+str(j)
                    temp_preds.append(Bool(name))
                    tp_2.append(Bool(name+'_watched'))
                    # self.linePreds[i][j] = Bool(name)
                self.linePreds.append(temp_preds)
                self.watchedPreds.append(tp_2)
            self.setLine(i, line[0], line[1], line[2], line[3])

    def setLine(self, lineNumber, lineFunction, lineOption, input1lineNumber, input2lineNumber):
        if lineFunction == 'MAP':
            self.setMap(lineNumber, lineOption, input1lineNumber)
        elif lineFunction == 'ZIPWITH':
            self.setZip(lineNumber, lineOption, input1lineNumber, input2lineNumber)
        elif lineFunction == 'SCANL1':
            self.setScan(lineNumber, lineOption, input1lineNumber)
        elif lineFunction == 'MAXIMUM':
            self.setMaximum(lineNumber, input1lineNumber)
        elif lineFunction == 'MINIMUM':
            self.setMinimum(lineNumber, input1lineNumber)
        elif lineFunction == 'FILTER':
            self.setFilter(lineNumber, lineOption, input1lineNumber)
        elif lineFunction == 'COUNT':
            self.setCount(lineNumber, lineOption, input1lineNumber)
        elif lineFunction == 'SORT':
            self.setSort(lineNumber, input1lineNumber)
        elif lineFunction == 'REVERSE':
            self.setReverse(lineNumber, input1lineNumber)
        elif lineFunction == 'HEAD':
            self.setHead(lineNumber, input1lineNumber)
        elif lineFunction == 'LAST':
            self.setLast(lineNumber, input1lineNumber)
        elif lineFunction == 'SUM':
            self.setSum(lineNumber, input1lineNumber)
        elif lineFunction == 'TAKE':
            self.setTake(lineNumber, input1lineNumber, input2lineNumber)
        elif lineFunction == 'DROP':
            self.setDrop(lineNumber, input1lineNumber, input2lineNumber)
        elif lineFunction == 'ACCESS':
            self.setAccess(lineNumber, input1lineNumber, input2lineNumber)

    # when we're not interested in tracking a feature for a line
    # slightly confusing method name - might be that this feature can't be changed by the line
    # or we might want to ignore it to force focus on another feature
    def setHeadIsFixed(self, lineNumber):
        if self.mode == 'varied':
            self.solver.add(self.watchedPreds[lineNumber][0] == False)

    def setTailIsFixed(self, lineNumber):
        if self.mode == 'varied':
            self.solver.add(self.watchedPreds[lineNumber][1] == False)

    def setMaxIsFixed(self, lineNumber):
        if self.mode == 'varied':
            self.solver.add(self.watchedPreds[lineNumber][2] == False)

    def setMinIsFixed(self, lineNumber):
        if self.mode == 'varied':
            self.solver.add(self.watchedPreds[lineNumber][3] == False)

    def setLengthIsFixed(self, lineNumber):
        if self.mode == 'varied':
            self.solver.add(self.watchedPreds[lineNumber][4] == False)

    def setHeadCanVary(self, lineNumber, input1lineNumber):
        if self.mode == 'varied':
            self.solver.add(Implies(
                self.linePreds[lineNumber][0],
                self.lineOutputs[input1lineNumber][0] != self.lineOutputs[lineNumber][0]
            ))
            self.solver.add(Implies(
                self.lineOutputs[input1lineNumber][0] != self.lineOutputs[lineNumber][0],
                self.linePreds[lineNumber][0]
            ))
            self.solver.add(Implies(
                And(
                    self.lineOutputLengths[input1lineNumber] == 0,
                    self.lineOutputLengths[lineNumber] == 0
                ),
                Not(self.linePreds[lineNumber][0])
            ))
            self.solver.add(Implies(
                Xor(
                    self.lineOutputLengths[input1lineNumber] == 0,
                    self.lineOutputLengths[lineNumber] == 0
                ),
                self.linePreds[lineNumber][0]
            ))

    def setTailCanVary(self, lineNumber, input1lineNumber):
        if self.mode == 'varied':
            for j in range(self.max_list_length):
                for k in range(self.max_list_length):
                    self.solver.add(Implies(
                        And(
                            j == self.lineOutputLengths[input1lineNumber] - 1,
                            k == self.lineOutputLengths[lineNumber] - 1
                        ),
                        Implies(
                            self.linePreds[lineNumber][1],
                            self.lineOutputs[input1lineNumber][j] != self.lineOutputs[lineNumber][k]
                        )
                    ))
                    self.solver.add(Implies(
                        And(
                            j == self.lineOutputLengths[input1lineNumber] - 1,
                            k == self.lineOutputLengths[lineNumber] - 1
                        ),
                        Implies(
                            self.lineOutputs[input1lineNumber][j] != self.lineOutputs[lineNumber][k],
                            self.linePreds[lineNumber][1]
                        )
                    ))
                    self.solver.add(Implies(
                        And(
                            self.lineOutputLengths[input1lineNumber] == 0,
                            self.lineOutputLengths[lineNumber] == 0
                        ),
                        Not(self.linePreds[lineNumber][1])
                    ))
                    self.solver.add(Implies(
                        Xor(
                            self.lineOutputLengths[input1lineNumber] == 0,
                            self.lineOutputLengths[lineNumber] == 0
                        ),
                        self.linePreds[lineNumber][1]
                    ))

    def setMaxCanVary(self, lineNumber, input1lineNumber):
        if self.mode == 'varied':
            local_max_out = BitVec('line'+str(lineNumber)+'max', 32)
            local_max_in = BitVec('line'+str(input1lineNumber)+'max', 32)
            self.solver.add(self.bound_int(local_max_out))
            self.solver.add(self.bound_int(local_max_in))
            eqCons = []
            for k in range(self.max_list_length):
                self.solver.add(Implies(
                    k < self.lineOutputLengths[input1lineNumber],
                    local_max_in >= self.lineOutputs[input1lineNumber][k]
                ))
                # as a side effect this will force the input not to be empty
                # but that's generally desirable, so I've allowed it
                eqCons.append(And(
                    local_max_in == self.lineOutputs[input1lineNumber][k],
                    k < self.lineOutputLengths[input1lineNumber]
                ))
            self.solver.add(Or(*eqCons))
            eqCons = []
            for k in range(self.max_list_length):
                self.solver.add(Implies(
                    k < self.lineOutputLengths[lineNumber],
                    local_max_out >= self.lineOutputs[lineNumber][k]
                ))
                # as above, this will force the output to not be empty. Seems fine.
                eqCons.append(And(
                    local_max_out == self.lineOutputs[lineNumber][k],
                    k < self.lineOutputLengths[lineNumber]
                ))
            self.solver.add(Or(*eqCons))

            self.solver.add(Implies(
                self.linePreds[lineNumber][2],
                local_max_in != local_max_out
            ))
            self.solver.add(Implies(
                local_max_in != local_max_out,
                self.linePreds[lineNumber][2]
            ))

    def setMinCanVary(self, lineNumber, input1lineNumber):
        if self.mode == 'varied':
            local_min_out = BitVec('line'+str(lineNumber)+'min', 32)
            local_min_in = BitVec('line'+str(input1lineNumber)+'min', 32)
            self.solver.add(self.bound_int(local_min_out))
            self.solver.add(self.bound_int(local_min_in))
            eqCons = []
            for k in range(self.max_list_length):
                self.solver.add(Implies(
                    k < self.lineOutputLengths[input1lineNumber],
                    local_min_in >= self.lineOutputs[input1lineNumber][k]
                ))
                # as a side effect this will force the input not to be empty
                # but that's generally desirable, so I've allowed it
                eqCons.append(And(
                    local_min_in == self.lineOutputs[input1lineNumber][k],
                    k < self.lineOutputLengths[input1lineNumber]
                ))
            self.solver.add(Or(*eqCons))
            eqCons = []
            for k in range(self.max_list_length):
                self.solver.add(Implies(
                    k < self.lineOutputLengths[lineNumber],
                    local_min_out >= self.lineOutputs[lineNumber][k]
                ))
                # as above, this will force the output to not be empty. Seems fine.
                eqCons.append(And(
                    local_min_out == self.lineOutputs[lineNumber][k],
                    k < self.lineOutputLengths[lineNumber]
                ))
            self.solver.add(Or(*eqCons))

            self.solver.add(Implies(
                self.linePreds[lineNumber][3],
                local_min_in != local_min_out
            ))
            self.solver.add(Implies(
                local_min_in != local_min_out,
                self.linePreds[lineNumber][3]
            ))


    def setLengthCanVary(self, lineNumber, input1lineNumber):
        if self.mode == 'varied':
            self.solver.add(Implies(
                self.linePreds[lineNumber][4],
                self.lineOutputLengths[lineNumber] != self.lineOutputLengths[input1lineNumber]
            ))
            self.solver.add(Implies(
                self.lineOutputLengths[lineNumber] != self.lineOutputLengths[input1lineNumber],
                self.linePreds[lineNumber][4]
            ))

    def setMap(self, lineNumber, lineOption, input1lineNumber):
        self.solver.add(self.lineOutputLengths[lineNumber] == self.lineOutputLengths[input1lineNumber])
        self.setLengthIsFixed(lineNumber)
        if lineOption == '+1':
            for k in range(self.max_list_length):
                self.solver.add(Implies(
                    k < self.lineOutputLengths[input1lineNumber],
                    self.lineOutputs[lineNumber][k] == self.lineOutputs[input1lineNumber][k] + 1
                ))
            # so we can satisfy not null behaviour constraint
            self.setHeadCanVary(lineNumber, input1lineNumber)
            self.setTailIsFixed(lineNumber)
            self.setMaxIsFixed(lineNumber)
            self.setMinIsFixed(lineNumber)
        if lineOption == '-1':
            for k in range(self.max_list_length):
                self.solver.add(Implies(
                    k < self.lineOutputLengths[input1lineNumber],
                    self.lineOutputs[lineNumber][k] == self.lineOutputs[input1lineNumber][k] - 1
                ))
            self.setHeadCanVary(lineNumber, input1lineNumber)
            self.setTailIsFixed(lineNumber)
            self.setMaxIsFixed(lineNumber)
            self.setMinIsFixed(lineNumber)
        if lineOption == '*2':
            for k in range(self.max_list_length):
                self.solver.add(Implies(
                    k < self.lineOutputLengths[input1lineNumber],
                    self.lineOutputs[lineNumber][k] == self.lineOutputs[input1lineNumber][k] * 2
                ))
            # change of values depends on whether they were zero at input
            self.setHeadIsFixed(lineNumber)
            self.setTailIsFixed(lineNumber)
            self.setMaxCanVary(lineNumber, input1lineNumber)
            self.setMinCanVary(lineNumber, input1lineNumber)
        if lineOption == '/2':
            for k in range(self.max_list_length):
                self.solver.add(Implies(
                    And(
                        k < self.lineOutputLengths[input1lineNumber],
                        Or(
                            self.lineOutputs[input1lineNumber][k] >= 0,
                            self.lineOutputs[input1lineNumber][k] % 2 == 0
                        )
                    ),
                    self.lineOutputs[lineNumber][k] == self.lineOutputs[input1lineNumber][k] / 2
                ))
                self.solver.add(Implies(
                    And(
                        k < self.lineOutputLengths[input1lineNumber],
                        self.lineOutputs[input1lineNumber][k] < 0,
                        self.lineOutputs[input1lineNumber][k] % 2 != 0
                    ),
                    self.lineOutputs[lineNumber][k] == (self.lineOutputs[input1lineNumber][k] / 2) - 1
                ))
            self.setHeadIsFixed(lineNumber)
            self.setTailIsFixed(lineNumber)
            self.setMaxCanVary(lineNumber, input1lineNumber)
            self.setMinCanVary(lineNumber, input1lineNumber)
        if lineOption == '*3':
            for k in range(self.max_list_length):
                self.solver.add(Implies(
                    k < self.lineOutputLengths[input1lineNumber],
                    self.lineOutputs[lineNumber][k] == self.lineOutputs[input1lineNumber][k] * 3
                ))
            self.setHeadIsFixed(lineNumber)
            self.setTailIsFixed(lineNumber)
            self.setMaxCanVary(lineNumber, input1lineNumber)
            self.setMinCanVary(lineNumber, input1lineNumber)
        if lineOption == '/3':
            for k in range(self.max_list_length):
                self.solver.add(Implies(
                    And(
                        k < self.lineOutputLengths[input1lineNumber],
                        Or(
                            self.lineOutputs[input1lineNumber][k] >= 0,
                            self.lineOutputs[input1lineNumber][k] % 3 == 0
                        )
                    ),
                    self.lineOutputs[lineNumber][k] == self.lineOutputs[input1lineNumber][k] / 3
                ))
                self.solver.add(Implies(
                    And(
                        k < self.lineOutputLengths[input1lineNumber],
                        self.lineOutputs[input1lineNumber][k] < 0,
                        self.lineOutputs[input1lineNumber][k] % 3 != 0
                    ),
                    self.lineOutputs[lineNumber][k] == (self.lineOutputs[input1lineNumber][k] / 3) - 1
                ))
            self.setHeadIsFixed(lineNumber)
            self.setTailIsFixed(lineNumber)
            self.setMaxCanVary(lineNumber, input1lineNumber)
            self.setMinCanVary(lineNumber, input1lineNumber)
        if lineOption == '*4':
            for k in range(self.max_list_length):
                self.solver.add(Implies(
                    k < self.lineOutputLengths[input1lineNumber],
                    self.lineOutputs[lineNumber][k] == self.lineOutputs[input1lineNumber][k] * 4
                ))
            self.setHeadIsFixed(lineNumber)
            self.setTailIsFixed(lineNumber)
            self.setMaxCanVary(lineNumber, input1lineNumber)
            self.setMinCanVary(lineNumber, input1lineNumber)
        if lineOption == '/4':
            for k in range(self.max_list_length):
                self.solver.add(Implies(
                    And(
                        k < self.lineOutputLengths[input1lineNumber],
                        Or(
                            self.lineOutputs[input1lineNumber][k] >= 0,
                            self.lineOutputs[input1lineNumber][k] % 4 == 0
                        )
                    ),
                    self.lineOutputs[lineNumber][k] == self.lineOutputs[input1lineNumber][k] / 4
                ))
                self.solver.add(Implies(
                    And(
                        k < self.lineOutputLengths[input1lineNumber],
                        self.lineOutputs[input1lineNumber][k] < 0,
                        self.lineOutputs[input1lineNumber][k] % 4 != 0
                    ),
                    self.lineOutputs[lineNumber][k] == (self.lineOutputs[input1lineNumber][k] / 4) - 1
                ))
            self.setHeadIsFixed(lineNumber)
            self.setTailIsFixed(lineNumber)
            self.setMaxCanVary(lineNumber, input1lineNumber)
            self.setMinCanVary(lineNumber, input1lineNumber)
        if lineOption == '**2':
            for k in range(self.max_list_length):
                self.solver.add(Implies(
                    k < self.lineOutputLengths[input1lineNumber],
                    self.lineOutputs[lineNumber][k] == self.lineOutputs[input1lineNumber][k] * self.lineOutputs[input1lineNumber][k]
                ))
            self.setHeadIsFixed(lineNumber)
            self.setTailIsFixed(lineNumber)
            self.setMaxCanVary(lineNumber, input1lineNumber)
            self.setMinCanVary(lineNumber, input1lineNumber)
        if lineOption == '*(-1)':
            for k in range(self.max_list_length):
                self.solver.add(Implies(
                    k < self.lineOutputLengths[input1lineNumber],
                    self.lineOutputs[lineNumber][k] == self.lineOutputs[input1lineNumber][k] * -1
                ))
            self.setHeadIsFixed(lineNumber)
            self.setTailIsFixed(lineNumber)
            self.setMaxCanVary(lineNumber, input1lineNumber)
            self.setMinCanVary(lineNumber, input1lineNumber)

    def setZip(self, lineNumber, lineOption, input1lineNumber, input2lineNumber):
        self.setLengthIsFixed(lineNumber)
        self.setHeadIsFixed(lineNumber)
        self.setTailIsFixed(lineNumber)
        self.setMaxCanVary(lineNumber, input1lineNumber)
        self.setMinCanVary(lineNumber, input1lineNumber)
        self.solver.add(
            Or(
                self.lineOutputLengths[lineNumber] == self.lineOutputLengths[input1lineNumber],
                self.lineOutputLengths[lineNumber] == self.lineOutputLengths[input2lineNumber]
            )
        )
        self.solver.add(
            self.lineOutputLengths[lineNumber] <= self.lineOutputLengths[input1lineNumber]
        )
        self.solver.add(
            self.lineOutputLengths[lineNumber] <= self.lineOutputLengths[input2lineNumber]
        )
        if lineOption == '+':
            for k in range(self.max_list_length):
                self.solver.add(Implies(
                    And(k < self.lineOutputLengths[input1lineNumber], k < self.lineOutputLengths[input2lineNumber]),
                    self.lineOutputs[lineNumber][k] == self.lineOutputs[input1lineNumber][k] + self.lineOutputs[input2lineNumber][k]
                ))
        elif lineOption == '*':
            for k in range(self.max_list_length):
                self.solver.add(Implies(
                    k < self.lineOutputLengths[lineNumber],
                    self.lineOutputs[lineNumber][k] == self.lineOutputs[input1lineNumber][k] * self.lineOutputs[input2lineNumber][k]
                ))
        elif lineOption == '-':
            for k in range(self.max_list_length):
                self.solver.add(Implies(
                    k < self.lineOutputLengths[lineNumber],
                    self.lineOutputs[lineNumber][k] == self.lineOutputs[input1lineNumber][k] - self.lineOutputs[input2lineNumber][k]
                ))
        elif lineOption == 'MAX':
            for k in range(self.max_list_length):
                self.solver.add(Implies(
                    k < self.lineOutputLengths[lineNumber],
                    And(
                        Or(
                            self.lineOutputs[lineNumber][k] == self.lineOutputs[input1lineNumber][k],
                            self.lineOutputs[lineNumber][k] == self.lineOutputs[input2lineNumber][k],
                        ),
                        self.lineOutputs[lineNumber][k] >= self.lineOutputs[input1lineNumber][k],
                        self.lineOutputs[lineNumber][k] >= self.lineOutputs[input2lineNumber][k]
                    )
                ))
        elif lineOption == 'MIN':
            for k in range(self.max_list_length):
                self.solver.add(Implies(
                    k < self.lineOutputLengths[lineNumber],
                    And(
                        Or(
                            self.lineOutputs[lineNumber][k] == self.lineOutputs[input1lineNumber][k],
                            self.lineOutputs[lineNumber][k] == self.lineOutputs[input2lineNumber][k],
                        ),
                        self.lineOutputs[lineNumber][k] <= self.lineOutputs[input1lineNumber][k],
                        self.lineOutputs[lineNumber][k] <= self.lineOutputs[input2lineNumber][k]
                    )
                ))

    def setScan(self, lineNumber, lineOption, input1lineNumber):
        self.setLengthIsFixed(lineNumber)
        self.setHeadIsFixed(lineNumber)
        self.setTailCanVary(lineNumber, input1lineNumber)
        self.solver.add(
            self.lineOutputLengths[lineNumber] == self.lineOutputLengths[input1lineNumber]
        )
        self.solver.add(self.lineOutputs[lineNumber][0] == self.lineOutputs[input1lineNumber][0])
        if lineOption == '+':
            for k in range(1, self.max_list_length):
                self.solver.add(Implies(
                    k < self.lineOutputLengths[input1lineNumber],
                    self.lineOutputs[lineNumber][k] == self.lineOutputs[lineNumber][k-1] + self.lineOutputs[input1lineNumber][k]
                ))
            self.setMaxCanVary(lineNumber, input1lineNumber)
            self.setMinCanVary(lineNumber, input1lineNumber)
        if lineOption == '*':
            for k in range(1, self.max_list_length):
                self.solver.add(Implies(
                    k < self.lineOutputLengths[input1lineNumber],
                    self.lineOutputs[lineNumber][k] == self.lineOutputs[lineNumber][k-1] * self.lineOutputs[input1lineNumber][k]
                ))
            self.setMaxCanVary(lineNumber, input1lineNumber)
            self.setMinCanVary(lineNumber, input1lineNumber)
        if lineOption == '-':
            for k in range(1, self.max_list_length):
                self.solver.add(Implies(
                    k < self.lineOutputLengths[input1lineNumber],
                    self.lineOutputs[lineNumber][k] == self.lineOutputs[lineNumber][k-1] - self.lineOutputs[input1lineNumber][k]
                ))
            self.setMaxCanVary(lineNumber, input1lineNumber)
            self.setMinCanVary(lineNumber, input1lineNumber)
        if lineOption == 'MAX':
            for k in range(1, self.max_list_length):
                self.solver.add(Implies(
                    k < self.lineOutputLengths[input1lineNumber],
                    And(
                        Or(
                            self.lineOutputs[lineNumber][k] == self.lineOutputs[lineNumber][k-1],
                            self.lineOutputs[lineNumber][k] == self.lineOutputs[input1lineNumber][k]
                        ),
                        self.lineOutputs[lineNumber][k] >= self.lineOutputs[lineNumber][k-1],
                        self.lineOutputs[lineNumber][k] >= self.lineOutputs[input1lineNumber][k]
                    )
                ))
            self.setMaxIsFixed(lineNumber)
            self.setMinIsFixed(lineNumber)
        if lineOption == 'MIN':
            for k in range(1, self.max_list_length):
                self.solver.add(Implies(
                    k < self.lineOutputLengths[input1lineNumber],
                    And(
                        Or(
                            self.lineOutputs[lineNumber][k] == self.lineOutputs[lineNumber][k-1],
                            self.lineOutputs[lineNumber][k] == self.lineOutputs[input1lineNumber][k]
                        ),
                        self.lineOutputs[lineNumber][k] <= self.lineOutputs[lineNumber][k-1],
                        self.lineOutputs[lineNumber][k] <= self.lineOutputs[input1lineNumber][k]
                    )
                ))
            self.setMaxIsFixed(lineNumber)
            self.setMinIsFixed(lineNumber)

    def setMaximum(self, lineNumber, input1lineNumber):
        self.setLengthIsFixed(lineNumber)
        self.setHeadCanVary(lineNumber, input1lineNumber)
        self.setTailCanVary(lineNumber, input1lineNumber)
        self.setMaxIsFixed(lineNumber)
        self.setMinIsFixed(lineNumber)
        self.solver.add(self.lineOutputLengths[lineNumber] == 1)
        eqCons = []
        for k in range(self.max_list_length):
            self.solver.add(Implies(
                k < self.lineOutputLengths[input1lineNumber],
                self.lineOutputs[lineNumber][0] >= self.lineOutputs[input1lineNumber][k]
            ))
            eqCons.append(And(self.lineOutputs[lineNumber][0] == self.lineOutputs[input1lineNumber][k], k < self.lineOutputLengths[input1lineNumber]))
        self.solver.add(Or(*eqCons))
        # output is an integer, integers are only useful within he length of the lists, unless it's the output
        if lineNumber != self.outputIndex:
            self.solver.add(self.bound_int(self.lineOutputs[lineNumber][0], -self.max_list_length, self.max_list_length))

    def setMinimum(self, lineNumber, input1lineNumber):
        self.setLengthIsFixed(lineNumber)
        self.setHeadCanVary(lineNumber, input1lineNumber)
        self.setTailCanVary(lineNumber, input1lineNumber)
        self.setMaxIsFixed(lineNumber)
        self.setMinIsFixed(lineNumber)
        self.solver.add(self.lineOutputLengths[lineNumber] == 1)
        eqCons = []
        for k in range(self.max_list_length):
            self.solver.add(Implies(
                k < self.lineOutputLengths[input1lineNumber],
                self.lineOutputs[lineNumber][0] <= self.lineOutputs[input1lineNumber][k]
            ))
            eqCons.append(And(self.lineOutputs[lineNumber][0] == self.lineOutputs[input1lineNumber][k], k < self.lineOutputLengths[input1lineNumber]))
        self.solver.add(Or(*eqCons))
        # output is an integer, integers are only useful within he length of the lists, unless it's the output
        if lineNumber != self.outputIndex:
            self.solver.add(self.bound_int(self.lineOutputs[lineNumber][0], -self.max_list_length, self.max_list_length))

    def setFilter(self, lineNumber, lineOption, input1lineNumber):
        self.setLengthCanVary(lineNumber, input1lineNumber)
        self.setHeadCanVary(lineNumber, input1lineNumber)
        self.setTailCanVary(lineNumber, input1lineNumber)
        self.setMaxIsFixed(lineNumber)
        self.setMinIsFixed(lineNumber)

        filterMap = self.BitVectorVector('filterMap_'+str(lineNumber), self.max_list_length)
        self.solver.add(self.bound_intvector(filterMap, 0, self.max_list_length))
        filterCount = self.BitVectorVector('filterCount_'+str(lineNumber), self.max_list_length)
        self.solver.add(self.bound_intvector(filterCount, 0, 1))

        self.solver.add(self.lineOutputLengths[lineNumber] == Sum(filterCount))

        for k in range(self.max_list_length):
            self.solver.add(Implies(
                filterCount[k] == 1,
                filterMap[k] < self.lineOutputLengths[lineNumber]
            ))
            self.solver.add(Implies(
                k >= self.lineOutputLengths[input1lineNumber],
                filterCount[k] == 0
            ))
            for l in range(self.max_list_length):
                self.solver.add(Implies(
                    And(filterCount[k] == 1, filterMap[k] == l),
                    self.lineOutputs[lineNumber][l] == self.lineOutputs[input1lineNumber][k]
                ))
                self.solver.add(Implies(
                    And(
                        filterCount[k] == 1,
                        filterCount[l] == 1,
                        k < l
                    ),
                    filterMap[k] < filterMap[l]
                ))

        if lineOption == '<0':
            for k in range(self.max_list_length):
                # if the value at this position is of interest (active range & satisfies condition) then map into new active range. without repetition & note its inclusion in filterCount
                self.solver.add(Implies(
                    And(
                        k < self.lineOutputLengths[input1lineNumber],
                        self.lineOutputs[input1lineNumber][k] < 0
                    ),
                    filterCount[k] == 1
                ))
                # if this position is not of interest then record this negative result in filterCount
                self.solver.add(Implies(
                    self.lineOutputs[input1lineNumber][k] >= 0,
                    filterCount[k] == 0
                ))
        if lineOption == '>0':
            for k in range(self.max_list_length):
                # if the value at this position is of interest (active range & satisfies condition) then map into new active range. without repetition & note its inclusion in filterCount
                self.solver.add(Implies(
                    And(
                        k < self.lineOutputLengths[input1lineNumber],
                        self.lineOutputs[input1lineNumber][k] > 0
                    ),
                    filterCount[k] == 1
                ))
                # if this position is not of interest then record this negative result in filterCount
                self.solver.add(Implies(
                    self.lineOutputs[input1lineNumber][k] <= 0,
                    filterCount[k] == 0
                ))
        if lineOption == '%2==0':
            for k in range(self.max_list_length):
                # if the value at this position is of interest (active range & satisfies condition) then map into new active range. without repetition & note its inclusion in filterCount
                self.solver.add(Implies(
                    And(
                        k < self.lineOutputLengths[input1lineNumber],
                        self.lineOutputs[input1lineNumber][k] % 2 == 0
                    ),
                    filterCount[k] == 1
                ))
                # if this position is not of interest then record this negative result in filterCount
                self.solver.add(Implies(
                    self.lineOutputs[input1lineNumber][k] % 2 == 1,
                    filterCount[k] == 0
                ))
        if lineOption == '%2==1':
            for k in range(self.max_list_length):
                # if the value at this position is of interest (active range & satisfies condition) then map into new active range. without repetition & note its inclusion in filterCount
                self.solver.add(Implies(
                    And(
                        k < self.lineOutputLengths[input1lineNumber],
                        self.lineOutputs[input1lineNumber][k] % 2 == 1
                    ),
                    filterCount[k] == 1
                ))
                # if this position is not of interest then record this negative result in filterCount
                self.solver.add(Implies(
                    self.lineOutputs[input1lineNumber][k] % 2 == 0,
                    filterCount[k] == 0
                ))

    def setCount(self, lineNumber, lineOption, input1lineNumber):
        self.setLengthIsFixed(lineNumber)
        self.setHeadCanVary(lineNumber, input1lineNumber)
        self.setTailCanVary(lineNumber, input1lineNumber)
        self.setMaxIsFixed(lineNumber)
        self.setMinIsFixed(lineNumber)
        filterCount = self.BitVectorVector('filterCount_'+str(lineNumber), self.max_list_length)
        self.solver.add(self.bound_intvector(filterCount, 0, 1))

        self.solver.add(self.lineOutputLengths[lineNumber] == 1)
        self.solver.add(self.lineOutputs[lineNumber][0] == Sum(filterCount))

        if lineOption == '<0':
            for k in range(self.max_list_length):
                self.solver.add(Implies(
                    And(
                        k < self.lineOutputLengths[input1lineNumber],
                        self.lineOutputs[input1lineNumber][k] < 0
                    ),
                    filterCount[k] == 1
                ))
                self.solver.add(Implies(
                    k >= self.lineOutputLengths[input1lineNumber],
                    filterCount[k] == 0
                ))
                self.solver.add(Implies(
                    self.lineOutputs[input1lineNumber][k] >= 0,
                    filterCount[k] == 0
                ))
        if lineOption == '>0':
            for k in range(self.max_list_length):
                self.solver.add(Implies(
                    And(
                        k < self.lineOutputLengths[input1lineNumber],
                        self.lineOutputs[input1lineNumber][k] > 0
                    ),
                    filterCount[k] == 1
                ))
                self.solver.add(Implies(
                    k >= self.lineOutputLengths[input1lineNumber],
                    filterCount[k] == 0
                ))
                self.solver.add(Implies(
                    self.lineOutputs[input1lineNumber][k] <= 0,
                    filterCount[k] == 0
                ))
        if lineOption == '%2==0':
            for k in range(self.max_list_length):
                self.solver.add(Implies(
                    And(
                        k < self.lineOutputLengths[input1lineNumber],
                        self.lineOutputs[input1lineNumber][k] % 2 == 0
                    ),
                    filterCount[k] == 1
                ))
                self.solver.add(Implies(
                    k >= self.lineOutputLengths[input1lineNumber],
                    filterCount[k] == 0
                ))
                self.solver.add(Implies(
                    self.lineOutputs[input1lineNumber][k] % 2 == 1,
                    filterCount[k] == 0
                ))
        if lineOption == '%2==1':
            for k in range(self.max_list_length):
                self.solver.add(Implies(
                    And(
                        k < self.lineOutputLengths[input1lineNumber],
                        self.lineOutputs[input1lineNumber][k] % 2 == 1
                    ),
                    filterCount[k] == 1
                ))
                self.solver.add(Implies(
                    k >= self.lineOutputLengths[input1lineNumber],
                    filterCount[k] == 0
                ))
                self.solver.add(Implies(
                    self.lineOutputs[input1lineNumber][k] % 2 == 0,
                    filterCount[k] == 0
                ))
        # output is an integer, integers are only useful within he length of the lists, unless it's the output
        if lineNumber != self.outputIndex:
            self.solver.add(self.bound_int(self.lineOutputs[lineNumber][0], -self.max_list_length, self.max_list_length))

    def setSort(self, lineNumber, input1lineNumber):
        self.setLengthIsFixed(lineNumber)
        self.setHeadCanVary(lineNumber, input1lineNumber)
        self.setTailCanVary(lineNumber, input1lineNumber)
        self.setMaxIsFixed(lineNumber)
        self.setMinIsFixed(lineNumber)
        # "sortMap[k] = l" means that position k of input goes to position l of output
        # want this map to be a bijection within the active range of the list i.e. for k < inputlength[i]
        self.sortMap = self.BitVectorVector('sortMap_'+str(lineNumber), self.max_list_length)
        self.solver.add(self.bound_intvector(self.sortMap, 0, self.max_list_length))
        self.solver.add(self.lineOutputLengths[lineNumber] == self.lineOutputLengths[input1lineNumber])

        for k in range(self.max_list_length):
            # if in active range then must map to active range
            self.solver.add(Implies(
                k < self.lineOutputLengths[input1lineNumber],
                self.sortMap[k] < self.lineOutputLengths[input1lineNumber]
            ))
            for l in range(self.max_list_length):
                if k != l:
                    # different positions of input (within active range) must map to different positions of output
                    # within the active range, our mapping must respect ordering of values - i.e. it sorts, rather than being just an arbitrary bijection
                    self.solver.add(Implies(
                        And(
                            k < self.lineOutputLengths[input1lineNumber],
                            l < self.lineOutputLengths[input1lineNumber]
                        ),
                        And(
                            self.sortMap[k] != self.sortMap[l],
                            Implies(self.lineOutputs[input1lineNumber][k] < self.lineOutputs[input1lineNumber][l], self.sortMap[k] < self.sortMap[l])
                        )
                    ))
                # having decided a suitable mapping, this fixes the values at each position in (the active range of) the output list
                self.solver.add(Implies(
                    And(
                        k < self.lineOutputLengths[input1lineNumber],
                        self.sortMap[k] == l
                    ),
                    self.lineOutputs[lineNumber][l] == self.lineOutputs[input1lineNumber][k]
                ))

    def setReverse(self, lineNumber, input1lineNumber):
        self.setLengthIsFixed(lineNumber)
        self.setHeadCanVary(lineNumber, input1lineNumber)
        self.setTailCanVary(lineNumber, input1lineNumber)
        self.setMaxIsFixed(lineNumber)
        self.setMinIsFixed(lineNumber)
        self.solver.add(self.lineOutputLengths[lineNumber] == self.lineOutputLengths[input1lineNumber])
        for k in range(self.max_list_length):
            self.solver.add(Implies(
                k < self.lineOutputLengths[input1lineNumber],
                self.getElement(self.lineOutputs[lineNumber][k], self.lineOutputs[input1lineNumber], self.lineOutputLengths[input1lineNumber] - k - 1)
            ))

    def setHead(self, lineNumber, input1lineNumber):
        self.setLengthCanVary(lineNumber, input1lineNumber)
        self.setHeadIsFixed(lineNumber)
        self.setTailCanVary(lineNumber, input1lineNumber)
        self.setMaxIsFixed(lineNumber)
        self.setMinIsFixed(lineNumber)
        self.solver.add(Implies(
            self.lineOutputLengths[input1lineNumber] == 0,
            self.lineOutputLengths[lineNumber] == 0
        ))
        self.solver.add(Implies(
            self.lineOutputLengths[input1lineNumber] > 0,
            self.lineOutputLengths[lineNumber] == 1
        ))

        self.solver.add(Implies(
            self.lineOutputLengths[input1lineNumber] > 0,
            self.lineOutputs[lineNumber][0] == self.lineOutputs[input1lineNumber][0]
        ))
        # output is an integer, integers are only useful within he length of the lists, unless it's the output
        if lineNumber != self.outputIndex:
            self.solver.add(self.bound_int(self.lineOutputs[lineNumber][0], -self.max_list_length, self.max_list_length))

    def setLast(self, lineNumber, input1lineNumber):
        self.setLengthCanVary(lineNumber, input1lineNumber)
        self.setHeadCanVary(lineNumber, input1lineNumber)
        self.setTailIsFixed(lineNumber)
        self.setMaxIsFixed(lineNumber)
        self.setMinIsFixed(lineNumber)
        self.solver.add(Implies(
            self.lineOutputLengths[input1lineNumber] == 0,
            self.lineOutputLengths[lineNumber] == 0
        ))
        self.solver.add(Implies(
            self.lineOutputLengths[input1lineNumber] > 0,
            self.lineOutputLengths[lineNumber] == 1
        ))

        for k in range(self.max_list_length):
            self.solver.add(Implies(
                k == self.lineOutputLengths[input1lineNumber] - 1,
                self.lineOutputs[lineNumber][0] == self.lineOutputs[input1lineNumber][k]
            ))
        # output is an integer, integers are only useful within he length of the lists, unless it's the output
        if lineNumber != self.outputIndex:
            self.solver.add(self.bound_int(self.lineOutputs[lineNumber][0], -self.max_list_length, self.max_list_length))

    def setSum(self, lineNumber, input1lineNumber):
        self.setLengthIsFixed(lineNumber)
        self.setHeadCanVary(lineNumber, input1lineNumber)
        self.setTailCanVary(lineNumber, input1lineNumber)
        self.setMaxIsFixed(lineNumber)
        self.setMinIsFixed(lineNumber)
        self.solver.add(self.lineOutputs[lineNumber][0] == Sum(self.lineOutputs[input1lineNumber]))
        self.solver.add(self.lineOutputLengths[lineNumber] == 1)

        for k in range(self.max_list_length):
            self.solver.add(Implies(
                k >= self.lineOutputLengths[input1lineNumber],
                self.lineOutputs[input1lineNumber][k] == 0
            ))
        # output is an integer, integers are only useful within he length of the lists, unless it's the output
        if lineNumber != self.outputIndex:
            self.solver.add(self.bound_int(self.lineOutputs[lineNumber][0], -self.max_list_length, self.max_list_length))

    def setTake(self, lineNumber, input1lineNumber, input2lineNumber):
        self.setLengthCanVary(lineNumber, input2lineNumber)
        self.setHeadIsFixed(lineNumber)
        self.setTailCanVary(lineNumber, input2lineNumber)
        self.setMaxIsFixed(lineNumber)
        self.setMinIsFixed(lineNumber)
        self.solver.add(Or(self.lineOutputLengths[input1lineNumber] == 0, self.lineOutputLengths[input1lineNumber] == 1))
        self.solver.add(Implies(
            And(
                self.lineOutputLengths[input1lineNumber] == 1,
                self.lineOutputs[input1lineNumber][0] >= 0
            ),
            And(
                self.lineOutputLengths[lineNumber] <= self.lineOutputLengths[input2lineNumber],
                self.lineOutputLengths[lineNumber] <= self.lineOutputs[input1lineNumber][0],
                Or(
                    self.lineOutputLengths[lineNumber] == self.lineOutputLengths[input2lineNumber],
                    self.lineOutputLengths[lineNumber] == self.lineOutputs[input1lineNumber][0],
                )
            )
        ))
        self.solver.add(Implies(
            And(
                self.lineOutputLengths[input1lineNumber] == 1,
                self.lineOutputs[input1lineNumber][0] < 0
            ),
            And(
                self.lineOutputLengths[lineNumber] <= self.lineOutputLengths[input2lineNumber],
                self.lineOutputLengths[lineNumber] <= self.lineOutputLengths[input2lineNumber] + self.lineOutputs[input1lineNumber][0],
                Or(
                    self.lineOutputLengths[lineNumber] == self.lineOutputLengths[input2lineNumber],
                    self.lineOutputLengths[lineNumber] == self.lineOutputLengths[input2lineNumber] + self.lineOutputs[input1lineNumber][0]
                )
            )
        ))
        self.solver.add(Implies(
            self.lineOutputLengths[input1lineNumber] == 0,
            self.lineOutputLengths[lineNumber] == self.lineOutputLengths[input2lineNumber]
        ))
        for k in range(self.max_list_length):
            self.solver.add(Implies(
                And(
                    self.lineOutputLengths[input1lineNumber] == 1,
                    self.lineOutputs[input1lineNumber][0] >= 0,
                    k < self.lineOutputs[input1lineNumber][0],
                    k < self.lineOutputLengths[input2lineNumber]
                ),
                self.lineOutputs[lineNumber][k] == self.lineOutputs[input2lineNumber][k]
            ))
            self.solver.add(Implies(
                And(
                    self.lineOutputLengths[input1lineNumber] == 1,
                    self.lineOutputs[input1lineNumber][0] < 0,
                    k < self.lineOutputLengths[input2lineNumber] + self.lineOutputs[input1lineNumber][0]
                ),
                self.lineOutputs[lineNumber][k] == self.lineOutputs[input2lineNumber][k]
            ))
            self.solver.add(Implies(
                And(
                    self.lineOutputLengths[input1lineNumber] == 0,
                    k < self.lineOutputLengths[input2lineNumber]
                ),
                self.lineOutputs[lineNumber][k] == self.lineOutputs[input2lineNumber][k]
            ))

    def setDrop(self, lineNumber, input1lineNumber, input2lineNumber):
        self.setLengthCanVary(lineNumber, input2lineNumber)
        self.setHeadIsFixed(lineNumber)
        self.setTailIsFixed(lineNumber)
        self.setMaxIsFixed(lineNumber)
        self.setMinIsFixed(lineNumber)
        self.solver.add(Or(self.lineOutputLengths[input1lineNumber] == 0, self.lineOutputLengths[input1lineNumber] == 1))
        self.solver.add(Implies(
            And(
                self.lineOutputLengths[input1lineNumber] == 1,
                self.lineOutputs[input1lineNumber][0] >= 0
            ),
            And(
                self.lineOutputLengths[lineNumber] >= self.lineOutputLengths[input2lineNumber] - self.lineOutputs[input1lineNumber][0],
                Or(
                    self.lineOutputLengths[lineNumber] == self.lineOutputLengths[input2lineNumber] - self.lineOutputs[input1lineNumber][0],
                    self.lineOutputLengths[lineNumber] == 0
                )
            )
        ))
        self.solver.add(Implies(
            And(
                self.lineOutputLengths[input1lineNumber] == 1,
                self.lineOutputs[input1lineNumber][0] < 0
            ),
            And(
                self.lineOutputLengths[lineNumber] <= -self.lineOutputs[input1lineNumber][0],
                self.lineOutputLengths[lineNumber] <= self.lineOutputLengths[input2lineNumber],
                Or(
                    self.lineOutputLengths[lineNumber] == -self.lineOutputs[input1lineNumber][0],
                    self.lineOutputLengths[lineNumber] == self.lineOutputLengths[input2lineNumber]
                )
            )
        ))
        self.solver.add(Implies(
            self.lineOutputLengths[input1lineNumber] == 0,
            self.lineOutputLengths[lineNumber] == self.lineOutputLengths[input2lineNumber]
        ))
        for k in range(self.max_list_length):
            self.solver.add(Implies(
                k < self.lineOutputLengths[lineNumber],
                self.getElement(self.lineOutputs[lineNumber][k], self.lineOutputs[input2lineNumber], k + self.lineOutputLengths[input2lineNumber] - self.lineOutputLengths[lineNumber])
            ))

    def setAccess(self, lineNumber, input1lineNumber, input2lineNumber):
        self.setLengthIsFixed(lineNumber)
        self.setHeadCanVary(lineNumber, input1lineNumber)
        self.setTailIsFixed(lineNumber)
        self.setMaxIsFixed(lineNumber)
        self.setMinIsFixed(lineNumber)
        self.solver.add(Or(self.lineOutputLengths[input1lineNumber] == 0, self.lineOutputLengths[input1lineNumber] == 1))
        self.solver.add(Implies(
            Or(
                self.lineOutputs[input1lineNumber][0] < -self.lineOutputLengths[input2lineNumber],
                self.lineOutputs[input1lineNumber][0] >= self.lineOutputLengths[input2lineNumber],
                self.lineOutputLengths[input1lineNumber] == 0
            ),
            self.lineOutputLengths[lineNumber] == 0
        ))
        self.solver.add(Implies(
            And(
                self.lineOutputs[input1lineNumber][0] >= -self.lineOutputLengths[input2lineNumber],
                self.lineOutputs[input1lineNumber][0] < self.lineOutputLengths[input2lineNumber],
                self.lineOutputLengths[input1lineNumber] == 1
            ),
            self.lineOutputLengths[lineNumber] == 1
        ))
        for k in range(self.max_list_length):
            self.solver.add(Implies(
                And(
                    self.lineOutputLengths[input1lineNumber] == 1,
                    self.lineOutputs[input1lineNumber][0] >= 0,
                    self.lineOutputs[input1lineNumber][0] < self.lineOutputLengths[input2lineNumber],
                    k == self.lineOutputs[input1lineNumber][0]
                ),
                self.lineOutputs[lineNumber][0] == self.lineOutputs[input2lineNumber][k],
            ))
            self.solver.add(Implies(
                And(
                    self.lineOutputLengths[input1lineNumber] == 1,
                    k == self.lineOutputLengths[input2lineNumber] + self.lineOutputs[input1lineNumber][0],
                    self.lineOutputs[input1lineNumber][0] < 0,
                    self.lineOutputs[input1lineNumber][0] >= -self.lineOutputLengths[input2lineNumber]
                ),
                self.getElement(self.lineOutputs[lineNumber][0], self.lineOutputs[input2lineNumber], self.lineOutputLengths[input2lineNumber] + self.lineOutputs[input1lineNumber][0])
            ))
        # output is an integer, integers are only useful within he length of the lists, unless it's the output
        if lineNumber != self.outputIndex:
            self.solver.add(self.bound_int(self.lineOutputs[lineNumber][0], -self.max_list_length, self.max_list_length))

    def inputsNotNone(self):
        for i in range(self.numberOfInputs):
            j = -(i+1)
            self.solver.add(self.lineOutputLengths[j] != 0)
        return self

    def outputNotNone(self):
        self.solver.add(self.lineOutputLengths[self.outputIndex] != 0)
        return self

    def setInputMinimumLengths(self, allLengths):
        for line, length in allLengths.items():
            self.solver.add(self.lineOutputLengths[line] >= length)
        return self

    def setLineMaximumLengths(self, length):
        for line in range(self.numberOfLines):
            self.solver.add(self.lineOutputLengths[line] <= length)
        for i in range(self.numberOfInputs):
            j = -(i+1)
            self.solver.add(self.lineOutputLengths[j] <= length)
        return self

    def setOutputMinimumLength(self, length):
        self.solver.add(self.lineOutputLengths[self.outputIndex] >= length)

    def setOutputNoZero(self):
        cons = []
        for i in range(self.max_list_length):
            cons.append(self.lineOutputs[self.outputIndex][i] != 0)
        self.solver.add(And(*cons))

    def inputVaried(self, inputIndex, offset, block_size):
        cons = []
        for k in range(0, self.max_list_length):
            for n in range(offset, block_size+offset):
                if k + n + 1 < self.max_list_length:
                    cons.append(self.lineOutputs[inputIndex][k] != self.lineOutputs[inputIndex][k+n+1])
        self.solver.add(And(*cons))

    # approximation
    def distinctInandOut(self):
        for i in range(self.numberOfInputs):
            j = -(i+1)
            self.solver.add(Not(And(
                self.lineOutputLengths[self.outputIndex] == self.lineOutputLengths[j],
                self.lineOutputLengths[j] == 1,
                self.lineOutputs[self.outputIndex][0] == self.lineOutputs[j][0]
            )))
            self.solver.add(Not(And(
                self.lineOutputLengths[self.outputIndex] == self.lineOutputLengths[j],
                self.lineOutputLengths[j] == 2,
                self.lineOutputs[self.outputIndex][0] == self.lineOutputs[j][0],
                self.lineOutputs[self.outputIndex][1] == self.lineOutputs[j][1]
            )))
            self.solver.add(Not(And(
                self.lineOutputLengths[self.outputIndex] == self.lineOutputLengths[j],
                self.lineOutputLengths[j] > 2,
                self.lineOutputs[self.outputIndex][0] == self.lineOutputs[j][0],
                self.lineOutputs[self.outputIndex][1] == self.lineOutputs[j][1],
                self.lineOutputs[self.outputIndex][2] == self.lineOutputs[j][2]
            )))

    def excludeListValueConstraint(self, lineOutputIndex, excludedList):
        cons = []
        for k in range(len(excludedList)):
            cons.append(self.lineOutputs[lineOutputIndex][k] != excludedList[k])
        cons.append(self.lineOutputLengths[lineOutputIndex] != len(excludedList))
        return Or(*cons)

    def excludeIntValueConstraint(self, lineOutputIndex, excludedInt):
        return Or(
            self.lineOutputs[lineOutputIndex][0] != excludedInt,
            self.lineOutputLengths[lineOutputIndex] != 1
        )

    def excludeValueConstraint(self, lineOutputIndex, value):
        OrCons = []
        if isinstance(value, list):
            OrCons.append(self.excludeListValueConstraint(lineOutputIndex, value))
        elif value is None:
            OrCons.append(self.lineOutputLengths[lineOutputIndex] != 0)
        else:
            OrCons.append(self.excludeIntValueConstraint(lineOutputIndex, value))
        return Or(*OrCons)

    def excludeInputConstraint(self, excludedValue):
        andCons = []
        ind = -1
        for __ in range(self.numberOfInputs):
            andCons.append(self.excludeValueConstraint(ind, excludedValue))
            ind += -1
        return And(*andCons)

    def excludeOutputs(self, example):
        self.solver.add(self.excludeValueConstraint(self.outputIndex, example))

    # force output to contain at least one value greater than val
    def setOutMax(self, val):
        cons = []
        for i in range(self.max_list_length):
            cons.append(And(
                self.lineOutputs[self.outputIndex][i] > val,
                self.lineOutputLengths[self.outputIndex] > i
            ))
        s = self.solver
        s.add(Or(*cons))

    # force output to contain at least one value less than val
    def setOutMin(self, val):
        cons = []
        for i in range(self.max_list_length):
            cons.append(And(
                self.lineOutputs[self.outputIndex][i] < val,
                self.lineOutputLengths[self.outputIndex] > i
            ))
        s = self.solver
        s.add(Or(*cons))

    # all elements of selected inputs (typically the list inputs) should be larger than val
    def setInputsMinAbsValue(self, val, whichInputs):
        cons = []
        for index in whichInputs:
            for j in range(self.max_list_length):
                cons.append(And(
                    Or(self.lineOutputs[index][j] > val, self.lineOutputs[index][j] < -val)
                ))
        self.solver.add(And(*cons))

    # each behaviour is list of lists of bools, indicating high level behaviours of line functions
    # want to exclude these exact combinations to encourage meaningfully different examples
    # it's a bit grim to rely on the meaning implicit in the order of the list. Sorry.
    # if this starts behaving wierdly, compare ordering in linePreds and in Program.compareLines
    def excludeBehaviours(self, behaviours):
        for b in behaviours:
            # difference only required in *some* line, not all
            or_cons = []
            for i in range(self.numberOfLines):
                # 5 == number of watched predicates
                for j in range(5):
                    value = bool(b[i][j])
                    # some value has to be opposite to previous
                    # and it must be a characteristic we're interested in
                    or_cons.append(And(self.linePreds[i][j] != value, self.watchedPreds[i][j] == True))
            self.solver.add(Or(*or_cons))

    # to ensure each line does something "interesting"
    # can vary what is considered interesting by
    #  set---CanVary / set---IsFixed in definition of dsl functions above
    def excludeNullBehaviours(self):
        for i in range(self.numberOfLines):
            # null behaviour forbidden for *every* line, not just one
            line_cons = []
            # 5 == number of watched predicates
            for j in range(5):
                line_cons.append(And(self.linePreds[i][j] == True, self.watchedPreds[i][j] == True))
            self.solver.add(Or(*line_cons))

    def getLastInputsAndOutputs(self):
        if self.isSat == sat:
            output = []
            allInputs = []
            ind = -1
            for __ in range(self.numberOfInputs):
                thisInput = []
                length = z3InputsOracle.fixValue(self.currModel[self.lineOutputLengths[ind]].as_long())
                for k in range(length):
                    nextVal = z3InputsOracle.fixValue(self.currModel[self.lineOutputs[ind][k]].as_long())
                    thisInput.append(nextVal)
                allInputs.append(thisInput)
                ind += -1
            allInputs.reverse()

            outputLength = z3InputsOracle.fixValue(self.currModel[self.lineOutputLengths[self.outputIndex]].as_long())
            for k in range(outputLength):
                nextVal = z3InputsOracle.fixValue(self.currModel[self.lineOutputs[self.outputIndex][k]].as_long())
                output.append(nextVal)

            result = [output]
            result.extend(allInputs)
            return result

    @staticmethod
    def fixValue(val):
        if val > 256:
            return -(2**32 - val)
        return val

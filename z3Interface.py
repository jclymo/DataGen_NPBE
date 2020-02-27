from z3 import *

class z3BaseOracle:
    class AvailableFunctions:
        MapMinus1 = 0
        MapPlus1 = 1
        MapMult2 = 2
        MapMult3 = 3
        MapMult4 = 4
        MapMultNeg1 = 5
        Reverse = 6
        Sort = 7
        FilterLessZero = 8
        FilterGreaterZero = 9
        CountLessZero = 10
        CountGreaterZero = 11
        ZipPlus = 12
        ZipMinus = 13
        ZipMin = 14
        ZipMax = 15
        Take = 16
        Drop = 17
        Access = 18
        Head = 19
        Last = 20
        Sum = 21
        Minimum = 22
        Maximum = 23
        ScanPlus = 24
        ScanMinus = 25
        ScanMin = 26
        ScanMax = 27
        MapDiv2 = 28
        MapDiv3 = 29
        MapDiv4 = 30
        MapSquare = 31
        FilterEven = 32
        FilterOdd = 33
        CountEven = 34
        CountOdd = 35
        ZipMult = 36
        ScanMult = 37

    def __init__(self):
        pass

    def setTimeout(self, timeoutms):
        self.solver.set("timeout", timeoutms)

    def bound_int(self, intvar, lw=-255, ub=255):
        # Returns a constraint bounding the domain of intvar
        return And(intvar <= ub, intvar >= lw)

    def bound_intvector(self, intvectorvar, lw=-255, ub=255):
        # Returns a constraint bounding the domain of each entry of intvectorvar
        cons = []
        for i in range(len(intvectorvar)):
            cons.append(self.bound_int(intvectorvar[i], lw, ub))
        return And(*cons)

    def BitVectorVector(self, name, len, bv_len=32):
        return [BitVec('{}__{}'.format(name, i), bv_len) for i in range(len)]

    def getElement(self, outputItem, inputList, element):
        conditions = []
        for val in range(self.max_list_length):
            conditions.append(Implies(element == val, outputItem == inputList[val]))
        return And(*conditions)

    def beginAddConstraints(self):
        s = self.solver
        s.push()
        return self

    def removeAddedConstraints(self):
        s = self.solver
        s.pop()
        return self

    def prepareDataTypesEnum(self):
        self.VarTypes = self.VarTypesClass()

    def checkSat(self):
        if self.solver.check() == unsat:
            return -1
        if self.solver.check() == sat:
            return 1
        return 0

    def evalSatAndUpdateModel(self):
        s = self.solver
        self.isSat = s.check()
        if self.isSat == sat:
            self.currModel = s.model()
        return self

    class VarTypesClass:
        def __init__(self):
            self.Int = 0
            self.List = 1
            self.NoneType = 2

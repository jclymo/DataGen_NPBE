import keras
import numpy as np
import os.path
import dsl

#Defining all auxilliary non-numerical characters required for inputs/outputs
arraytype = np.array([516])
inttype = np.array([515])
arraysep = np.array([514])
nullchar = np.array([513])
outofbounds = np.array([512])

onelines = [x.split(',') for x in dsl.getCompositeFunctionKeys()]
for l in onelines:
    if len(l) == 1: l.append('')
functionList = dsl.getAllFunctionsAndOptionsList()
oldFunctionList  = ['HEAD', 'LAST', 'ACCESS', 'MINIMUM', 'MAXIMUM', 'TAKE', 'DROP', 'FILTER', '>0', '<0', '%2==1',
                   '%2==0', 'COUNT', 'MAP', 'MIN', 'MAX', '+', '-', '*', 'ZIPWITH', 'SCANL1', 'SORT', 'REVERSE',
                   '*(-1)', '**2', '+1', '-1', '*2', '*3', '*4', '/2', '/3', '/4', 'SUM']
allFncs = len(dsl.getCompositeFunctionKeys())
takeLambda = dsl.getFunctionKeysWithLambda()

#DeepCoder attribute
def deepCoderAttribute(line):
    lineSplit = line.split('\\')[2:]
    y = np.zeros(len(functionList))
    for jj in lineSplit:
        temp = jj.split(',')
        for i, x in enumerate(functionList):
            if x  in temp:
                y[i] = 1
    return y

#Shift - takes an arbitrary integer and returns a number from 0 - 511 if the integer is in the desired range
#[-256, 256). Otherwise returns an out of bounds character (512 in this case). We need this because Keras' embedding layers expect only positive ints as input.
def shift(x):
    if x>255:
        return outofbounds[0]
    elif x<-256:
        return outofbounds[0]
    elif (x<0 & x>-257):
        return  np.abs(x) + 255
    else:
        return x

#Pads arrays to a given length (max_len) with the null value (513).
def pad(x, padding):
    while len(x)<padding:
        x.append(nullchar[0])
    return x

#Helper function normalizes sets of 5 I/0 examples to maximum length set by max_len (should be as the network expects it).
def ioNormalizer(inputL1s, inputL2s, inputints, outputs, max_len):
    nInputs = []
    nOutputs = []
    totalinputlength = max_len*2 + 1 + 1 + 1
    # totalinputlength = max_len

    if len(inputL2s) == 0 and len(inputints) == 0:
        #The situation is just 1 set of 5 I/O lists
        for listx in inputL1s:
            inputs = [shift(x) for x in listx]
            while len(inputs)<totalinputlength-1:
                inputs.append(nullchar[0])
            inputs = np.concatenate((arraytype, np.array(inputs)))
            nInputs.append(inputs)

    elif len(inputL2s) > 0 and len(inputints) == 0:
        for i in range(0, len(inputL1s)):
            shiftinputs1 = [shift(x) for x in inputL1s[i]]
            shiftinputs2 = [shift(x) for x in inputL2s[i]]
            randinput1pad = np.array(pad(shiftinputs1, max_len))
            randinput2pad = np.array(pad(shiftinputs2, max_len))
            inputs = np.concatenate((arraytype,randinput1pad,arraysep,arraytype, randinput2pad))
            nInputs.append(inputs)

    elif len(inputL2s) == 0 and len(inputints) > 0:
        for i in range(0, len(inputL1s)):
            shiftinputs1 = [shift(x) for x in inputL1s[i]]
            shiftinputs2 = [shift(inputints[i])]
            randinput1pad = np.array(pad(shiftinputs1, max_len))
            randinput2pad = np.array(pad(shiftinputs2, max_len))
            inputs = np.concatenate((arraytype,randinput1pad,arraysep,inttype, randinput2pad))
            nInputs.append(inputs)
    #Handle outputs - **handle tuples as input**
    for olist in outputs:
        if type(olist) == list:
            sOutputs = [shift(x) for x in olist]
            while len(sOutputs)<totalinputlength-1:
                sOutputs.append(nullchar[0])
            sOutputs = np.concatenate((arraytype, np.array(sOutputs)))
        elif type(olist) == int:
            sOutputs = [shift(olist)]
            while len(sOutputs)<totalinputlength-1:
                sOutputs.append(nullchar[0])
            sOutputs = np.concatenate((inttype, np.array(sOutputs)))
        elif olist == None:
            sOutputs = []
            while len(sOutputs)<totalinputlength-1:
                sOutputs.append(nullchar[0])
            sOutputs = np.concatenate((inttype, np.array(sOutputs)))
        nOutputs.append(sOutputs)

    return nInputs, nOutputs

def readInForANN(filename, max_len):
    with open(filename, 'r') as dataSet:
        ann_set = dataSet.readlines()
    setSize = int(len(ann_set)/6)

    ins = [[],[],[],[],[]]
    outs = [[],[],[],[],[]]

    Ys = []

    for i in range(setSize):
#         print('--- '+ str(float((i+1)/setSize)*100)[:5] + '% Complete ---', end = '\r', flush=True)
        testSetIndex = i

        inputsI1 = []
        inputsI2 = []
        inputsI3 = []
        outputspre = []

        line = ann_set[6*i]
        #Read in 5 I/O examples per test program
        try:
            for i in range(testSetIndex*6 + 1, testSetIndex*6 + 6):
                #Sampled Training Data
                inputStr = ann_set[i].split('|')[0]
                outputStr = ann_set[i].split('|')[1]
                inputsI1.append(eval(inputStr)['I1'])
                if 'I2' in ann_set[i]:
                    val = eval(inputStr)['I2']
                    if type(val) is int:
                        inputsI3.append(val)
                    else:
                        # inputsI2.append(eval(inputStr)['I2'])
                        inputsI2.append(val)
                elif 'I3' in ann_set[i]:
                    inputsI3.append(eval(inputStr)['I3'])
                outputspre.append(eval(outputStr))

            #Normalize them for ANN
            inputs, outputs = ioNormalizer(inputsI1, inputsI2, inputsI3, outputspre, max_len)

            for k in range(5):
                ins[k].append(inputs[k])
                outs[k].append(outputs[k])
            Ys.append(deepCoderAttribute(line))
        except:
            pass
    ins = np.array([np.array(ins[i]) for i in range(5)])
    outs = np.array([np.array(outs[i]) for i in range(5)])

    Ys = np.array(Ys)
    print(Ys.shape, ins.shape, outs.shape)
    return Ys, ins, outs

#Go through test set and calculate accuracy for predicted top k orderings.
def calculateAccuracy(testSetFile, model, bl, oldOrder = False):
    if oldOrder:
        functionListInternal = oldFunctionList
    else:
        functionListInternal = functionList

    with open(testSetFile, 'r') as f2:
        testSet = f2.readlines()

    tops = [[] for i in range(allFncs)]
    topsb= [[] for i in range(allFncs)]

    #Get max_len from ANN
    totinputlen = model.get_input_shape_at(0)[0][1]
    max_len = (totinputlen - 1 - 1 - 1)/2

    acc_bf = np.zeros(allFncs)
    acc_bl = np.zeros(allFncs)


    acc_f = np.zeros(allFncs)
    acc_l = np.zeros(allFncs)

    acc_w = np.zeros(allFncs)
    acc_wb = np.zeros(allFncs)

    tot = 0

    for i in range(int(len(testSet)/6)):
#         print('--- '+ str(float((i+1)/int(len(testSet)/6))*100)[:6] + '% Complete ---', end='\r', flush=True)
        testSetIndex = i
        inputsI1 = []
        inputsI2 = []
        inputsI3 = []
        outputspre = []
        try:
            #Read in 5 I/O examples per test program
            for i in range(testSetIndex*6 + 1, testSetIndex*6 + 6):
                inputStr = testSet[i].split('|')[0]
                outputStr = testSet[i].split('|')[1]
                inputsI1.append(eval(inputStr)['I1'])
                if 'I2' in testSet[i]:
                    val = eval(inputStr)['I2']
                    if type(val) is int:
                        inputsI3.append(val)
                    else:
                        # inputsI2.append(eval(inputStr)['I2'])
                        inputsI2.append(val)
                elif 'I3' in testSet[i]:
                    inputsI3.append(eval(inputStr)['I3'])
                outputspre.append(eval(outputStr))

            #Normalize them for ANN
            inputs, outputs = ioNormalizer(inputsI1, inputsI2, inputsI3, outputspre, max_len)
            inputs = np.array([[np.array(x)] for x in inputs])
            outputs = np.array([[np.array(x)] for x in outputs])
            prediction = model.predict([inputs[0], outputs[0], inputs[1],
                                            outputs[1],inputs[2], outputs[2],
                                            inputs[3], outputs[3],inputs[4],
                                            outputs[4]]).flatten()

            #These top5,10,20 are all the individual functional element predictions. Must translate them into
            #predictions for actual lines.
            allpreds = np.flip(np.argsort(prediction), axis = 0)
            allpreds = [[functionListInternal[k], prediction[k]] for k in allpreds]

            #Extract program from the test set and split it into lines.
            result = sum([x.split(',') for x in testSet[testSetIndex*6].split('\\')[1:]], [])
            proglist=[]
            #Drop symbols for input, I3, X2 etc..
            for k in result:
                if k in functionListInternal:
                    proglist.append(k)
            #Concatinate Functions that take lambdas with their lambda i.e. 'COUNT', '<0' becomes 'COUNT,<0'
            for i, k in enumerate(proglist):
                if k in takeLambda:
                    proglist[i] = proglist[i] + ',' +  proglist[i+1]
                    del proglist[i+1]
                else:
                    proglist[i] = proglist[i] + ','

            onelines = [x.split(',') for x in dsl.getCompositeFunctionKeys()]
            for l in onelines:
                if len(l) == 1: 
                    l.append('')

            linepreds = onelines
            for x in linepreds:
                for y in allpreds:
                    if y[0] in x:
                        x.append(y[1])
            for x in linepreds:
                if len(x) == 4:
                    x[2] = min(x[2:])
                    del x[3]
                x[0] = x[0] + ',' + x[1]
                del x[1]
            linepreds.sort(key=lambda x: float(x[1]), reverse=True)

            for i in range(1, len(tops) + 1):
                tops[i-1] = [x[0] for x in linepreds[0:i]]
                topsb[i-1] = [x for x in bl[0:i]]

            for i in range(0, len(tops)):
                if proglist[0] in tops[i]:
                    acc_f[i]+=1
                if proglist[-1] in tops[i]:
                    acc_l[i]+=1

                if proglist[-1] in topsb[i]:
                    acc_bl[i]+=1
                if proglist[0] in topsb[i]:
                    acc_bf[i]+=1
                if set(proglist) < set(tops[i]):
                    acc_w[i]+=1
                if set(proglist) < set(topsb[i]):
                    acc_wb[i]+=1
            tot+=1
        except:
#             print('Could not find example, skipped')
            pass
    return acc_f/tot, acc_l/tot, acc_w/tot, acc_bf/tot, acc_bl/tot, acc_wb/tot

#Reading I/O in for histograms
def IO_hist_data(ioProgFile):
    with open(ioProgFile, 'r') as temp:
        dataset = temp.readlines()
    numProgs = int(len(dataset)/6)

    inputs = []
    inputsC = [[] for i in range(34)]
    outputs = []
    outputsC = [[] for i in range(34)]

    for i in range(numProgs):
    #     print('--- '+ str(float((i+1)/numProgs)*100)[:6] + '% Complete ---', end='\r', flush=True)
        atrib = deepCoderAttribute(dataset[i*6])
        for j in range(1,6):
            try:
                inz = eval(dataset[i*6+j].split('|')[0]).get('I1')
                inz2 = eval(dataset[i*6+j].split('|')[0]).get('I2')
                outz = eval(dataset[i*6+j].split('|')[1])
                if inz2 is None:
                    inz2 = []
                if type(outz) == int:
                    outz = [outz]
                if outz is None:
                    outz = []
                temp = inz + inz2
                inputs.extend(temp)
                outputs.extend(outz)
                for k, x in enumerate(atrib):
                    if x == 1.0:
                        inputsC[k].extend(temp)
                        outputsC[k].extend(outz)
            except:
                pass
    return inputs, inputsC, outputs, outputsC

##ANN with shared weights between I/O 
def DeepCoderNN_shared(embeddingDim, totalinputlength, outshape, activation):
    input1 = keras.layers.Input(shape=(totalinputlength,))
    e1 = keras.layers.Embedding(256*2+5, embeddingDim, input_length=totalinputlength)
    input2 = keras.layers.Input(shape=(totalinputlength,))
    e2 = keras.layers.Embedding(256*2+5, embeddingDim, input_length=totalinputlength)

    x11 = e1(input1)
    x12 = e2(input2)

    concatenated1 = keras.layers.Concatenate()([x11, x12])
    flattened1 = keras.layers.Flatten()(concatenated1)
    e3 = keras.layers.Dense(256, activation=activation)
    e4 = keras.layers.Dense(256, activation=activation)
    e5 = keras.layers.Dense(256, activation=activation)

    h11 = e3(flattened1)
    h12 = e4(h11)
    h13 = e5(h12)

    input3 = keras.layers.Input(shape=(totalinputlength,))
    x21 = e1(input3)
    input4 = keras.layers.Input(shape=(totalinputlength,))
    x22 = e2(input4)
    concatenated2 = keras.layers.Concatenate()([x21, x22])
    flattened2 = keras.layers.Flatten()(concatenated2)
    h21 = e3(flattened2)
    h22 = e4(h21)
    h23 = e5(h22)

    input5 = keras.layers.Input(shape=(totalinputlength,))
    x31 = e1(input5)
    input6 = keras.layers.Input(shape=(totalinputlength,))
    x32 = e2(input6)
    concatenated3 = keras.layers.Concatenate()([x31, x32])
    flattened3 = keras.layers.Flatten()(concatenated3)
    h31 = e3(flattened3)
    h32 = e4(h31)
    h33 = e5(h32)

    input7 = keras.layers.Input(shape=(totalinputlength,))
    x41 = e1(input7)
    input8 = keras.layers.Input(shape=(totalinputlength,))
    x42 = e2(input8)
    concatenated4 = keras.layers.Concatenate()([x41, x42])
    flattened4 = keras.layers.Flatten()(concatenated4)
    h41 = e3(flattened4)
    h42 = e4(h41)
    h43 = e5(h42)

    input9 = keras.layers.Input(shape=(totalinputlength,))
    x51 = e1(input9)
    input10 = keras.layers.Input(shape=(totalinputlength,))
    x52 = e2(input10)
    concatenated5 = keras.layers.Concatenate()([x51, x52])
    flattened5 = keras.layers.Flatten()(concatenated5)
    h51 = e3(flattened5)
    h52 = e4(h51)
    h53 = e5(h52)

    concatenated_all = keras.layers.Average()([h53, h43, h33, h23, h13])
    #flattened6 = keras.layers.Flatten()(concatenated6)

    h_all = keras.layers.Dense(256, activation=activation)(concatenated_all)
    #h17 = keras.layers.Dense(256, activation='relu')(h16)
    #h18 = keras.layers.Dense(256, activation='relu')(h17)


    out = keras.layers.Dense(outshape, activation='sigmoid')(h_all)
    #out = keras.layers.Activation('softmax')(out)
    model = keras.models.Model(inputs=[input1, input2, input3, input4, input5,
                                       input6, input7, input8, input9, input10], outputs=out)
    return model


def DeepCoderNN_split(embeddingDim, totalinputlength, outshape, activation):
    input1 = keras.layers.Input(shape=(totalinputlength,))
    x1 = keras.layers.Embedding(256*2+5, embeddingDim, input_length=totalinputlength)(input1)
    input2 = keras.layers.Input(shape=(totalinputlength,))
    x2 = keras.layers.Embedding(256*2+5, embeddingDim, input_length=totalinputlength)(input2)

    concatenated = keras.layers.Concatenate()([x1, x2])
    flattened = keras.layers.Flatten()(concatenated)
    h1 = keras.layers.Dense(256, activation=activation)(flattened)
    h2 = keras.layers.Dense(256, activation=activation)(h1)
    h3 = keras.layers.Dense(256, activation=activation)(h2)

    input3 = keras.layers.Input(shape=(totalinputlength,))
    x3 = keras.layers.Embedding(256*2+5, embeddingDim, input_length=totalinputlength)(input3)
    input4 = keras.layers.Input(shape=(totalinputlength,))
    x4 = keras.layers.Embedding(256*2+5, embeddingDim, input_length=totalinputlength)(input4)

    concatenated2 = keras.layers.Concatenate()([x3, x4])
    flattened2 = keras.layers.Flatten()(concatenated2)
    h4 = keras.layers.Dense(256, activation=activation)(flattened2)
    h5 = keras.layers.Dense(256, activation=activation)(h4)
    #mid = keras.layers.BatchNormalization()(h5)
    h6 = keras.layers.Dense(256, activation=activation)(h5)

    input5 = keras.layers.Input(shape=(totalinputlength,))
    x5 = keras.layers.Embedding(256*2+5, embeddingDim, input_length=totalinputlength)(input5)
    input6 = keras.layers.Input(shape=(totalinputlength,))
    x6 = keras.layers.Embedding(256*2+5, embeddingDim, input_length=totalinputlength)(input6)

    concatenated3 = keras.layers.Concatenate()([x5, x6])
    flattened3 = keras.layers.Flatten()(concatenated3)
    h7 = keras.layers.Dense(256, activation=activation)(flattened3)
    h8 = keras.layers.Dense(256, activation=activation)(h7)
    #mid = keras.layers.BatchNormalization()(h5)
    h9 = keras.layers.Dense(256, activation=activation)(h8)

    input7 = keras.layers.Input(shape=(totalinputlength,))
    x7 = keras.layers.Embedding(256*2+5, embeddingDim, input_length=totalinputlength)(input7)
    input8 = keras.layers.Input(shape=(totalinputlength,))
    x8 = keras.layers.Embedding(256*2+5, embeddingDim, input_length=totalinputlength)(input8)

    concatenated4 = keras.layers.Concatenate()([x7, x8])
    flattened4 = keras.layers.Flatten()(concatenated4)
    h10 = keras.layers.Dense(256, activation=activation)(flattened4)
    h11 = keras.layers.Dense(256, activation=activation)(h10)
    #mid = keras.layers.BatchNormalization()(h5)
    h12 = keras.layers.Dense(256, activation=activation)(h11)

    input9 = keras.layers.Input(shape=(totalinputlength,))
    x9 = keras.layers.Embedding(256*2+5, embeddingDim, input_length=totalinputlength)(input9)
    input10 = keras.layers.Input(shape=(totalinputlength,))
    x10 = keras.layers.Embedding(256*2+5, embeddingDim, input_length=totalinputlength)(input10)

    concatenated5 = keras.layers.Concatenate()([x9, x10])
    flattened5 = keras.layers.Flatten()(concatenated5)
    h13 = keras.layers.Dense(256, activation=activation)(flattened5)
    h14 = keras.layers.Dense(256, activation=activation)(h13)
    #mid = keras.layers.BatchNormalization()(h5)
    h15 = keras.layers.Dense(256, activation=activation)(h14)


    concatenated6 = keras.layers.Average()([h3, h6, h9, h12, h15])
    #flattened6 = keras.layers.Flatten()(concatenated6)

    h16 = keras.layers.Dense(256, activation=activation)(concatenated6)
    #h17 = keras.layers.Dense(256, activation='relu')(h16)
    #h18 = keras.layers.Dense(256, activation='relu')(h17)


    out = keras.layers.Dense(outshape, activation='sigmoid')(h16)
    #out = keras.layers.Activation('softmax')(out)
    model = keras.models.Model(inputs=[input1, input2, input3, input4, input5,
                                    input6, input7, input8, input9, input10], outputs=out)
    return model

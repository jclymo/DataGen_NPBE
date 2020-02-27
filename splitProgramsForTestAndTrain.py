import random

def splitTrainAndTestRandom(programFileName, frac_for_training):
    training = []
    testing = []
    with open(programFileName+'.txt', 'r', encoding='utf-8') as f:
        line = f.readline()
        while line != '':
            random_number = random.random()
            if random_number <= frac_for_training:
                training.append(line)
            else:
                testing.append(line)
            line = f.readline()
    with open(programFileName+'_training' + '_'+ str(frac_for_training)+'.txt', 'w', encoding='utf-8') as f2:
        for tr in training:
            f2.write(tr)
    with open(programFileName+'_testing' + '_' + str(round(1-frac_for_training, 3))+'.txt', 'w', encoding='utf-8') as f3:
        for te in testing:
            f3.write(te)

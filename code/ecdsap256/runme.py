import os

def writeResult(s):
    w = genFileW()
    f = open("/home/nkulatov/master/hacl-star/code/ecdsap256/dist/log", "a+")
    toWrite = s + "\n" + w + "\n \n"
    f.write(toWrite)
    print(toWrite)

def genFileW():
    i = printInline()
    loc = computeLOC()
    return (i + "Lines of code: \n" + loc)

def computeInline():
    f = open("/home/nkulatov/master/hacl-star/code/ecdsap256/dist/Hacl_P256.c", "r")
    ff = f.read()
    index = 0
    s = ""
    while (index != -1):
        index = ff.find("inline", index + 1)
        index2 = ff.find("\n", index)
        s = s + ff[index: index2:] + "\n"

    return s

def printInline():
    return ("Inlined functions in the code: \n") + computeInline()

def makeInt(output):
    return [int(s) for s in output.split() if s.isdigit()][0]

def readLastLOC():
    f = open("/home/nkulatov/master/hacl-star/code/ecdsap256/dist/log", "r")
    ff = f.read()
    index = 0
    index2 = 0
    index3 = 0

    while (index != -1):
        index = ff.find("Lines of code:", index + 1)
        if index != -1:
         index2 = index
        index3 = ff.find(" ", index)

    return(makeInt(ff[index2: index3]))


def computeLOC():
    stream = os.popen('wc -l ./dist/Hacl_P256.c')
    output = stream.read() 
    locNow = makeInt(output)

    locBefore = readLastLOC()

    try:
        locDiff = locNow - locBefore
    except Exception as e:
        locDiff = 0

    sign = ""

    if locDiff >0:
        sign = "+"
    elif locDiff < 0:
        sign = "-"


    return str(makeInt(output)) + "  (" + sign + " " + str(locDiff) + ") "



def readLast():
    f = open("/home/nkulatov/master/hacl-star/code/ecdsap256/dist/log", "r")
    ff = f.read()
    index = 0
    index2 = 0
    index3 = 0

    while (index != -1):
        index = ff.find("bw   ", index + 1)
        if index != -1:
            index2 = index
            index3 = ff.find("Lines", index)

    print("The previous parameters: \n" + ff[index2: index3])


if __name__ == '__main__':
    stream = os.popen('make dist/test.exe')
    output = stream.read()
    stream = os.popen('./dist/test.exe')
    output = stream.read()

    l = writeResult(output)

    readLast()


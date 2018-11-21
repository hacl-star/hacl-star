#!/usr/local/bin/python3
import sys

line = sys.argv[1]
lines = [line[i:i+2] for i in range(0, len(line), 2)]
array = ["0x"+x+"uy" for x in lines]
print("["+(";".join(array))+"]")
print("length = "+(str(len(line)//2)))

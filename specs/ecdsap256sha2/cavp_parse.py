#!/bin/python3

import argparse
import re
import random
#import sys



if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Generate ECDSA CAVP test vectors.')
    parser.add_argument('FILE_VER', type=str, help='CAVP rsp file.')
    parser.add_argument('FILE_GEN', type=str, help='CAVP txt file.')
    parser.add_argument('--prob', type=int, choices=range(1,100), default=1, help='Extract each vector with probability 1/prob.')
    args = parser.parse_args()

    random.seed()
    
    ver = open(args.FILE_VER, 'r')
    gen = open(args.FILE_GEN, 'r')
    header_field = re.compile('\[P-256,SHA-([^\]]+)\]')
    field = re.compile('[^=]+= (\S+)')

    def next_section(rsp, line):
        while line:
            m = header_field.match(line)
            if m:
                a = 'SHA1' if m.group(1) == '1' else 'SHA2_' + m.group(1)
                return a
            line = rsp.readline()
        return False

    print("let sigver_vectors : list vec_SigVer = [")
   
    def process_sigver(a):
        line = ver.readline()
        while line:
            m = header_field.match(line)
            if m:
                return line

            if a not in {'SHA2_256'}:
                line = ver.readline()
                continue

            if line[:6] == 'Msg = ':
                msg = field.match(line).group(1)
             
                line = ver.readline()
                qx = field.match(line).group(1)
             
                line = ver.readline()
                qy = field.match(line).group(1)
             
                line = ver.readline()
                r = field.match(line).group(1)
             
                line = ver.readline()
                s = field.match(line).group(1)
             
                line = ver.readline()
                result = "true" if field.match(line).group(1) == 'P' else "false"
             
                if random.random() < 1 / args.prob:
                    print("  { msg = \"%s\";" % msg)
                    print("    qx  = \"%s\";" % qx)
                    print("    qy  = \"%s\";" % qy)
                    print("    r   = \"%s\";" % r)
                    print("    s   = \"%s\";" % s)
                    print("    result = %s;" % result)
                    print("  };")
             
            line = ver.readline()
   
    line = ver.readline()
    a = next_section(ver, line)
    while a:
        #print("Processing [P-256,%s]..." % a, file=sys.stderr)
        line = process_sigver(a)
        a = next_section(ver, line)

    print("]\n")

    ### SigGen.txt
    print("let siggen_vectors : list vec_SigGen = [")

    def process_siggen(a):
        line = gen.readline()
        while line:
            m = header_field.match(line)
            if m:
                return line

            if a not in {'SHA2_256'}:
                line = gen.readline()
                continue

            if line[:6] == 'Msg = ':
                msg = field.match(line).group(1)

                line = gen.readline()
                d = field.match(line).group(1)
             
                line = gen.readline()
                qx = field.match(line).group(1)
             
                line = gen.readline()
                qy = field.match(line).group(1)

                line = gen.readline()
                k = field.match(line).group(1)

                line = gen.readline()
                r = field.match(line).group(1)
             
                line = gen.readline()
                s = field.match(line).group(1)
             
                if random.random() < 1 / args.prob:
                    print("  { msg' = \"%s\";" % msg)
                    print("    d    = \"%s\";" % d)
                    print("    qx'  = \"%s\";" % qx)
                    print("    qy'  = \"%s\";" % qy)
                    print("    k    = \"%s\";" % k)
                    print("    r'   = \"%s\";" % r)
                    print("    s'   = \"%s\";" % s)
                    print("  };")
             
            line = gen.readline()

    line = gen.readline()
    a = next_section(gen, line)
    while a:
        #print("Processing [P-256,%s]..." % a, file=sys.stderr)
        line = process_siggen(a)
        a = next_section(gen, line)

    print("]")

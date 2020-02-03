#!/bin/python3

import argparse
import re
import random
#import sys


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Generate ECDSA CAVP test vectors.')
    parser.add_argument('FILE', type=str, help='CAVP rsp file.')
    parser.add_argument('--prob', type=int, choices=range(1,100), default=1, help='Extract each vector with probability 1/prob.')
    args = parser.parse_args()

    random.seed()
    
    rsp = open(args.FILE, 'r')
    header_field = re.compile('\[P-256,SHA-([^\]]+)\]')
    field = re.compile('[^=]+= (\S+)')

    print("let test_vectors : list vec = [")

    def next_section(line):
        while line:
            m = header_field.match(line)
            if m:
                a = 'SHA1' if m.group(1) == '1' else 'SHA2_' + m.group(1)
                return a
            line = rsp.readline()
        return False
   
    def process_section(a):
        line = rsp.readline()
        while line:
            m = header_field.match(line)
            if m:
                return line

            if a not in {'SHA2_256'}:
                line = rsp.readline()
                continue

            if line[:6] == 'Msg = ':
                msg = field.match(line).group(1)
             
                line = rsp.readline()
                qx = field.match(line).group(1)
             
                line = rsp.readline()
                qy = field.match(line).group(1)
             
                line = rsp.readline()
                r = field.match(line).group(1)
             
                line = rsp.readline()
                s = field.match(line).group(1)
             
                line = rsp.readline()
                result = "true" if field.match(line).group(1) == 'P' else "false"
             
                if random.random() < 1 / args.prob:
                    print("  { msg = \"%s\";" % msg)
                    print("    qx  = \"%s\";" % qx)
                    print("    qy = \"%s\";" % qy)
                    print("    r  = \"%s\";" % r)
                    print("    s = \"%s\";" % s)
                    print("    result = %s;" % result)
                    print("  } ;")
             
            line = rsp.readline()
   
    line = rsp.readline()
    a = next_section(line)
    while a:
        #print("Processing [P-256,%s]..." % a, file=sys.stderr)
        process_section(a)
        a = next_section(line)

    print("]")

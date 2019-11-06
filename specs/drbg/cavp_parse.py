#!/bin/python3

import argparse
import re
import random

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Generate HMAC-DRBG CAVP test vectors.')
    parser.add_argument('FILE', type=str, help='CAVP rsp file.')
    parser.add_argument('--prob', type=int, choices=range(1,100), default=1, help='Extract each vector with probability 1/prob.')
    args = parser.parse_args()

    random.seed()
    
    rsp = open(args.FILE, 'r')

    header_field = re.compile('\[SHA-([^\]]+)\]')
    field = re.compile('[^=]+= (\S+)')

    print("let test_vectors : list vec = [")
        
    line = rsp.readline()
    while line:
        m = header_field.match(line)
        if m:
            a = 'SHA1' if m.group(1) == '1' else 'SHA2_' + m.group(1)
 
        if line[:8] == 'COUNT = ':
            if a not in {'SHA1', 'SHA2_256', 'SHA2_384', 'SHA2_512'}:
                line = rsp.readline()
                continue
            
            line = rsp.readline()
            entropy_input = field.match(line).group(1)

            line = rsp.readline()
            nonce = field.match(line).group(1)

            line = rsp.readline()
            m = field.match(line)
            personalization_string = m.group(1) if m else ""

            line = rsp.readline()
            m = field.match(line)
            entropy_input_reseed = m.group(1) if m else ""

            line = rsp.readline()
            m = field.match(line)
            additional_input_reseed = m.group(1) if m else ""

            line = rsp.readline()
            m = field.match(line)
            additional_input_1 = m.group(1) if m else ""

            line = rsp.readline()
            m = field.match(line)
            additional_input_2 = m.group(1) if m else ""

            line = rsp.readline()
            m = field.match(line)
            returned_bits = field.match(line).group(1)

            if random.random() < 1 / args.prob:
                print("  { a = %s;" % a)
                print("    entropy_input = \"%s\";" % entropy_input)
                print("    nonce = \"%s\";" % nonce)
                print("    personalization_string = \"%s\";" % personalization_string)
                print("    entropy_input_reseed = \"%s\";" % entropy_input_reseed)
                print("    additional_input_reseed = \"%s\";" % additional_input_reseed)
                print("    additional_input_1 = \"%s\";" % additional_input_1)
                print("    additional_input_2 = \"%s\";" % additional_input_2)
                print("    returned_bits = \"%s\";" % returned_bits)
                print("  } ;")
            
        line = rsp.readline()

    print("]")

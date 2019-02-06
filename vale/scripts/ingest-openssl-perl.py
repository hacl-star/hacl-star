#!/usr/bin/python

import argparse
import glob
import re

# For details, see: https://github.com/lark-parser/lark
from lark import Lark, Transformer, v_args  # pip install lark-parser


grammar = """

    COMMENT: /#.*/
    hex: "0x" (NUMBER | "a".."f" | "A".."F")+
    exp: /`.*`/
    num: NUMBER | hex | exp
    const: "\\$" num
    var: "$" NAME
    reg: "%" NAME
    base: var | reg
    offset_add: num "+" num
    offset_sub: num "-" num
    offset: num | offset_add | offset_sub
    mem_op: offset "(" base ")"
    label_target: "." NAME
    op: const | var | mem_op | label_target
    ops: [op ("," op)*]
    instruction: NAME ops COMMENT?
    label: "." NAME ":"

    ignored: ALIGN | TYPE
    proc_decl: NAME ":"    
    procedure: proc_decl (instruction|label)+
    code: ".text" procedure+ ".text"

    ALIGN: /\.align.*/
    TYPE: /\.type.*/

    start: code

    %import common.CNAME -> NAME
    %import common.INT -> NUMBER
    %import common.WS
    %ignore WS 

"""

example = """

.text
_aesni_ctr32_ghash_6x:
    	vmovdqu		0x20($const),$T2	# borrow $T2, .Lone_msb
	sub		\$6,$len
	vpxor		$Z0,$Z0,$Z0		# $Z0   = 0
        vmovdqu		0x00-0x80($key),$rndkey
	vpaddb		$T2,$T1,$inout1
        vmovdqu		$Z0,16+8(%rsp)		# "$Z3" = 0
	jmp		.Loop6x

.Loop6x:
	add		\$`6<<24`,$counter
	jc		.Lhandle_ctr32		# discard $inout[1-5]?
	vmovdqu		0x00-0x20($Xip),$Hkey	# $Hkey^1
	  vpaddb	$T2,$inout5,$T1		# next counter value
	  vpxor		$rndkey,$inout1,$inout1
	  vpxor		$rndkey,$inout2,$inout2

.text

"""

#def parse(filename):
#    with open(filename) as f:
#        parse = False
#        for line in f.readlines():
#            if line.startswith(".text"):
#                parse = not parse 
#            if parse:
#                r = re.search("^\([\w-]+\):", line)
#                if r:
#                    print "procedure {:quick} %s ()" % r.group(1)
#                    print "\t\tlets"
#                    print "\t\t\tinp @= rdi; out @= rsi; len @= rdx; key @= rcx; ivp @= r8; Xip @= r9;"
#                    print "\t\t\tIi @= xmm0; T1 @= xmm1; T2 @= xmm2; Hkey @= xmm3; Z0 @= xmm4;"
#                    print "\t\t\tZ1 @= xmm5; Z2 @= xmm6; Z3 @= xmm7; Xi @= xmm8;"
#                    print "\t\t\tinout0 @= xmm9; inout1 @= xmm10; inout2 @= xmm11; inout3 @= xmm12; inout4 @= xmm13; inout5 @= xmm14; rndkey @= xmm15;"
#                    print "\t\t\tcounter @= ebx; rounds @= ebp; ret @= r10; const @= r11; in0 @= r14; end0 @= r15;"
#                    print "\n\t\treads"
#                    print "\t\t\tmemTaint;"
#                    print "\n\t\tmodifies"
#                    print "\t\t\tmem; efl;"
#                    print "\n\t\trequires"
#                    print "\n\t\tensures"
#                    print "{\n}\n"
#                    continue
#                r = re.search("\([\w-]+\)               
#                if 
#
#                else:
#                    print line.rstrip()

def parse(filename):

def test():
    parser = Lark(grammar)
    print(parser.parse(example).pretty())




############  Argument parsing and dispatch  ##################

def main():
  parser = argparse.ArgumentParser(description='Translate OpenSSL Perl code into Vale')
  parser.add_argument('--in', action='append', required=True,
    help='Perl code')
  args = parser.parse_args()

  #parse(args.in)
  test()


if (__name__=="__main__"):
  main()

#!/usr/local/bin/python

import argparse
import glob
import re
import sys

# For details, see: https://github.com/lark-parser/lark
from lark import Lark, Transformer, UnexpectedToken, UnexpectedCharacters, v_args  # pip install lark-parser

sys.setrecursionlimit(10000)

grammar = """

    COMMENT: /#.*/
    hex: "-"? "0x" (NUMBER | "a".."f" | "A".."F")+
    exp: /`.*`/
    num: NUMBER | hex | exp
    const: "\\$" "-"? num
    var: "$" NAME
    reg: "%" NAME
    base: var | reg
    offset_add: num "+" num
    offset_sub: num "-" num
    offset: num | "-" num | offset_add | offset_sub
    mem_op: offset? "(" base ("," base)? ")"
    label_target: "." NAME
    op: const | base | mem_op | label_target
    ops: [op ("," op)*]
    instruction: NAME ops COMMENT?
    label: "." NAME ":"

    ignored: ALIGN | TYPE | SIZE
    proc_decl: NAME ":"    
    procedure: proc_decl (instruction|label|COMMENT|ignored)+
    code: (COMMENT|ignored)* ".text" (COMMENT|ignored)* procedure+ (COMMENT|ignored)* 

    ALIGN: ".align" /.*/
    TYPE: ".type" /.*/
    SIZE: ".size" /.*/

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

def print_proc(procname):
    print "procedure {:quick} %s ()" % procname
    print "\t\tlets"
    print "\t\t\tinp @= rdi; out @= rsi; len @= rdx; key @= rcx; ivp @= r8; Xip @= r9;"
    print "\t\t\tIi @= xmm0; T1 @= xmm1; T2 @= xmm2; Hkey @= xmm3; Z0 @= xmm4;"
    print "\t\t\tZ1 @= xmm5; Z2 @= xmm6; Z3 @= xmm7; Xi @= xmm8;"
    print "\t\t\tinout0 @= xmm9; inout1 @= xmm10; inout2 @= xmm11; inout3 @= xmm12; inout4 @= xmm13; inout5 @= xmm14; rndkey @= xmm15;"
    print "\t\t\tcounter @= ebx; rounds @= ebp; ret @= r10; const @= r11; in0 @= r14; end0 @= r15;"
    print "\n\t\treads"
    print "\t\t\tmemTaint;"
    print "\n\t\tmodifies"
    print "\t\t\tmem; efl;"
    print "\n\t\trequires"
    print "\n\t\tensures"
    print "{\n}\n"

def parse(filename):
    parser = Lark(grammar)
    #print "Reading from %s" % filename
    ast = None
    with open(filename) as f:
        try:
            ast = parser.parse(f.read())
        except UnexpectedToken as e:
            print e
            print e.considered_rules
        except UnexpectedCharacters as e:
            print e
            print e.considered_tokens
    return ast

def test():
    parser = Lark(grammar)
    print(parser.parse(example).pretty())

def print_vale(ast):
    print ast


############  Argument parsing and dispatch  ##################

def main():
  parser = argparse.ArgumentParser(description='Translate OpenSSL Perl code into Vale')
  parser.add_argument('--open', action='store', required=True,
    help='Perl code')
  args = parser.parse_args()

  #test()
  ast = parse(args.open)
  print_vale(ast)


if (__name__=="__main__"):
  main()

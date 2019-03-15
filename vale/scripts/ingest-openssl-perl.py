#!/usr/local/bin/python

import argparse
import glob
import re
import sys

# For details, see: https://github.com/lark-parser/lark
from lark import Lark, Transformer, UnexpectedToken, UnexpectedCharacters, v_args  # pip install lark-parser
import lark

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
    comment: COMMENT
    instruction: NAME ops comment?
    label: "." NAME ":"

    ignored: ALIGN | TYPE | SIZE
    proc_decl: NAME ":"   
    _proc_item: instruction
              | label
              | ignored
    procedure: proc_decl _proc_item+
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

.Loop6x:
"""

#        vmovdqu		0x00-0x80($key),$rndkey
#	vpaddb		$T2,$T1,$inout1
#        vmovdqu		$Z0,16+8(%rsp)		# "$Z3" = 0
#	jmp		.Loop6x
#
#.Loop6x:
#	add		\$`6<<24`,$counter
#	jc		.Lhandle_ctr32		# discard $inout[1-5]?
#	vmovdqu		0x00-0x20($Xip),$Hkey	# $Hkey^1
#	  vpaddb	$T2,$inout5,$T1		# next counter value
#	  vpxor		$rndkey,$inout1,$inout1
#	  vpxor		$rndkey,$inout2,$inout2
#
#"""

def print_proc_header(procname):
    print "procedure {:quick} %s ()" % procname
    print "    lets"
    print "      inp @= rdi; outp @= rsi; len @= rdx; key @= rcx; ivp @= r8; Xip @= r9;"
    print "      Ii @= xmm0; T1 @= xmm1; T2 @= xmm2; Hkey @= xmm3; Z0 @= xmm4;"
    print "      Z1 @= xmm5; Z2 @= xmm6; Z3 @= xmm7; Xi @= xmm8;"
    print "      inout0 @= xmm9; inout1 @= xmm10; inout2 @= xmm11; inout3 @= xmm12;"
    print "      inout4 @= xmm13; inout5 @= xmm14; rndkey @= xmm15;"
    print "      counter @= rbx; rounds @= rbp; ret @= r10; constp @= r11; in0 @= r14; end0 @= r15;"
    print "\n    reads"
    print "      memTaint;"
    print "\n    modifies"
    print "      mem; efl;"
    print "\n    requires"
    print "\n    ensures"
    print "{\n}\n"

def parse(filename):
    parser = Lark(grammar)
    #print "Reading from %s" % filename
    ast = None
    with open(filename) as f:
        try:
            #ast = parser.parse(f.read())
            ast = parser.parse(example)
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

def is_load(ops):
    for op in ops[:-1]:
        if op.data == "mem_op":
            return True
    return False

def is_store(ops):
    return ops[-1].data == "mem_op"


def print_op(op):
    print "Data: %s" % op.data
    print "Data of children[0]: %s" % op.children[0].data
    if op.children[0].data == "base":
        return op.children[0].children[0].children[0]
    return "<NotImpl>"
    #return "%s" % op

def print_instr(nodes):
    proc_name = nodes[0]
    print "Intr name: %s" % proc_name 
    ops = nodes[1].children
    comment = None
    if len(nodes) > 2:
        comment = nodes[2].children[0]
        print "Comment: %s" % comment

    if proc_name == "vmovdqu":
        if is_load(ops):
            print "\tLoad128_buffer(" + print_op(ops[0]) + ", " + print_op(ops[1]) + ", " + offset + "Secret, some_buffer, some_index);"
            pass
        elif is_store(ops):
            print "\tStore128_buffer(" + print_op(ops[1]) + ", " + print_op(ops[0]) + ", " + offset + "Secret, some_buffer, some_index);"
            pass
        else:
            print "\tMov128(" + print_op(ops[1]) + ", " + print_op(ops[0]) + ");"


def print_procedure(nodes):
    for n in nodes:
#        print "Checking %s" % n
#        print "It's of type %s " % type(n)
        if n.data == 'proc_decl':
            print "Found decl: %s" % n.children[0]
            #print_proc_header(n.children[0])
        elif n.data == 'label':
            print "\t// Label: .%s" % n.children[0]
        elif n.data == 'instruction':
            print_instr(n.children)
        else:
            print "WARNING: Unknown node: %s" % n

def print_vale(ast):
    #print ast.pretty()
    #print ast.children[0]
    #print ast.children[0].children[0]
    for child in ast.children[0].children:  # Skip to the contents of `code`
        if child.data == 'ignored':
            continue
        if child.data == 'procedure':
            print_procedure(child.children)


############  Argument parsing and dispatch  ##################

def main():
  parser = argparse.ArgumentParser(description='Translate OpenSSL Perl code into Vale')
  parser.add_argument('--open', action='store', required=True,
    help='Perl code')
  args = parser.parse_args()

  #test()
  #ast = parse(args.open)
  #print_vale(ast)
  print_proc_header("loop6x_preamble")
  print_proc_header("loop6x_step")


if (__name__=="__main__"):
  main()

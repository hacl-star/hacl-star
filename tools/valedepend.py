# This file requires Python version >= 3.3

import re
import sys
import argparse
import os, os.path
#import subprocess
#import traceback
#import pdb
#import SCons.Util
#import atexit
#import platform
#import fnmatch
#import pathlib
#import shutil

if sys.version_info < (3, 3):
  print('Requires Python version >= 3.3, found version ' + sys.version_info)
  exit(1)

##################################################################################################
#
#   Command-line options
#
##################################################################################################

arg_parser = argparse.ArgumentParser()
arg_parser.add_argument('-in', action = 'append', dest = 'vaf_file', required = True)
arg_parser.add_argument('-include', action = 'append', dest = 'include_dir', required = False)
args = arg_parser.parse_args()
vaf_files = args.vaf_file
inc_dirs = [] if args.include_dir == None else args.include_dir

##################################################################################################
#
#   Dependency analysis
#
##################################################################################################

deps = {}

# match 'include {:attr1} ... {:attrn} "filename"'
# where attr may be 'verbatim' or 'from BASE'
vale_include_re = re.compile(r'include((?:\s*\{\:(?:\w|[ ])*\})*)\s*"(\S+)"', re.M)
vale_fstar_re = re.compile(r'\{\:\s*fstar\s*\}')
vale_from_base_re = re.compile(r'\{\:\s*from\s*BASE\s*\}')
vale_import_re = re.compile(r'module\s+[a-zA-Z0-9_]+\s*[=]\s*([a-zA-Z0-9_.]+)')

# Drop the '.vaf', '.fst', etc.
def file_drop_extension(file):
    return os.path.splitext(file)[0]

# Given source file name, return file name in object directory
def to_obj_dir(file):
    if file.startswith('obj'):
        return file
    else:
        return os.path.join('obj', file)

def depends(target, source):
    target = os.path.normpath(target)
    source = os.path.normpath(source)
    if not (target in deps):
        deps[target] = set()
    deps[target].add(source)

def find_fsti(module):
    for d in inc_dirs:
        if os.path.isfile(os.path.join(d, module + '.fsti')):
            return os.path.join(d, module + '.fsti')
        elif os.path.isfile(os.path.join(d, module + '.fst')):
            return os.path.join(d, module + '.fst')
    raise Exception('Could not find fst/fsti for dependency ' + module)

def vale_dependency_scan(vaf):
    with open(vaf) as f:
        contents = f.read()
    dirname = os.path.dirname(vaf)
    vaf_includes = vale_include_re.findall(contents)
    fst_includes = vale_import_re.findall(contents)
    obj_file_base = file_drop_extension(to_obj_dir(vaf))
    fst = obj_file_base + '.fst'
    fsti = obj_file_base + '.fsti'
    types_vaf = obj_file_base + '.types.vaf'
    depends(fst, vaf)
    depends(fsti, vaf)
    depends(fst, types_vaf)
    depends(fsti, types_vaf)
    for (attrs, inc) in vaf_includes:
       if vale_fstar_re.search(attrs):
           dumpsourcebase = to_obj_dir(find_fsti(inc))
           dumpsourcefile = dumpsourcebase + '.dump'
           depends(types_vaf, dumpsourcefile)
       else:
           f = os.path.join('code' if vale_from_base_re.search(attrs) else dirname, inc)
           ffsti = to_obj_dir(file_drop_extension(f) + '.fsti')
           ftypes_vaf = to_obj_dir(file_drop_extension(f) + '.types.vaf')
           depends(fst, ffsti)
           depends(fsti, ffsti)
           depends(types_vaf, ftypes_vaf)

for vaf in vaf_files:
    try:
        vale_dependency_scan(vaf)
    except Exception as e:
        print('Error in file ' + vaf)
        print(e)
        exit(1)

for target in sorted(deps.keys()):
    print(target + " : " + " ".join(list(deps[target])))
    print()


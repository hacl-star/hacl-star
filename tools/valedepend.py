# This file requires Python version >= 3.3

import re
import sys
import argparse
import os, os.path
import traceback

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
arg_parser.add_argument('-deps', action = 'store', dest = 'deps_file', required = False)
args = arg_parser.parse_args()
vaf_files = args.vaf_file
inc_dirs = [] if args.include_dir == None else args.include_dir
deps_file = args.deps_file

##################################################################################################
#
#   Dependency analysis
#
##################################################################################################

deps = {}  # map target names to source names
commands = {}  # map target names to commands (recipes)
dump_deps = {}  # map F* type .dump file names x.dump to sets of .dump file names that x.dump depends on
vaf_dump_deps = {}  # map .vaf file names x.vaf to sets of .dump file names that x.vaf depends on
vaf_vaf_deps = {}  # map .vaf file names x.vaf to sets of y.vaf file names that x.vaf depends on

# match 'include {:attr1} ... {:attrn} "filename"'
# where attr may be 'verbatim' or 'from BASE'
vale_include_re = re.compile(r'include((?:\s*\{\:(?:\w|[ ])*\})*)\s*"(\S+)"', re.M)
vale_fstar_re = re.compile(r'\{\:\s*fstar\s*\}')
vale_from_base_re = re.compile(r'\{\:\s*from\s*BASE\s*\}')
vale_import_re = re.compile(r'module\s+[a-zA-Z0-9_]+\s*[=]\s*([a-zA-Z0-9_.]+)')

cwd = os.path.normpath(os.getcwd()).replace('\\', '/')

def norm(path):
    p = os.path.normpath(path).replace('\\', '/')
    if p.startswith(cwd):
        p = p[len(cwd) + 1:]
    return p

# Drop the '.vaf', '.fst', etc.
def file_drop_extension(file):
    return norm(os.path.splitext(file)[0])

# Given source file name, return file name in object directory
def to_obj_dir(file):
    file = norm(file)
    return file
    if os.path.isabs(file):
        file = os.path.join('external', os.path.basename(file))
    if file.startswith('obj'):
        return norm(file)
    else:
        return norm(os.path.join('obj', file))

def depends(target, source):
    target = norm(target)
    source = norm(source)
    if not (target in deps):
        deps[target] = set()
    deps[target].add(source)

def command(target, cmd):
    target = norm(target)
    if not (target in deps):
        deps[target] = set()
    commands[target] = cmd

def find_fsti(module):
    for d in inc_dirs:
        if os.path.isfile(os.path.join(d, module + '.fsti')):
            return norm(os.path.join(d, module + '.fsti'))
        elif os.path.isfile(os.path.join(d, module + '.fst')):
            return norm(os.path.join(d, module + '.fst'))
    raise Exception('Could not find fst/fsti for dependency ' + module)

def vale_dependency_scan(vaf):
    with open(vaf) as f:
        contents = f.read()
    dirname = norm(os.path.dirname(vaf))
    vaf_includes = vale_include_re.findall(contents)
    fst_includes = vale_import_re.findall(contents)
    obj_file_base = file_drop_extension(to_obj_dir(vaf))
    fst = obj_file_base + '.fst'
    fsti = obj_file_base + '.fsti'
    types_vaf = obj_file_base + '.types.vaf'
    vaf_dump_deps[vaf] = set()
    vaf_vaf_deps[vaf] = set()
    depends(fst, vaf)
    depends(fsti, vaf)
    depends(fst, types_vaf)
    depends(fsti, types_vaf)
    for (attrs, inc) in vaf_includes:
        if vale_fstar_re.search(attrs):
            dumpsourcebase = to_obj_dir(find_fsti(inc))
            dumpsourcefile = dumpsourcebase + '.dump'
            depends(types_vaf, dumpsourcefile)
            vaf_dump_deps[vaf].add(dumpsourcefile)
        else:
            f = norm(os.path.join('code' if vale_from_base_re.search(attrs) else dirname, inc))
            ffsti = to_obj_dir(file_drop_extension(f) + '.fsti')
            ftypes_vaf = to_obj_dir(file_drop_extension(f) + '.types.vaf')
            depends(fst, ffsti)
            depends(fsti, ffsti)
            depends(types_vaf, ftypes_vaf)
            vaf_vaf_deps[vaf].add(f)

def vale_types_command(source_vaf):
    source_base = file_drop_extension(to_obj_dir(source_vaf))
    types_vaf = source_base + '.types.vaf'
    done = set()
    dumps = []
    def collect_dumps_in_order(x):
        if not (x in done):
            done.add(x)
            for y in sorted(dump_deps[x]):
                # if x depends on y, y must appear first
                collect_dumps_in_order(y)
            x_vaf = re.sub('\.dump$', '.types.vaf', x)
            dumps.append(x)
    for vaf in sorted(vaf_vaf_deps[source_vaf] | {source_vaf}):
        for x in sorted(vaf_dump_deps[vaf]):
            collect_dumps_in_order(x)
    # FIXME this is supposed to be a set which is not ordered so adding a single
    # entry with spaces in it to get the right order
    # FIXME this is supposed to generate a command but instead we really just
    # want dependencies
    deps[types_vaf] = set()
    deps[types_vaf].add(" ".join([x for x in dumps]))

def compute_fstar_deps():
    with open(deps_file, "r") as lines:
        for line in lines:
            line = line.strip()
            if 'Warning:' in line:
                print(line)
                continue
            if len(line) == 0:
                continue
            if '(Warning ' in line:
                # example: "(Warning 307) logic qualifier is deprecated"
                continue
            if line.endswith(':'):
                line = line + ' '
            # lines are of the form:
            #   a1.fst a2.fst ... : b1.fst b2.fst ...
            targets, sources = line.split(': ', 1) # ': ', not ':', because of Windows drive letters
            sources = sources.split()
            targets = targets.split()
            # Computing types from F* files
            # Dump F* types for for each of a1.fst a2.fst ... into a1.fst.dump, a2.fst.dump, ...
            for t in targets:
                dumptargetfile = to_obj_dir(t + '.dump')
                if not (dumptargetfile in dump_deps):
                    dump_deps[dumptargetfile] = set()
                for s in sources:
                    dump_deps[dumptargetfile].add(to_obj_dir(s + '.dump'))

for vaf in vaf_files:
    try:
        vale_dependency_scan(norm(vaf))
    except Exception as e:
        print('Error in file ' + vaf)
        print(e)
        print(traceback.format_exc())
        exit(1)

if deps_file != None:
    compute_fstar_deps()
    for vaf in vaf_files:
        try:
            vale_types_command(norm(vaf))
        except Exception as e:
            print('Error in file ' + vaf)
            print(e)
            print(traceback.format_exc())
            exit(1)

for target in sorted(deps.keys()):
    print(target + " : " + " ".join(list(deps[target])))
    if (target in commands):
        print('\t' + commands[target])
    print()


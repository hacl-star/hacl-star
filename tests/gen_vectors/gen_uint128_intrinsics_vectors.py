import os
import random

vector_template = '''static uint64_t {}[{}] =
  {{
    {}
  }};

'''

max_u64 = 0xffffffffffffffff

def get_random_u64 (size):
  return '0x' + (os.urandom(size).hex() if size != 0 else '0')

def print_vectors (name, l):
  return vector_template.format(name, str(len(l)), ',\n    '.join(l))

def main():
  # (size of a, size of b, number of vectors to generate)
  configs = [(0,0,1), (0,1,10), (1,1,10), (2,2,10), (2,3,10), (3,4,10),
             (4,4,10), (5,4,10), (4,5,10), (6,6,10), (7,7,10), (8,8,20)]
  a_vectors = []
  b_vectors = []
  cin_vectors = []
  addcarry_res_vectors = []
  addcarry_cout_vectors = []
  subborrow_res_vectors = []
  subborrow_cout_vectors = []
  for c in configs:
    for i in range(c[2]):
      a = get_random_u64(c[0])
      b = get_random_u64(c[1])
      cin = '0x' + str(random.randint(0,1))
      a_vectors.append(a)
      b_vectors.append(b)
      cin_vectors.append(cin)

      addition = int(a, 16) + int(b, 16) + int(cin, 16)
      cout = addition // max_u64
      res = addition % max_u64
      res = res - 1 if cout == 1 else res
      addcarry_res_vectors.append(hex(res))
      addcarry_cout_vectors.append(hex(cout))

      subtraction = int(a, 16) - int(b, 16) - int(cin, 16)
      if subtraction >= 0:
        res = subtraction
        cout = 0
      else:
        res = max_u64 + subtraction + 1
        cout = 1
      subborrow_res_vectors.append(hex(res))
      subborrow_cout_vectors.append(hex(cout))

  with open('uint128-intrinsics_vectors.h', 'w') as f:
    f.write('static uint32_t num_vectors = {};\n\n'.format(len(a_vectors)))
    f.write(print_vectors('a_vectors', a_vectors))
    f.write(print_vectors('b_vectors', b_vectors))
    f.write(print_vectors('cin_vectors', cin_vectors))
    f.write(print_vectors('addcarry_res_vectors', addcarry_res_vectors))
    f.write(print_vectors('addcarry_cout_vectors', addcarry_cout_vectors))
    f.write(print_vectors('subborrow_res_vectors', subborrow_res_vectors))
    f.write(print_vectors('subborrow_cout_vectors', subborrow_cout_vectors))

main ()

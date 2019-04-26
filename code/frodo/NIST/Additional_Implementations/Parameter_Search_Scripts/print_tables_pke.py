"""Generation of LaTeX tables for the paper and CDFs for the C code.

Copyright (c) 2016 Joppe Bos, Leo Ducas, Ilya Mironov, Valeria Nikolaenko,
                   Ananth Raghunathan, Douglas Stebila

Released under the MIT License; see LICENSE.txt for details.
"""
from math import log
from approx_distr import approximate_dgauss
from discrete_distr import dgauss, bits_needed_to_sample, nonnegative_half, \
  pdf_product, cutoff_tails, distribution_to_c
from failure_prob_pke import exact_failure_prob_pke
from pqsec import optimize_attack, svp_classical, svp_quantum, svp_plausible, \
  primal_cost, dual_cost
from renyi import renyi, opt_renyi_bound


def distribution_to_tex(p):
  """Formats distribution for use in TeX file.

  Args:
    p: A dictionary with entries for 'distr', 'sigma', 'a', 'name'

  Returns:
    LaTeX string.
  """

  distr, sigma, a, distr_name = p['distr'], p['sigma'], p['a'], p['name']

  dg = dgauss(sigma)

  b = bits_needed_to_sample(distr)
  ret = '{} & {} & {:.3f} &'.format(distr_name, b + 1, sigma)

  for i in sorted(distr.iterkeys()):
    if i >= 0:
      p = int(round(distr[i] * 2**b))
      if i == 0:
        p *= 2
      ret += r'\!\!{}\!\!&'.format(p)

  for i in xrange(max(distr.iterkeys()), 11):
    ret += '&'

  divergence = renyi(distr, nonnegative_half(dg), a)
  ret += r' {:.1f} & ${:.2f}\times 10^{{-4}}$'.format(a, divergence * 10**4)
  return ret + r' \\'


def security_to_tex(p, print_sec=True):
  """Formats security estimates for use in TeX file.

  Args:
    p: A dictionary with entries for 'name', 'n', 'q', 'distr', 'sigma'
    print_sec: If true, output will include security estimates

  Returns:
    LaTeX string.
  """
  name, n, qlog, d, sigma = p['name'], p['n'], p['q'], p['distr'], p['sigma']

  samples = n * (p['n_bar'] + p['m_bar']) + p['n_bar'] * p['m_bar']
  q = 2**qlog
  ret = ''

  ret += r'\multirow{2}{*}{' + name.capitalize() + '} '

  for cost in [primal_cost, dual_cost]:
    m_pc, b_pc, cost_pc = optimize_attack(
        q, n, samples, sigma, cost, svp_classical, verbose=False)
    _, _, cost_pq = optimize_attack(
        q, n, samples, sigma, cost, svp_quantum, verbose=False)
    _, _, cost_pp = optimize_attack(
        q, n, samples, sigma, cost, svp_plausible, verbose=False)

    if cost == primal_cost:
      ret += '& Primal & '
    else:
      ret += '& Dual & '

    ret += '{} & {} &'.format(m_pc, b_pc)

    if print_sec:
      sym_d = pdf_product(d, {+1: .5, -1: .5})
      dg = dgauss(sigma)

      _, cost_pc_reduced = opt_renyi_bound(-cost_pc * log(2), sym_d, dg,
                                           samples)
      _, cost_pq_reduced = opt_renyi_bound(-cost_pq * log(2), sym_d, dg,
                                           samples)
      _, cost_pp_reduced = opt_renyi_bound(-cost_pp * log(2), sym_d, dg,
                                           samples)

      ret += '{} & {} & {} & {} & {} & {} \\\\'.format(
          int(cost_pc), int(cost_pq), int(cost_pp),
          int(-cost_pc_reduced / log(2)), int(-cost_pq_reduced / log(2)),
          int(-cost_pp_reduced / log(2)))  # always round down
    else:
      ret += '-- & -- & -- & -- & -- & -- \\\\'

    ret += '\n'
  return ret


def parameters_to_tex(p):
  """Formats parameters for use in TeX file.

  Args:
    p: A dictionary with entries for 'name', 'n', 'q', 'D', 'B', 'distr'

  Returns:
    LaTeX string.
  """

  def print_cost(attack_type):
    _, _, cost_pc = optimize_attack(
        2**q, n,
        max(nbar, mbar) + n, sigma, dual_cost, attack_type
    )  # Only compute the dual cost, since it is smaller than the primal cost.
    cost_pc -= log(nbar + mbar) / log(
        2)  # Take into account the hybrid argument over mbar + nbar instances.
    _, cost_pc_reduced = opt_renyi_bound(-cost_pc * log(2), sym_distr, dg,
                                         samples)
    return ' & {}'.format(int(-cost_pc_reduced / log(2)))

  name, n, q, b, distr, sigma, nbar, mbar, keylen = (p['name'], p['n'], p['q'],
                                                     p['B'], p['distr'],
                                                     p['sigma'],
                                                     p['n_bar'], p['m_bar'],
                                                     p['key_len'])

  s = name.capitalize()
  s += r' & \!\! {} \!\!'.format(n)
  s += r' & \!\! $2^{{{}}}$ \!\!'.format(q)
  sigma_str = r'{:.3f}'.format(sigma).rstrip('0.')
  s += r' &\quad ' + sigma_str
  s += r' &$[{}\dots {}]$'.format(-max(distr), max(distr))
  s += r' &\!\!{}\!\!'.format(b)

  s += r' & ${}\\times {}$'.format(nbar, mbar)

  sym_distr = pdf_product(distr, {+1: .5, -1: .5})
  failure_prob = exact_failure_prob_pke(sym_distr, 2**q, n, b, keylen)
  if failure_prob == 0:
    s += r' & $0$ '
  else:
    s += r' & $2^{{{:.1f}}}$'.format(log(failure_prob) / log(2))

  ct_len = ((mbar * n + mbar * nbar) * q + keylen) // 8

  s += r' & {}'.format(ct_len)

  samples = n * (nbar + mbar) + nbar * mbar
  dg = dgauss(sigma)

  s += print_cost(svp_classical)
  # s += print_cost(svp_quantum)
  s += print_cost(svp_plausible)

  s += r' \\'

  return s


def print_sizes(p, prefix, kem):
  """Print sizes (in bytes) for a parameter setting.

  Args:
    p: A dictionary with entries for 'n', 'q', 'B', 'n_bar', 'm_bar', 'key_len'
    prefix: A prefix for the scheme's name (e.g., 'Frodo').
    kem: True if the scheme is a KEM, False is the scheme is PKE.

  Returns:
    LaTeX string.
  """
  n, q, b, nbar, mbar, keylen = (p['n'], p['q'], p['B'], p['n_bar'], p['m_bar'],
                                 p['key_len'])

  len_a, len_s, len_d = 128, keylen, keylen

  if kem:
    name = prefix + 'KEM-' + str(n)
    pk_bits = len_a + q * n * nbar
    sk_bits = len_s + pk_bits + 16 * n * nbar
    ct_bits = (mbar * n + mbar * nbar) * q + len_d
    assert keylen % 8 == 0
    ss_str = str(keylen // 8)
  else:  # PKE
    name = prefix + 'PKE-' + str(n)
    pk_bits = len_a + q * n * nbar
    sk_bits = 16 * n * nbar
    ct_bits = (mbar * n + mbar * nbar) * q
    ss_str = ''

  assert pk_bits % 8 == 0 and sk_bits % 8 == 0 and ct_bits % 8 == 0

  return r'{} & {} & {} & {} & {} \\'.format(name, sk_bits // 8, pk_bits // 8,
                                     ct_bits // 8, ss_str)

def main():
  parameters = [
      {
          'name': 'Frodo-640',
          'sigma': 2.750,
          'n': 640,
          'm_bar': 8,
          'n_bar': 8,
          'q': 15,
          'B': 2,
          'key_len': 128,
          'rand_bits': 16,
          'sec_base': 104
      },
      {
          'name': 'Frodo-976',
          'sigma': 2.300,
          'n': 976,
          'm_bar': 8,
          'n_bar': 8,
          'q': 16,
          'B': 3,
          'key_len': 192,
          'rand_bits': 16,
          'sec_base': 151
      },
  ]

  for p in parameters:
    if p['rand_bits'] is not None:
      samples = (p['n_bar'] + p['m_bar']) * p['n'] + p['n_bar'] * p['m_bar']
      _, p['distr'], p['a'] = approximate_dgauss(
          p['sigma'], samples, p['sec_base'], None, p['rand_bits'], quiet=True)
    else:
      gauss_dist = cutoff_tails(dgauss(p['sigma']), 2**-16)
      p['distr'], p['a'] = gauss_dist, float('inf')

  print '### C Code ###'
  for p in parameters:
    print distribution_to_c(p['distr'])
    print

  print '### TABLE 1 ###'
  for p in parameters:
    print parameters_to_tex(p)
  print

  print '### TABLE 2 ###'
  for p in parameters:
    print distribution_to_tex(p)
  print

  print '### TABLE 6 ###'
  for p in parameters:
    print print_sizes(p, 'Frodo', kem=True)
  print r'\midrule'
  for p in parameters:
    print print_sizes(p, 'Frodo', kem=False)
  print

  print '### PARAMETERS FOR CRYPTANALYIS ###'
  for p in parameters:
    print security_to_tex(p, True),
    if p['key_len'] == 192:
      print r'\bottomrule'
    else:
      print r'\midrule'


if __name__ == '__main__':
  main()

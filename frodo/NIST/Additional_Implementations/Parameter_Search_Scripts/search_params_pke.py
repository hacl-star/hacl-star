"""Searches parameter space for LWE-based key exchange protocols.

Copyright (c) 2016 Joppe Bos, Leo Ducas, Ilya Mironov, Valeria Nikolaenko,
                   Ananth Raghunathan, Douglas Stebila

Released under the MIT License; see LICENSE.txt for details.
"""

from math import sqrt, ceil, isinf, floor, log
from pqsec import optimize_attack, svp_classical, svp_quantum, svp_plausible, primal_cost, dual_cost
from failure_prob_pke import heuristic_failure_prob_pke, exact_failure_prob_pke
from approx_distr import approximate_dgauss
from discrete_distr import pdf_product, dgauss, sym_binomial, distr_to_str, nonnegative_half, bits_needed_to_sample
from renyi import opt_renyi_bound
import argparse


def minimize_sum(n):
  """Finds a pair of integers so that their product is at least n and the sum is minimal.

  Args:
     n: An integer.

  Returns:
    A pair of integers.
  """
  opt_k1, opt_k2 = 1, n
  k1 = int(floor(sqrt(n))) + 1
  while k1 > 0 and k1 + n * 1. / k1 < opt_k1 + opt_k2:
    k2 = int(ceil(n * 1. / k1))
    if k1 + k2 < opt_k1 + opt_k2:
      opt_k1, opt_k2 = k1, k2
    k1 -= 1
  return opt_k1, opt_k2


def estimate_cost(q, n, max_m, s, attacks):
  """Finds attack costs (classical, quantum, plausible quantum) for an LWE instance.

  Args:
    q: LWE modulus.
    n: LWE dimension.
    max_m: maximum number of samples
    s: standard deviation of the error distribution
    attacks: A vector specifying types of attacks to consider (svp_classical,
        svp_quantum, svp_plausible)

  Returns:
    A triple of log_2 of the costs of three attacks: classical, quantum, and
    plausible quantum.
    Infinity if analysis is not run.
  """
  r = [float('inf')] * 3
  for cost in [primal_cost, dual_cost]:
    for i, attack in enumerate(attacks):
      _, _, c = optimize_attack(q, n, max_m, s, cost, attack)
      r[i] = min(r[i], c)
  return r


def find_opt_distr(sigma, samples, ubits, cost_cl, cost_pq, cost_pp):
  """Finds an optimal distribution approximating rounded continuous Gaussian.

  Args:
    sigma: The standard deviation of the target (rounded) Gaussian.
    samples: The total number of samples drawn by both parties combined.
    ubits: The bound on the number of uniform bits required for sampling.
    cost_cl, cost_pq, cost_pp: Estimated costs of the rounded Gaussian.

  Returns:
    Four-tuple consisting of the distribution and the cost triplet.
  """
  cost_cl_opt, d, _ = approximate_dgauss(
      sigma, samples, cost_cl, None, ubits, quiet=True)

  sym_d = pdf_product(d, {+1: .5, -1: .5})

  dg = dgauss(sigma)

  _, cost_pq_opt = opt_renyi_bound(-cost_pq * log(2), sym_d, dg, samples)
  _, cost_pp_opt = opt_renyi_bound(-cost_pp * log(2), sym_d, dg, samples)

  return [
      sym_d, cost_cl_opt, -cost_pq_opt / log(2), -cost_pp_opt / log(2)
  ]


def find_binomial_cost(sigma, samples, cost_cl, cost_pq, cost_pp):
  """Estimates the cost of replacing a rounded Gaussian with a binomial.

  Args:
    sigma: The standard deviation of the Gaussian.
    samples: The total number of samples drawn by Alice and Bob.
    cost_cl, cost_pq, cost_pp: Estimated costs of the rounded Gaussian.

  Returns:
    Four-tuple consisting of the distribution and the cost triplet.
  """

  dg = dgauss(sigma)
  # The binomial is defined as B(2*z, .5) - z.
  sb = sym_binomial(2 * sigma**2)

  _, cost_cl_binomial = opt_renyi_bound(-cost_cl * log(2), sb, dg, samples)
  _, cost_pq_binomial = opt_renyi_bound(-cost_pq * log(2), sb, dg, samples)
  _, cost_pp_binomial = opt_renyi_bound(-cost_pp * log(2), sb, dg, samples)

  return [
      sb, -cost_cl_binomial / log(2), -cost_pq_binomial / log(2),
      -cost_pp_binomial / log(2)
  ]


def minimize_bandwidth(classical_lb,
                       quantum_lb,
                       plausible_lb,
                       ubits,
                       sigmas,
                       prob_of_failure=128,
                       agree_bits=256):
  """Searches the parameter space to minimize bandwidth. Prints to stdout.

  Args:
    classical_lb: A lower bound on classical security (None if undefined).
    quantum_lb: A lower bound on quantum security (None if undefined).
    plausible_lb: A conservative lower bound on security (None if undefined).
    ubits: The bound on the number of uniform bits required for sampling.
    sigmas: The list of sigmas to explore.
    prob_of_failure: Minimally acceptable probability of failure.
    agree_bits: Target key length.
  """

  def check_costs(cost_cl, cost_pq, cost_pp):
    """Checks whether the costs satisfy lower bounds.

    Args:
      cost_cl, cost_pq, cost_pp: Costs as binary logarithms.

    Returns:
      True if lower bounds are satisfied.
    """
    return ((classical_lb is None or cost_cl >= classical_lb) and
            (quantum_lb is None or cost_pq >= quantum_lb) and
            (plausible_lb is None or cost_pp >= plausible_lb))

  def print_intermediate_result(opt_d, qlog, n, w, m_bar, n_bar, sigma,
                                bandwidth, heuristic_pr_failure,
                                actual_pr_failure, costs_gauss, costs_opt):
    """A printer helper.
    """
    print distr_to_str(nonnegative_half(opt_d))
    print 'q = 2**{}, n = {}, w = {}, mbar x nbar = {} x {}, sigma = {:.3f}:'.format(
        qlog, n, w, m_bar, n_bar, sigma),
    print 'bandwidth = {:.2f} kB,'.format(bandwidth / (8. * 1000)),

    print('heuristic Pr of failure = {:.1f}, '
          'actual Pr of failure = {:.1f},'.format(
              log(heuristic_pr_failure) / log(2),  # can be 0
              log(actual_pr_failure) / log(2))),  # can be 0

    formatted_costs = ', '.join(
        '{:.1f}'.format(c) for c in costs_gauss if not isinf(c))
    print 'security = [{}],'.format(formatted_costs),

    formatted_costs_opt = ', '.join(
        '{:.1f}'.format(c) for c in costs_opt if not isinf(c))
    print 'security after reduction = [{}],'.format(formatted_costs_opt),

    bits = bits_needed_to_sample(opt_d)
    print 'distribution on [{}, {}], {} bits to sample'.format(
        min(opt_d.iterkeys()), max(opt_d.iterkeys()), bits)

    print ("Parameters for print_tables_pke.py: 'sigma': {:.3f}, 'n': {}, "
           "'m_bar':{}, 'n_bar':{}, 'q': {}, 'B': {}, 'key_len': {}, "
           "'rand_bits': {}, 'sec_base': {:.0f}").format(sigma, n, m_bar, n_bar,
                                                         qlog, w, agree_bits,
                                                         bits, min(costs_gauss))

  # Main body of minimize_bandwidth starts here.

  attacks = [svp_classical]
  if quantum_lb is not None:
    attacks.append(svp_quantum)
  if plausible_lb is not None:
    attacks.append(svp_plausible)

  qlog_list = range(8, 17) # + [24, 32]
  n_list = [n for n in xrange(256, 1200, 16)]

  min_bandwidth_bits = 8 * 50000  # Upper bound on the bandwidth in bits.

  for qlog in qlog_list:
    print 'q = 2**{}'.format(qlog)
    for n in n_list:
      prev_k = None  # number of columns already considered
      # The number of bits to extract; can range between 1 and be as large as
      # the modulus.
      w_list = range(1, 1 + qlog)
      for w in w_list:
        # number of coordinates needed to achieve agree_bits
        required_coordinates = (agree_bits + w - 1) / w
        # number of rows, columns
        m_bar, n_bar = minimize_sum(required_coordinates)
        if (m_bar, n_bar) == prev_k:
          # Nothing to do: w is larger than before but the number
          # of columns is the same.
          continue
        prev_k = (m_bar, n_bar)

        max_m = n + max(m_bar, n_bar)
        bandwidth = (m_bar + n_bar) * qlog * n
        if bandwidth > min_bandwidth_bits:
          continue

        for sigma in sigmas:
          # Quick-and-dirty check on the probability of failure
          heuristic_pr_failure = heuristic_failure_prob_pke(
              2**qlog, n, sigma, w, agree_bits)
          if heuristic_pr_failure > 2**-prob_of_failure:  # very loose bound
            continue

          samples = (m_bar + n_bar) * n + required_coordinates

          # Attack complexity of a single instantiation of the LWE problem.
          costs_gauss_single_shot = estimate_cost(2**qlog, n, max_m, sigma,
                                                  attacks)
          # Taking into account that there are m_bar + n_bar simultaneous instances that all must hold.
          costs_gauss = [
              c - log(m_bar + n_bar) / log(2)
              for c in costs_gauss_single_shot
          ]

          # Checking upper bounds on costs, before trying to find an optimal
          # approximation.
          if not check_costs(*costs_gauss):
            continue

          [opt_d, cost_cl_opt, cost_pq_opt, cost_pp_opt] = find_opt_distr(
              sigma, samples, ubits, *costs_gauss)

          costs_opt = [cost_cl_opt, cost_pq_opt, cost_pp_opt]

          if not check_costs(*costs_opt):
            continue

          actual_pr_failure = exact_failure_prob_pke(opt_d, 2**qlog, n, w,
                                                     agree_bits)
          if actual_pr_failure > 2**-prob_of_failure:
            continue

          min_bandwidth_bits = bandwidth
          print_intermediate_result(opt_d, qlog, n, w, m_bar, n_bar, sigma,
                                    bandwidth, heuristic_pr_failure,
                                    actual_pr_failure, costs_gauss, costs_opt)

  return


def main():
  sigmas = [2.15, 2.2, 2.25, 2.3, 2.35, 2.4, 2.45, 2.5, 2.55, 2.6, 2.65, 2.7,
            2.75, 2.8, 3.]

  parser = argparse.ArgumentParser(description='Sweep parameter space.')
  parser.add_argument(
      '-level', type=int, nargs='?', required=False, help='Level')
  args = parser.parse_args()

  if args.level is None or args.level == 1:
    print '### NIST Level 1 ###'
    minimize_bandwidth(143, 85, 85, 16, sigmas, 128, agree_bits=128)
    print

  if args.level is None or args.level == 3:
    print '### NIST Level 3 ###'
    minimize_bandwidth(207, 116.5, 116.5, 16, sigmas, 192, agree_bits=192)
    print

  # if args.level is None or args.level == 5:
  #   print "### NIST Level 5 ###"
  #   minimize_bandwidth(272, 149, 149, 16, large_sigmas, 256, agree_bits=256)
  #   print


if __name__ == '__main__':
  main()

"""Approximates a rounded continuous Gaussian with a bounded-accuracy distribution.

Exhaustively searches the space of feasible distributions for the best
approximation of the target distribution in the sense of minimizing their
Renyi divergence. The feasible distribution is subject to the following
constraints:
  - Bounded support
  - Fixed precision of probability masses.

Copyright (c) 2016-2017 Joppe Bos, Leo Ducas, Ilya Mironov, Valeria Nikolaenko,
                   Ananth Raghunathan, Douglas Stebila

Released under the MIT License; see LICENSE.txt for details.
"""

from math import fmod, modf, log
from discrete_distr import valid_distr, dgauss, sym_binomial, distr_to_str, filter_negl, nonnegative_half
from renyi import renyi, opt_renyi_bound, renyi_bound, orders

# _cache_round_distr_opt is used to cache results of running round_distr_opt.
# It is a dictionary mapping inputs of round_distr_opt, encoded as a tuple in a
# canonical order, to its output.
_cache_round_distr_opt = {}


def round_distr_opt(d, eps, a, maxsupport=None, quiet=True):
  """Finds a distribution of accuracy eps approximating d, minimizing their Renyi divergence of order a.

  Args:
    d: A distribution given as a dictionary.
    eps: The rounding parameter. eps must divide 1 evenly (typically eps is a
         negative power of 2).
    a: The order of Renyi divergence between d and its approximation.
    maxsupport: An upper bound on the support of the output (can be None).
    quiet: Suppress outputs if True.

  Returns:
    A discrete distribution encoded as a dictionary. All probabilities are
    multiple of eps.
    None if no such distribution is found.
  """

  def round_distr(d, eps, vec, support):
    """Rounds a distribution in a given direction.

    Args:
      d: A distribution given as a dictionary.
      eps: The rounding parameter.
      vec: The direction of rounding as a string ('0' - down, '1' - up).
      support: Support of the distribution as a vector.

    Returns:
      A distribution with entries that are multiple of eps.
    """

    # Although support represents the set of d's keys, support is a vector and
    # as such its order is fixed (unlike d.iter_keys()). An OrderedDict would be
    # just fine too.
    assert len(vec) == len(support)

    r = {}

    for i, ch in enumerate(vec):
      v = support[i]
      _, int_part = modf(d[v] / eps)
      if ch == '0':  # round down
        if int_part > 0:
          r[v] = int_part * eps
      else:  # round up
        r[v] = (int_part + 1) * eps
    return r

  assert valid_distr(d)
  assert fmod(1. / eps, 1.0) < 1E-9

  cache_key = (distr_to_str(filter_negl(d)), eps, a, maxsupport)
  if quiet and cache_key in _cache_round_distr_opt:
    return _cache_round_distr_opt[cache_key]

  # Only keep enough elements of d to get sufficiently close to 1.
  d_trunc = {}
  s = 0.
  for v in sorted(d, key=d.get, reverse=True):
    if s > 1. - eps / 8:
      break
    s += d[v]
    d_trunc[v] = d[v]
    if maxsupport is not None and len(d_trunc) == maxsupport:
      break

  if not quiet:
    print('Truncated distribution has support {}. The truncated tail has mass '
          '{}.').format(len(d_trunc), 1. - sum(d_trunc.itervalues()))

  support = d_trunc.keys()
  n = len(support)

  # round everything down
  lb = sum(round_distr(d_trunc, eps, '0' * n, support).itervalues())
  # round everything up
  lu = sum(round_distr(d_trunc, eps, '1' * n, support).itervalues())
  if lb > 1. or lu < 1.:  # Fail early
    if not quiet:
      print 'Rounding is not feasible.'
    return None

  best_rdiv = float('inf')
  best_appr = None

  # Enumerate all possible combinations of rounding
  for vec in xrange(2**n):
    binvec = bin(vec)[2:].zfill(n)
    appr = round_distr(d_trunc, eps, binvec, support)
    if valid_distr(appr):
      rdiv = renyi(appr, d, a)
      if rdiv < best_rdiv:
        best_rdiv = rdiv
        best_appr = appr

  if not quiet:
    if best_appr is None:
      print 'The distribution cannot be rounded.'
    else:
      best_appr = filter_negl(best_appr)
      print(
          'Optimal distribution rounded to {} has support {}. Renyi divergence '
          'of order {} is {:.5f}.').format(eps, len(best_appr), a, best_rdiv)

  _cache_round_distr_opt[cache_key] = best_appr
  return best_appr


def approximate_dgauss(sigma,
                       samples,
                       base_security,
                       max_table_len,
                       max_rand_bits,
                       suffix='',
                       quiet=True):
  """Approximates rounded Gaussian with a binomial and an optimal discrete distribution.

  Args:
    sigma: The standard deviation of the target Gaussian distribution.
    samples: Total number of samples per protocol run.
    base_security: The baseline security level, in bits (e.g., 150.34).
    max_table_len: Upper bound on the support of the distribution (can be
      None).
    max_rand_bits: Total number of uniformly random bits required for
      sampling.
    suffix: Suffix for printed out names.
    quiet: If quiet, suppress all output.

  Returns:
    (security bound, non-negative part of distribution, optimal Renyi order).
    """

  dg = dgauss(sigma)
  half_dg = nonnegative_half(dg)

  if not quiet:
    print suffix
    z = sigma**2 * 2
    if fmod(z, 1.) != 0:
      print 'Skipping binomial'
    else:
      sb = sym_binomial(2 * int(z))
      opt_a_sb, opt_bound_sb = opt_renyi_bound(-base_security * log(2), sb, dg,
                                               samples)

      print(
          'Sigma = {:.3f}: Binomial distribution z = {}, security = {:.2f}, a '
          '= {:.2f};').format(sigma, z, -opt_bound_sb / log(2), opt_a_sb)

  max_security = 0
  opt_r = None
  opt_d = {}
  opt_a = None

  for a in orders:
    for random_bits in xrange(1, max_rand_bits):  # reserve one bit for the sign
      d = round_distr_opt(
          half_dg, 2**-random_bits, a, max_table_len, quiet=True)
      if d is not None:
        r = renyi(d, half_dg, a)
        security = -renyi_bound(-base_security * log(2), r * samples, a)
        if security > max_security:
          max_security = security
          opt_a = a
          opt_d = d
          opt_r = r

  if not quiet:
    if max_security == 0:
      print 'Approximation is infeasible under given constraints'
    else:
      print 'Security = {:.2f} a = {} Renyi divergence = {}'.format(
          max_security / log(2), opt_a, opt_r)
  return [max_security / log(2), opt_d, opt_a]

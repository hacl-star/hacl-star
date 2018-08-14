"""Support functions for computing Renyi divergence.

Copyright (c) 2016 Joppe Bos, Leo Ducas, Ilya Mironov, Valeria Nikolaenko,
                   Ananth Raghunathan, Douglas Stebila

Released under the MIT License; see LICENSE.txt for details.
"""

from math import log

# Constrain Renyi orders of interest to the following set for performance
# and aesthetic reasons.
orders = [
    1.5, 2., 5., 10., 15., 20., 25., 30., 40., 50., 75., 100., 200., 500.,
    float('inf')
]


def renyi(p1, p2, a):
  """Computes the Renyi divergence between two distributions.

  Args:
    p1, p2: Discrete distributions represented as dictionaries.
    a: Order of the Renyi divergence, a <> 1, a can be infinity

  Returns:
    Renyi divergence D_a(p1 || p2). Can be infinity.
  """
  if any([v not in p2 for v in p1 if p1[v] > 0]):
    return float('inf')

  if a == float('inf'):
    return log(max([p1[v] / p2[v] for v in p1 if p1[v] > 0]))

  try:
    # It is possible to do addition in the logspace by way of numpy.logaddexp.
    s = sum([p1[v] * float(p1[v] / p2[v]) ** (a - 1) for v in p1 if p1[v] > 0])
  except OverflowError:
    return float('inf')

  return log(s) / (a - 1)


def renyi_bound(ln_pr, r, a):
  """Computes an upper bound on probability via Renyi divergence.

  Computes an upper bound on probability of a distribution under p1 given a
  bound on its probability under p2 and a bound on the Renyi divergence
  between p1 and p2.

  Args:
    ln_pr: Natural logarithm of the probability of an event under p2.
    r: Renyi divergence D_a(p1 || p2).
    a: The Renyi divergence order.

  Returns:
    Natural logarithm on an upper bound on the probability of the same event under p1.
  """
  if a == float('inf'):
    return ln_pr + r
  else:
    return (ln_pr + r) * ((a - 1.) / a)


def opt_renyi_bound(ln_pr, p1, p2, n):
  """Finds the optimal Renyi order and the corresponding bound.

  Given two distributions p1 and p2, and an event of probability exp(ln_pr)
  under p2^n (n-fold direct product), finds the optimal Renyi order so that
  the upper bound via Renyi divergence on the event's probability under p1^n
  is minimized.

  Args:
    ln_pr: Natural logarithm of the event's probability under p2^n.
    p1, p2: Two discrete distributions represented as dictionaries.
    n: Number of samples.

  Returns:
    A pair of floats - an optimal Renyi order and the natural logarithm of an
    upper bound on probability under p1^n.
  """
  if ln_pr is None:
    return None

  minbound = 0
  best_a = 1.0
  for a in orders:
    rn = renyi(p1, p2, a) * n
    bound = renyi_bound(ln_pr, rn, a)  # bound on ln(prob under p1^n)
    if bound < minbound:
      minbound = bound
      best_a = a
  return best_a, minbound

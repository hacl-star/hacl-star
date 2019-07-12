"""Support functions for estimating probability of failure for a PKE scheme.

Copyright (c) 2016 Joppe Bos, Leo Ducas, Ilya Mironov, Valeria Nikolaenko,
                   Ananth Raghunathan, Douglas Stebila

Released under the MIT License; see LICENSE.txt for details.
"""

from math import sqrt, exp, log
from discrete_distr import pdf_product, nfoldconvolution, convolution


def exact_failure_prob_pke(noise, q, n, w, reclen):
  """Computes the probability of failure of PKE (exactly).

  Args:
    noise: The noise distribution as a dictionary.
    q: Modulus.
    n: Vector length.
    w: Number of extracted bits per coordinate.
    reclen: Number of bits to be extracted.

  Returns:
    The probability of failure.
  """

  def pr_rec_failure_pke(x):
    # Probability of failing to recover from an error of magnitude x.
    #        0% if -B/2 <= x < B/2
    #        100% if x >= B/2 or x < -B/2

    x = min(x, q - x)
    b = q / (2**w)
    if x >= b / 2:
      return 1.
    elif x < -b / 2:
      return 1.
    else:
      return 0

  noise_sqr = pdf_product(noise, noise, q)

  v = nfoldconvolution(2 * n, noise_sqr, q)

  v = convolution(v, noise, q)  # v = 2n * (noise^2) + noise

  exact_pr = {x: p * pr_rec_failure_pke(x) for (x, p) in v.iteritems()}

  r1r2 = (reclen + w - 1) / w

  failure_pr = r1r2 * sum(exact_pr.itervalues())

  return failure_pr


def heuristic_failure_prob_pke(q, n, sigma, w, reclen):
  """Computes a heuristic approximation to the probability of failure of PKE.

  Args:
    q: Modulus.
    n: Vector length.
    sigma: Standard deviation of the noise distribution.
    w: Number of extracted bits per coordinate.
    reclen: Number of bits to be extracted.

  Returns:
    A heuristic probability of failure.
  """
  std = sqrt(2 * n * sigma**4 + sigma**2)
  cuttail = q / (std * 2**(w + 1))
  r1r2 = (reclen + w - 1) / w
  return 2 * r1r2 * exp(-cuttail**2 / 2) / log(2)

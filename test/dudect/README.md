dudect: dude, is my code constant time?
=======================================

This is a humble try at determining whether a piece of code runs in
constant time or not. The approach is easy: run it with different
inputs, measure execution time and apply statistics.
This tool is fairly small: the relevant code is around 350 lines.

The approach is described in our paper:
> Oscar Reparaz, Josep Balasch and Ingrid Verbauwhede  
> [dude, is my code constant time?](https://eprint.iacr.org/2016/1123.pdf)  
> DATE 2017

Requirements
------------
A C compiler.

Quick start
-----------
To build, run `make`. This builds a bunch of binaries named `dudect_*`.

Typical output
--------------

Let's have a look at `memcmp()`-based comparison of passwords or MAC tags.
It fails very quickly:

```
$ ./dudect_cmpmemcmp_-O2
meas:    0.37 M, max t: +1271.13, max tau: 3.47e-03, (5/tau)^2: 2.07e+06. Definitely not constant time.
```

The output says: the tested function was executed 370k times
("measurements") and we got a t statistic value of 1271,
deeming the implementation not constant time. t values
larger than 5 mean there is very likely a timing leakage.
(The other figures are not so relevant now.)

Now try some crypto. This is a 32-bit AES128 implementation:
```
$ ./dudect_aes32_-O2
meas:    0.59 M, max t: +561.16, max tau: 9.58e-04, (5/tau)^2: 2.72e+07. Definitely not constant time.
```

In this case, the output says that after 590k measurements we got
a t statistic of 561. A value of 561 is overwhelming evidence
that there is timing leakage.

The two previous cases were easy to catch, since the timing leaks are
huge. There are some cases that are a bit more elaborated. In those
cases, the tool may not detect at first the timing leak, but only when
enough measurements are accumulated. For example let's try a curve25519
implementation with an intentional timing leak:

```
 $ ./dudect_donnabad_-O2
meas:    0.00 M, not enough measurements (9000 still to go).
[...]
meas:    0.01 M, max t:   +0.36, max tau: 3.59e-05, (5/tau)^2: 1.94e+10. For the moment, maybe constant time.
meas:    0.02 M, max t:   +8.22, max tau: 4.02e-04, (5/tau)^2: 1.55e+08. For the moment, maybe constant time.
[...]
meas:    0.02 M, max t:  +11.35, max tau: 5.63e-04, (5/tau)^2: 7.89e+07. Probably not constant time.
meas:    0.02 M, max t:  +16.38, max tau: 7.91e-04, (5/tau)^2: 4.00e+07. Probably not constant time.
meas:    0.02 M, max t:  +23.71, max tau: 1.20e-03, (5/tau)^2: 1.73e+07. Probably not constant time.
^C
```

(I Ctrl-C'ed after some minutes.) Here is what happened:

 * at first we didn't have enough measurements;
 * after 10k measurements (0.01 M) the timing leak is not yet detectable
   (the t statistic is smaller than 10).
 * Once we have around 20k measurements, the timing leak starts to be
   detectable, and we can conclude that the implementation is not constant time
   (t value larger than 10).

If the code exhibits timing variability, the t statistic grows as more
measurements are available. If it surpasses 10 then most likely there
is some timing leak.

If there is no leak, the t statistic will not go beyond 10, for whatever
number of measurements. This is the case when testing a constant-time
piece of code:

```
$ ./dudect_cmpct_-O2
meas:    1.00 M, max t:   +1.94, max tau: 1.94e-06, (5/tau)^2: 6.64e+12. For the moment, maybe constant time.
meas:    2.00 M, max t:   +1.85, max tau: 9.27e-07, (5/tau)^2: 2.91e+13. For the moment, maybe constant time.
meas:    3.00 M, max t:   +1.56, max tau: 5.20e-07, (5/tau)^2: 9.24e+13. For the moment, maybe constant time.
meas:    4.00 M, max t:   +1.63, max tau: 4.08e-07, (5/tau)^2: 1.50e+14. For the moment, maybe constant time.
meas:    4.98 M, max t:   +1.22, max tau: 2.45e-07, (5/tau)^2: 4.15e+14. For the moment, maybe constant time.
meas:    5.98 M, max t:   +1.32, max tau: 2.20e-07, (5/tau)^2: 5.14e+14. For the moment, maybe constant time.
meas:    7.00 M, max t:   +1.52, max tau: 2.17e-07, (5/tau)^2: 5.33e+14. For the moment, maybe constant time.
meas:    7.96 M, max t:   +1.70, max tau: 2.13e-07, (5/tau)^2: 5.52e+14. For the moment, maybe constant time.
meas:    9.00 M, max t:   +1.19, max tau: 1.33e-07, (5/tau)^2: 1.42e+15. For the moment, maybe constant time.
[...]
meas:   70.71 M, max t:   +2.78, max tau: 3.93e-08, (5/tau)^2: 1.62e+16. For the moment, maybe constant time.
^C
```

Here the t statistic will never go beyond 10, since the code is
constant time. The tool runs until it sees enough evidence that
the code is not constant time. This means that *if* the code is
constant time, it will run forever. Just Ctrl-C it when you think
you are done.

Examples
--------

* `dudect_cmpmemcmp` Variable-time memory comparison function
  based on stock `memcmp()`.

* `dudect_cmpct` Purported time-constant memory comparison.
 
* `dudect_aes32` T-tables implementation of the AES.
  A nice example of variable-time crypto implementation.

* `dudect_aesbitsliced` [Bitsliced](https://eprint.iacr.org/2009/129)
  constant-time AES implementation.

* `dudect_donna` Langley's curve25519-donna. Intended to yield
  constant-time code.

* `dudect_donnabad` Variant with a glaring timing leak.


Questions
---------

**How does this work?**
   In a nutshell, this code takes two different inputs, runs the
   piece of code many times for each input and measures how much
   time it takes. If there is a statistical difference on the
   (average) time it takes to run with different inputs, the
   implementation is deemed not time constant. For details, read
   [our paper](https://eprint.iacr.org/2016/1123.pdf) or have a look
   at [the source](src/fixture.c).

**Is this a timing attack?**
   No. This is [leakage detection](http://saluc.engr.uconn.edu/refs/sidechannel/coron04statistics.pdf).
   Presence of leakage is necessary, but not sufficient for an
   attack to work.

**My code passes this tests. Does it mean it is really time constant?**
   Absolutely not. The test implemented is perhaps the simplest form
   of leakage detection. For serious assessment, you should also run
   many other tests, with specially crafted input vectors.
   The test harness implemented here is not yet that comprehensive.
   You're encourage to submit an implementation that is not constant
   time yet passes the test--in that way we can improve the test suite.
   The more you know about the implementation, the better you can
   design input vectors. For inspiration, see [these RSA test vectors](http://csrc.nist.gov/news_events/non-invasive-attack-testing-workshop/papers/09_Jaffe.pdf).

**This was done before.**
   Sure. For example, see the previous work of [Barthe et al.](http://fdupress.net/publications.html#ct-verif) or [Langley](https://github.com/agl/ctgrind).
   Here we take another, very different approach. We do not
   try to formally verify that the piece of code is constant time, but
   rely on actual measurements on the target platform to gather
   statistical evidence to disprove the null hypothesis "the code
   seems to run in constant time". Also, this is standard C code and
   you don't need any exotic tools to run it.

**Warning: experimental quality software.**

Contact
-------
Oscar Reparaz ([COSIC/KU Leuven](http://cosic.be))

(oscar dot reparaz at esat dot kuleuven dot be)

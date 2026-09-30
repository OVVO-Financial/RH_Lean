#!/usr/bin/env python3
"""Analytic critical-edge values for research/LI_DISCRETE_POISSON_OMEGA_NO_GO.md.

Evaluates the entire continuations of the critical Dirichlet series at w = 1/2:
  unit kernel   exp(-P0(w)) = (w-1) exp(-Q(w)),  Q' = -(zeta - 1 - 1/(w-1))
  Poisson       exp(-Gd(w)) = (w-1) exp(-Qd(w)), Qd' = -(zeta - 1 - 2^-w + E - 1/(w-1))
  hard-core     Phi = exp(-Gd) * prod_{q>=3} (1 - w_q q^-w) exp(w_q q^-w)
These match the finite cumulatives of experiments/li_discrete_omega_diagnostics.c,
confirming the identifications.  Agreement is NOT evidence of boundedness.
Requires: mpmath, numpy, scipy.
"""
import mpmath as mp, numpy as np
mp.mp.dps = 20
# unit kernel: P0(w) = sum_{q>=2} q^-w / log q,  Q = P0 + log(w-1),  Q' = -(zeta - 1 - 1/(w-1))
P0_2 = mp.nsum(lambda q: q**-2/mp.log(q), [2, mp.inf])
I0 = mp.quad(lambda u: mp.zeta(u) - 1 - 1/(u-1), [0.5, 1, 2])
Q_half = P0_2 + I0
print("unit kernel  F0(0) = -(1/2) exp(-Q(1/2)) =", -0.5*mp.e**(-Q_half))
# Li weights w_q = int_{q-1}^q dt/log t (q>=3), eps_q = log(q) w_q - 1
Qmax = 2_000_000
q = np.arange(3, Qmax+1, dtype=np.float64)
from scipy.special import expi
li = lambda x: expi(np.log(x))
wq = li(q) - li(q-1)
eps = np.log(q)*wq - 1
def E(u):   # sum_{q>=3} eps_q q^-u, tail via eps_q ~ 1/(2 q log q) integral
    head = np.sum(eps * q**(-u))
    tail = mp.quad(lambda x: x**(-1-u)/(2*mp.log(x)), [Qmax+0.5, mp.inf])
    return head + float(tail)
Gd_2 = float(np.sum(wq*q**-2.0))
Id = mp.quad(lambda u: mp.zeta(u) - 1 - 2**(-u) + E(float(u)) - 1/(u-1), [0.5, 1, 2])
Qd_half = Gd_2 + Id
FP = -0.5*mp.e**(-Qd_half)
print("Poisson      FP(0) = -(1/2) exp(-Qd(1/2)) =", FP)
x = wq/np.sqrt(q)
logcorr = np.sum(np.log1p(-x) + x)
print("hard-core    Phi(1/2) = FP(0) * prod (1-x)e^x =", FP*mp.e**logcorr)
print("sum eps_q/sqrt q (q<=%d) =" % Qmax, np.sum(eps/np.sqrt(q)))

# The QRH leaderboard leader: precise NNS covariance entry point (October 26, 2026)

**Goal:** improve on the certified canonical all-Dirichlet boundary
349843/400000 = 0.8746075 (GTimG/QuasiRiemannTracker PR #76), not
the original 7/8=0.875 baseline. An open PR #79 claims 0.8746074;
do not treat it as verified until the tracker admits it.

## Public verified source of truth

- GTimG/QuasiRiemannTracker main, submission
  arvi-repeated-marks-on-sil-face-20261025.
- Candidate/Main.lean: all Dirichlet characters and positive moduli,
  excludes only the principal pole.
- Source/NFStep2.lean: verified repeated-mark HIGH/LOW feedback.
- Source/ActualWeightedK.lean: squared *actual* row-sum coefficient
  with original characters, conductor zeros and all labels.
- Gain/Gain.lean: exact six-branch per-amplitude detector gain,
  with eight repeated marked slots.
- FourthPower/RepairedRestrictedSource.lean: the actual independent
  fourth-power source supplies GlobalSource (99999/100000) (93/25)
  (3/50), i.e. slope 3.72 rather than the ordinary cost 9/2.
- FourthPower/MixedFirstZero.lean: the zero Fourier mode is
  **exactly diagonal** on fifth-power-free whole columns.
- FinalReturn/ReturnConstants.lean: exact final count/physical
  supplier faces and return certificate.
- Graph/Endpoint.lean: final all-Dirichlet theorem.

The tracker final physical face has exact
  nu=149843/200000=0.749215,
  B=335106151738000623869543064163 /
    344806846470553600000000000000 ≈0.9718662931671763,
  lam=631360617375411063383 /
    210453397504000000000 ≈3.000002018800438,
  h=401/500=0.802.

## A proved detector hard face, independent of marking count

The actual leader defines for amplitude class p in [0,1/2],
marking multiplicity K, live slot width S, and ambient Q:

  invThr(p,K,x,S,Q)=max(x-2*p*K*S, (x-p*Q)/(1-p)),

  plainThr(p,B,lam,h,x,S,Q)=
    max(x-2*p*S, x-2*p*h*Q,
        (x-2*p*B*Q/lam)/(1-2*p/lam)).

The detector root xi(p) is the **minimum** over all six
inverse/plain branch pairs. Its class gain is

  gainP=(1-2*p)*nu*S+nu*(xi(p)-10*Q/(15-6*nu)).

Fix p=1/2, inverse branch 1 (the non-K branch) and plain
branch 2 (the affine source face). Then the exact branch root is

\[
 \xi_{\rm aff}(Q)=
 Q\,\frac{5+(5-6\nu)\left(1+\frac{B}{2(\lambda-1)}\right)}
 {6\nu+(5-6\nu)\left(2+\frac{\lambda}{2(\lambda-1)}\right)}.
\]

Because the class gain is the minimum over the six roots, and
the global gain is at most the p=1/2 class gain, there is a
**universal upper ceiling**

\[
\boxed{
 G_K(\nu,B,\lambda,h,S,Q)\le
 \nu\,\left(\xi_{\rm aff}(Q)
 -\frac{10Q}{15-6\nu}\right).
}
\]

**The right side is independent of K, S and h.** The accompanying
Lean file proves the full six-face implication and the exact
leader-parent cap. This does NOT prove G_K equals its ceiling
uniformly; it proves extra repeated marks cannot breach it.

With the true published physical parent and Q=1, the ceiling
is approximately 0.00340804534 and strictly below 1/290
(=0.0034482759), as formalized in Lean.

Direct finite minimization over p in [0,1/2] of the original six
branches (uniform grid width 0.0001; NUMERICAL, not certified)
gives for K=8 and K=16, respectively, the SAME worst class gain:

| Live slot S | K=8 | K=16 | Worst p |
|--|--:|--:|--:|
| 0.005 | 0.00301319 | 0.00301319 | ≈0.3381 |
| 0.0075 | 0.00339561 | 0.00339561 | ≈0.4808 |
| 0.010 | 0.00340805 | 0.00340805 | 0.5 |
| 0.020 | 0.00340805 | 0.00340805 | 0.5 |
| 0.050 | 0.00340805 | 0.00340805 | 0.5 |

The class p is an **amplitude class**, not the density of
Möbius signs or prime-factor classes. Numerical scan indicates
the repeated-marks strategy is already saturated in the
terminal source regime. More copies are not a credible broad
advance, even though they might improve OTHER sectors.

## Exactly where RH_Lean's NNS/CoDiv can enter

The first Poisson Fourier ZERO mode in the verified fourth-power
source is already exactly diagonal:

  MixedFirstZero.zero_energy_diagonal,
  MixedFirstZero.grouped_first_zero.

So zero-mode offdiagonal negative covariance CANNOT lower its
positive diagonal; the offdiagonal terms vanish exactly.

The proper signed-covariance attack is the *nonzero* Fourier
frequency sector with its actual ideal-labelled, phase-bearing
Gauss columns. Let A_I(k) denote the genuine column response,
and c_I its full complex ideal coefficient. On each admitted
physical bin, with nonnegative weights rho(k):

\[
 E_{\ne0}
 =\sum_{k\ne0}\rho(k)\left|\sum_I c_I A_I(k)\right|^2
 =D_{\ne0}+C_{\ne0},
\]

where

\[
 D_{\ne0}=\sum_I|c_I|^2\sum_{k\ne0}\rho(k)|A_I(k)|^2,
\]

\[
 C_{\ne0}=2\,\Re\sum_{I<J}c_I\overline{c_J}
  \sum_{k\ne0}\rho(k)A_I(k)\overline{A_J(k)}.
\]

This is exactly the NNS/Gram polarization coordinate system.
One can further split real/imaginary signed populations into
upper/lower partial moments, but an inequality about signed
populations must retain the *complex phases, all ideal labels,
full physical weights and changing conductor support*.

RH_Lean's scalar a6(n), periodic 36 decoder, square-block
signed covariance and numerical R=1027 evidence are genuine.
They do NOT by themselves bound these phase-bearing
frequency-dependent offdiagonals. A norm-fiber projection
can erase energy: coefficients c1=1,c2=-1 aggregate to zero,
while responses A1=1,A2=-1 yield |c1*A1+c2*A2|^2=4.
Thus an inequality solely on aggregate a6(n) cannot certify
a bound on the original complete source energy.

## Specific competitive proof target

The viable target is a **new bound on the actual original
nonzero-frequency fourth-power source**, sufficient to replace
one of the two certified source-face parameters:

  current source face: GlobalSource (0.99999) (3.72) (0.06).

Two options:
1. Prove a stronger, unconditional uniform source moment with
   a cost slope lambda < 3.72 (keeping all source phases), or
   change its intercept/cap with all required margin bills.
2. Prove a genuinely stronger HIGH count at amplitude p=1/2,
   breaking the inverse-cap/affine-plain branch ceiling.

The derivative of the explicit hard-face cap with respect to
the parent physical B (for fixed nu, lam, Q) is

\[
 \frac{\partial G_{\rm aff}}{\partial B}
 =\frac{\nu(5-6\nu)Q}
 {2(\lambda-1)
 [6\nu+(5-6\nu)(2+\lambda/(2(\lambda-1)))]}>0
\]

for nu in [1/2,3/4], lambda>1, Q>0. A genuinely better
parent B can change the binding face. At the current final
physical parent, raising B from ~0.971866 to 1 increases
the ceiling from ~0.0034080 to only ~0.0038601:
that by itself is NOT a big leap to 1/2.

The new theorem must be uniformly source-compatible:
for every permitted admissible row bin, amplitude class,
moving conductor, Eisenstein ideal and sextic character,
with both zero masks and the original normalizations,
show a stronger bound on the *whole nonzero frequency
source*. Check all positive diagonal, exceptional,
collision, ramified, tail and height bills. After proving
it, regenerate the actual source face and re-run
the final return certificates at the stronger target.

**Acceptance:** a kernel-checked Lean theorem at a bound
strictly below the current tracker leader, through the
unchanged all-Dirichlet canonical target, with no unproved
new analytic hypotheses. For a MATERIAL leap (e.g. toward
0.85), look for a new source moment or counting mechanism,
not a 1e-6 parameter tweak.

Immediate inspection targets in the tracker:
  FourthPower/MixedFirstActualNonexceptional.lean,
  FourthPower/MixedPoissonLocalization.lean,
  FourthPower/MixedFirstZero.lean,
  FourthPower/KernelCollisionEnergy.lean,
  Source/ActualWeightedK.lean,
  Gain/Gain.lean.

The exact source theorem already controls positive energy
and the p=1/2 class is an explicit obstruction to arbitrarily
large marking gains. A source-level sign-sensitive gain in the
nonzero-frequency fourth-power term would be real new
mathematics. Until proved, no claim of improvement.

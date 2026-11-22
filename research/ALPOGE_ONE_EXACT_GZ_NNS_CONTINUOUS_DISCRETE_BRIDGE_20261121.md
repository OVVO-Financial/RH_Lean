# The one exact bridge point: Alpöge Gz = NNS signed Erdős history

Date: 2026-11-21. Target: direct source-preserving equivalence of the
critical ONE-SIDED analytic observable, not a new abstract Sha model.

## The decisive existing unconditional theorem

The original Alpöge real observable is
  Gz(x) = sum_(1<=n<=floor x) Lambda(n)*(x/n-1)
          -x*log x+(1+gamma)*x.
Source: CocoSgt/riemann-hypothesis-lean,
src/Formalism/StatementOC.lean.

At N>=1, the endpoint term n=N is zero. Consequently the native
RHLean arithmetic definition in
RHLean/Analysis/AlpogeGzErdosReciprocalHistory.lean is the SAME Gz(N).
The existing no-sorry theorem

  alpogeErdosGz_eq_mul_history

proves exactly, for every integer N>=1,

  Gz(N) = N*(sum_(1<=n<N) (psi(n)-n)/(n*(n+1))
               + harmonic(N)-log(N)+gamma).                 (1)

And the existing
  alpogeErdosGz_le_iff_history_le
states the exact, reversible inequality.

This is the *single* scalar equivalent bridge point. Neither a Sha
embedding nor a Gram determinant is necessary to transfer the
one-sided analytic growth bound across this identification.

## Native NNS: same signed sites, same endpoint

Define the actual local error atom
  e_N(n)=(psi(n)-n)/(n*(n+1)), 1<=n<N.
Let U_N=sum max(e_N(n),0), L_N=sum max(-e_N(n),0).
Then by the already proven native NNS theorem
  upperPartialMass_sub_lowerPartialMass_eq_finiteSignedSum

  Gz(N)=N*(U_N-L_N+harmonic(N)-log(N)+gamma).                (2)

This is now explicitly formalized in
  RHLean/Analysis/AlpogeExactNNSGzBridge.lean
as
  alpogeGzNNSHistory_eq_centeredHistory
  alpogeGz_eq_exact_NNSHistory
  alpogeGz_bound_iff_exact_NNS
  alpogeGz_uniformBound_iff_exact_NNS
  alpogeGz_square_iff_exact_NNS.

In particular, for every exponent a and prefactor c, exactly,

  (for all N>=N0>=1, Gz(N)<=c*N^a)
    IFF
  (for all N>=N0>=1, U_N-L_N+harmonic(N)-log(N)+gamma
                        <=c*N^(a-1)).                      (3)

No positivity, approximation, probabilistic independence, or
external uniform bound is assumed in (3).

## Genuine discrete <-> continuous real integral, not resolvent

For N>=2, m=N-1, form the explicit step function
  F_N(t) := m*e_N(floor(m*t)+1), 0<=t<1,
and assign F_N(1)=m*e_N(m) (any value at the endpoint works).
It is Riemann and Lebesgue integrable, with only m-1 jumps.
Partition into the m equal intervals [j/m,(j+1)/m); on each interval
the integrand is constant. Hence exactly

  integral_[0,1] F_N(t) dt = sum_(1<=n<N) e_N(n).            (4)

Thus the original Gz is literally

  Gz(N) = N*(integral_[0,1] F_N(t) dt
                +harmonic(N)-log(N)+gamma).                 (5)

The NNS UPM/LPM are computed on the corresponding same-site atoms
e_N(n), so (4) is a direct *one-source* discrete-to-real integral
identification. NO determinant, Sha proxy, or unrelated sampling
distribution enters.

For a mesh n=q*m and interior tags, the tagged sum equals (4)
exactly at every q>=1. For arbitrary tags with mesh n,
bounded variation yields

 |quadrature(n) - integral_[0,1] F_N|
    <= Var(F_N)/n
    <= (m*sum_(1<=j<m)|e_N(j+1)-e_N(j)|)/n.                (6)

Because this error tends to zero for each FIXED N independent of
all tags, the convergence is pathwise and hence almost sure for
every distribution on tags. This is an exact deterministic analytic
bridge; it does not manufacture uniform-in-N savings.

The integral equality (4) and the variation estimate (6) are fully
proved here mathematically, while the new Lean module formalizes
the exact NNS/arithmetic identities and bound iff. The step-function
integral (4) is not yet claimed as a Lean-checked theorem.

For N=1 set F_1=0 and the empty sum is zero.

## Transfer from integers back to the ORIGINAL REAL Gz

The external repo already contains
  Formalism.zetaPrimeSumErrorLipschitz : GzLipschitz
in src/Formalism/ZetaNonvanishing/GzLipschitz.lean.

Its proof gives for x,y>=1/2 the quantitative constant
  |Gz(x)-Gz(y)| <= (log(4)+7)*|x-y|.
Taking y=floor x for x>=2 gives
  |Gz(x)-Gz(floor x)| <= log(4)+7.                         (7)

Consequently an eventually uniform one-sided bound
  Gz(N) <= C_eps*N^(1/2+eps)
for integers N is equivalent, up to the harmless change of
positive constants and the starting threshold, to the SAME
one-sided growth bound for all real x>=1.
No new Frobenius-to-cochain or class-group identification is
needed for this specific analytic equivalence.

Alpöge's original external statement
  Formalism.LFunctionChainParameters.ConditionalMainTheorem.
    riemann_hypothesis_of_power_bound
takes the real critical Gz bound and supplies RH via
the zetaLandauEps / half-plane nonvanishing route.
The theorem has its own explicit growth premise: this note
does not prove that premise or independently certify the
entire external claimed RH proof.

## What this does and does not close

It closes the *representation* equivalence for the decisive
ONE-SIDED analytic observable, including continuous/discrete
passage and integer/real interpolation. Thus if a genuine
Alpöge critical bound is proved and trusted, it can be
applied immediately to RHLean's exact NNS signed population
at this single bridge point, and conversely.

It does NOT establish that every cohomological payment claim
in the original proof is true; nor does mere equivalence
make the one-sided bound unconditional. The finite Sha
representation developed separately in PR #1180 is optional
for this analytic transport, not a necessary prerequisite.

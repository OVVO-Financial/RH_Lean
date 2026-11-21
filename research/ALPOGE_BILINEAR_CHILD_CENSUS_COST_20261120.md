# Alpöge / RH_Lean: source-faithful bilinear cost test (2026-11-20)

## Outcome

The selected signed-Selberg carrier family from PR #1163 *really does*
have distinct smaller-scale arithmetic error arguments. That is a
substantial **arithmetic identification**. But the particular
"square-root saving just from m distinct arguments" suggested as a
bootstrap is **not a valid general inference**, and in the finite true
prime-source census it very nearly saturates the coherent rather than
the square-root-cancelled regime.

This note gives an exact, theorem-level reformulation of the same
signed source, and measures what is and is not paid. This is NOT
the uniform power bound or a new RH theorem.

## Exact physical input

At X_R=R²-1, p ranges through genuine odd primes R/2<=p<=2R/3,
t_p=floor(X_R/(2p)), a_p=2 log(2) log(p)>0.
The existing source theorem in
RHLean/Analysis/NativePNTSignedSecondSelbergWheelFrontier.lean proves
K2(2p)=a_p and hence the actual selected response is

    S_R := sum_p a_p E(t_p),     E(t)=psi(t)-t.

PR #1163 verifies t_p are distinct, lie in [p,R), and that the
FULL signed Selberg recurrence equals this selected family PLUS
every unselected prime-power/cross-prime term and all first-Selberg
and floor returns. Do not replace those returns by zero.

## NEW exact bilinear source identification

The new Lean file
  research/ALPOGE_BILINEAR_CHILD_CENSUS_COST_20261120.lean
uses an arbitrary finite weighted family and proves the identity

    sum_{p in P} w_p E(t_p)
       = sum_{1<=n<=N} (Lambda(n)-1) W(n)

whenever t_p<=N for all p, where

    W(n) = sum_{p in P, n<=t_p} w_p.

There is no probabilistic expectation, no independence, and no omission
of Lambda at higher prime powers. For the physical carrier 2p this
becomes exactly

    S_R = sum_{1<=n<=X_R} (Lambda(n)-1) W_R(n),
    W_R(n) = 2 log(2) sum_{p in P_R, 2pn<=X_R} log(p).

The floor predicate is equivalent to this raw physical inequality
by the ordinary natural division lemma, with p>0.

Note W_R(n)>=0 for actual primes and is *monotone nonincreasing*
in n. A positive sampling kernel alone cannot cancel coherently signed
error data. The center Lambda(n)-1 is the genuine arithmetic source:
this is an exact bilinear TYPE-II prime census, not m statistically
independent draws. The full source still contains all other K2
returns and first-Selberg/floor channels.

The elementary generic coherence theorem in the Lean file proves:

    (sum_{p in P} 1)^2
       = |P| * sum_{p in P} 1^2.

Thus an m-fold response can have a coherence factor sqrt(m)
relative to its diagonal L2 even with entirely distinct labels.
This theorem is a counterexample ONLY to inference from injectivity;
it is not a statement about the actual prime E(t_p).

## Deterministic physical census, actual prime powers, no random signs

The accompanying script
  scripts/alpoge_child_signed_bilinear_census.py
computes Lambda(n) on all prime powers n<=maxR, psi and reciprocal
Lambda prefixes, and the external Alpoge Gz at each literal child
integer:
    Gz(t)=t*(LambdaRecip(t)-log(t)+gamma)-E(t).
It checks distinct quotient sites and exact finite bilinear Fubini,
then reports Q=(sum_p a_p Gz(t_p))/sqrt(sum_p (a_p Gz(t_p))²).

    R      m      negative Gz fraction       Q        sqrt(m)
    317    10            0.000               3.156       3.162
    549    14            0.000               3.726       3.742
    1027   27            0.000               5.169       5.196
    3000   64            0.000               7.839       8.000
    10000 190            0.000              12.121      13.784
    30000 508            0.063              20.219      22.539

A Cauchy/diagonal-L2 square-root-cancelled *m-fold* sum would have
Q=O(1), not Q close to sqrt(m). At these tested scales, the actual
selected child Gz signals are **coherent**, not decorrelated. The
unweighted Chebyshev errors show both signs at some scales; this is
why the signed complete source and the exact Gz transformation must
both be checked rather than treating either signal as random.

Finite census is NOT proof of an asymptotic lower bound or no-go.
The exact finite statements, however, DO disprove any claimed
logical implication from injectivity to a uniform norm gain.

## Correct complete-source cost gate

The actual upstream bracket in
CocoSgt/riemann-hypothesis-lean,
src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean
requires the SAME family of

  HostFacts D, AskMainBalance, GrowthInequalityHypotheses,
  NodeSizes, ThinScales, ValuesAtX, topExcess<=Err, SmallCosts,
  SizeWindows C eps x n nT nT2 m b k aE Err,

with genuine Frobenius/inertia, finite-character group and integral
Hecke/height/covolume data. The native 2p physical labels supply
NEITHER HostFacts nor the automorphic error estimate.

Of particular note, its SizeWindows includes simultaneously

   x^(1/2-eps) <= m,     x*m <= k,
   k <= n² * x^(1/2-eps).

Combining these NECESSARILY gives n²>=x for large positive x.
Thus an arbitrary *trivial* host group cannot pay Alpoge's window
cost, even if m prime labels are available. The host group size
has to grow at least on the order of sqrt(x); that is additional
arithmetic/geometric structure, not an index provided by 2I-J.

The useful remaining theorem must do AT LEAST ONE of:

1. Prove a quantitative signed bound for the **complete joint**
   parent source including S_R, other K2, Lambda*S, floor defect and
   the reciprocal-Lambda channel, with all constants uniform in R.
   The new bilinear source makes its Type-II content explicit.
2. Supply the exact HostFacts/characters/thick subsets/weights and
   all height, covolume, movement and size-window costs in the
   ORIGINAL Alpoge theorem; then use its existing published
   proof without substituting raw mu for a Dirichlet character.

Until (1) or (2), no unconditional map beta -> beta/2+1/4
has been established. The previously discussed exponent map is
CONDITIONAL on precisely the full-source saving that this
census shows cannot simply be assumed from distinctness.

## Verification boundary

The new research Lean file and script should be accepted only after
the exact-head warning-fatal research-closure workflow passes.
No axioms, sorry or global exponent are asserted. This PR does not
reconfigure agents or change human-only merge safeguards.

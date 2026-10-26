# Exact CORR-4 power biconditional: paper-level all-integer proof

Status 2026-10-25: original finite source identities, 211/900 frame,
signed first-owner Gram equivalence, parent energy renewal and arithmetic
subcritical constants are Lean-compiled on PR #1021. This note proves the
missing general-exponent strong induction **on paper**, independent of the
original OpenAI 7/8 theorem. Only promote the FULL Mertens biconditional to a
Lean theorem once the complete induction is compiled warning-fatally.

## The target propositions

Let X_R=R²-1 and S_R={odd primes q:q²<R}, Y_q=floor(X_R/q²).
Let E_R=sum_(q in S_R)|M(Y_q)|², C_R=M(R-1)-M(X_R),
U_R=sum_(q in S_R)M(Y_q)/q, and B_R=C_R-U_R.

For beta in [1/2,7/8), define:

  (MP_beta): exists H>=0 such that forall n>=1, |M(n)|<=H*n^beta.

  (BP_beta): exists A>=0 such that forall R>=56,
              |B_R|² <= (9/4)E_R + A R^(4beta).

  (GP_beta): exists A>=0 such that forall R>=56,
              2Gamma_R <=(9/4)E_R + A R^(4beta) - D_R.

The original first-owner identity |B_R|²=D_R+2Gamma_R gives BP_beta
iff GP_beta pointwise, with identical A, without any exponent hypothesis.
MP_beta => BP_beta follows from the proven reverse Young inequality and
C_R=M(R-1)-M(X_R). The nontrivial direction is BP_beta => MP_beta.

## Sharper direct endpoint recurrence; NO square rounding needed

Existing finite identities yield

  |C_R|² <= (886/225) E_R + (4/3) A R^(4beta).

Since M(X_R)=M(R-1)-C_R, applying the 101/100 Young split gives

  |M(X_R)|²
  <= (101/100)(886/225) E_R
     + (101/75) A R^(4beta) + 101 |M(R-1)|².        (1)

This is a direct *unrounded* recurrence on the literal q² daughters. It
is sharper than the nearest-square operator since the induction below
already controls ALL integer cutoffs Y_q.

For every beta>=1/2 and every odd q>=3, q^(4beta)>=q². Hence

  sum_(q in S_R) q^(-4beta) <= sum_(odd prime q) q^-2 <= 211/900.

If |M(n)|<=H*n^beta for every 1<=n<=X_R, then Y_q<=X_R and

  E_R <= H² R^(4beta) * 211/900.                    (2)

The root-prefix term needs no nontrivial arithmetic:
|M(R-1)|<=R-1<=R (since each Mobius step is at most 1).

Equations (1)-(2) give

  |M(X_R)|² <= [lambda0 H² + (101/75)A + 101] R^(4beta),

  lambda0=(101/100)(886/225)(211/900)
         = 18881546/20250000 < (49/50)²=0.9604.  (3)

The 101 root term uses R²<=R^(4beta), valid for beta>=1/2.

## Full all-integer square-shell induction

Fix A>=0 from BP_beta, and take H=1000*(A+1).
Then H>=1000 and A/H²<=10^-6. In particular

 lambda0 + (101/75)*A/H² + 101/H² < (49/50)².

We prove by induction on the square root R>=56 the strong statement

  P(R): for ALL integers 1<=n<=R²-1,
        |M(n)|<=H*n^beta.

Base R=56: |M(n)|<=n by the elementary Mobius bound. For n<=56²,
n^beta>=sqrt(n) and n<=56sqrt(n), so H>=1000 suffices.

Inductive R -> R+1: assuming P(R), equations (1)-(3) yield the
**BUFFERED** endpoint estimate

  |M(R²-1)| <= (49/50) H R^(2beta).                (4)

Take R²<=n<=(R+1)²-1. The trivial interval variation (no statistical
independence, no cancellation hypothesis) gives

  |M(n)| <= |M(R²-1)| + n-(R²-1)
         <= (49/50)H R^(2beta) + 2R+1.

As beta>=1/2, R^(2beta)>=R; for R>=56, 2R+1<=3R.
Since H>=1000, the second term is at most (1/50)H R^(2beta).
Therefore |M(n)|<=H R^(2beta)<=H n^beta.

For n<=R²-1 use P(R). Thus P(R+1). Every positive integer is inside
a sufficiently large complete square prefix, hence MP_beta.

This proves BP_beta iff MP_beta iff GP_beta, for beta in [1/2,7/8),
at the paper level; in fact the elementary induction works for every
beta in [1/2,1] with the same fixed constants.

## Research consequences and non-consequences

* The biconditional, once fully compiled, is a valid unconditional
  *REDUCTION*, not an unconditional new exponent.
* The OAI imported Mertens 7/8 theorem supplies GP_(7/8+epsilon) via
  the reverse direction, but cannot be recycled as an independent
  GP_beta source when beta<7/8.
* A new unconditional beta=3/4 would require bottom-up
  2Gamma_R <=(9/4) E_R-D_R+O(R^3) at EVERY sufficiently large R.
  A dyadic AVERAGE statement is not a pointwise statement.
* #1011 phase-resonance and #1017 fixed heavy-slot algebra do not by
  themselves establish a uniform source moment gap. The heavy-slot
  weight is at least 7/(37|S|), not a scale-independent fraction.
  Conductor change alone does not imply normalized cross-channel
  orthogonality, and constant-factor savings alone do not prove a
  strictly smaller power without a quantitative global amplification
  mechanism.

## Lean implementation obligation

1. Compile the exact first-owner Gram iff original B_R power bill.
2. Compile MP_beta -> BP_beta with its exact n to R² power conversion.
3. Compile (2) pointwise and after summation for all physical S_R.
4. Compile (1) and the rational strict buffer (3).
5. Compile P(R) induction and finish the existential equivalence.
6. Audit the axiom footprint and the actual OAI 7/8 certificate separately.

No change to the source weight, owner set, sharp cutoff, sign, or physical
restoring terms is permitted. A named mathematical hypothesis that has
not been proved must not be hidden as a declaration.

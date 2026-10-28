# Exact asymmetric Euler corner and signed historical Gram

Date: 2026-10-28.  Source: original integer Mobius coefficients.
Status: finite identities and unconditional corner estimate; no exponent
improvement or unproved signed-cancellation hypothesis.

## Setup

For every integer R >= 2 put

    X = R^2 - 1, N = R - 1, H = floor(sqrt R), B = N - H.
    F_R = sum_(1<=b<=B) sum_(1<=a<=N)
              mu(a) mu(b) floor(X/(ab)).
    Gamma_R = sum_(B<b<=N) mu(b) [M(floor(X/b)) - M(N)].

The exact corner has the equivalent original-lattice description

    Gamma_R = sum_(B<b<=N) sum_(N<a<=floor(X/b)) mu(a)mu(b).

The latter is a product coefficient with **unit** floor weight on every
admitted pair, not zero floor weight.

## Exact theorem

    F_R = M(N) + M(B) - M(X) + Gamma_R.

This reuses the existing certified self-dual identity

    Q_R = sum_(a,b<=N) mu(a)mu(b)floor(X/(ab)) = 2M(N)-M(X)

from `eulerSelfDualBilinear_eq_two_mertens_sub_endpoint`.  Let

    O_R = sum_(B<b<=N) mu(b)
             sum_(a<=N) mu(a)floor(X/(ab)).

For each omitted b-row the FULL Mobius floor inversion gives

    sum_(a<=N) mu(a)floor(X/(ab))
      = 1 - [M(floor(X/b))-M(N)].

Hence O_R=M(N)-M(B)-Gamma_R and F_R=Q_R-O_R.

For b in (B,N], X/b lies between R and R+H+1.  If
R<=a<=floor(X/b), then floor(X/(ab))=1.  The inner corner therefore
contains <=H+2 elements, and there are exactly H omitted b indices.
Using |mu|<=1, H^2<=R and 2H<=R, we get

    |Gamma_R| <= H(H+2) <= 2R.

This is unconditional, all R>=2, and requires neither PNT nor RH,
no historical K_R envelope, and no new covariance estimate.

## Source-faithful signed covariance bridge

The already proved theorem

    eulerSelfDualBilinear_eq_diagonal_add_signedStrictCross

expresses the full historical signed square as

    Q_R = D_R + 2 B_R,

where

    D_R = sum_(b<N+1) M(b)^2
      [floor(X/b^2)-floor(X/(b+1)^2)],

    B_R = sum_(b<=N) mu(b) sum_(a<b) M(a)
      [floor(X/(ab))-floor(X/((a+1)b))].

The new two-cutoff bridge is EXACTLY

    F_R = D_R + 2B_R - O_R
        = D_R + 2B_R - (M(N)-M(B)) + Gamma_R.

This retains every actual Mobius sign, the strict off-diagonal,
both the boundary and the short corner.  It does NOT say
B_R is small, negative, or paid.  Replacing D_R+2B_R by the known
2M(N)-M(X) is coordinate conservation, not a new cancellation bound.

To import the original punctured row `C_R` from PR #1041, separately
retain the reciprocal smooth mode and the divisor-puncture correction.
Do not equate that punctured residual to F_R without these terms.
The #1041 source-faithful five-piece formula is not needed to prove
this module and has not yet been merged into main.

## Verification contract

New module: `research/EULER_ASYMMETRIC_CORNER_SIGNED_GRAM_20261028.lean`
and the exact genuine-Mobius regression
`scripts/euler_asymmetric_corner_exact_probe_20261028.py`.

The dedicated GitHub Actions job uses pinned Lean 4.34.1, the
repository's cached research import-closure compiler,
warning-as-error, standard-axiom checks and no admitted proofs.
Until that job passes at the final commit, treat these Lean
declarations as an implementation under verification, not as
certified theorems.  Do not auto-merge.

## Unproved arithmetic target, kept separate

The open improvement of the existing 7/8 Mertens exponent or the
historical finite-C/RH target must enter through an **independent
signed estimate** for the original D_R+2B_R (or a genuinely equivalent,
source-preserving cross term).  The elementary O(R) corner, the
short historical M(N)-M(B) increment, and the exact two-cutoff
identity are *not* independent evidence of such a saving.

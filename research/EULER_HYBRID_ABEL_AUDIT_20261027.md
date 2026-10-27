# Euler self-dual one-sided Abel and truncated divisor annihilator (2026-10-27)

## Scope and provenance

This is **not** a new argument for RH or a proof of finite-C. It targets the genuine historical Mobius bilinear at the self-dual horizon X_R = R^2 - 1, and distinguishes exact arithmetic from quantitative estimates.

The following key results were already proved **before this branch**:

- `RHLean/Proof/RecursivePrimeReplacement.lean`: `squareRootReplacementKernel`, `mertensEndpoint_eq_pred_sub_recursiveReplacement`, and quotient-fibre recombination. This is the exact signed truncated-divisor tail.
- `research/DYADIC_BUCHSTAB_OTHELLO_GLIDER_WALL.lean`: `squareRootReplacementKernel_postRootReplication_eq_zero_of_nonunit`. For a post-root prime p and a nonunit cofactor c below R, the divisor cube completes and the truncated coefficient vanishes.
- `RHLean/Analysis/PrimeSieveAbelIdentity.lean`: `sum_mertensSummatory_mul_forwardDifference`. This is an unconditional one-sided Mertens Abel identity.
- `research/GLOBAL_RETURNED_CORE_COMPENSATED_FOUR_CORNER.lean`: original physical first-owner four-corner signed products. Its first-separation prime is **not** the integer least prime factor; the q² daughter index is independent of both.

## New formalized targets

For R >= 2 and F_R(a,b)=floor((R²-1)/(ab)), define

    Q_R = sum_{a,b < R} mu(a) mu(b) F_R(a,b).

The first theorem is exactly

    Q_R
      = sum_{b<R} mu(b) sum_{a<R} M(a) [F_R(a,b)-F_R(a+1,b)]
          + M(R-1) sum_{b<R} mu(b) F_R(R,b).

The upper boundary must be kept. On square-root endpoints it can be further shown to equal M(R-1), using the standard Mobius divisor inversion. Any removal of this term without a proof is an error.

The second theorem specializes the previously proved high-prime annihilator *without assuming* c<R: if c>=2, p>=R is prime, and c*p<=R²-1, the endpoint geometry forces c<R and the original truncated Euler divisor coefficient at cp vanishes.

The third statement simply displays the already-proved recursive replacement identity. It is included as a direct consumer/provenance link, not claimed as new mathematics.

## Next exact bilinear target

For M(a)=sum_{d<=a}mu(d) and F_R symmetric, define

    D_R = sum_{b<R} M(b)^2 [F_R(b,b)-F_R(b+1,b+1)]
    B_R = sum_{b<R} mu(b) sum_{a<b} M(a) [F_R(a,b)-F_R(a+1,b)].

At the actual square endpoint F_R(R,R)=0, the desired **exact** identity is Q_R = D_R + 2 B_R. The generic finite version must retain the corner M(N)^2 F(N+1,N+1), which vanishes only at the self-dual horizon.

The current source has no universal estimate on B_R. In particular, D_R+2B_R is a signed reconstruction, not a proof that the cross term pays the diagonal.

## Separate bridge to PR #1033

The original low-owner AMP weight is not a function of the least prime factor. The physical crossing gradient is

    lowOwnerDaughterCrossingWeight R p a -
    lowOwnerRootCrossingIndicator R p a,

with original reciprocal q² daughter and clipped/virtual-corner compensation. Consequently the additive Abel hyperbola differences do **not** equal physical first-owner four-corner atoms term-by-term without a new occurrence-preserving reindexing and correction theorem. No such identification is claimed here.

## Acceptance / proof status

- Lean 4.34.1, warnings fatal, zero `sorry`/`admit`/new axioms; confirm exact-head CI.
- No estimated C, no new Mertens exponent, no RH.
- The next genuinely independent arithmetic target remains a uniform estimate of the full signed B_R interaction (or original CORR4 mixed-tail), not a renaming of the finite-C bound.

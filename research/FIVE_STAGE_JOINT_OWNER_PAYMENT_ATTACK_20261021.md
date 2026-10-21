# Finite-history joint returned-owner attack: exact native obstruction and quantitative seam

Date: 2026-10-21. Base: main@4401034feccf148cb7e32820e51d31fb3a9d75a8. Status: **independent arithmetic lemmas and reproducible finite audit; NOT a proof of any new zero-free exponent, finite-A/C, #915 payment, or RH**.

## The externally proved mechanism under examination

The QuasiRiemannTracker merged PR #68 (Gao, 2026-10-21) proves the all-Dirichlet boundary 0.8748087 with five **finite affine source** stages. It preserves literal ideal-labelled ancestry and reciprocal source weights, returns HIGH analytic rows, and counts the returned family **once with a terminal zero-density payment**; see:
- https://github.com/GTimG/QuasiRiemannTracker/pull/68
- https://github.com/GTimG/QuasiRiemannTracker/blob/main/submissions/gao-five-step-affine-20261020/src/Candidate/Research/RecursiveAffine/ActualCarrierReturnedSum.lean
- https://github.com/GTimG/QuasiRiemannTracker/blob/main/submissions/gao-five-step-affine-20261020/src/Candidate/Research/RecursiveAffine/FiniteDepthPrefix.lean

Crucial type distinction: the tracker’s LOW/HIGH refer to detector rows and analytic source geometry, **not** the canonical Möbius-height LOW/HIGH in this repository. Its nonnegative terminal returned-row count cannot simply be substituted for the original signed #915 VF source bill.

## I. Exact root-clock high-prime owner transport

Fix an integer R>=3 and X=R^2-1; write mu for the usual Mobius function and M(k)=sum_{n<=k} mu(n). Every squarefree n<=X with a prime q>R has the **unique** representation n=qc, 1<=c<=floor(X/q)<R, and mu(qc)=-mu(c).

Define:
- T_R=sum_{q>R, q prime, q<=X} M(floor(X/q));
- H_R=-T_R, the complete signed high-prime-owner population (including prime roots);
- S_R=sum_{n<=X, P+(n)<=R} mu(n), including n=1;
- A_R=sum_{q>R, q prime, q<=X} |M(floor(X/q))|, the positive complete-owner return mass.

Then exact Fubini, with **each n charged once**, yields

    M(X)=S_R-T_R=S_R+H_R.

This equality is already familiar from RH_Lean; it is recalled to specify the ACTUAL source of the returned-count test.

### New necessary obstacle for a positive single terminal payment

For EVERY prime X/2<q<=X, floor(X/q)=1 and M(1)=1, so

    A_R >= pi(X)-pi(floor(X/2)).

The right-hand side is asymptotic to X/(2 log X) by the already-available PNT. Therefore, for any fixed eta>0,

    A_R is NOT O(X^(1-eta)) as R->infinity.

This remains true **after each complete owner has already internally cancelled all its cofactor signs**: the root-only k=1 cohort cannot disappear inside its owner. In particular a native estimate

    positive all-HIGH returned-owner bill = O_epsilon(X^(7/8+epsilon))

is FALSE. The defect is not source history overcounting; it is the real prime-root contribution. Any method transferring Gao's one-terminal count to native Mobius must therefore **pair high-prime roots against R-smooth contributions before taking a positive norm** or use a phase-sensitive mixed analytic moment estimate.

For X/3<q<=X/2, floor(X/q)=2 and M(2)=0. That entire k=2 owner cohort vanishes exactly. This genuine cancellation cannot remove the k=1 lower-bound obstruction.

## II. Fixed-depth prime-history multiplicity is only subpolynomial

For squarefree n and a FIXED depth d, an ordered strictly decreasing d-prime subhistory is specified by a d-element subset of the omega(n) distinct prime factors. Hence

    #history_d(n) <= binomial(omega(n),d)
                  <= (log_2 n)^d / d!.

Since n>=2^omega(n), for each fixed d and epsilon>0,

    #history_d(n) = O_(d,epsilon)(n^epsilon).

For d=5 the finite audit below finds maximum 56 paths (binomial(8,5)) through X=9,998,243.

SCOPE: this bound applies to **strictly ordered prime-choice histories over a fixed integer n**, not automatically to extra physical #915 labels (age, owner, signature, original parent, clip, orientation, or anchor). Those labels require their own exact full-key injection. Furthermore O(X^epsilon) fibre congestion never supplies the missing NEGATIVE signed compensation. It just proves that fixed-depth prime branching can be paid without a fixed positive power of X, once histories are correctly restricted.

## III. Exact #915 compatibility test and missing new theorem

The original first-bad packet is NOT H_R and NOT A_R. The original physical source obeys, in research/VF_MID_FIRST_BAD_FINAL_AGGREGATE_CONTRACTION.lean and research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean:

    E_R=G_R+4 B_R-2 H_R
       =G_R+2 U_B-6 L_B,

with U_B,L_B the same-occurrence positive/negative original VF partial masses, and G_R the full historical anchor, squareful restoring, diagonal, and omitted-seat global residual.

Existing theorem:
    vfMidActiveThreeBoundaryExcess_add_transported_nonpos.

This matches each active returned occurrence to a sign-flipped stripped parent at the original retained child scalar; it already gives local nonpositive owner heat. The transported parents are **NOT independent spare capacity**. Their occurrence multiplicities must stay tagged.

Existing conditional consumer:
    vfMidActualPrimeFirstBadAt_two_succ_activeExcess_nonpos_of_transport.

Its premise is:
    vfMidActiveGlobalResidualExcess R
      <= vfMidActiveThreeBoundaryTransportedExcess R.

This remains UNPROVED and cannot be obtained by counting positive returned records alone. A stronger-looking variant that merely adds 4*absBoundary is proved equivalent to the ORIGINAL anchored gate in #915; it is NOT an independent estimate.

### Specific non-circular proof experiment

1. Begin from the ACTUAL three clipped boundary carriers, original signed coefficient, original VF scale, original historical anchor and original total U+L. Enumerate full keys (original owner, revealed prime, raw parent, age, orientation, clip, child), not just stripped arithmetic parents.
2. Follow at most five greatest-prime descents on each legal full-key history, preserving the original coefficient and the exact total new missing-factor/normalization cost. A descended child must lie in a **contiguous lower run**, not be assumed to violate the wall at an isolated endpoint; use research/VF974_FIRST_BAD_BOUNDARY_DESCENT_OBSTRUCTION_20261018.md.
3. Derive an INDEPENDENT, sign-sensitive inequality for the complete mixed root/smooth/anchor packet **before** absolute value or positive moment. It must pay the actual G_R historical/restoring term. The sole cardinality or finite-history multiplicity bound is insufficient, by I.
4. Only AFTER this signed compensation apply a one-time positive terminal density / complete Hermitian moment estimate, tracking the genuine Hecke character labels and phases if OpenAI estimates are invoked. Cite each analytical estimate against the same physical source, not an unproved carrier substitution.
5. Validate at production R=8 and R=18, where raw recursive sector-six cone balance fails; also R=317,1027. The positive-root obstruction in I is an all-R falsifier to any premature magnitude-first terminal bound.
6. If the full signed packet bound yields E_R<=0 UNDER genuine first-bad at R+1, use the existing #915 terminal consumer; if it yields merely an improved global Mertens exponent, use the established Mertens-to-strip bridge. These are different proof targets.

The quantitative benchmark inherited from merged tracker #68 is M(X)=O_epsilon(X^(0.8748087+epsilon)), obtained via the zeta case and classical Mertens/strip equivalence. A genuinely independent native improvement must either improve this exponent or establish a first-bad-specific estimate beyond it.

## IV. Reproducible integer-exact finite falsifier

Compile and run scripts/rhlean_joint_returned_owner_attack.cpp (source included in this draft PR). Its sieve verifies the exact root/smooth transport, lower-bound A_R>=pi(X)-pi(X/2), zero k=2 packets and five-prime factor-choice history multiplicity.

| R | X | A_R positive complete-owner mass | k=1 prime-root minimum | high-prime signed H_R | smooth S_R | M(X) | max five-prime histories |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 100 | 9999 | 1225 | 560 | 101 | -124 | -23 | 1 |
| 317 | 100488 | 9913 | 4474 | 887 | -915 | -28 | 6 |
| 1027 | 1054728 | 85539 | 38831 | 6969 | -6602 | 367 | 21 |
| 3162 | 9998243 | 689741 | 316027 | 48331 | -47266 | 1065 | 56 |

The numerical audit is a regression/falsifier, NOT proof of a global new sign estimate.

## Conclusion

**Verified insight:** fixed-depth prime history congestion is subpolynomial; the positive high-prime returned-root mass is at least Omega(X/log X) and hence CANNOT itself enjoy any subunit power bound. The cancellation must occur across high-prime roots, smooth descendants, and the original anchor **before the first global positive payment**.

**Open theorem:** build a source-faithful, phase-preserving, original-weight mixed analytic moment or first-bad-specific signed descendant/anchor comparison with a genuinely new power saving. Do not claim that a finite recursive dictionary or a positive terminal density bound supplies it automatically.

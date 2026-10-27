# Euler parity -> physical mixed-tail: corrected work package (2026-10-27)

## Status

Package A: the unrestricted finite weighted Euler step and the minFac-preserving prime insertion have been implemented in
`research/WEIGHTED_EULER_BOUNDARY_20261027.lean`, together with the **genuine** physical AMP daughter/root crossing identity (reused from the pre-existing `lowOwnerZeroFrequencyMobiusWeight_sub_mul` theorem). The new file is a compilation candidate, not a claim of a verified CI build before the exact-head Actions finish.

Package B: **OPEN** as an exact occurrence-preserving correspondence between new Euler boundary layers and the existing physical mixed-tail first-separation Gram. Existing signed cell/Fubini identities are NOT the proposed boundary representation.

Package C: **OPEN**. No independent power-saving estimate is constructed or assumed.

## Two different first owners

The integer-level owner `Nat.minFac c` is unchanged on `c -> p*c` when `p > Nat.minFac c`; this is the valid algebraic insight.

The **actual first-owner Gram** uses `IsSquarefreePairFreshPrimeOwner p m n`, the least prime in the symmetric difference of the two complete prime-factor sets (see `RHLean/Analysis/PrimeWheelRunOthelloBoundary.lean`). For (3,69), the integer owner of both is 3 while the first-separating Gram owner is 23. These owners cannot be interchanged.

## The true weighted defect is already proved

`lowOwnerZeroFrequencyMobiusWeight R n` is defined in `research/GLOBAL_RETURNED_CORE_WEIGHTED_GRAM.lean` as

    1_{R <= n} + sum_{q in canonicalRoughLowQ2Owners R}
                            (1/q)*1_{n <= Y_(R,q)}.

It is NOT `w_R (Nat.minFac n)`. Even if `Nat.minFac (p*c) = Nat.minFac c`, its difference is

    a_R(c)-a_R(p*c)
      = lowOwnerDaughterCrossingWeight R p c
        - lowOwnerRootCrossingIndicator R p c.

Existing theorems already give the exact four-corner product
`lowOwnerZeroFrequencyFreshPrimeFourCorner_eq_crossingProduct`, and
`lowOwnerFirstOwnerCompensatedInterior_sq_eq_sum_fourCornerMass`.
A new Task B must re-use those source-faithful theorems instead of discarding either threshold crossing or the square/cross terms.

Concrete counterexample: R=56, c=3, p=23. Both integer least-prime factors are 3, yet a_R(3)=71/105 and a_R(69)=23/15; the difference is -6/7.

The *literal collision quotient* no-go in
`RHLean/Analysis/PrimeBoundaryCollisionQuotientNoGo.lean` is specifically caused by corrected physical weights being **zero on selected-prime square-hit sites**, not in general by p<minFac(c) or by a change of first-owner coordinate. The new work must avoid reading those zero-weight physical collision labels as valid paid descendants.

## Daughter indices are not integer factor owners

The reciprocal daughter index `q` in
`lowOwnerReciprocalDaughterWeight R n` is an independent prime summation
index; it is *not* constrained to divide n. The already-proved common-clock
Fubini `lowOwnerReciprocalMertensColumnReal_eq_weightedMobiusSum` makes
this explicit. At R=56, n=1 receives 1/3+1/5+1/7 even though none of
3,5,7 divides the site. Consequently, decomposing every daughter term as
`n=q*m` with `Nat.minFac n=q` does NOT reproduce the original AMP
column. For Task B, distinguish all three independent indices: daughter
cutoff q, first-separating Gram owner p, and least integer factor minFac(n).

Likewise the pair-side first-owner cell includes arbitrary distinct squarefree
m,n whose sets of primes below p match and whose p-divisibility differs.
They need not be literal p-multiplication mates. For example the pair
(21,429) first differs at p=7 but is not related by multiplying by 7.
The four-corner virtual-parent completion and the original signed Gram
are required to recover all pair atoms.

## Corrected factor and cutoff geometry

Let `X=R^2-1`, `q` the least prime factor of the parent `q*m`, `p>q` fresh, and assume all factors of m lie in (q,p). The child `q*p*m` is outside the physical horizon precisely when

    floor(X/(q*p)) < m <= floor(X/q).

If the full product of primes in (q,p) is <= X/(q*p), this restricted unmatched-parent set is indeed empty. This exact finite emptiness criterion survives, but its force depends on the varying primorial and cannot be applied to m with prime factors >=p.

If m>1 and its greatest prime factor is p'<p, m=p'*m', then

    X/(q*p*p') < m' <= X/(q*p') <= floor(X/q^2).

The final inequality is support geometry ONLY. A bound for the unweighted complete daughter Mertens square M(Y_(R,q))^2 does not automatically control a signed, masked, varying-p' subfamily, or an independent ownerwise norm. Preserve the weighted sum and all complements before invoking `canonicalRoughLowQ2DaughterEnergy`.

**Large p does not imply small m.** From p>P0 and m>X/(q*p) one cannot conclude m<=X/(q*P0). Witness R=56, q=3, P0=8, p=13, m=385=5*7*11: p>P0, X/(3*13)<385<=X/3, but m>X/(3*8). All factors of m lie between q and p; it is squarefree.

**The unmatched-prime interval was reversed.** For fixed q,m, the condition q*p*m>X is

    p > X/(q*m),

so within any chosen finite prime range P0<p<=P1 and p>P+(m), the *unmatched* count is

    pi(P1) - pi(max(P0, P+(m), floor(X/(q*m))))

provided the upper bound exceeds the lower bound, and zero otherwise.

In contrast, primes in (max(R,P+(m)), floor(X/(q*m))] are **admitted** children and their count is pi(floor(X/(q*m)))-pi(max(R,P+(m))) when positive.

There is currently no theorem cancelling the corresponding Li main term: `squareRootPrimeSmoothState_eq_mertensInt_sub_one` is an **exact reconstruction identity** and supplies no quantitative weighted prime-window cancellation.

## Implement Task B only after these tests

1. Fix the exact source object: the returned-core first-separation `p` and lower signature `sig`, not the integer least-prime owner `q`.
2. State the weighted Euler parent/child extension on the admitted `lowOwnerFirstOwnerAdmittedBaseFiber R p sig`. Preserve `lowOwnerDaughterCrossingWeight - lowOwnerRootCrossingIndicator` and both virtual/cutoff sibling corrections.
3. Reuse `lowOwnerFirstOwnerCompensatedInterior_sq_eq_sum_fourCornerMass` and `sum_lowOwnerFirstOwnerSignedCellTelescope_eq_prefix_add_tailMixed` to isolate an exact *difference* between the new boundary bilinear and the physical `lowOwnerPrefixTailMixedRawCellMass`. Do NOT assert exact equality without all correction terms.
4. Probe R=56, R=317, R=1027 and both p orientations. If the candidate identity fails, retain a smallest certified counterexample.
5. Prove source admission, signed multiplicity, and the complete correction equality before any norm.

## Implement Task C as a genuinely independent arithmetic statement

Target the existing kernel-checked consumer `mertensSevenEighthsImprovement_of_corr4MixedTailPowerSaving`:

    2 * lowOwnerPrefixTailMixedRawCellMass R
      <= 2 * canonicalRoughLowQ2DaughterEnergy R
         + A * R^(7/2-eta),

uniformly for R>=56 and fixed A>=0, eta>0.

A new result is meaningful only if it proves the estimate from independently checkable prime/cofactor arithmetic, rather than renaming it, assuming the target signed correlation, or bounding masked daughter subfamilies from M(Y)^2 without a proved operator inequality.

Do not re-prove `booleanCubeAlternatingSum_eq_zero`, `frozenPrimeUniverseMass_insert`, `deathHeightShellMass_eq_cofactorParityMass`, or the already-proved global first-owner Fubini and four-corner identities.

## CI acceptance

- Lean v4.34.1, warnings fatal, exact-head full source audit.
- No `sorry`, `admit`, new axioms, or circular quantitative assumption.
- Publish what is proved vs open; do not call a paper-level or merely enumerated equality a newly Lean-verified result.

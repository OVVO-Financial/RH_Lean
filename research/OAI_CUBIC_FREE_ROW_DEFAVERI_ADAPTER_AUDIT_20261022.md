# De Faveri cubic sieve adapter for actual OAI sixth-free rows

**Date:** 2026-10-22. **Reference:** Alexandre de Faveri, arXiv:2610.04045v1, Theorem 1.1 and Example 2.2. **Scope:** PR #1008 research, stacked on #1006; all Lean proofs must be verified by warning-fatal v4.34.1.

## Directly certified finite arithmetic (pending new CI)

1. `sixthPowerFree_equiv_sqFree_mul_cube_cubeFree` proves the exact base-3 inverse at every bounded prime-valuation coordinate: v=3c+r, c in {0,1}, r in {0,1,2}. c and u0 MAY share a prime.
2. `cubic_masked_cube_character_invariant` (and its conjugated form) proves the exact separation of coprimality masks and invariance of the cubic character under a masked cube factor, assuming true sixth-root phase for the c factor. This pays no analytic cancellation.
3. `cubic_head_fiber_reduction_le` converts a true slice-wise cubic operator estimate into a weighted row energy bound using rho_max. The operator estimate is an **explicit premise**, not silently manufactured.
4. `deFaveri_cubic_fiber_sum_bound` pays the sum over cube roots from a precise per-fiber bound and explicit zeta(2), zeta(3), and number-of-fibers caps. Those ideal counting bounds are not claimed to be Lean-proved by this finite consumer.
5. `deFaveri_cubic_P54_exponent_budget` confirms exactly the -7/12 and -1/2 exponents at U=P^(5/4), before epsilon.

## Exact fixed-family theorem and limitations

Theorem 1.1 bounds **both cube-free modulus ideals and cube-free row ideals**, with
`(AB)^eps*(A+B+2*(AB)^(2/3))` for n=3, with implied constants depending on fixed K, n and excluded finite prime places. Example 2.2 takes K=Q(zeta_3), S={prime over 3}, fixed ray modulus (9), and PRIMARY generators congruent to 1 mod 3. OpenAI's actual family must be identified with one of those fixed cubic character families; theorems about a different abstract family cannot be substituted.

OpenAI source `Hecke/InverseAmplificationRows.lean` defines
`FreeRow={u:O // u!=0 and SixthFree(Ideal.span {u})}`.
The normalizedFactors multiplicities are indeed below six. The base-3 decomposition currently proved as the coordinate equivalence must still be lifted to an **actual Eisenstein ideal factorization**, and from ideals back to OpenAI element rows; when obtaining unique primary generators, unit associates must be accounted for (at most 6). Do not label the coordinate equivalence a completed element-level `FreeRow` equivalence.

OpenAI's compensated leading D-head is `-eta*conj(v)^2*(NP)^(-x)`, the **conjugated** cubic character. Squaring its true sextic symbol kills purely quadratic sign factors but the exact identification with the paper's cubic Hecke family and fixed bad-prime local normalizer needs an actual source lemma. In particular, the paper does not assert that every masked/supported OAI coefficient is one of its `chi_a` characters.

For each prime ideal p, the cubic mask obeys
`1_{p not| c^3*u0}*(chi_p(c^3*u0))^2 = 1_{p not|c}*1_{p not|u0}*(chi_p(u0))^2`.
The left-hand character factor is `chi_p(c)^6=1` only on a coprime c-fiber; a divisibility mask is indispensable.

## Exact fiber budget with visible hypotheses

Fix norm-dyadic prime ideals of size P with coefficient square norm
`A²=sum_p |alpha_p|² <= C_alpha P^(-3/4)`, actual physical row energy `W`, upper bound `rhoMax` on each row weight, and sixth-free ideal norm `U`.

Assuming valid row and modulus character matching, the cube-free inner fiber at squarefree c, q=N(c), obeys
`S_c <= C_eps*(U*P)^eps*(U/q³ + P + 2*(U*P)^(2/3)/q²) * A²`.
Here `C_eps` is for the true fixed cubic family, not a free conductor- or c-dependent constant. The extra `(U/q³*P)^eps` was uniformly replaced by `(U*P)^eps`, using q>=1.

Then nonnegative physical weights give
`E_cubic <= rhoMax * A² * C_eps*(UP)^eps * (U*Z3 + K*U^(1/3)*P + 2*Z2*(UP)^(2/3))`,
provided independent ideal bounds `sum_c q^-3<=Z3`,
`sum_c q^-2<=Z2`,
`#c<=K*U^(1/3)`.
A concrete valid choice is Z2=zeta_K(2), Z3=zeta_K(3), K from elementary ideal lattice counting, but **those instances remain to be certified**.

With `R=U*rhoMax/W` and U=P^(5/4), divide by W to obtain:
`E_cubic/W <= C*R*(UP)^eps * (P^-3/4 + P^-7/12 + P^-1/2)`.
Thus `E_cubic/W <<_eps R * P^(-1/2+(9/4)*eps)`.
This is a **conditional application** of de Faveri. The identity of the true physical rows, operator coefficients and spread ratio is the remaining analytic source work.

The assertion `R=O(1)` does not follow from a positive density of all sixth-free ideals when the actual detector restricts to bins/fibers or has a highly concentrated weight. Its proof requires the exact physical W and rhoMax after ALL source masks. Do not assume it from an unrestricted lattice count.

## Remaining source acceptance chain

1. Instantiate the coordinate valuation equivalence in the actual normalizedFactors of Eisenstein ideals, reconstruct c and u0 uniquely, and show u itself equals a chosen primary-generator product TIMES A UNIT. Track the unit slice without counting ideal classes multiple times.
2. Prove the true sextic-symbol square is the conjugated cubic symbol in de Faveri Example 2.2, with the row mask, prime-ideal masks, ramified and degree-two ideals, fixed bad-prime modulus, source Hecke eta and OAI Gaussian coefficients all intact.
3. Prove the exact physical source `E_S^{cubic}` reindexes as the sum of c-slice energies in the native finite consumer.
4. Establish the row-spread ratio `U*rhoMax/W=O(1)` for the actual physical detector weights, or keep it in the exponent budget explicitly.
5. Instantiate the paper's analytic operator theorem with correct identification (not merely assume the same inequality for an arbitrary family); check all dyadic parameters and the C_eps dependence.
6. Pass warning-fatal Lean on this file AND the original OAI module in #1008; do not merge these drafts simply to bypass CI.


## New original OAI certified ideal/character adapter (pending CI)

The pinned source already has factorPart_valuation, ideal_eq_of_valuation_eq, canonicalSextic_pow_two and canonicalSextic_sixth_power_mask. New source module VF919OriginalCubeFreeIdealAdapter supplies true squarefree cube root and cube-free remainder for the ACTUAL ideal span of OpenAI FreeRow, plus an actual character-square equality and sixth-power zero-mask, with no invented phase. A source-to-element equivalence, primary unit normalizers, and exact fixed-family de Faveri large-sieve admission are still separate open obligations. Workflow KERNEL-CHECK original FreeRow ideal base-3 and true cubic mask enforces warning-fatal Lean v4.34.1; do not count it kernel-certified until green.


The same original adapter now reindexes the EXACT physical labelled FreeRow finite weighted energy by the real squarefree cube-root ideal, using Finset.sum_fiberwise_of_maps_to. It proves original_FreeRow_cube_ideal_norm_identity and original_FreeRow_cube_fiber_weighted_reindex without assuming uniform weights, density or injectivity of element representatives. This pays the finite partition/admission bookkeeping; the character-family operator and row spread remain independent.

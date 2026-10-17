# OAI 7/8 zero-free theorem: exact Möbius covariance consequences

Date 2026-10-17. Companion to draft stacked PR #969 over #968. STATUS: conditional arithmetic/analytic transfer; NOT RH, NOT a new zero-free region and NOT a proof of a near-minus-one asymptotic correlation.

## Source and provenance

External OAI (OpenAI) claimed Lean 4.34.1 theorem `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` (OpenAI math repository). RH_Lean is pinned to Lean 4.24.0. This PR does NOT transplant or postulate that external theorem as a local axiom; it makes a `SevenEighthsZeroFree` **explicit theorem argument**, interpreted as nontrivial zeta zeros having real part <=7/8. Mathlib completed-zeta reflection then gives the left wall >=1/8. The repo's existing kernel-proved `MertensExponent.growthAtMost_of_strip` provides the classical zero-strip -> Mertens epsilon-loss power bound. The reverse direction `MertensExponent.growthAtMost_iff_strip` already exists in the repo on main.

Do not claim this was a classically established 7/8 region before the OpenAI 2026 work; it is a documented external formal claim subject to independent mathematical review.

## Primary quantitative theorem (true conditional transfer)

Let M(n)=sum_(1<=k<=n) mu(k), and let D(n)=sum_(k<=n)mu(k)^2, C(n)=sum_(a<b<=n)mu(a)mu(b). Exactly,

  M(n)^2 = D(n) + 2*C(n),      0 <= D(n) <= n.

Under OAI's zero-free input, for every delta>0 one can take K_delta >=0 with

  |M(n)| <= K_delta n^(7/8+delta) for all n>=1.

Therefore

  0 <= D(n)+2*C(n) <= K_delta^2 n^(7/4+2delta),

and in particular a signed one-sided upper bound for C(n). THIS is the unconditional-as-to-carrier *power saving relative to the trivial n^2 bound*, conditional only on OAI's zero-free result.

The signed sum C(n) is not a Pearson correlation; it is not restricted to [-1,1].

## Weighted criterion threshold is exactly 3/8

For eps>0, define E_eps(N), D_eps(N), C_eps(N) with weights n^(-2-2eps), as in #968. The actual Lean carrier uses the equivalent shifted weight (n+1)^(-2-2eps); the n=0 contribution vanishes and the weights are comparable for n>=1.

  E_eps(N) = D_eps(N)+2*C_eps(N).
  0 <= D_eps(N) <= zeta(1+2eps).

Fix eps > 3/8. Pick 0<delta<eps-3/8. From the 7/8 bound,

  E_eps(N) <= K_delta^2 * sum_(n>=1) n^(-1/4-2eps+2delta).

The latter series converges because 1/4+2eps-2delta>1. Thus,

  [OAI ZF78] => for every eps>3/8, sup_N E_eps(N)<infinity
             => for every eps>3/8, sup_N C_eps(N)<infinity.

New Lean definitions/theorems in `OAI_SEVEN_EIGHTHS_WEIGHTED_COVARIANCE.lean` use the original Mertens sum and #968 signed physical pair carrier, the existing classical Mertens converse, and `Real.summable_nat_rpow_inv`. The constant depends on eps. No bound for eps<=3/8 is claimed; convergence at eps=3/8 does NOT follow from an epsilon-loss OAI power bound.

## Original root/smooth near -1 cancellation

Existing exact root/smooth carriers (not Pearson correlation):
  U_R = squareRootPrimeRootReal R
  V_R = squareRootSmoothMassReal R
  Droot_R = U_R^2 + V_R^2
  M(R^2-1)-1 = U_R+V_R.

When Droot_R>0, define rho_R=2U_R*V_R / (U_R^2+V_R^2).
Then rigorously

  -1 <= rho_R <= 1,
  1+rho_R = (M(R^2-1)-1)^2 / Droot_R.

At R=5561, the repository's exact finite census reports U=125204, V=-127749,
rho=-0.9997975667069334, 1+rho=0.00020243329306660846. These are finite measurements, not a proof of a uniform bound or asymptotic law. A different centered distinguished-q Gram failed its own negative-correlation gate (see CENTERED_CROSS_Q_GRAM_FALSIFICATION.md). Do not transplant favorable correlation from one carrier to another.

Under OAI ZF78 and an ordinary zero-strip->Mertens quantitative transfer,

 (1+rho_R) Droot_R = (M(R^2-1)-1)^2
   = O_eta(R^(7/2+eta)).

**Crucial:** This does NOT imply rho_R -> -1. That would require an *independent adequate lower bound on Droot_R*, or a stronger signed numerator estimate. For the RH-scale target the numerator should be O_eta(R^(2+eta)) instead of the 7/8-scale R^(7/2+eta).

The separate Lean file `OAI_SEVEN_EIGHTHS_ROOT_SMOOTH_ANTIALIGNMENT.lean` proves the generic [-1,1] normalization and exact native source equality. It does not assume or assert an unproved denominator lower bound.

## Threshold for a genuine improvement

For any eps0 with 0<eps0<3/8, an independent theorem

  sup_N C_eps0(N)<infinity

would imply convergence of the corresponding positive weighted energy. A classical Mellin/Cauchy-Schwarz argument would make 1/zeta analytic on Re(s)>1/2+eps0, then functional-equation symmetry confines all nontrivial zeros to [1/2-eps0,1/2+eps0]. This would strictly improve the OAI 7/8 boundary. At every eps0>0 it would establish RH.

The **weighted L2 -> analytic continuation** direction remains a named, explicit ordinary hypothesis in #968/#969; formalize it to complete the end-to-end Lean proof of this standard conditional implication. Neither convergence nor better zero exclusion is presently established for eps0<3/8.

## Acceptance and ownership

Run warning-fatal Lean compilation at the exact PR head; verify every `#print axioms` reports standard Lean axioms only. The upstream OAI theorem does NOT import across pinned toolchains. PR #969 is stacked on #968; after #968 is green, merge/rebase #969 to main and re-run checks. The original historical masked/clipped #915 NNS covariance is a different consumer; do not silently identify carriers.

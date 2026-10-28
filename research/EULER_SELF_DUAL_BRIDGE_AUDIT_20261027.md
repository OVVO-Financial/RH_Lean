# Euler self-dual pointwise bridge and finite-C gate

Date: 2026-10-27. Track: genuine integer Möbius, original RH_Lean finite-C, historical square root.

## The structural identity, not a norm estimate

For R>=2 set X=R^2-1 and let P_R(n)=mu(n) for n<R, zero otherwise. In the integer Dirichlet-convolution algebra set

    q_R(n) = (P_R * P_R * zeta)(n).

The older compiled theorem `MertensFiniteExtension.newtonLift_prefix_exact` asserts that
`2P_R - P_R*P_R*zeta = mu` coefficientwise on n<R^2. This gives

    q_R(n) = mu(n)    for 0<=n<R,
    q_R(n) = -mu(n)   for R<=n<R^2.

The statement is not extended to n>=R^2: the square of the omitted future tail starts precisely there. This is a support theorem about arithmetic functions, not reflection symmetry and not a sign estimate.

## Exact original floor bilinear

The cumulative Dirichlet coefficients have a *literal*, occurrence-preserving
positive-product reindexing by divisors (not a bound):

    sum_{1<=n<=X} (P_R*P_R*zeta)(n)
      = sum_{1<=a,b<R} mu(a)mu(b) floor(X/(a*b))
      = eulerSelfDualBilinear R.

At X=R^2-1 the entire historical rectangle a,b<R is inside ab<=X, so no artificial hyperbola corner is created. This reuses
`sum_Icc_divisorsAntidiagonal_eq_sum_div` and the #1034 historical kernel.

Summing the pointwise coefficient identity gives

    Q_R = 2M(R-1)-M(R^2-1).

This explicit terminal identity is the missing algebraic interface between #1034 and the already proved conditional critical-energy consumer.

## Homogeneity: correct scope

`eulerHybridAbelMain R = sum_b mu(b) sum_a M(a) [F(a,b)-F(a+1,b)]`
is linear in M(a) only when mu(b) and the kernel are held fixed. But
mu(b)=M(b)-M(b-1). The full `Q_R` is genuinely quadratic in the coefficient vector. A term such as `D_R=sum M(b)^2 diff F` scales like K under an abstract envelope `|M(b)-1|<=sqrt(K(b+1))`, **not K^2**. On the other hand, independently bounding D_R=O(R^2K) is too large for FC's O(R sqrt K).

K is a bound for the one fixed Möbius sequence, not a freely variable scaling parameter. Even unit increment and the single inversion constraint admit synthetic counterexamples to finite-C. The original divisor-by-divisor constraints and signed cross interactions are necessary.

## Conditional finite-C consumer

Define `EulerSelfDualFiniteCStatement`:

    exists C>=0, for all R>=2 and all historical envelopes K,
      norm (eulerSelfDualBilinear R) <= C*R*sqrt(K).

The terminal complex identity and historical envelope yield

    |M(R^2-1)-1| <= (C+3)*R*sqrt(K).

(The handoff uses the deliberately relaxed constant C+3. The sharpened
paper constant C+sqrt(2)+1/2 is available but unnecessary.)

Consequently, `A=(C+3)^2` satisfies
`SquareRootMertensEndpointAmplificationStatement`. Existing Lean theorems
`mertensEnergyBounded_of_squareRootEndpointAmplification` and
`riemannHypothesis_of_mertensEnergy` then give RH, *conditionally on the
unproved finite-C premise*.

## Certified scope vs remaining mathematics

- The pointwise coefficient identity was already implied by the prior Newton lift; new file gives the exact signed endpoint specialization and no novelty claim.
- The literal hyperbola/floor reconciliation and named finite-C gate are this PR's intended added proof.
- The signed estimate `EulerSelfDualFiniteCStatement` is **OPEN**. Nothing here establishes a finite constant.
- The original first-separating prime-owner cells and independent daughter q^2 coordinates are different from the additive Abel indices. Do not call these objects termwise identical without a separate source-faithful occurrence reindexing.
- The only route to improvement is new arithmetic cancellation in `D_R+2B_R`, possibly via the actual divisor owner constraints. Neither generic spectral bounds nor the one-sided coordinate transformation supplies that cancellation.

## Compilation contract

Warning-fatal Lean v4.34.1 through the repo's pinned cached CI; check full imported research closure, theorem axioms and absent sorry/admit/new axioms. Keep draft until exact-head workflow proves the stated theorems.

# Mertens weighted covariance and RH: exact mathematics and Lean scope

**Date:** 2026-10-17. **Status:** user-requested formalization, NOT an independent proof of RH. All arithmetic uses genuine Mathlib Möbius coefficients and existing repository Mertens/signed Green--Kubo definitions. Current Lean status is determined exclusively by exact PR-head GitHub Actions, not the existence of this source file.

## 1. Is this a known equivalence?

**Yes as a consequence of the classical Littlewood Mertens criterion (1912):**
`RH iff for every δ>0, M(x)=O_δ(x^(1/2+δ))`.
See Titchmarsh *The Theory of the Riemann Zeta-Function*, §14.25; Edwards *Riemann's Zeta Function*, pp. 260--261. The particular discrete weighted Green--Kubo/off-diagonal presentation is a direct algebraic restatement of a weighted-square criterion; no claim of priority, newly proven RH, or a new zero-free region is made.

Define for positive epsilon
```text
E_epsilon(N) = sum_(1<=n<=N) M(n)^2 / n^(2+2epsilon)
D_epsilon(N) = sum_(1<=n<=N) [sum_(1<=a<=n) mu(a)^2] / n^(2+2epsilon)
C_epsilon(N) = sum_(1<=n<=N) [sum_(1<=a<b<=n) mu(a)mu(b)] / n^(2+2epsilon).
```
The exact identity is `E=D+2C`. The diagonal has the unconditional bound
```text
0 <= D_epsilon(N) <= sum_(n>=1) n^(-(1+2epsilon)) = zeta(1+2epsilon) < infinity.
```
The off-diagonal C is SIGNED. An upper bound, not an absolute bound, is the precise input because E is nonnegative. For each fixed epsilon>0,
```text
sup_N C_epsilon(N)<infinity   iff   sup_N E_epsilon(N)<infinity.
```
Constants can depend on epsilon; uniformity as epsilon tends to zero is NOT required.

The Lean implementation defines the equivalent shifted series over n>=0:
```text
weight(epsilon,n) = (n+1)^(-(2+2epsilon))
energy(epsilon,N)=sum_(0<=n<N)|M(n)|^2*weight(epsilon,n)
diagonal(epsilon,N)=sum_(0<=n<N)sum_(0<=a<=n) mu(a)^2*weight(epsilon,n)
covariance(epsilon,N)=sum_(0<=n<N)sum_(0<=a<b<=n)mu(a)mu(b)*weight(epsilon,n).
```
Here n=0 contributes zero, and the difference between n and n+1 weights for n>=1 is bounded by 2^(2+2epsilon); therefore shifted and unshifted convergence/bounded-prefix criteria agree for every fixed epsilon>0. The finite square identity, complete ordered pair sum and unconditional diagonal uniform upper bound are separate kernel theorems.

## 2. Precise analytic equivalence (paper proof, no new number theory)

Define `AllEnergyUpperBounded` as the assertion that the nonnegative finite E_epsilon prefixes are bounded for every epsilon>0. Then

```text
RH ⇔ AllEnergyUpperBounded ⇔ AllCovarianceUpperBounded.
```

**RH ⇒ weighted energy:** Given epsilon>0, Littlewood implies
`|M(n)| <= K_epsilon n^(1/2+epsilon/2)` for sufficiently large n.
Hence `|M(n)|²/n^(2+2epsilon) <= K² n^(-(1+epsilon))`, a convergent p-series.
Absorb finitely many initial n into the constant.

**Weighted energy ⇒ zero-free strip:** Let `epsilon>0`, `sigma>1/2+epsilon`. For the unshifted energy, Cauchy--Schwarz gives
```text
sum_(n>=1) |M(n)|/n^(sigma+1)
 <= (sum_(n>=1) M(n)^2/n^(2+2epsilon))^(1/2)
    (sum_(n>=1)n^(-2(sigma-epsilon)))^(1/2) < infinity.
```
The same absolute-integrability argument applies to the step function `M(floor t)`, since the step-weighted integral over each [n,n+1) is comparable to its n-term. Thus for each `Re(s)>1/2` select sufficiently small epsilon and obtain a locally holomorphic Abel/Mellin transform
`F(s)=s*integral_(1 to infinity) M(floor t)*t^(-s-1)dt`.
The usual Abel identity proves `F(s)=1/zeta(s)` initially on `Re(s)>1`. The identity theorem extends `zeta(s)F(s)=1` to the whole half-plane `Re(s)>1/2` away from the zeta pole; consequently zeta is zero-free there. The completed-zeta functional equation reflects this across `Re(s)=1/2`. All nontrivial zeros therefore lie on the critical line.

**No inference from a finite census:** `E=D+2C` and finite p-series estimates are known identities. The decisive assertion `sup_N C_epsilon(N)<infinity` for **every epsilon>0** is not presently established. Asserting it without proof would be precisely equivalent to assuming RH.

## 3. Formal proof inventory and what remains to formalize

**Pre-existing kernel-verified on main:**
- `RHLean/Analysis/DeterministicTGreenKuboComparison.lean`: `realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum`, `realMertensPositiveLagPairSum_eq_doubleSum`, `realMertensDiagonal_le`.
- `RHLean/Analysis/MathlibMertensHook.lean`: native squarefree diagonal and signed covariance arithmetic.
- `research/MERTENS_CONVERSE_IDENTIFICATION.lean`: `growthAtMost_iff_strip`, `growthExponent_eq_rightmost`, `growthAtMost_half_iff_criticalZeros` (existing two-way analytic mapping; no need to re-prove).
- `RHLean/Analysis/MertensZetaIdentityContinuation.lean`: Abel/Mellin reciprocal identity theorem under the existing **stronger pointwise** Mertens-energy premise.

**New code in this PR:**
- True weighted finite energy, diagonal and signed ordered-pair covariance (genuine Möbius carriers).
- `energy_eq_diagonal_add_two_covariance`.
- `diagonal_uniform_bounded` using an elementary convergent p-series.
- `covarianceUpperBounded_iff_energyUpperBounded` at each epsilon>0 and its all-epsilon version.
- `WeightedEnergyMellinCriterion` is an **ordinary Prop naming the remaining analytic L2→holomorphic continuation step**. `criticalZeros_of_covariance` requires that premise explicitly. It is not postulated as an axiom and is not counted as proved.

**Remaining Lean work, do not pretend otherwise:** Formalize the weighted L2 to Abel/Mellin holomorphy step and the Littlewood RH→L2 p-series converse using the existing validated APIs; then promote the full RH-equivalent signed-covariance statement from paper proof to a closed kernel-certified iff. Reusing the existing analytic result for a stronger pointwise premise **does not** discharge weighted L2 input by itself. A separate norm comparison or analytic construction is necessary.

## 4. Acceptance and research relevance

- All proof compilation must be warnings-fatal with only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
- Any named conditional analytic consumer must expose its premise; no `sorry`, project axiom, modified definition of RH or new assumption passed as a hidden instance.
- Link the result to original signed source carrier only via exact occurrence-preserving maps. The weighted aggregate `C_epsilon` is NOT automatically the native masked #915 NNS covariance.
- A numerical inequality, a verified algebraic identity, or a conditional equivalence is **not** an independent Mertens exponent bound.

**Research interpretation:** The signed covariance formulation is a potentially useful analytical *view* of the same RH-strength statement. It is a classical RH-equivalent research target, not a solution. Its value depends on proving new arithmetic sign/correlation constraints on the complete actual Möbius pair population.

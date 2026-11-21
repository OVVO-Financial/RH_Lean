# Masullo x RH_Lean: exact high-prime restoration and finite-trace bypass

Date: 2026-11-20. Proposed research addition for review, **not** an RH or GRH proof.

**Statuses:** exact finite source identity (algebraically proved; independent coefficient regression passed); classical-PNT asymptotic (mathematical corollary, **not** Lean-formalized); abstract two-mode stability (elementary, **not** the manuscript quotient theorem); finite-dimensional trace (algebraically immediate); global nuclearity, trace/geometric cutoff matching and RH-strength envelope (OPEN). New Lean research file is proposed without a local Lean compiler; require exact-head `lake env lean research/MASULLO_EULER_TRACE_SOURCE_20261120.lean` and normal repo checks before certifying anything.

## 1. Source and audit boundaries

Alessandro Maria Masullo, *The Music of the Primes*, uploaded 940-page manuscript, specifically:

- pp. 443-444, Proposition 10.2.1.3 and Terminology 10.2.1.2: bounded/nonvanishing norms of a Markushevich basis's evaluation vectors are taken to imply a uniform bound on its biorthogonal functionals. **That implication is false in a general Hilbert space.** For normalized `u=(1,0)`, `v=(1,epsilon)/sqrt(1+epsilon^2)`, the biorthogonal duals have norms of order `1/epsilon`.
- p. 450, formula (10.3.1.16) and subsequent estimate: an entire finite interval's spectral dimension is asserted to be `O_s(log T)` for fixed `s`. In the zeta case, choosing an interval containing the first `N(T)` zeros on the critical line is incompatible with the known critical-line zero count `Omega(T log T)`; at minimum the citation to a local zero-multiplicity bound cannot be applied as a global interval-counting bound. This is a **proof audit**, not an assertion about possible valid alternative constructions.
- p. 451, around formulas (10.3.1.18)-(10.3.1.22): the uniform biorthogonal-norm bound is used in the singular-value/nuclearity step. This step is **not established by normalization**.
- pp. 514, 519-522: the global-to-local transition, the independent cutoff parameters, and the final divisor-of-`L` statement contain explicit uncompleted instructions. The claimed strip-independent geometric trace cannot be imported as an unconditional theorem.

The paper's spectral theory is distinct from RH_Lean's prime-wheel Fourier and Schauder components. No claim that an arbitrary abstract eigenvector model proves results for Masullo's quotient spaces is authorized.

## 2. The new concrete arithmetic package: entire order-`R^2` ghost and pointwise restoration

Let `R>=2`, `X=R^2-1`, `mu` the *actual* Möbius function, `Lambda=mu * log`, `psi(y)=sum_{n<=y} Lambda(n)`, and `pi` the *actual* prime count. Let `mu_R(d)=mu(d)` when every prime divisor of `d` is at most `R`, zero otherwise. Retain the full Dirichlet convolution and its omitted part separately.

For any **prime** `p>R` and integer `2<=m<R` such that `pm<=X`, we have `(p,m)=1` and every divisor of `pm` with no prime factor above `R` is a divisor of `m`. Therefore:

```
(mu_R * log)(pm)
  = sum_{d|m} mu(d) [log(p)+log(m/d)]
  = log(p) * sum_{d|m} mu(d) + (mu * log)(m)
  = Lambda(m)                 (m>1).

((mu-mu_R)*log)(pm) = -Lambda(m)
(mu*log)(pm) = Lambda(pm) = 0.
```

**Do not include `m=1`: `pm=p` is genuinely prime, so `Lambda(p)=log(p)`, not zero.** Prime powers in `m` are retained; they supply the corresponding `Lambda(m)` coefficients and do not disappear through a squarefree-only shortcut.

The total spurious positive low-prime-only contribution is the exact, finite mass

```
G_R = sum_{p prime, R<p<=X} psi(floor(X/p))
    = sum_{2<=m<R} Lambda(m) [pi(floor(X/m)) - pi(R)].
```

The second formula follows solely by **finite Fubini** and actual prime counting; `floor(X/p)<R` for all `p>R`, which ensures every cofactor is below the historical root. Both formulas are nonnegative, and the omitted high-prime-divisor contribution is **exactly `-G_R`**, term by term. No appeal to random signs, smoothing, or prime uniformity is required.

### Nontrivial asymptotic (classical-PNT input)

By the prime number theorem and partial summation,

```
G_R / R^2 -> log(2) = 0.69314718056...
```

Sketch: uniformly for `2<=m<R`, the argument `X/m` is at least `R`, so `pi(X/m)=(1+o(1))(X/m)/log(X/m)`. Since `psi(t)~t`, one obtains

```
G_R / X = (1+o(1)) sum_{2<=m<R} Lambda(m)/(m log(X/m))
          - pi(R)*psi(R-1)/X
        = integral_2^R dt/[t log(X/t)] + o(1)
        -> log(2).
```

The subtracted term is `O(1/log R)`. This asymptotic is **not** claimed Lean-certified. It quantitatively proves that any purportedly RH-scale approximation replacing the complete source by its low-prime-only convolution would incur an entire non-negligible main term. It does **not** show that the manuscript's actual adelic trace performs this truncation or that the cancellation yields an RH-strength bound.

### Exact numerical ledger

The Python regression represents the logarithmic source as an **integer coefficient vector indexed by the prime `q` in `log q`**; it compares the two finite expressions component-by-component, not by floating-point closeness. The displayed `G_R` is evaluated using floating logarithms only after the exact coefficient agreement.

| `R` | `G_R` | `G_R/R^2` |
|---:|---:|---:|
| 31 | 362.454630 | 0.3771640 |
| 100 | 4,865.622770 | 0.4865623 |
| 317 | 53,071.370037 | 0.5281311 |
| 1,027 | 595,972.744500 | 0.5650482 |
| 3,000 | 5,260,234.166399 | 0.5844705 |

Additionally, the pointwise retained/omitted divisor channels were validated in **443 actual high-prime/composite fibres** at `R=7,13,31`, retaining every prime-power factor of `m`. These are finite tests, not substitutes for the general theorem.

## 3. Native Lean crosswalk and proposed deliverable

Pre-existing on main (do not double-count as new work):

- `RHLean/Analysis/LogWeightedPrimeExtensionEndpoint.lean`: `nativePsi`, logarithmic Dirichlet derivation, prime-extension Fubini and exact fresh/square correction.
- `RHLean/Analysis/RamanujanDivisorBoundary.lean`: `sum_moebius_divisors_eq_one_or_zero`.
- `RHLean/Analysis/SquareRootMatchedTransport.lean`: `primeDilatedLowCofactorMass_eq_mertensSummatory`.
- `research/PNT_FIRST_LAMBDA_HYPERBOLA_ANCHOR_20261018.lean`: `pntFirst_landau_vonMangoldt_mertens` and the complete `Lambda-1` hyperbola.
- `docs/RHLEAN_MULTIPLICITY_VS_COST_TO_HALF_20261120.md`: the *original* prime/composite population and strict historical `K_R` are indispensable; neither Euler derivative nor spectral lift is entitled to replace them by analogy.

New research module `research/MASULLO_EULER_TRACE_SOURCE_20261120.lean` records a complete finite `Lambda`-weighted prime/cofactor Fubini pair, the prime-fibre multiplicity form, the nonnegative ghost mass, the `mu*log=Lambda` algebraic kernel, the nonunit-cofactor log-prime cancellation, and the elementary finite matrix trace. Its `masulloRetainedLogFibre` is an **explicit convolution model**: the extra physical identification of its divisors with the actual `pm` low-prime truncation must keep assumptions `p` prime, `p>R`, `m<R`, and `pm<=X` visible and should be a distinct subsequent Lean theorem if not already derived. The PNT asymptotic is not embedded as a hidden hypothesis.

This change does **not** modify `RHLean.lean`, the user/agent priority, or the generated proof-obligation registry. After review and **exact-head Lean compilation**, add a DAG `PROVED` entry only for the actual compiled finite identity; any edge to an RH-strength consumer is `CONDITIONAL_IMPLICATION` with nonempty unpaid inputs.

## 4. A spectral shortcut: bypass separate biorthogonal norm estimates

Suppose, as the manuscript's finite Jordan matrix (10.3.1.17) purports, a finite-dimensional invariant spectral space `E_T` is actually constructed with diagonal `f(rho)` at each zero `rho` (with multiplicities). Pure finite algebra gives

```
Tr(A_f | E_T) = sum_{rho in E_T} mult(rho) * f(rho).
```

The finite-dimensional trace is the sum of diagonal entries even if the chosen biorthogonal vectors are ill-conditioned. This step needs **no global uniform biorthogonal bound and no Schatten-class theorem**. Since compactly supported smooth test functions have rapidly decaying Fourier/Mellin transforms, classical zero counting is sufficient for absolute convergence of the *scalar* zero sum on each fixed vertical line, provided the test and zero multiplicities satisfy the stated standard estimates.

**But** finite trace convergence does not imply that the untruncated operator is nuclear, does not ensure trace convergence for arbitrary nonorthogonal cutoffs, and does not identify a geometric trace. To exploit this bypass, the following remain **OPEN**, and must be proved with quantified uniformity:

1. The proposed finite zero/Jordan subspaces are actual invariant spaces of the claimed quotient operator, with correct multiplicities and no unaccounted boundary modes.
2. The spectral cutoff and geometric cutoff yield the same finite trace, with every orbital/archimedean term and independent `lambda,lambda'` cutoff captured.
3. A suitable limit interchange is valid, uniformly in the strip parameter if strip-independent zero exclusion is desired. Pointwise dominated convergence or uniform boundedness of complete convolution does not suffice.
4. A complete zero-exclusion/strip-variation implication is proved without assuming off-line zeros absent or substituting RH into test-function approximation.

### Local two-mode diagnostic (NOT a global operator theorem)

In the abstract degree-zero weighted strip model with log-coordinate weight `exp(-2 alpha |x|)`, the normalized Gram off-diagonal for distinct ordinates separated by `d` is

```
c = 4 alpha^2 / (4 alpha^2 + d^2).
```

For the complete two-mode multiplier, the off-diagonal in the orthonormalized basis is `c(f(u)-f(t))/sqrt(1-c^2)`, yielding the gap-independent estimate

```
||A_f|| <= ||f||_infinity + sqrt(2)*alpha*||f'||_infinity.
```

The separated rank-one projections grow like `alpha/d`. Their combined operator need not. This shows a loss of correlation **in the abstract model**. It does not prove that the author's Hilbert quotient has the same stable two-mode reduction or that arbitrary clusters admit a summable trace norm.

## 5. RH_Lean gate: only a quantitative continuation to `1/2` qualifies

Live RH_Lean contract (as of this research date): `X_R=R^2-1`, `K_R=max_{0<=y<R}(M(y)-1)^2/(y+1)`. The merged #1135 universal-envelope dictionary would reach the critical line if an unconditional *fixed* `delta>0` and all `epsilon>0` bound

```
|M(X_R)-1| <= C_epsilon * R^(1+epsilon) * K_R^(1-delta/2)
```

were proved. **Nothing in this PR pays that bound.** In particular:

- The `G_R` main term cancels **exactly** against its missing divisor partner; that cancellation alone makes no saving on the full complete physical source.
- Normalized Markushevich vectors are not a Riesz basis, and per-mode bounds must not be substituted for complete operator estimates.
- A trace over test functions of *fixed compact support* need not control windows with support growing with `R` or solve the original signed HIGH channel.
- Do not equate Hecke zero multiplicity, prime-fibre incidence multiplicity, or NNS Gram rank without a typed comparison.

**Next unpaid result:** produce a complete-source, cutoff-uniform spectral/geometric identity whose error explicitly controls RH_Lean's original actual Möbius/VF/square-block endpoint, or falsify that exact bridge. Absent that, this work is a rigorous lemma and a candidate reduction, **not a numerical exponent gain**.

## 6. Review and execution contract

Run:

```
python3 scripts/masullo_ghost_compensation_regression.py
lake env lean research/MASULLO_EULER_TRACE_SOURCE_20261120.lean
python3 scripts/proof_obligation_dag.py --check
```

Check the exact-head CI status before calling any new Lean declaration certified. Keep the manuscript's trace assertions as **CLAIMED/OPEN**, its omitted proof paragraphs as unproved, and the generated DAG unchanged until a reviewed typed source identity is accepted. No agent instruction, schedule, merge permission, or current 1/2 research priority changes in this PR.
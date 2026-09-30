# Discrete pure-Li model: Poisson stability no-go

Status date: 2026-09-30. This is a research-state note. It is not Lean-certified.
The decisive step uses a classical unconditional Omega-theorem for `zeta`,
and Mathlib does not contain it. See "Scope" at the end.

## Verdict

The proposed "discrete Poisson/Volterra stability theorem" is false. That is
the renewal statement

```text
sum_{n<=X} log(n) a(n) = - sum_{2<=q<=X} (1 + eps_q)/sqrt(q) * A(floor(X/q)),
sum_q |eps_q|/sqrt(q) < infinity   ==>   A bounded (or A(X) = O(X^delta))
```

It is false for **every** admissible `eps`, including `eps = 0` and the exact
PR #817 defect `eps_q = log(q) w_q - 1`. Specifically:

1. **Stability is true, but it is automatic.** Summable `eps` changes `A`
   only by an absolutely summable Dirichlet-convolution factor, in both
   directions (Section 2). So the proposed theorem for all admissible `eps`
   is equivalent to the single case `eps = 0`. This is also the Banach-algebra
   fact behind "exponential-convolution stability".
2. **The comparison hypothesis is false.** The discrete critical generator
   does *not* differ from the continuous (Dickman) generator by a measure of
   finite total variation. This holds literally, since the two are mutually
   singular. It also holds in every weakened form whose Mellin transform is
   bounded on a half-plane `Re w >= sigma_0 < 1`. The proof is elementary
   (Section 3).
3. **The conclusion is false.** For every `theta < 1`, all of the following
   fail to be `O(X^theta)` (Section 4):
   - the unit-kernel cumulative;
   - the Poisson reference `exactLiPoissonIntegerReference` (PRs #816/#817), and its
     critical form `exactLiCriticalPoissonIntegerReference` at the
     corresponding critical scale;
   - the all-scale hard-core Li diagonal `L(X, X)`, even when sampled only
     at `X = R^2 - 1`.

   In particular `AllScaleLiSquareRootBoundedStatement` is **false**. The
   uniform critical-Poisson premise of
   `allScaleLiSquareRootBounded_of_criticalPoisson_uniform` (PR #817) is
   **false** as well. The conditional implications remain valid, but their
   premises cannot be proved.

Finite data do not show this failure. Through `X = 10^8` all three critical
cumulatives appear to converge to the analytically continued edge values
(Section 5). The violation lives at heights where `|zeta(sigma+it)|` exceeds
every fixed multiple of `log t` in the strip, so it occurs at astronomically
large `X`.

## 1. Exact objects

Write `w_q = Li(q) - Li(q-1) = int_{q-1}^q dt/log t` for `q >= 3` and
`w_2 = 0`. This is `primeSievePNTDensity`, where `Li` is
`logarithmicIntegralFromTwo`.

**Real-space form.** The discrete generator is the push-forward of the
continuous Li generator under the ceiling map:

```text
sum_{q>=3} w_q delta_q  =  ceil_* ( 1_{t>=2} dt / log t ).
```

Every site of the continuous Dickman model is rounded up to the next integer.

| Object | Coefficients | Dirichlet series (`Re w > 1`) |
| --- | --- | --- |
| Hard-core Li state diagonal `L(X,X)` (`IsAllScaleLiState`) | `nu = prod_{q>=3} (1 - w_q delta_q)` | `Phi(w) = prod_{q>=3} (1 - w_q q^-w)` |
| Poisson reference (PR #816/#817) | `b = exp_*(- sum w_q delta_q)` | `exp(-G_d(w))`, `G_d(w) = sum_{q>=3} w_q q^-w` |
| Unit kernel (`eps = 0`) | `b0 log = -1_{q>=2} * b0` | `exp(-P_0(w))`, `P_0(w) = sum_{q>=2} q^-w / log q` |
| General kernel `(1+eps_q)` | `b_eps log = -k * b_eps` | `exp(-G_eps(w))`, `G_eps(w) = sum_{q>=2} (1+eps_q) q^-w / log q` |

Critical normalization divides every coefficient by `sqrt(n)`. Equivalently
it evaluates the series at `w = s + 1/2`.

The PR #817 renewal
`sum log(n) a(n) = -sum log(q) (w_q/sqrt q) A(floor(X/q))` is exactly the
Mellin identity below. Log-multiplication is a derivation of Dirichlet
convolution, and the Poisson product is a convolution exponential.

```text
-G_d'(w) = sum_{q>=3} log(q) w_q q^-w = sum_{q>=3} (1 + eps_q) q^-w
         = zeta(w) - 1 - 2^-w + E(w),        E(w) = sum_{q>=3} eps_q q^-w.
```

PR #817 proves `0 <= eps_q <= 1/((q-1) log 2)`, so `E` is bounded and
analytic on `Re w >= 1/2`. The continuous generator has
`G_c(w) = int_2^inf t^-w dt/log t = E_1((w-1) log 2)` and
`-G_c'(w) = 2^(1-w)/(w-1)`. Hence the exact generator difference satisfies

```text
D(w) := G_d(w) - G_c(w),
D'(w) = -( zeta(w) - 2^(1-w)/(w-1) - 1 - 2^-w + E(w) ).          (1.1)
```

So rounding to the next integer injects exactly the regular part of `zeta`
into the generator. The continuous model has no such term. That is why the
continuous model is bounded ([`EXACT_LI_DICKMAN_ATTACK.md`](EXACT_LI_DICKMAN_ATTACK.md), bound `2e^2 - 1`)
while the discrete one is not.

For the hard-core state,

```text
Phi(w) = exp(-G_d(w)) * Corr(w),
Corr(w) = prod_{q>=3} (1 - w_q q^-w) exp(w_q q^-w).
```

Here `w_q q^-1/2 <= w_3/sqrt 3 < 0.65` and `sum_q w_q^2/q < infinity`, so
`Corr` and `1/Corr` are bounded and analytic on `Re w >= 1/2`. This is the
Mellin form of the repository's `exactLiCorrectionKernel_uniformVariation`.

## 2. What is true: exponential-convolution stability

Let `kappa_eps(q) = eps_q / (sqrt(q) log q)`, so `||kappa_eps||_1 <= sum
|eps_q|/(sqrt(q) log 2)`. The critical solutions satisfy
`a_eps = a_0 * h` with `h = exp_*(-kappa_eps)`. Also `a_0 = a_eps * h^{-1}`
with `h^{-1} = exp_*(kappa_eps)`. Both factors lie in the Dirichlet-convolution
Banach algebra `l^1`, with norm at most `exp(||kappa_eps||_1)`. Hence

```text
A_eps(X) = sum_{d<=X} h(d) A_0(floor(X/d)),
|A_eps(X)| <= e^{||kappa||} sup_{Y<=X} |A_0(Y)|,
|A_0(X)|   <= e^{||kappa||} sup_{Y<=X} |A_eps(Y)|.
```

The same holds with `C X^delta` envelopes. A Lean-friendly proof needs no
exponential series. Put `H(N) = sum_{n<=N} |h(n)|`. The recursion gives
`sum_{n<=N} |h(n)| log n <= ||e||_1 H(N)`, where `e(q) = eps_q/sqrt q`. Hence
`H(N) <= H(M) log M / (log M - ||e||_1)` for `log M > ||e||_1`.

**Consequence.** Every admissible `eps` gives a bounded reference exactly
when the unit kernel does. Stability cannot help, because nothing is lost
or gained by it. The whole question is the single sequence `b0`.

## 3. The finite-total-variation hypothesis is false (elementary)

*Literal form.* `sum w_q delta_q` is atomic and `dt/log t` is absolutely
continuous. Therefore `|g_d - g_c| = |g_d| + |g_c|`. The critical total
variation is `sum w_q/sqrt q + int t^-1/2 dt/log t = infinity`.

*Every Mellin-bounded weakening.* Suppose `D` were bounded on
`{Re w >= sigma_0, |Im w| >= 1}` for some `sigma_0 < 1`. This is what finite
`x^(-sigma_0)`-weighted variation of any decomposition gives. It is also
what exponential-convolution stability consumes. Put
`r = (1 - sigma_0)/2`. Cauchy's estimate bounds `D'` on
`{Re w >= 1 - r, |Im w| >= 2}`. That set contains the strip `1 < Re w < 2`.
There, (1.1) and the boundedness of `E`, `2^-w` and `2^(1-w)/(w-1)` force
`zeta` to be bounded.

This is false. For fixed `sigma > 1`, Dirichlet's simultaneous
approximation gives arbitrarily large `t` with `|n^-it - 1|` small for all
`n <= N`. Hence `sup_{t>=2} |zeta(sigma+it)| = zeta(sigma)`, and
`zeta(sigma) -> infinity` as `sigma -> 1+`.

So no bounded-variation (or bounded-Mellin) comparison between the discrete
and continuous generators exists, at the critical scale or at any scale
below `1`. In real-space terms, the ceiling transport is small in
Kantorovich or CDF distance but not in total variation. Exponentials are
stable only for total variation.

## 4. The conclusion is false (classical Omega-theorem)

**Theorem.** Let `c` be `b_eps` (any admissible `eps`: unit kernel,
Poisson, PR #817 defect) or the hard-core `nu`. Let `theta < 1`. Then
`C(X) = sum_{n<=X} c(n)` is not `O(X^theta)`. For `nu` it is not
`O(X^theta)` even along `X_R = R^2 - 1`.

In critical normalization: no cumulative `sum_{n<=X} c(n)/sqrt n` is
`O(X^delta)` for any `delta < 1/2`. In particular none is bounded.

*Proof.* We may take `1/2 <= theta < 1`.

1. **Continuation.** For `Re w > 1`, the generating function is
   `exp(-G(w))`, times `Corr(w)` for `nu`. Here `-G'(w) = zeta(w) - 1 +
   E_eps(w)` with `E_eps` bounded and analytic on `Re w >= 1/2`. So
   `Q(w) := G(w) + log(w-1)` extends analytically to `Re w > 1/2`, with

   ```text
   Q'(w) = -( zeta(w) - 1/(w-1) - 1 + E_eps(w) ),
   exp(-G(w)) = (w - 1) exp(-Q(w)).
   ```

2. **Growth from the hypothesis.** If `|C(X)| <= K X^theta`, then
   `sum c(n) n^-w = w int_1^inf C(x) x^(-w-1) dx` is analytic on
   `Re w > theta`. It is bounded by `K'|w|/(Re w - theta)`, and it equals
   the continuation above.

   For `nu` sampled only at `X_R`: `|nu(n)| <= c+(n)`, where
   `sum c+(n) n^-w = prod (1 + w_q q^-w)`. The short intervals
   `(X_R, X_{R+1}]` contribute at most
   `C sum_n c+(n) n^(-sigma-1/2) < infinity` for `sigma > 1/2`. The sampled
   values contribute `sum_R R^(2 theta) R^(-2 sigma - 1) < infinity` for
   `sigma > theta`.

   Put `sigma_1 = theta + eta`. Since `|w|/|w-1|` is bounded for
   `|Im w| >= 1`, we get `Re(-Q(w)) <= K''` on
   `{Re w >= sigma_1, |Im w| >= 1}`.

3. **Borel-Caratheodory.** For `|t| >= 3`, apply it on the disc centred at
   `2 + it` with radius `2 - sigma_1`. We have
   `|Q(2+it)| <= |G(2+it)| + |log(1+it)| << log|t|`. This gives
   `|Q(w)| << log|t|` on `Re w >= sigma_1 + eta`.

4. **Cauchy.** `|Q'(w)| << log|t|` on `Re w >= theta + 3 eta`. So
   `|zeta(sigma+it)| << log t` there.

5. **Contradiction.** For fixed `sigma` in `(1/2, 1)` it is classical and
   unconditional that `log|zeta(sigma+it)| = Omega((log t)^(1-sigma-epsilon))`
   (Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., Ch. VIII,
   Thm. 8.12; Montgomery 1977 sharpens it under RH). In particular
   `zeta(sigma+it)` is not `O(log t)`. Choose `eta` with
   `theta + 3 eta < 1`. ∎

The argument uses no zeta zeros and no prime-counting input. It uses only
how large `zeta` gets in the strip, and that is exactly what the floor
transport (1.1) injects.

**Beurling reading.** The weights are "primes" with
`psi_B(x) = floor(x) - 1 = x + O(1)`, far better than RH quality. Yet the
generated integers and Möbius function have no power saving. This matches
the known Beurling phenomenon that prime regularity does not imply integer
regularity (Broucke-Debruyne-Vindas, *Beurling integers with RH and large
oscillation*, 2020). For the actual primes, `1/zeta` inherits finite order
from `N(x) = floor(x)`. The actual-prime displacement `Lambda - 1` is not
summable. It is exactly the term that must cancel the `exp(-int zeta)`
blow-up of the discrete Li model. The actual primes do not perturb a good
pure-Li model: the pure-Li model is worse.

## 5. Finite data (diagnostic only)

[`experiments/li_discrete_omega_diagnostics.c`](../experiments/li_discrete_omega_diagnostics.c)
computes the exact recursions. [`experiments/li_discrete_omega_edge_values.py`](../experiments/li_discrete_omega_edge_values.py)
evaluates the analytic continuations at the critical edge `w = 1/2`:

```text
(w-1) exp(-Q(w)) at w = 1/2,
Q(1/2) = Q(2) + int_{1/2}^2 (zeta(u) - 1 - 1/(u-1) [+ E-terms]) du.
```

| `X` | hard-core crit. | Poisson crit. | unit crit. | `L(X,X)/sqrt X` | `M(X)/sqrt X` (actual `mu`) |
| --- | --- | --- | --- | --- | --- |
| 210 | -0.680928 | -1.092092 | -0.499460 | 0.189019 | -0.069007 |
| 317 | -0.619595 | -1.113426 | -0.511617 | 0.209832 | -0.224662 |
| 10^4 (8924) | -0.447982 | -1.092944 | -0.501131 | 0.071593 | 0.095271 |
| 10^6 | -0.484074 | -1.094693 | -0.501675 | 0.000752 | 0.212000 |
| 10^8 | -0.476285 | -1.094410 | -0.501556 | 0.002742 | 0.192800 |
| analytic edge value | -0.469742 | -1.094463 | -0.501624 | | |

The Poisson entries at 210 and 317 reproduce the PR #817 diagnostics
(`-1.092092054907`, `-1.113426371077`). The edge values confirm that the
Dirichlet-series identifications in Section 1 are exact. The hard-core column
converges slowly because of the `q^2` correction tail
(`sum_{q > sqrt X} w_q^2/q ~ 1/log X`).

These tables look bounded and convergent. The theorem above proves they are
not. They are the reverse case of the contract's warning that finite
successes cannot certify uniform bounds: here finite data wrongly suggest a
uniform bound that is provably false.

## 6. Consequences

- Do not attempt a uniform bound on `exactLiCriticalPoissonIntegerReference`
  or `exactLiPoissonIntegerReference / sqrt X`. Do not attempt
  `AllScaleLiSquareRootBoundedStatement`. Do not attempt a
  discrete-to-Dickman total-variation comparison. Do not run renewal
  regressions at larger `X`. All targets are false.
- The exact identities of PRs #812–#817 remain valid and should be kept as
  regression structure. This includes the hard-core/Poisson factorization,
  the log-derivation renewal, the `eps_q` budget, and the correction-kernel
  variation bound. Only the quantitative pure-Li target is refuted.
- A route through "pure Li first, then transfer to actual primes" must now
  put **all** of the square-root content into the transfer. The transfer
  would have to cancel `exp(-int zeta)` growth. That is RH-strength in the
  strip, not a perturbation.
- CORR-4 and the actual-`mu` target in `CURRENT_PROOF_CONTRACT.md` are
  untouched. This note concerns the model only.

## Scope

- Sections 2 and 3 are elementary and could be formalized. Section 3 needs
  Mellin transforms of measures, Cauchy estimates, and Dirichlet
  simultaneous approximation for `zeta` on `Re > 1`.
- Section 4 needs an Omega-theorem for `zeta` in the critical strip. It is
  classical and unconditional, but it is not in Mathlib. No executable
  finite counterexample can exist: the statement fails only asymptotically,
  far outside computable range.
- Nothing here bears on RH or on the actual Mertens function.

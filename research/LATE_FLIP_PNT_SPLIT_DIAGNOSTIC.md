# Late-flip PNT split: exact bridge and finite diagnostic

Status date: 2026-09-28. This note tests a proposed program: cancel the exact
Euler pairs first, group the late primes by reciprocal quotient band, replace
only their prime multiplicities by PNT density, and then bound the signed effect
of that replacement on the assembled Stokes energy.

**Outcome.** The exact structure is real and is already compiled; this PR adds
the bridge that places the proposed split on the compiled carrier. The finite
test finds the specific residual that the proposal anticipated might appear.
The location error `eta_R` created by the density substitution is not a small
perturbation. On every tested window it closely follows a fixed multiple of the
top Mertens value, `eta_R ≈ 1.35 M(X)` plus an explicit prime-square term. The
classical explicit formula gives the heuristic coefficient `2 log 2 ≈ 1.386`.
The split therefore moves the open CORR-4 quantity into `eta_R`; it does not
bound that quantity. No impossibility theorem is claimed.

## 1. The proposal, on the production carrier

Take `X = R² − 1` and `R >= 56`. Put `h(k) = 2(1 − M(k))`. Let
`N_R(k) = #{p prime : R < p <= X, floor(X/p) = k}`. Then

```text
H_R    = sum_{k=2}^{R-1} h(k) N_R(k)          (h(1) = 0),
B_root = M(X) − H_R,
Nbar_R(k) = L(u_k) − L(l_k),   u_k = floor(X/k),   l_k = max(R, floor(X/(k+1))),
Hbar_R = sum_{k=2}^{R-1} h(k) Nbar_R(k),      eta_R = H_R − Hbar_R,
A_R    = (B_root − M(R−1) + Q_R) + Hbar_R,
FinalStokes_R = (A_R + eta_R)² − D_R.
```

Here `L(t) = int_2^t du/log u` is the repository's
`logarithmicIntegralFromTwo`. The proposal asks two questions:

1. whether the smooth late correction cancels the root-stage imbalance to the
   required scale; and
2. whether replacing smooth counts by actual counts preserves that bound.

## 2. What was already compiled on this carrier

| Ingredient of the proposal | Compiled source |
| --- | --- |
| `Delta B_p = 2(1 − M(floor(X/p)))`, band constancy, `h(k+1) − h(k) = −2 mu(k+1)` | [`PrimeCombReciprocalBandCancellation`](../RHLean/Proof/PrimeCombReciprocalBandCancellation.lean) |
| Upper primes share no site below `X`; one unprocessed prime per source | [`PrimeSievePostSqrtGap`](../RHLean/Proof/PrimeSievePostSqrtGap.lean) |
| Top half inert: its Mertens tail is exactly its prime count; the middle residual is exactly `−M(X)` | [`SquareRootTransportTopFibreNoGo`](../RHLean/Analysis/SquareRootTransportTopFibreNoGo.lean) |
| `M(x) = PNT-corrected all-plus mass − 2 * PNT error` | [`PrimeSievePNTCentering`](../RHLean/Analysis/PrimeSievePNTCentering.lean) |
| PNT error reindexed by quotient bands `d = floor(x/q)` | [`PrimeSieveQuotientPNTError`](../RHLean/Analysis/PrimeSieveQuotientPNTError.lean) |

The proposal is thus a regrouping of the compiled PNT centering. It is not a
new carrier.

## 3. New exact bridge (this PR)

[`LateFlipPNTSplitBridge`](../RHLean/Proof/LateFlipPNTSplitBridge.lean) works
prime-first for arbitrary `y < q <= x`. It writes
`Disc(y,x) = sum_{y<q<=x} (1_prime(q) − rho(q))`, with
`rho(q) = L(q) − L(q−1)`.

| Theorem | Statement |
| --- | --- |
| `primeCombReciprocalBandKernel_one` | `h(1) = 0` |
| `lateFlipPNTError_eq_lowerHalf` | `eta` only sums over `y < q <= x/2` |
| `mertensSummatory_eq_lateFlipRootField_add_correction` | `M(x) = B_root + H` once `sqrt x < y` |
| `mertensSummatory_eq_lateFlipModel_add_pntError` | `M(x) = (B_root + Hbar) + eta` |
| `lateFlipPNTError_eq_two_discrepancy_sub_two_pntError` | `eta = 2 Disc(y,x) − 2 primeSievePNTError(y,x)` |
| `lateFlipPNTError_eq_two_discrepancy_sub_two_reciprocalPNTError` | the same with the compiled quotient-band error |
| `lateFlipRootField_add_liModel_eq_pntCorrected_sub_two_discrepancy` | `B_root + Hbar = primeSievePNTCorrectedAllPlusMass(y,x) − 2 Disc(y,x)` |
| `lateFlipPrimeCountDiscrepancy_eq_count_sub_li` | `Disc(y,x) = (pi(x) − pi(y)) − (L(x) − L(y))` |
| `squareRoot_lateFlipModel_add_pntError_eq_gap_add_column` | at `X = R² − 1`: `A_R + eta_R = G_R + Q_R` |

Consequences:

- The proposed pair `(model, eta)` is the compiled pair
  `(PNT-corrected mass, −2 PNT error)` with one unweighted count `2 Disc`
  moved across. The top half is inert in the late-flip operator, but its primes
  remain in `Disc` and in the exact root field.
- The root field is linear in the same band counts. With
  `Psi_mu(X,R) = sum_{n<=X, all prime factors <= R} mu(n)`, it equals
  `Psi_mu(X,R) − (pi(X) − pi(R)) + sum_{k=1}^{R-1} (M(k) − 1) N_R(k)`
  (checked literally at `R = 60`), while `H_R` has kernel
  `2(1 − M(k))`. The combined kernel is `−M(k)`, the compiled prime tail. The
  split smooths only one copy of each `N_R(k)`, so the discrepancy reappears as
  `eta_R`.
- `A_R` is not a smoothed object. It contains the exact all-plus comb and the
  exact late prime count.

## 4. Telescoped form of `eta_R`

For `1 <= k <= R−2`, `floor(X/(k+1)) >= R+1`, so `l_k = u_{k+1}`; also
`l_{R−1} = R`. Write `Delta = pi − L`; then
`N_R(k) − Nbar_R(k) = Delta(u_k) − Delta(u_{k+1})`, with `u_R := R`.
Summation by parts uses `h(2) = 2` (since `M(2) = 0`) and
`h(k) − h(k−1) = −2 mu(k)`:

```text
eta_R = −2 sum_{k=2}^{R-1} mu(k) Delta(floor(X/k)) − 2 (1 − M(R−1)) Delta(R).
```

Thus `eta_R` is a Möbius-twisted sum of prime-count discrepancies at top-scale
arguments `X/k >= R`. Removing the inert top band removes `Delta(X)`, but
`Delta(floor(X/2))` enters with coefficient `+2`. The probe verifies this form
and the Lean bridge to within `1e-10` on every tested root.

**PNT used band by band does not reach the target scale.** The consumer needs
`|G_R + Q_R| = O(R sqrt(K))`. The best unconditional prime-number-theorem
error term gives `|Delta(t)| << t exp(−c (log t)^{3/5} (log log t)^{−1/5})`,
so the triangle inequality leaves `eta_R` near `R²` up to a subpolynomial
factor. Even the RH-quality pointwise bound `|Delta(t)| << sqrt(t) log t`
gives only `|eta_R| << R^{3/2} log R`, because `sum_{k<R} sqrt(X/k) ≈ 2R^{3/2}`.
Any saving must come from the `mu(k)` twist across bands. Section 5 shows that
this twist is carrying the top Mertens value.

## 5. Finite diagnostic

[`scripts/late_flip_pnt_split_probe.c`](../scripts/late_flip_pnt_split_probe.c)
computes every object of section 1 from a linear sieve. It uses the least
admissible envelope `K_R = max(1, max_{y<R} (M(y)−1)²/(y+1))`. The script
[`scripts/check_late_flip_pnt_split_probe.py`](../scripts/check_late_flip_pnt_split_probe.py)
recomputes each row for `R = 56..90` from the literal all-plus comb, the
prime-first sums, and the site-by-site diagonal. It then reproduces the default
summary. `K_R = 3/2` on the whole range, attained at `y = 5`.

| Range of `R` | 56–3000 | 56–10000 | 5000–10000 |
| --- | --- | --- | --- |
| roots | 2945 | 9945 | 5001 |
| rms `abs(G+Q)/R` | 0.179 | 0.180 | 0.187 |
| rms `abs(eta)/R` | 0.412 | 0.356 | 0.332 |
| rms `abs(A)/R` | 0.340 | 0.282 | 0.248 |
| Pearson(`M(X)`, `eta`) | 0.968 | 0.976 | 0.996 |
| fit `eta/R ≈ a + b M(X)/R`: `a`, `b` | −0.328, 1.335 | −0.272, 1.357 | −0.243, 1.354 |
| same after removing `Bsq`: `a`, `b`, `r` | −0.039, 1.338, 0.990 | −0.025, 1.349, 0.994 | −0.017, 1.351, 0.997 |
| rms residual of that fit / `R` | 0.033 | 0.026 | 0.020 |
| model Stokes `A²−D` > `FinalStokes` | 2730 / 2945 | 8448 / 9945 | — |
| max `(FinalStokes − 9E/4)/(R²K)` | −0.330 | −0.312 | — |
| max `(A² − D − 9E/4)/(R²K)` | −0.098 | −0.098 | — |

Here the explicit prime-square term is

```text
Bsq_R = sum_{k=2}^{R-1} mu(k) li(sqrt(X/k)) + (1 − M(R−1)) li(sqrt R).
```

Answers on the tested range:

- **Question 1.** The smooth late correction does not cancel the root-stage
  imbalance down to the size of `G+Q`. `A_R` is larger than `G_R + Q_R` in
  rms, and `A² − D` exceeds `FinalStokes` on 85–93% of the tested roots.
- **Question 2.** `eta_R` is not a small perturbation. After `Bsq_R` is
  removed, a fixed multiple of `M(X)` explains all but about `0.02 R` of it.
  Since `A_R + eta_R = G_R + Q_R` exactly, saving through the cross term is the
  statement that `G_R + Q_R` is small. The split adds no information unless one
  summand is bounded independently.
- Both Stokes quantities pass the `9/4` threshold with `C = 0` on this range.
  That is expected, because `D_R` is of order `0.6 R²`. A finite pass does not
  certify the uniform all-`R` estimate.

## 6. Heuristic reading (classical explicit formula; not formalized)

With simple zeros and the usual conditional convergence,
`Delta(t) = −li(sqrt t)/2 − sum_rho li(t^rho) + (lower order)`.

- The `−li(sqrt t)/2` term contributes exactly `Bsq_R` to the telescoped form.
  This matches the fitted intercept, which drops from about `−0.3` to about
  `−0.02`.
- For the zero terms, put `li(t^rho) ≈ t^rho/(rho log t)` and
  `1/log(X/k) = int_0^∞ (X/k)^{−u} du`. Near the pole of `1/zeta` at `rho`,
  the Perron residues of `sum_{k<R} mu(k) k^{−(rho−u)}` at `w = 0` and `w = u`
  combine to `(R^u − 1)/(u zeta'(rho))`. Frullani's integral with `R ≈ X^{1/2}`
  then gives

  ```text
  −2 sum_{k<R} mu(k) Delta_zeros(X/k)
      ≈ 2 sum_rho X^rho/(rho zeta'(rho)) int_0^∞ (X^{−u/2} − X^{−u}) du/u
      = 2 log 2 * sum_rho X^rho/(rho zeta'(rho)).
  ```

  The last sum is the zero part of the explicit formula for `M(X)`. The factor
  `log 2` arises because the bands `k < R` cover exactly half of the logarithmic
  range of `X/k`. The omitted `k = 1` term and the `Delta(R)` boundary term are
  smaller by about `1/log X`.

The fitted slopes, 1.34–1.35, are consistent with `2 log 2 ≈ 1.386` up to such
lower-order terms. This is the same coherent zero mode that the
[K₂ closeout](K2_COHERENT_MODE_KILL_GATE.md) found under a `log x` weight. Here
the weight is `2 log 2`.

## 7. Classification

- **Exact results retained.** Every identity in section 3 is a compiled
  regression; section 4 is checked numerically by the probe.
- **Mechanism status.** Substituting PNT density for the late-flip multiplicities
  adds no quantitative ingredient. The error of that substitution carries
  `M(X)`.
- **What a genuine ingredient would have to supply here.** It would need a
  uniform bound, at scale `R sqrt(K)` and with the contract's lower-envelope
  quantifiers, on the twisted top-scale discrepancy
  `T_R = sum_{2<=k<R} mu(k) Delta(floor(X/k))`. It would also need a bound on
  `A_R`, or on `G_R + Q_R` directly. The finite data and the heuristic put `T_R`
  on the scale of `M(X)`. No reverse implication is proved, so this identifies
  the residual. It does not show that the residual is unprovable.

## Reproduction

```text
cc -std=c11 -O2 -Wall -Wextra -Werror -o late_flip_pnt_split_probe \
   scripts/late_flip_pnt_split_probe.c -lm
./late_flip_pnt_split_probe                 # default R = 56..3000
./late_flip_pnt_split_probe 10000           # R = 56..10000 (about 25 s)
./late_flip_pnt_split_probe 10000 5000      # window R = 5000..10000
python3 scripts/check_late_flip_pnt_split_probe.py ./late_flip_pnt_split_probe
```

The dedicated workflow compiles the probe with warnings as errors and runs the
checker. The Lean bridge is certified only by the hosted Lean build.

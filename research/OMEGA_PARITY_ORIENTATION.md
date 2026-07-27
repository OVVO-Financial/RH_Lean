# Omega-parity vs orientation: the 2-vs-3 prime-factor lever

This note records a predeclared test of the "prove parity between the 2- and
3-prime-factor classes to get parity for Mobius" attack vector, its result, and
the reframing the data forces. It follows the acceptance rule in
[`RESEARCH_ROUTE_REGISTRY.md`](../RESEARCH_ROUTE_REGISTRY.md).

Diagnostic: [`experiments/omega_parity_orientation.py`](../experiments/omega_parity_orientation.py)
(dependency-free; exact integer arithmetic; `M(X)` cross-checked against the
Mertens sum at every scale).

## 1. The exact object

For squarefree `m` in `(1, X]` let `q = P+(m)` be the largest prime factor and
`c = m/q` the canonical cofactor. Then `omega(c) = omega(m) - 1` and, because
`q` is prime with `q ∤ c`,

```text
mu(m) = -mu(c) = (-1)^omega(m).
```

Grouping squarefree `m` by `k = omega(m)` gives the finite alternating identity

```text
M(X) = sum_{m<=X} mu(m) = 1 + sum_{k>=1} (-1)^k Q_k(X),
Q_k(X) = #{ squarefree m <= X : omega(m) = k }.
```

This is the **already-compiled** coordinate. `RHLean.Proof.DeathShellCofactorParity`
proves the per-shell version

```text
Delta death_t = sum_k N_k(t) * (-1)^(k+1),
```

with `N_k(t)` counting shell sources whose canonical cofactor has `k` distinct
primes. The global `Q_k` here is the same object aggregated over the square
prefix. So the "2 vs 3 prime factor" lever is not a new coordinate; it is the
`k = 2` and `k = 3` terms of an identity the library already contains.

## 2. The literal lever is false

The lever asks for `Q_2(X) ~ Q_3(X)` (and pairwise `Q_{2j} ~ Q_{2j+1}`), so that
consecutive classes cancel. Exact counts:

| X       | M(X) | Q_2      | Q_3      | Q_2 − Q_3 | Q_4 − Q_5 |
|---------|------|----------|----------|-----------|-----------|
| 1e4     | −23  | 2600     | 1800     | +800      | +405      |
| 1e5     | −48  | 23313    | 19919    | +3394     | +6129     |
| 1e6     | +212 | 209867   | 206964   | +2903     | +74579    |
| 4e6     | +192 | 790683   | 834198   | **−43515**| +317718   |

The consecutive gap `Q_2 − Q_3`:

- is **orders of magnitude larger** than `M(X)`;
- **grows** with `X`;
- **changes sign** (positive through `1e6`, negative by `4e6`), tracking the
  Landau shift of the peak class toward `k ~ log log X`.

It carries no information about `M(X)`. This is exactly the caution recorded in
`BIG_PICTURE_PROOF_MAP.md` §3 ("individual comparisons such as `N_2(t)` versus
`N_3(t)` do not replace the complete alternating sum over all represented `k`"),
now confirmed numerically. `M` is small only because of near-total cancellation
across **all** classes simultaneously, not any two-class balance. **STOP** on the
literal 2-vs-3 lever.

## 3. What the parity instinct is really pointing at

Partition squarefree `m` by the largest prime factor against the square-root
boundary and form the two orientation-restricted Mertens sums:

```text
high (transport):  P+(m) >  sqrt(m)     A_high(X) = sum_{high} mu(m) = sum_k (-1)^k Q_k^high
low  (smooth)   :  P+(m) <= sqrt(m)     A_low(X)  = sum_{low}  mu(m) = sum_k (-1)^k Q_k^low
A_high(X) + A_low(X) = M(X).
```

| X    | A_high | A_low  | M   | \|M\|/\|A_high\| |
|------|--------|--------|-----|------------------|
| 1e4  | +132   | −156   | −23 | 0.174            |
| 1e5  | +966   | −1015  | −48 | 0.050            |
| 1e6  | +6752  | −6541  | +212| 0.031            |
| 4e6  | +22140 | −21949 | +192| 0.0087           |

Each orientation sum is large and **grows**, while their signed total `M` stays
small: the ratio `|M| / |A_high|` **decreases monotonically** (0.174 → 0.0087).
The operative cancellation is `A_high ~ -A_low`, not `Q_2 ~ Q_3`.

This is not a new mechanism — it is the program's own target seen from the
omega-parity angle. `A_high` is the transport population, `A_low` the smooth
population, and `M = A_high + A_low` is the signed residual
`squareBlockSmoothPrefix - squareBlockTransportPrefix` of
`BIG_PICTURE_PROOF_MAP.md` §1. The omega-parity route therefore **rederives**
that the decisive pairing is smooth-vs-transport across the `sqrt(m)` boundary,
and supplies no shortcut around it. Meeting the predeclared "interesting"
criterion (`|M|/|A_high|` decreasing) only says the existing target is the right
one; it is not itself an estimate.

## 4. One exact sub-fact worth recording

The high/low split is not free of theorems. For squarefree `m` with
`omega(m) <= 2` the largest prime factor **always** exceeds `sqrt(m)`:

- `omega(m) = 1`: `m = q`, so `P+(m) = m > sqrt(m)`;
- `omega(m) = 2`: `m = c*q` with primes `c < q`, so `c < sqrt(m) < q`.

Hence `Q_1` and `Q_2` are entirely high-orientation, which the data confirms
(`Q_k low = 0` for `k <= 2` at every scale). The low orientation begins only at
`omega(m) >= 3`.

This is a clean, unconditional statement, and it is now compiled in
`RHLean.Proof.LowOmegaHighOrientation`:

```text
canonicalCofactor_lt_largestPrimeFactor :
  Squarefree m → 1 < m → m.primeFactors.card ≤ 2 →
    canonicalCofactor m < canonicalLargestPrimeFactor m
lt_largestPrimeFactor_sq :                  ... → m < (canonicalLargestPrimeFactor m) ^ 2
canonicalHeightTwice_pos_of_card_primeFactors_le_two :
                                            ... → 0 < canonicalHeightTwice m
```

Because `canonicalHeightTwice m = P⁺(m)^2 - c^2`, the cofactor inequality is
exactly the positive-height (pure `q > c`, high-orientation) statement. It is a
support fact about where the `omega ≤ 2` classes live, not amplitude control: it
lets those terms be treated as pure high-orientation mass without splitting the
smooth/transport interaction, but it does not bound any cumulative sum.

## 5. Verdict

- **Exact identity retained:** `M(X) = 1 + sum_k (-1)^k Q_k`, and the orientation
  split `M = A_high + A_low` (both already implied by compiled results).
- **Falsified as a lever:** `Q_2 ~ Q_3` (and any fixed consecutive-pair balance).
  The gap is large, growing, and sign-changing.
- **Reframed, not new:** the surviving cancellation is `A_high ~ -A_low`, i.e.
  the smooth/transport residual the program already protects. The omega-parity
  view is a faithful re-encoding of the target, useful for intuition, but it does
  not by itself outperform the existing coordinate or beat randomized signed
  mixing.

Per the registry's do-not-repeat discipline: do not restart the 2-vs-3 lever by
enlarging `X`, renaming `N_2/N_3`, or pairing a different fixed consecutive
class. A future omega-parity theorem must control the full `A_high` (transport)
sum itself, with the `sqrt(m)` boundary geometry retained.

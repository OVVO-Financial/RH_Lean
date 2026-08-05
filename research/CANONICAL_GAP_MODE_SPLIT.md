# Canonical-gap cancellation: coherent mode versus orthogonal residual

This note sharpens `CANONICAL_GAP_PREFIX_GRAM_SCAN.md`. The near-perfect raw
balanced/extreme anti-correlation is real, but it is not a single homogeneous effect.
An exact orthogonal projection isolates two distinct cancellation mechanisms.

## Exact projection

For a window of `H` square blocks, let

```text
B_r = sum_{j=0}^r b_{N+j},
E_r = sum_{j=0}^r e_{N+j},
t_r = r+1,                    0 <= r < H.
```

Project each prefix vector onto the linear vector `t = (1,...,H)`:

```text
alpha_B = <B,t> / <t,t>,      R_B = B - alpha_B t,
alpha_E = <E,t> / <t,t>,      R_E = E - alpha_E t.
```

By construction, `R_B` and `R_E` are orthogonal to `t`, so the total energy splits
without a cross term between modes:

```text
||B+E||^2
  = (alpha_B + alpha_E)^2 ||t||^2
    + ||R_B + R_E||^2.
```

This is an exact finite identity. The checked-in scanner computes it with integer
numerators; floating-point values below are used only to display ratios.

## Exact finite results

| window | `alpha_B` | `alpha_E` | coherent cancellation | residual `rho` | residual cancellation | residual `Q_BB/(HN^2)` | residual `Q_EE/(HN^2)` | residual `Q_tot/(HN^2)` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `[1000,2000)` | -17.67724766 | 17.32737489 | 99.980022% | -0.944360248 | 93.374256% | 0.436241 | 0.589645 | 0.067973 |
| `[5000,10000)` | -60.69949295 | 60.58451763 | 99.999820% | -0.991779131 | 98.967076% | 3.492826 | 3.979822 | 0.077187 |
| `[10000,20000)` | -103.0650630 | 102.8443726 | 99.999770% | -0.997482668 | 99.680272% | 11.163067 | 12.018872 | 0.074119 |
| `[50000,51000)` | -307.7208633 | 292.8900419 | 99.878127% | -0.062457684 | 1.487616% | 0.000024 | 0.001662 | 0.001661 |
| `[100000,101000)` | -497.8678723 | 509.3538517 | 99.973995% | +0.605182925 | -38.092338% | 0.000190 | 0.001511 | 0.002348 |

The interpretation is now precise.

### 1. The coherent linear mode cancels at every tested scale

The balanced and extreme slopes are large and opposite. This is the dominant source
of the raw prefix anti-correlation, especially on short windows. It is the canonical-
gap version of smooth/transport matching: the two populations carry nearly equal and
opposite average increment rates.

### 2. Short-window orthogonal residuals are already subcritical

For `H/N = 0.01` and `0.02`, each residual diagonal energy is far below `H N^2`.
Residual correlation can therefore be weak or even positive without threatening the
required bound. A theorem demanding residual anti-alignment on every short window
would be false and unnecessary.

### 3. Long-window residuals require a second cancellation

When `H` is comparable to `N`, the separate residual energies become supercritical.
The data then show strong residual anti-alignment, reducing their coupled total back
to the target scale. On `[10000,20000)`, the residual diagonal energies are about
`11.16 HN^2` and `12.02 HN^2`, while the coupled residual is only
`0.0741 HN^2`.

Thus the remaining theorem is scale-sensitive:

```text
coherent mode: prove balanced/extreme slope matching uniformly;
short residual mode: prove separate subcritical estimates;
long residual mode: retain and prove the coupled balanced/extreme cross term.
```

## Extreme pairs are automatically high

`RHLean/Proof/CanonicalExtremeHeight.lean` proves, for the extreme regime `u <= d`,

```text
3 * u * (u+d) <= 2 * d * (2u+d).
```

Hence for a pair in square block `B_n`,

```text
3 n^2 <= 2 * doubledHeight(u,d).
```

Every subquadratic canonical-height cutoff therefore retains all sufficiently mature
extreme pairs. This explains why removing the low-height band changes the balanced
sector but leaves the extreme sector unchanged: the low-band theorem is removing only
near-diagonal balanced pairs, not the extreme transport population.

## Frozen analytic target

The exact total target remains

```text
sum_{r=0}^{H-1} |B_r + E_r|^2 <<_eps H N^(2+eps).
```

But it should now be proved through the orthogonal mode split, not by separate raw
bounds for balanced and extreme sectors and not by a universal residual-correlation
claim.

The first analytic obligation is the coherent matching estimate. After that, the
orthogonal residual theorem should be divided by window scale: separate estimates in
the subcritical short range and a coupled cross-energy estimate in the long range.

## Reproduction

The checked-in compact scanner reproduces full-window raw, endpoint-bridge, and
orthogonal-mode ledgers for four thresholds:

```bash
gcc -O3 -Wall -Wextra \
  -o canonical_gap_prefix_scan canonical_gap_prefix_scan.c -lm

./canonical_gap_prefix_scan 1000 1000
./canonical_gap_prefix_scan 5000 5000
./canonical_gap_prefix_scan 10000 10000
./canonical_gap_prefix_scan 50000 1000
./canonical_gap_prefix_scan 100000 1000
```

It exits nonzero if the all-source balanced/extreme reconstruction fails in any square
block. The exhaustive sliding-window statistics in the companion report were produced
by the development scanner before compacting the checked-in reproducer.
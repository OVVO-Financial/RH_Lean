# Cross-scale cancellation diagnostic

## Scope

This record tests the only remaining proposed use of the dyadic distinguished-prime
`q`-fibres after the positive diagonal route was closed: a bounded-width signed block
mechanism that keeps the exact top prime boundary attached to its compensator.

The diagnostic is finite and route-falsifying, not an asymptotic theorem.

For global prefix paths `F_k` on a window, define

```text
G_{k,l} = sum_n F_k(n) F_l(n)
D       = sum_k G_{k,k}
E       = sum_{k,l} G_{k,l}
```

The program uses the unordered-pair convention

```text
eta_w = -2 sum_{k<l, l-k <= w} G_{k,l} / (D-E),
```

so full width gives `eta = 1` exactly.

For the formal gatekeeper, the top scale changes with `n`:

```text
k_top(n) = floor(log_2 ((n+1)^2 - 1)).
```

The dynamic top-row statistic is

```text
theta_w =
  -2 sum_n sum_{0 < |l-k_top(n)| <= w} F_{k_top(n)}(n) F_l(n)
  / sum_n F_{k_top(n)}(n)^2.
```

`theta_share_w` divides the same numerator by its full-width value. Positive offset
mass means cancellation of the top fibre; negative mass means reinforcement.

The implementation uses integer increments and prefixes and `__int128` quadratic
sums. Every run checks both the exact Gram identity and the numeric top-fibre identity
against the pure prime contribution.

## Reproduction

```text
cc -O3 -std=c11 -Wall -Wextra \
  -o packet_cross_scale packet_cross_scale.c -lm

./packet_cross_scale 2000 2000
./packet_cross_scale 5000 5000
./packet_cross_scale 2000 1
./packet_cross_scale 5000 1
```

All four runs returned success with:

```text
Gram identity check  : PASS
top gatekeeper audit : PASS
```

## Locality results

A first crossing is not enough because the cumulative signed mass is strongly
nonmonotone. The stable width is the first `w` after which every larger width remains
within the stated tolerance of the full-width value.

| `N` | `H` | live scales | first `eta >= 0.90` | stable `eta` within 5% | first top share `>= 0.90` | stable top share within 5% | global tail TV at `w=5` | top tail TV at `w=5` |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 2000 | 2000 | 23 | 6 | 15 | 4 | 15 | 0.979607 | 0.478901 |
| 5000 | 5000 | 26 | 7 | 16 | 5 | 16 | 1.031919 | 0.553238 |
| 2000 | 1 | 21 | 6 | 14 | 4 | 13 | 0.880911 | 0.376895 |
| 5000 | 1 | 24 | 7 | 16 | 5 | 16 | 1.168242 | 0.573742 |

At `H=N`, the apparently favorable first crossings hide large signed tails:

| `N` | `eta_5` | `eta_8` | global tail TV at `w=8` | top share at `w=5` | top tail TV at `w=8` |
|---:|---:|---:|---:|---:|---:|
| 2000 | 0.824324 | 1.058464 | 0.745467 | 1.054438 | 0.355048 |
| 5000 | 0.817500 | 0.990660 | 0.858759 | 1.027548 | 0.398900 |

Thus width five captures a large net top-row cancellation, but the omitted signed
variation is still roughly half of the full top-row cancellation and about the entire
global required cross-term. The cumulative answer stabilizes only at widths `15` to
`17`, a substantial fraction of all live scales.

## Mandatory top-fibre compensators

The dominant dynamic-top offsets at `H=N` are:

| `N` | offset `l-k_top` | share of full top-row cancellation |
|---:|---:|---:|
| 2000 | -1 | -0.247810 |
| 2000 | -2 | +0.509695 |
| 2000 | -3 | +0.422870 |
| 2000 | -4 | +0.235370 |
| 2000 | -12 | -0.146769 |
| 2000 | -13 | -0.105517 |
| 5000 | -1 | -0.501787 |
| 5000 | -2 | +0.562567 |
| 5000 | -3 | +0.509780 |
| 5000 | -4 | +0.296576 |
| 5000 | -14 | -0.159906 |
| 5000 | -13 | -0.086712 |

The nearest lower scale, `k_top-1`, reinforces the prime boundary rather than
cancelling it. The leading compensators are `k_top-2` and `k_top-3`, with `k_top-4`
secondary. Far lower scales then make material corrections. This is a concrete
compensator signature, but not a bounded-width closure.

## Disjoint contiguous block test

For each width and phase, the diagnostic partitions scales by

```text
block(k) = floor((k + phase) / width)
```

and computes

```text
kappa_block = sum_blocks ||sum_{k in block} F_k||^2 / ||sum_k F_k||^2.
```

Even after fitting the phase, bounded widths remain extremely inflated:

| `N` | `H` | best `kappa_block`, widths 2 through 8 | width | phase | phase-zero `kappa` at width 8 |
|---:|---:|---:|---:|---:|---:|
| 2000 | 2000 | 3548.061 | 8 | 6 | 10353.697 |
| 5000 | 5000 | 14952.312 | 8 | 4 | 2533805.306 |
| 2000 | 1 | 1681.480 | 8 | 7 | 8086.353 |
| 5000 | 1 | 4695.892 | 8 | 5 | 2031979.296 |

Allowing widths through 16 only lowers the best value by using blocks that cover most
of the live scale range, and the fitted phase changes with `N` and `H`. For example,
the best `H=N` value changes from `253.050` at width 16 and phase 8 for `N=2000` to
`4377.625` at width 15 or 16 and phase 3 or 4 for `N=5000`.

## Decision

**The bounded-width contiguous `q`-block route fails the predeclared acceptance
criteria.**

1. The net first-crossing widths look small, but signed tail variation remains of the
   same order as the full required cancellation.
2. Stable locality requires width `15` to `17`, not a fixed small neighborhood on the
   tested range.
3. The mandatory top fibre has identifiable nearby compensators, but `k_top-1`
   reinforces it and far scales make non-negligible corrections.
4. Disjoint block energies are huge, grow between `N=2000` and `N=5000`, depend
   violently on phase, and fail at `H=1` as well as `H=N`.

This does not prove that every conceivable data-independent signed transform of the
`q`-fibres is impossible. It closes the natural bounded-width locality mechanism that
motivated `eta_w`. The `q`-packet layer should now be retained as an exact audit and
obstruction layer rather than the primary estimation coordinate.

The next proof search should move to a coordinate system in which cancellation is
built into the atoms, specifically the original chain-impulse Fourier packets or the
two-anchor centered residual. Every replacement must still pass the merged top-fibre
gatekeeper test explicitly.

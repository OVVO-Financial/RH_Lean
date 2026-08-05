# Canonical-gap prefix Gram scan: cancellation between balanced and extreme sectors

This note records the exact scan of the balanced/extreme decomposition from
`RHLean/Proof/BalancedCanonicalGap.lean` and then removes the coherent increment
mode to determine where the cancellation actually lives.

## Status

- **Exact finite computation:** yes. The segmented sieve uses integer Möbius values,
  exact largest-prime-factor recovery, integer canonical heights, and `__int128`
  energy accumulation.
- **Exact reconstruction check:** zero mismatches in every scan: the all-source
  balanced increment plus the all-source extreme increment equals the direct
  square-block Möbius increment at every block.
- **Analytic theorem:** still open. The scan decides the shape and scale split of the
  theorem to attack; it does not prove the uniform asymptotic estimate.

## Definitions tested

For a squarefree source `m`, let `q = P+(m)`, `c = m/q`, and write

```text
u = min(c,q),   v = max(c,q),   d = v-u,
h2 = d(u+v) = |q-c|(q+c) = 2Z.
```

A source is

```text
balanced  when 0 < d < u,
extreme   when u <= d.
```

For a chosen high-band threshold `K_n`, let `b_n` and `e_n` be the signed Möbius
increments of the balanced and extreme sectors in square block
`[n^2,(n+1)^2)`. For a window `[N,N+H)`, define local prefixes

```text
B_r = sum_{j=0}^r b_{N+j},
E_r = sum_{j=0}^r e_{N+j}.
```

The exact prefix ledger is

```text
Q_BB  = sum_r B_r^2,
Q_EE  = sum_r E_r^2,
Q_BE  = sum_r B_r E_r,
Q_tot = Q_BB + 2 Q_BE + Q_EE = sum_r (B_r+E_r)^2.
```

Thresholds are expressed using doubled height:

```text
all:       h2 > 0,
Lambda=L:  h2 > 2 L n,
delta=a:   h2 > 2 n floor(n^a).
```

## First conclusion: the raw prefix energies cancel between sectors

All rows below satisfy `H <= N`, so `H N^2` is the natural local square-prefix scale.

| square-block window | squarefree sources | `B_H` | `E_H` | `B_H+E_H` | raw `rho` | cross cancellation | `Q_BB/(HN^2)` | `Q_EE/(HN^2)` | `Q_tot/(HN^2)` | diagonal/total |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `[1000,2000)` | 1,823,810 | -18,469 | 18,449 | -20 | -0.9996537301 | 99.9471% | 104.754 | 100.819 | 0.10884 | 1,888.8 |
| `[5000,10000)` | 45,594,514 | -327,447 | 328,743 | 1,296 | -0.9999682612 | 99.9967% | 1,232.004 | 1,227.841 | 0.08159 | 30,147.2 |
| `[10000,20000)` | 182,378,211 | -1,100,659 | 1,097,132 | -3,527 | -0.9999892889 | 99.9987% | 3,552.497 | 3,538.203 | 0.09036 | 78,474.9 |
| `[50000,51000)` | 61,400,708 | -307,441 | 292,287 | -15,154 | -0.9999275390 | 99.8712% | 12.645 | 11.457 | 0.03103 | 776.6 |
| `[100000,101000)` | 122,193,379 | -501,079 | 506,914 | 5,835 | -0.9998630970 | 99.9601% | 8.275 | 8.663 | 0.00675 | 2,508.5 |

The exact ledger on `[10000,20000)` is

```text
Q_BB   =  3,552,496,605,692,747
Q_EE   =  3,538,202,728,567,550
2 Q_BE = -7,090,608,977,992,656
Q_tot  =         90,356,267,641
```

Separate diagonal estimates are therefore the wrong primary target: each diagonal
energy can exceed the nominal scale by thousands while the coupled residual remains
below it.

## The decisive refinement: remove the coherent increment mode

The raw prefix correlation can be dominated by opposite linear drifts. To remove that
mode exactly, define the integer-scaled bridge prefixes

```text
B^o_r = H B_r - (r+1) B_{H-1},
E^o_r = H E_r - (r+1) E_{H-1}.
```

Equivalently, `B^o/H` and `E^o/H` are the prefixes after subtracting each increment
sequence's window mean. They both vanish at the right endpoint. The scanner computes
the exact bridge ledger

```text
Q^o_BB  = H^-2 sum_r (B^o_r)^2,
Q^o_EE  = H^-2 sum_r (E^o_r)^2,
Q^o_BE  = H^-2 sum_r B^o_r E^o_r,
Q^o_tot = Q^o_BB + 2 Q^o_BE + Q^o_EE.
```

The factor `H^-2` is only a reporting normalization; all comparisons and signs are
computed before division in exact integer arithmetic.

### Full-window bridge results

| window | `H/N` | bridge `rho` | bridge cancellation | `Q^o_BB/(HN^2)` | `Q^o_EE/(HN^2)` | `Q^o_tot/(HN^2)` | bridge diagonal/total |
|---|---:|---:|---:|---:|---:|---:|---:|
| `[1000,2000)` | 1.00 | -0.960515 | 93.70% | 0.645512 | 1.009622 | 0.104299 | 15.9 |
| `[5000,10000)` | 1.00 | -0.997430 | 99.48% | 11.142857 | 12.871737 | 0.123870 | 193.9 |
| `[10000,20000)` | 1.00 | -0.998563 | 99.86% | 27.502757 | 27.748161 | 0.079929 | 691.3 |
| `[50000,51000)` | 0.02 | -0.143928 | 4.02% | 0.000035 | 0.001711 | 0.001675 | 1.04 |
| `[100000,101000)` | 0.01 | +0.612826 | -52.19% | 0.000534 | 0.001709 | 0.003414 | 0.66 |

This changes the interpretation materially:

1. **Short windows:** after removal of the coherent drift, each sector's bridge energy
   is already far below the RH-scale budget. The bridge cross term need not be
   favorable and can even be positive.
2. **Long square-scale windows:** the separate bridge energies grow beyond the budget,
   and a second, genuinely nonzero-frequency balanced/extreme anti-alignment appears.

Thus the universal raw correlation near `-1` is not one homogeneous phenomenon. It
contains a coherent zero-mode cancellation at every tested scale and an additional
fluctuation cancellation only when the window is long enough for separate bridge
energies to become dangerous.

### Scale transition at fixed `N = 10000`

| `H` | `H/N` | bridge `rho` | `Q^o_BB/(HN^2)` | `Q^o_EE/(HN^2)` | `Q^o_tot/(HN^2)` |
|---:|---:|---:|---:|---:|---:|
| 64 | 0.0064 | +0.1943 | 0.000019 | 0.000889 | 0.000957 |
| 128 | 0.0128 | -0.4137 | 0.000019 | 0.006223 | 0.005956 |
| 256 | 0.0256 | -0.8126 | 0.000990 | 0.007041 | 0.003739 |
| 512 | 0.0512 | -0.7764 | 0.003162 | 0.005883 | 0.002348 |
| 1,024 | 0.1024 | +0.2147 | 0.003626 | 0.099867 | 0.111664 |
| 2,048 | 0.2048 | +0.3803 | 0.002866 | 0.056908 | 0.069488 |
| 4,096 | 0.4096 | -0.9867 | 1.952126 | 2.272669 | 0.068090 |
| 8,192 | 0.8192 | -0.9974 | 12.483901 | 13.899999 | 0.105844 |
| 10,000 | 1.0000 | -0.9986 | 27.502757 | 27.748161 | 0.079929 |

The bridge correlation is not monotone at small widths, nor does it need to be: the
separate bridge energies there are already negligible. Once those diagonal energies
cross the target scale, strong anti-alignment appears in the tested data.

## Sliding-window robustness of the raw mode

For the super-window `[10000,20000)`, every subwindow was tested, not sampled.

| width | windows | raw `Q_BE < 0` | raw total below each diagonal | median raw `rho` | median raw cancellation | bridge `Q^o_BE < 0` | median bridge `rho` | median bridge cancellation |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 64 | 9,937 | 100% | 99.99% | -0.997214 | 98.87% | 35.21% | +0.219730 | -7.66% |
| 256 | 9,745 | 100% | 100% | -0.999252 | 99.69% | 40.89% | +0.162994 | -5.63% |
| 1,024 | 8,977 | 100% | 100% | -0.999759 | 99.93% | 57.64% | -0.259260 | 15.94% |
| 10,000 | 1 | 100% | 100% | -0.999989 | 99.9987% | 100% | -0.998563 | 99.86% |

Again, short-window raw anti-alignment is coherent-mode cancellation, not a claim of
universal centered anticorrelation.

## Robustness to removing the low canonical-height band

On `[10000,20000)`, the long-window conclusion survives removal of growing low-height
bands:

| threshold | raw `rho` | raw cancellation | bridge `rho` | bridge cancellation | raw `Q_tot/(HN^2)` |
|---|---:|---:|---:|---:|---:|
| all, `h2 > 0` | -0.9999893 | 99.9987% | -0.998563 | 99.8553% | 0.09036 |
| `h2 > 2n floor(n^(1/4))` | -0.9999893 | 99.9989% | -0.998564 | 99.8551% | 0.08079 |
| `h2 > 2n floor(n^(1/2))` | -0.9999893 | 99.9931% | -0.998501 | 99.8449% | 0.48401 |

The long-scale anti-alignment is therefore not generated by the already-controlled
low-imbalance population.

## What the scan now decides

The remaining proof has a scale-sensitive two-mode structure.

### Coherent increment mode

The opposite endpoint drifts must be matched:

```text
B_{H-1} + E_{H-1} is small compared with B_{H-1} and E_{H-1}.
```

This is the balanced/extreme version of the original smooth-transport matching.
It is present at every tested window length.

### Mean-zero bridge mode

For the residual prefixes after subtracting each sector's increment mean:

```text
short H/N:  prove separate bridge-energy bounds;
long H/N:   retain and prove the coupled bridge cross term.
```

The exact coupled analytic target remains

```text
sum_{r=0}^{H-1} |B_r + E_r|^2  <<_eps  H N^(2+eps),
```

but the scan now identifies how it should be attacked rather than merely restating it:
control the coherent endpoint mode, use separate centered estimates while they are
subcritical, and invoke a coupled long-window anti-alignment theorem only where the
centered diagonal energies become supercritical.

## Formal companion

`RHLean/Proof/CanonicalGapPrefixGram.lean` formalizes, without analytic assumptions:

- additivity of finite prefix sums;
- the exact energy ledger `Q_tot = Q_BB + 2 Q_BE + Q_EE`;
- the prefix Gram kernel `K_H(i,j) = H - max(i,j)`;
- the arithmetic balanced/extreme instantiation.

The next exact formal addition is the mean-zero increment bridge
`H * prefix - (r+1) * endpoint` and its identical balanced/extreme Gram ledger.

## Reproduction

```bash
gcc -O3 -march=native -Wall -Wextra \
  -o canonical_gap_prefix_scan canonical_gap_prefix_scan.c -lm

./canonical_gap_prefix_scan 1000 1000
./canonical_gap_prefix_scan 5000 5000
./canonical_gap_prefix_scan 10000 10000
./canonical_gap_prefix_scan 50000 1000
./canonical_gap_prefix_scan 100000 1000
```

The scanner exits nonzero if the all-source balanced/extreme reconstruction fails in
any square block.
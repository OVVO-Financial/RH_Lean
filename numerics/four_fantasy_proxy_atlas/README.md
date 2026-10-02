# Four fantasy proxy numerical atlas

This directory visualizes the four counterfactual prime-count proxies formalized in
`research/FOUR_FANTASY_PROXY_RH_CLOSURES.lean`, always with the actual prime-count
function overlaid or compared on the same finite range.

The four proxy series are:

1. **continuous Li**: `vfMidLogarithmicIntegralFromTwo`;
2. **fractional VF cluster**: `vfMidFractionalPrimeClusterMass`, defined at square endpoints and proved equal to `vfMid` there;
3. **literal midpoint-linear VF**: `vfMidLinearMidpointInterpolant`;
4. **integer-cutoff floor(Li)**: `liIntegerCutoffFloorPrimeCountProxy`.

The Lean file proves that each corresponding actual-to-proxy tracking statement at
von-Koch scale is sufficient for RH (and, through the classical criterion, equivalent
to the relevant RH-scale statement). The figures here are **finite diagnostics** only:
they show how closely actual `pi` follows those already-solved deterministic proxy
geometries, but they do not prove the missing asymptotic actual-to-proxy bound.

## Default numerical extent

`run_atlas.py` uses:

- square-root indices `R = 2,...,10000`;
- square endpoints through `x = 100,000,000`;
- exact prime counts from an Eratosthenes sieve;
- local staircase views through `x = 2500`;
- RH-normalized residual plots from `R >= 56`.

The proxy formulas mirror the Lean definitions rather than fitting curves to the
prime data.

## Recorded finite results

Over `R >= 56`, the largest observed values of

[
|pi(R^2)-proxy(R^2)|/(R log R)
]

through `R=10000` are:

| Proxy | Maximum | R of maximum | Value at R=10000 |
|---|---:|---:|---:|
| continuous Li | 0.06794593 | 57 | 0.00817918 |
| fractional VF cluster | 0.05887789 | 57 | 0.00815634 |
| midpoint-linear VF | 0.05884490 | 57 | 0.00815633 |
| floor(Li) | 0.06508893 | 57 | 0.00817559 |

Thus all four finite actual-to-proxy discrepancies remain far inside a unit
`R log R` envelope over this tested range. This is numerical evidence, not a
uniform asymptotic theorem.

For the anchored VF step graph with

[
c_0 = pi(9)-VF_{mid}(9),
]

the finite scan through `R=10000` finds **zero full-graph misses**. The only
non-horizontal blocks are `R = 2, 119, 178, 547, 549`, and each is rescued by a
vertical graph face.

## Figures

- `results/four_proxy_pi_overlay_global.png` — all four proxies plus actual `pi(R^2)` through `x=10^8`.
- `results/four_proxy_rh_normalized_residuals.png` — signed actual-minus-proxy residuals in the exact square-endpoint RH scale `R log R`.
- `results/four_proxy_block_scale_residuals.png` — absolute discrepancies in one-block units `R/log R`.
- `results/overlay_continuous_li.png` — local actual `pi(x)` staircase versus continuous Li.
- `results/overlay_fractional_cluster.png` — local actual `pi(x)` versus the exact fractional VF cluster at its native square endpoints.
- `results/overlay_linear_midpoint_vf.png` — local actual `pi(x)` versus the literal midpoint-linear VF interpolant.
- `results/overlay_floor_li.png` — local actual `pi(x)` versus the integer-cutoff floor(Li) staircase.
- `results/vf_step_graph_crossing_diagnostic.png` — horizontal crossings, vertical rescues, and misses by square block.

## Reproduction

```bash
python numerics/four_fantasy_proxy_atlas/run_atlas.py
```

Dependencies: NumPy, SciPy, and Matplotlib.

The script also writes `results/square_endpoint_proxy_comparison.csv` and
`results/summary.json`. The CSV is intentionally regenerable from the exact formulas
and sieve; the compact JSON summary and rendered figures are committed as the
human-auditable numerical record.

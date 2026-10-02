# VF-mid NNS.meboot dependence stress numerics

This directory records the maximum-entropy bootstrap experiment used to probe how much serial dependence the square-block VF discrepancy can tolerate before approaching the RH/von-Koch envelope.

The experiment is diagnostic only. It is not a premise of the Lean theorem chain and it does not prove an asymptotic statement about primes.

## Series under test

For square block

\[
I_R=(R^2,(R+1)^2],
\]

write

\[
P_R=\pi((R+1)^2)-\pi(R^2),
\qquad
V_R=\frac{2R+1}{\log(R^2+R+1/2)}.
\]

On the exact odd-seat VF carrier, set

\[
w_R=\frac{V_R}{R},
\qquad
b_R=R w_R(1-w_R),
\qquad
z_R=\frac{P_R-V_R}{\sqrt{b_R}}.
\]

The run uses `R = 56,...,3161`, so the final square endpoint is `R = 3162` (`x = 9,998,244`). Prime counts are generated exactly by an Eratosthenes sieve.

The cumulative endpoint error reconstructed from a synthetic standardized path is

\[
D_R=D_{56}+\sum_{r=56}^{R-1} z_r\sqrt{b_r}.
\]

The main diagnostic is

\[
\max_{R\ge1000}\frac{|D_R|}{R\log R}.
\]

The proposed polylogarithmic variance-inflation diagnostic is

\[
K_{\rm req}
=
\max_R\frac{C_R^2}{(\log R)^3B_R},
\qquad
C_R=\sum_{r=56}^{R-1}(P_r-V_r),
\qquad
B_R=\sum_{r=56}^{R-1}b_r.
\]

## NNS.meboot source

The suite uses `nns.meboot.nns_meboot` from OVVO's NNS-Python implementation. The run recorded here was matched against:

- repository: `OVVO-Financial/NNS-python`
- source commit checked during the run: `55d15c9d6412a68942af467e9129551f4801f325`
- implementation: `src/nns/meboot.py`

The checked implementation targets requested Pearson or Spearman correlation by rank-aligned/anti-aligned maximum-entropy bootstrap interpolation and preserves the requested drift/variance controls.

## Monte Carlo design

Two experiments were run.

### 1. Dependence-to-actual sweep

For each of Pearson and Spearman targeting,

\[
\rho\in\{-0.95,-0.75,-0.50,-0.25,0,0.25,0.50,0.75,0.95\}
\]

with 199 replicates per target. Total: `2 x 9 x 199 = 3582` paths.

This answers a narrow question: does a bootstrap path need to be nearly independent of the observed standardized VF-error path in order to remain below the RH-normalized envelope?

### 2. Serial-persistence stress

The actual `z_R` values are rank-reordered onto AR(1) templates with

\[
\phi\in\{-0.90,-0.50,0,0.50,0.90,0.97,0.99\}.
\]

For each `phi`, three independent templates are formed. Each template is then passed through `nns_meboot` with target Spearman correlation `0.95`, with 49 replicates per template. Total: `7 x 3 x 49 = 1029` paths.

This is the more relevant adversarial experiment because it directly manufactures sustained internal serial coherence while retaining the empirical standardized-error marginal.

Total suite size: **4611 paths**.

## Recorded results

Actual VF/primes over the tested range:

- lag-1 correlation: `-0.13828406098`
- lag-2 correlation: `-0.09383200041`
- `max_{R>=1000} |D_R|/(R log R) = 0.01978508950`
- final ratio at `R=3162`: `0.01292307895`
- `K_req = 0.00579160968`

Dependence-to-actual sweep:

- pooled 99th percentile of `max_{R>=1000} |D_R|/(R log R)`: `0.1842733`
- pooled maximum: `0.2165517`

Serial-persistence stress:

- pooled 99th percentile of the same RH-normalized maximum: `0.3997581`
- pooled maximum: `0.4777509`
- pooled 99th percentile of `K_req`: `0.849714`
- pooled maximum `K_req`: `1.078695`
- `1025 / 1029 = 99.611%` of serial-stress paths satisfy `K_req <= 1`

At the strongest persistence setting `phi=0.99`, the realized lag-1 correlation has median `0.925596` and reaches `0.969942`. The corresponding RH-normalized maximum has median `0.244605`, 95th percentile `0.397586`, and maximum `0.477751`. Even there, `143 / 147 = 97.279%` of paths satisfy `K_req <= 1`.

Every one of the 4611 generated paths satisfies

\[
\max_{R\ge1000}\frac{|D_R|}{R\log R}<1
\]

over the finite range tested.

## Interpretation and scope

These results strongly falsify the numerical claim that near-independence is required for the VF route. Very large positive serial correlation is compatible, over the tested range, with substantial room inside the RH-normalized envelope.

They do **not** show that the actual deterministic prime process has a uniform asymptotic correlation bound, and they do **not** exclude a pathological coherence mode appearing only at much larger scales. The appropriate theorem target remains deterministic: control positive coherent accumulation of the actual block errors, for example through a bound of the form

\[
C_R^2\le K(\log R)^3B_R
\]

for a fixed constant `K`, or an equivalent signed owner-tree/Gram estimate.

The numerical point is that this target appears to allow a wide corridor: the actual tested path needs only `K ~= 0.0058`, while deliberately manufactured paths with lag-1 persistence above `0.9` usually still fit under `K=1`.

## Reproduction

Install NNS-Python plus the plotting/data dependencies, then run:

```bash
python numerics/vf_mid_meboot/run_vf_mid_meboot.py \
  --out numerics/vf_mid_meboot/results
```

The default seeds, grid, replicate counts, and endpoint range reproduce the experiment recorded here.

The CSV/JSON files in `results/` are the committed numerical record. Plots are regenerated by the script.

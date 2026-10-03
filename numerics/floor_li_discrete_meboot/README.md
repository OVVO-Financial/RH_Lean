# Floor-Li discrete backlog NNS.meboot numerics

This directory records the discrete prime-vs-floor-Li experiment that complements the earlier `numerics/vf_mid_meboot/` suite.

The primitive integer-lattice mismatch is

\[
\xi_n=1_{\mathbb P}(n)-\left(\lfloor Li_2(n)\rfloor-\lfloor Li_2(n-1)\rfloor\right)\in\{-1,0,1\},
\]

with the repository normalization \(Li_2(x)=\int_2^x dt/\log t\).  At square blocks,

\[
P_R-F_R=\sum_{R^2<n\le (R+1)^2}\xi_n,
\qquad
F_R=\lfloor Li_2((R+1)^2)\rfloor-\lfloor Li_2(R^2)\rfloor.
\]

The cumulative square-endpoint backlog is therefore exactly

\[
E_R=\pi(R^2)-\lfloor Li_2(R^2)\rfloor.
\]

## Scope and exactness

The primitive stream was evaluated at every integer site from \(56^2+1\) through \(3162^2=9,998,244\), i.e. **9,995,108 sites**.  Five Li values within \(2\times10^{-7}\) of an integer were re-evaluated at 80 decimal digits before flooring; none changed floor.  The largest double-vs-high-precision Li difference among those checks was \(2.91\times10^{-10}\).

Two exact consistency checks passed:

- the primitive cumulative sum reproduces \(\pi(n)-\lfloor Li_2(n)\rfloor\);
- every square-block sum of \(\xi_n\) reproduces \(P_R-F_R\).

A literal 4,611-path NNS matrix on all 9,995,108 primitive sites would contain about 46 billion values.  The full NNS stress suite is therefore run on the **exact square-block sums** \(P_R-F_R\), which are the square-endpoint carrier used by the Lean theorem.  The primitive lattice itself is still computed exhaustively, not sampled.

## Primitive {-1,0,1} findings

Over the full lattice:

- \(\xi=-1\): **619,749**
- \(\xi=0\): **8,755,928**
- \(\xi=+1\): **619,431**
- nonzero fraction: **0.1239786504**
- lattice lag-1 correlation: **-0.0719121087**
- lattice lag-2 correlation: **-0.0242410485**
- mismatch-event-time lag-1 correlation after deleting zeros: **-0.3667695403**
- maximum consecutive +1 run: **1**
- maximum consecutive -1 run: **1**
- backlog range: **[-345,-9]**
- final backlog: **-331**

The observed absence of same-sign adjacent primitive mismatches is not used as a theorem here, but it suggests an elementary formal target: for sufficiently large \(n\), consecutive primes are impossible and two consecutive floor-Li jumps are impossible once \(Li(n+1)-Li(n-1)<1\).

## Square-block actual path

For \(56\le R<3162\):

- standardized block lag-1: **-0.1408353596**
- standardized block lag-2: **-0.0940938748**
- raw integer block-error lag-1: **-0.1368745970**
- raw integer block-error lag-2: **-0.0776266342**
- \(\max_{R\ge1000}|E_R|/(R\log R)\): **0.01999057423**
- final ratio at \(R=3162\): **0.01298934126**
- variance diagnostic \(K_{req}\): **0.00576425184**

The block error \(P_R-F_R\) is exactly integer-valued; its observed range is **[-47,42]**.

## Full NNS.meboot suite

The experiment uses the same design as the earlier VF suite:

1. Pearson and Spearman dependence-to-actual sweeps for
   \(\rho\in\{-0.95,-0.75,-0.50,-0.25,0,0.25,0.50,0.75,0.95\}\),
   199 replicates each: **3,582 paths**.
2. Serial-persistence stress using AR(1) rank templates
   \(\phi\in\{-0.90,-0.50,0,0.50,0.90,0.97,0.99\}\),
   three templates per \(\phi\), 49 NNS replicates each: **1,029 paths**.

Total: **4,611 NNS paths**.  A companion calculation rounds each synthetic block error to the nearest integer and clips only impossible implied block prime counts, so both continuous-bootstrap and integerized results are recorded.

### Continuous NNS reconstruction

- main-sweep 99th percentile RH ratio: **0.1877290551**
- main-sweep maximum: **0.2235263692**
- serial-stress 99th percentile RH ratio: **0.4033255305**
- serial-stress maximum: **0.4803810491**
- serial-stress 99th percentile \(K_{req}\): **0.8546456721**
- serial-stress maximum \(K_{req}\): **1.0568193833**
- fraction of serial paths with \(K_{req}\le1\): **99.5141%**
- every one of the 4,611 paths has \(\max_{R\ge1000}|E_R|/(R\log R)<1\).

### Integerized companion

- main-sweep 99th percentile RH ratio: **0.1885396579**
- main-sweep maximum: **0.2239191691**
- serial-stress 99th percentile RH ratio: **0.4021916308**
- serial-stress maximum: **0.4795642966**
- serial-stress 99th percentile \(K_{req}\): **0.8485645241**
- serial-stress maximum \(K_{req}\): **1.0640015079**
- fraction of serial paths with \(K_{req}\le1\): **99.5141%**
- every one of the 4,611 integerized paths also remains below ratio 1.

Across all 4,611 integerized paths, 445 individual block values required physical clipping after rounding; at the strongest \(\phi=0.99\) stress there were **zero** clips.

At \(\phi=0.99\), realized lag-1 correlation reaches **0.9714128** (median **0.9296280**), while the RH-normalized maximum has median **0.2507266**, 95th percentile **0.4019924**, and maximum **0.4803810**.  The integerized companion is nearly identical.

## NNS implementation validation

The run is matched to `OVVO-Financial/NNS-python` commit
`55d15c9d6412a68942af467e9129551f4801f325`, `src/nns/meboot.py`.

Because the execution container did not have the package installed and has no package-network access, the run used the source-matched Python implementation of the NNS.meboot code path for Pearson/Spearman targeting.  Before accepting the new results, that runner was validated by reproducing the previously committed VF suite:

- old main q99: **0.1842732885**, max **0.2165516598**
- old serial q99: **0.3997581202**, max **0.4777508947**
- old serial \(K\) q99: **0.8497143382**, max **1.0786950871**
- old \(\phi=0.99\) lag-1 median/max: **0.9255964632 / 0.9699422675**

These match the existing committed VF results to displayed precision.

## Interpretation

This is diagnostic, not an asymptotic proof.  It does show that integerizing Li does not create a fragile tracking problem.  The actual floor-Li mismatch carrier is negatively correlated at lag 1, while manufactured paths with realized lag-1 correlation above 0.97 still remain far inside the finite \(R\log R\) envelope.

The theorem-discovery target is therefore sharper than “prove primes are random”: control the positive coherent accumulation of the **integer backlog**

\[
\sum_{r=A}^{B-1}(P_r-F_r),
\]

or equivalently the chronological owner census minus floor-Li integer demand.  The deterministic floor-Li-to-VF correction is only root scale and is formalized separately in `research/VF_MID_FLOOR_LI_DISCRETE_BACKLOG.lean`.

## Reproduction

Install NNS-Python at the source commit above plus NumPy, SciPy, pandas and matplotlib, then run:

```bash
python numerics/floor_li_discrete_meboot/run_floor_li_discrete_meboot.py \
  --out numerics/floor_li_discrete_meboot/results
```

The script uses fixed seeds and regenerates the CSV/JSON/PNG outputs.  `results_sha256.txt` records the hashes from the run summarized here.

The strict repository workflow kernel-checks `VF_MID_FLOOR_LI_DISCRETE_BACKLOG.lean` after its owner dependencies.

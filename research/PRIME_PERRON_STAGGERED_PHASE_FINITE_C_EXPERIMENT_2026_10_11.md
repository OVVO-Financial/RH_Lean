# Prime-frequency staggering, square-endpoint CRT selection, and finite-C amplification

> **Repository preservation (2026-10-11).** This is the full experiment report from the conversation. The original source archive `prime_phase_experiment.zip` and its binary plots/complete CSVs were produced as conversation artifacts. Reproducible source and a script-based artifact generation route are recorded under [`experiments/prime_phase_finite_c/`](../experiments/prime_phase_finite_c/). Figures/CSVs are generated outputs unless explicitly tracked in Git. Results are finite and do not prove finite C or A.


**Date:** 2026-10-11  
**Reproducibility:** All original scripts, CSVs, JSON results, and figures included in `prime_phase_experiment.zip`.  
**Proof status:** Exact finite CRT maxima, exact local Euler distributions, exact 44,100-phase Fourier/Gram decompositions, and exact Möbius censuses are established within their stated finite scope. The 1,500,000-sample CRT tail estimates are sampled, not exhaustive. No finite-C / finite-A theorem or RH result is asserted.

## 1. Hypotheses and three genuinely different objects

The supplied R script defines a *schematic, staggered* additive prime-wave field,

\[
Y(t)=\sum_{\substack{p\le29\\p\le t}}\sin(2\pi t/p),
\]

where each term starts at zero at `t=p` and oscillates with period `p`. For all **integer** endpoint samples `n>=29`, all ten waves are active and the `p=2` term vanishes identically. The prime frequencies are additive rational `1/p`; they are **not** the logarithmic `log p` frequencies from Perron's inversion.

The actual multiplicative Euler field for finite prime set `P` is

\[
F_P(n)=\prod_{p\in P}(1-2\mathbf1_{p\mid n}+\mathbf1_{p^2\mid n}),
\]

which tracks distinct-factor parity and square-factor elimination. It equals `mu(n)` only once all relevant prime factors of `n` are included.

The actual finite-C target is instead the complete historical Mertens **prefix**,

\[
Q_R=2M(R-1)-M(R^2-1),\quad
K_R=\max_{0\le y<R}\frac{(M(y)-1)^2}{y+1},\quad
C_R=\frac{|Q_R|}{R\sqrt{K_R}}.
\]

It is essential **not** to substitute `Y(R²-1)` or `F_P(R²-1)` for `M(R²-1)`.

## 2. Experiment A — exact prime-sine CRT extremes

Primes: `2,3,5,7,11,13,17,19,23,29`. Their complete joint integer period is

\[
L=\prod_{p\le29}p=6,469,693,230.
\]

For ordinary integer `n`, CRT allows all residues `n mod p` independently. For square-root endpoint `n=R²-1`, CRT independently allows root residues `R mod p`, but each individual wave is constrained by the quadratic residue map `R²-1 mod p`. Therefore the maxima and minima **over the complete period** can be computed exactly as sums of individual local extrema, without enumerating `L` values.

| Exact attainable extremum | Ordinary n mod L | n=R²-1 for R mod L |
|---|---:|---:|
| Maximum | +8.763061 | +6.622020 |
| Minimum | -8.763061 | -8.451179 |
| Maximum absolute magnitude | 8.763061 | 8.451179 |

**Square roots reduce the possible positive maximum by 24.43%, but reduce the worst absolute maximum by only 3.56%.** The one-sided/absolute distinction must not be conflated.

In particular, `R²-1` modulo `3` or `5` forces the corresponding sine component to be **nonpositive**: squares modulo 3 are 0,1; squares modulo 5 are 0,1,4. Thus simultaneous positivity of all nine odd-prime waves is impossible at square endpoints. By contrast, the ordinary-CRT probability of all nine being positive at an integer endpoint sampled uniformly modulo `L` is **exactly 0.000616981340242** (0.061698%, approximately 1 in 1,621).

This is a deterministic modular/combinatorial result, not an independence hypothesis on the Möbius function. Uniform sampling of the *root residue* is the explicit finite probability measure.

A full exact enumeration of the **30,030** root residues for the smaller set `p<=13` validates the local-extremum/CRT method: its attainable square-root maximum is `2.764361798447`, its minimum `-4.523751087114`, both realized in the enumeration.

### Tail-frequency CRT sampling

Using 1,500,000 independent uniform joint CRT phase samples (fixed seed `20261011`), equivalent to sampling uniformly over the respective integer/root congruence periods:

| Measure | Ordinary integer phase | Square-root phase |
|---|---:|---:|
| Mean | ~0 | -0.06384 (exact -0.06335) |
| Standard deviation | 2.12229 (exact 2.12132) | 1.90179 (exact 1.90113) |
| Fraction with \(|Y|\ge3\) | 16.0473% | 11.6103% |
| Fraction with \(|Y|\ge4\) | 5.8397% | 3.3512% |
| Fraction with \(|Y|\ge5\) | 1.6355% | 0.6569% |
| All nine odd-prime waves positive | 943/1,500,000 | impossible: 0 |

The sampled `|Y|>=5` tail is **59.8% less frequent** at square phases. These sampled frequencies are not worst-case bounds. The exact extreme is still as negative as `-8.451`.

**Plots:** `phase_distributions.png`, `exact_crt_phase_extremes.png`. Numerical local phase factors: `phase_prime_local_stats.csv`.

## 3. Experiment B — the exact multiplicative Euler phase map

For the same ten primes, calculate the sign, zero, and squared-support probabilities of

\[
F_P(n)=\prod_{p\le29}\Bigl(1-2\mathbf1_{p\mid n}+\mathbf1_{p^2\mid n}\Bigr)
\]

under two *specified* complete CRT sampling measures: uniform `n mod product(p²)`, and uniform root `R mod product(p²)` with `n=R²-1`. Distinct prime coordinates are independent under the *uniform CRT residue ensemble*; this does **not** say consecutive physical endpoints are independent.

For **odd** `p`, the **square-root sample** has

\[
\begin{aligned}
\mathbb P(p\mid R^2-1)&=2/p,\\
\mathbb P(p^2\mid R^2-1)&=2/p^2,\\
\mathbb E[g_p(R^2-1)]&=1-4/p+2/p^2,\\
\mathbb E[g_p(R^2-1)^2]&=1-2/p^2.
\end{aligned}
\]

At `p=2` the square-root law is special: `g_2(R²-1)=0` for odd `R`, `+1` for even `R`, so both mean and nonzero support are `1/2`.

For uniform ordinary integers, the local Euler mean and squared support are `(1-1/p)²` and `1-1/p²` respectively. Multiply local means and supports; recover `P(+1)=(E[F²]+E[F])/2`, `P(-1)=(E[F²]-E[F])/2`, and `P(0)=1-E[F²]`.

| Exact CRT state population for P = primes <=29 | Ordinary | Square-root |
|---|---:|---:|
| Positive | 31.8645% | 16.2931% |
| Negative | 29.3698% | 16.4408% |
| Zero | 38.7657% | **67.2660%** |
| Nonzero squarefree support | 61.2343% | **32.7340%** |

Thus the original phase restriction **does survive in the exact local Euler field**: square endpoints are strongly biased toward prime-square kills. This is an exact finite-wheel fact and must not be confused with a result about the **summatory** Möbius function `M(R²-1)`.

**Plot:** `euler_factor_distribution.png`.

## 4. Experiment C — actual Euler Fourier conductor energy on the complete period

Primes `2,3,5,7` yield full square-sensitive Euler period `L=(2*3*5*7)²=44,100`. Exhaustively enumerate all `L` phases. Compute the exact mean `mean(F_P)=product(1-1/p)²` and centered prefix

\[
B_P(X)=\sum_{1\le n\le X}(F_P(n)-\mathbb E[F_P]).
\]

Use FFT to partition `B_P(X)` into its **80 nonzero reduced additive conductor shells** `H_q(X)`. The reconstruction identity

\[
B_P(X)=\sum_{q>1} H_q(X)
\]

was checked at **every** endpoint residue with maximal floating residual **1.1e-12**. Retain the signed Gram identity

\[
B_P(X)^2=\sum_q H_q(X)^2+2\sum_{q<q'}H_q(X)H_{q'}(X).
\]

The exact mean energies over all 44,100 ordinary/square-root phases are:

| Complete finite-wheel quantity | Uniform ordinary endpoints | Square-root endpoints |
|---|---:|---:|
| Conductor diagonal energy | 21.135651 | 20.533960 |
| Signed conductor cross-energy | **-4.881228** | **-4.724690** |
| Total centered prefix energy | **16.254423** | **15.809270** |
| Maximum absolute centered prefix | 11.777959 | 10.496327 |
| 95th percentile absolute prefix | 7.658000 | 7.742857 |

**Interpretation:** the true multiplicative Fourier field retains substantial **negative** cross-conductor cancellation (~23% of diagonal) for both endpoint ensembles. However, the mean signed prefix energy decreases only **2.74%** under square sampling, despite the much larger change in local Euler zeros. Some near-tail quantiles even increase. Thus a striking local phase restriction need not translate into a strong improvement for cumulative energy.

**Plots:** `euler_fourier_signed_gram.png`, `exact_euler_prefix_deviation.png`. Reproduce with `python euler_fourier_conductor_audit.py`.

## 5. Experiment D — actual Perron log-prime waves

To avoid identifying additive `1/p` frequencies with Perron's logarithmic frequencies, independently study the fixed ten-mode critical-line toy

\[
Z(\tau)=\sum_{p\le29}\frac1p e^{-2i\tau\log p}.
\]

Its phase-averaged squared magnitude has an exact elementary formula

\[
\frac1T\int_0^T|Z(\tau)|^2d\tau
=\sum_{p\le29}\frac1{p^2}
+2\sum_{p<q\le29}\frac1{pq}
\frac{\sin(2T\log(q/p))}{2T\log(q/p)}.
\]

The diagonal is **0.4450106075**, while perfectly aligned energy at `tau=0` is **2.3514344671**. Exact finite-height averages:

| Height window T | Exact average \(|Z|^2\) |
|---:|---:|
| 1 | 1.237956 |
| 10 | 0.466594 |
| 100 | 0.444339 |
| 1,000 | 0.444907 |
| 10,000 | 0.444965 |
| 100,000 | 0.445016 |

The height-average dephasing is real and explicit. But at `tau=0` all modes align, and the calculation uses **unit toy coefficients** rather than the physical Perron cofactor weights and the true inversion kernel. Consequently it does not directly control a *pointwise* physical square-endpoint sum.

**Plot:** `perron_exact_mean_energy.png`.

## 6. Experiment E — true Möbius finite-C / finite-A scan

An independently compiled C++ Mobius sieve computed **every actual** `M(R²-1)` and `M(R-1)` for `2<=R<=6000` (all integers through **35,999,999**). The exact historical envelope `K_R` and the original normalized ratios `C_R`, `A_R` were calculated for each root. This is an arithmetic census, not a sampling model.

Selected checks:

| R | M(R²-1) | M(R-1) | Q_R | C_R |
|---:|---:|---:|---:|---:|
| 56 | +6 | -2 | -10 | 0.145803 |
| 317 | -28 | -3 | +22 | 0.056665 |
| 1,000 | +212 | +2 | -208 | 0.169831 |
| 5,561 | -2,544 | +5 | +2,554 | **0.374992** |
| 6,000 | +2,256 | 0 | -2,256 | 0.307003 |

For `31<=R<=6000`, **Pearson correlations** between schematic/small-wheel measurements and the actual amplification:

| Probe | Correlation with C_R |
|---|---:|
| Fixed-ten sine amplitude `abs(Y(R²-1))` | **-0.02393** |
| Four-prime centered Euler prefix amplitude `abs(B_P(R²-1))` | **+0.01126** |
| Growing sine modes all primes `p<=R`: `abs(Y_growing(R))` | **-0.00038** |
| Growing sine modes normalized by `sqrt(pi(R))` | **-0.01485** |
| Growing sine modes with amplitudes `1/p` | **-0.02000** |

The actual **largest observed C_R among roots 31..6000** is `0.374992` at `R=5561`. Over **all** roots 2..6000, `C_2=1.5` already requires a larger universal constant; no finite scan can establish such a universal bound.

**Conclusion of this direct test:** neither the schematic fixed-prime superposition nor the tested growing-prime sine models predict genuine Mertens amplification in this finite range. The finite Fourier Euler prefix with only four primes is likewise not predictive. This does **not** refute a more complete arithmetic Perron/cofactor spectral bound; it shows exactly which simplified surrogates are inadequate.

**Plots:** `sine_vs_finite_C.png`, `growing_sine_vs_finite_C.png`, `actual_C_by_root.png`. Data: `actual_root_scan.csv`, `growing_prime_wave_scan.csv`.

## 7. Where this leaves finite C and the next experiment

The original target remains

\[
\boxed{\exists C<\infty\quad\forall R\ge2:\quad
|2M(R-1)-M(R^2-1)|\le CR\sqrt{K_R}.}
\]

**Supported by experiment:** (i) square endpoint CRT arithmetic eliminates entire prime-phase alignment configurations; (ii) the exact multiplicative Euler field has dramatically different square-endpoint sign/zero densities; (iii) actual Fourier conductor energies retain large signed cross interactions; (iv) fixed-mode Perron energy disperses over long height windows.

**Not supported by experiment:** a direct relation between the toy aligned sine amplitude and the actual finite-C amplification, or a claim that the square restriction alone uniformly contracts the centered multiplicative prefix energy. The latter showed a small 2.74% average energy reduction in the exhaustive `p<=7` wheel.

**Most useful next attack:** apply **the genuine finite-C signed physical coefficients** to the square-clock reduced-conductor spectral response. Retain the zero-mode, nonzero modes, and their mixed cross-energy; use the historical `K_R` from the actual Mertens prefix. Do not replace this operator with `sum sin(2pi x/p)` or discard rare coherent phases because they are small in an averaged ensemble. Test the actual expansion on increasingly large prime supports and compare direct signed boundary energies to `Q_R²/(R²K_R)`.

### Reproduction

Run from the directory containing these scripts:

```bash
g++ -O3 -std=c++17 mobius_root_census.cpp -o mobius_root_census
./mobius_root_census 6000 actual_root_scan.csv
python prime_phase_experiment.py
python euler_fourier_conductor_audit.py
python growing_prime_wave_audit.py
```

Python dependencies: NumPy, SciPy (correlations), Matplotlib. The C++ program uses only the standard library. Seed for CRT Monte Carlo is `20261011`; the 30,030-point and 44,100-point enumerations are exhaustive. All numeric results are exported in `results.json`, `fourier_conductor_results.json`, and `growing_prime_wave_results.json`.

**Repository theorem touchpoints:** `RHLean/Analysis/SquareWheelQuadraticSampling.lean`, `RHLean/Analysis/PrimeWheelConductorGram.lean`, `research/STOKES_ENDPOINT_MAX_ALIGNMENT.lean`, and `research/STABLE_FAR_PERRON_REAL_GRAM_COSINE.lean`. This experiment does not claim newly compiled Lean theorems or a proof of RH.
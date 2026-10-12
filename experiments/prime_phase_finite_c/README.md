# Staggered prime-period alignment vs finite-C: reproducible experiment

**Date:** 2026-10-11. **Proof status:** finite CRT results, fixed-seed CRT sampling, Fourier numerics and genuine Mobius census. **No finite universal C/A or proof of RH.**

**[Full mathematical report](../../research/PRIME_PERRON_STAGGERED_PHASE_FINITE_C_EXPERIMENT_2026_10_11.md)** | [Standalone finite-C/A research note](../../research/SEQUENTIAL_EULER_SQUARE_BLOCK_FINITE_C_A_RESEARCH_NOTE.md)

## Four genuinely different objects

1. **Original user visualization:** Staggered additive prime-period waves, \(Y(t)=\sum_{p\le t,\ p\le29}\sin(2\pi t/p)\). The reciprocal primes are frequencies; amplitudes are 1. At integer sample times beyond 29, all ten waves are active.
2. **Actual multiplicative Euler field:** \(F_P(n)=\prod_{p\in P}(1-2\,\mathbf1_{p\mid n}+\mathbf1_{p^2\mid n})\), including sign parity and square-factor zeros.
3. **Perron log-frequency toy:** \(Z(\tau)=\sum_{p\le29}p^{-1}e^{-2i\tau\log p}\). Here reciprocals are amplitudes; this is not the physical inversion of the finite-C kernel.
4. **Actual finite-C target:** \(Q_R=2M(R-1)-M(R^2-1)\), \(K_R=\max_{0\le y<R}(M(y)-1)^2/(y+1)\), \(C_R=|Q_R|/(R\sqrt{K_R})\).

## Key results

| Experiment | Ordinary phases | Square phases \(R^2-1\) | Scope |
|---|---:|---:|---|
| Maximum positive ten-prime sine sum | +8.763061 | +6.622020 | Exact CRT-compatible extremes |
| Maximum absolute ten-prime sine sum | 8.763061 | 8.451179 | Exact CRT-compatible extremes |
| Tail probability \(|Y|\ge5\) | 1.6355% | 0.6569% | 1,500,000 fixed-seed CRT samples |
| Finite Euler-wheel zero proportion | 38.7657% | 67.2660% | Exact prime-square CRT ensemble |
| Four-prime centered-prefix mean energy | 16.254423 | 15.809270 | Exhaustive 44,100 phases; FFT numerics |
| Four-prime signed cross-conductor energy | -4.881228 | -4.724690 | Exhaustive 44,100 phases; FFT numerics |

For the ten-prime fixed Perron-height toy, the exact mean-square diagonal is 0.4450106075, height-zero coherent energy is 2.3514344671, and mean energy on the height interval \(0\le\tau\le1000\) is 0.444907.

The genuine Mobius census over **all roots \(R=2,\ldots,6000\)** independently computed exact \(M(R^2-1)\), \(K_R\), \(Q_R\), \(C_R\), and \(A_R\). For roots 31 through 6000, Pearson correlations with \(C_R\) were:

| Simplified wave probe | Pearson correlation |
|---|---:|
| Fixed-ten sine magnitude | -0.02393 |
| Four-prime Euler centered-prefix magnitude | +0.01126 |
| Growing all \(p\le R\) sine magnitude | -0.00038 |
| Growing sine divided by square root of prime count | -0.01485 |
| Growing \(1/p\)-weighted sine magnitude | -0.02000 |

**Negative finding:** although squared endpoints rule out some exact alignments and drastically increase local Euler zeros, none of these toy-wave amplitudes predicts finite-C amplification in the scanned range. Square sampling improves mean four-prime *prefix* energy by only 2.74%. Do not promote mean energy to worst-case pointwise control.

## Source files

- [Original staggered R plot](original_staggered_waves.R): user's exact concept and visualization.
- [C++ Mobius census](mobius_root_census.cpp): historical \(K_R\), actual \(C_R\), \(A_R\), and square endpoints.
- [CRT/Euler/Perron Python driver](prime_phase_experiment.py): fixed-seed 1.5 million phase draws, exact per-prime CRT extrema and Euler probabilities, centered-prefix plots, Perron-height toy, actual Mobius comparisons.
- [Full conductor FFT audit](euler_fourier_conductor_audit.py): exact 44,100-residue scan and retained signed Gram cross-interactions.
- [Growing-prime-wave audit](growing_prime_wave_audit.py): inclusion of all primes \(p\le R\), with normalization and reciprocal weights.
- [Compact benchmark ledger](EXPERIMENT_RESULTS.json): baseline numerical outcomes for CI and independent review.
- GitHub Actions workflow: .github/workflows/prime-phase-finite-c.yml. It regenerates all CSV, JSON, and PNG files as a downloadable **Actions artifact** on demand or on changes to these experiment sources.

Python dependencies: NumPy, SciPy and Matplotlib. C++17 compiler required.

From the repository root:

~~~bash
cd experiments/prime_phase_finite_c
g++ -O3 -std=c++17 mobius_root_census.cpp -o mobius_root_census
./mobius_root_census 6000 actual_root_scan.csv
python3 prime_phase_experiment.py
python3 euler_fourier_conductor_audit.py
python3 growing_prime_wave_audit.py
~~~

Generated plots: phase_distributions.png, exact_crt_phase_extremes.png, euler_factor_distribution.png, exact_euler_prefix_deviation.png, euler_fourier_signed_gram.png, perron_exact_mean_energy.png, sine_vs_finite_C.png, growing_sine_vs_finite_C.png, actual_C_by_root.png.

Generated data: actual_root_scan.csv, growing_prime_wave_scan.csv, phase_prime_local_stats.csv, results.json, fourier_conductor_results.json, growing_prime_wave_results.json.

**Archive status:** The original conversation supplied a 2.2 MB package prime_phase_experiment.zip containing the exact output binaries. This repository preserves the report, source, numerical benchmarks, and regeneration workflow; the binary PNG/CSV outputs are generated artifacts, not Git-tracked files. Run the GitHub workflow to obtain them within GitHub. Do not describe those binary files as committed.

## Finite-C connection and next step

\[
\exists C<\infty\ \forall R\ge2:\quad
\left|\sum_{a,b<R}\mu(a)\mu(b)\lfloor(R^2-1)/(ab)\rfloor\right|
\le CR\sqrt{K_R}
\]
is the unchanged open theorem. The fixed finite-C implication to finite A and RH is conditional and formalized elsewhere in RH_Lean.

The non-circular task is to quantitatively control the **physical signed square-wheel/Perron response** with the genuine Mobius/cofactor coefficients and all mixed modes retained. Fixed-ten additive waves and unweighted phase averages are not substitutes.

Related formal modules: RHLean/Analysis/SquareWheelQuadraticSampling.lean; RHLean/Analysis/PrimeWheelConductorGram.lean; research/STOKES_ENDPOINT_MAX_ALIGNMENT.lean; research/STABLE_FAR_PERRON_REAL_GRAM_COSINE.lean.

# Sequential low-prime dissipation diagnostics

**Status:** finite diagnostic only.  Nothing in this note is used as evidence for an asymptotic estimate, and none of the numerical observations below has theorem status.

This note records the finite experiment that motivated the current final analytic target for `LowPrimeProcessedResponse`.

## 1. Exact formal object being scanned

Let

\[
X_R=R^2-1,
\qquad
P_R=R-\lfloor\sqrt R\rfloor.
\]

`RHLean.Proof.LowPrimeFreshLayerBridge` defines the running processed response

\[
S_R(p)=\operatorname{squareRootBornPostTailRunningLowPrimeResponse}(R,K,j,p),
\]

obtained by replacing the final largest-prime-factor cutoff `P_R` in `LowPrimeProcessedResponse` by a running cutoff `p`.

At the terminal cutoff the formal theorem

` squareRootBornPostTailRunningLowPrimeResponse_at_cutoff `

identifies

\[
S_R(P_R)=\operatorname{LowPrimeProcessedResponse}(R,K,j).
\]

At a prime `p`, the fresh-step theorem

` squareRootBornPostTailRunningLowPrimeResponse_step_eq_freshBooleanFaceLayer `

identifies

\[
S_R(p)-S_R(p-1)
\]

with the exact Boolean faces whose canonical largest prime factor is `p`.

The numerical scanner below evaluates this literal finite state.  It is not a surrogate Mertens sum and does not substitute `M(R^2-1)` into the trajectory.

Define

\[
T_R(p)=1-S_R(p),
\qquad
\Delta_p=S_R(p)-S_R(p^-),
\]

where `p^-` means the state immediately before the fresh prime is inserted.  Then

\[
T_R(p)=T_R(p^-)-\Delta_p
\]

and the exact energy increment is

\[
\boxed{
T_R(p)^2-T_R(p^-)^2
=-2T_R(p^-)\Delta_p+\Delta_p^2.
}
\]

Thus a prime step contracts the squared imbalance precisely when

\[
2T_R(p^-)\Delta_p>\Delta_p^2.
\]

No probabilistic interpretation is imposed on this identity.

## 2. Finite scan

The scan was run at the nineteen endpoints

\[
R\in\{200,300,400,500,600,800,1000,1200,1500,2000,2500,3000,
4000,5000,6000,7000,8000,9000,10000\}.
\]

For each endpoint the scanner computes exactly:

* the Möbius function and canonical largest prime factor through `X_R`;
* the shallow reciprocal crossing `(K,j,V)`;
* the born-partner response from the same cofactor sum used by Lean;
* the post-crossing high response from the same cofactor sum used by Lean;
* the contribution bucket indexed by `P^+(c)`;
* the running state `S_R(p)`, imbalance `T_R(p)`, and energy change at every prime `p<=P_R`.

The exact C++ reproducer is `research/sequential_lpr_test.cpp`.  The full nineteen-endpoint post-crossing summary is `research/sequential_lpr_deep_metrics.csv`.

## 3. Shallow creation followed by deep dissipation

The dominant finite pattern is not global monotonicity.  The shallow primes first create a large coherent excursion, and the later primes overwhelmingly remove it.

Selected rows from the full table are:

| `R` | `K` | shallow energy growth | deep contracting steps | deep final/start energy | `|T(P_R)|/R` |
|---:|---:|---:|---:|---:|---:|
| 500 | 30 | 5.8737 | 97.53% | 7.906e-3 | 0.4060 |
| 1000 | 31 | 7.9395 | 98.68% | 2.696e-6 | 0.0150 |
| 2000 | 33 | 11.2412 | 100.00% | 9.076e-5 | 0.1770 |
| 5000 | 37 | 13.8929 | 99.69% | 5.944e-6 | 0.0980 |
| 10000 | 43 | 16.8384 | 99.42% | 3.475e-10 | 0.0013 |

Across all nineteen tested endpoints,

\[
\max_R \frac{|T_R(P_R)|}{R}
=0.488333\ldots,
\]

attained at `R=600` in this grid.

For `R>=1000`, the largest observed ratio

\[
\frac{T_R(P_R)^2}{T_R(K)^2}
\]

in the table is approximately

\[
1.2105\times10^{-3},
\]

at `R=1200`.

These are finite observations only.  They do not imply a uniform bound.

## 4. The `R=10000` trajectory

At

\[
R=10000,
\qquad
X_R=99,999,999,
\qquad
P_R=9900,
\qquad
K=43,
\]

the shallow phase reaches

\[
T_R(K)^2=486,389,077,056.
\]

After the remaining prime steps through `P_R`,

\[
T_R(P_R)=-13,
\qquad
T_R(P_R)^2=169.
\]

Hence the observed post-`K` energy ratio is

\[
\frac{169}{486,389,077,056}
\approx3.4746\times10^{-10}.
\]

There are `1206` prime steps after the shallow crossing.  Of these,

\[
1199\text{ contract},
\qquad
7\text{ expand},
\]

so the observed deep contraction fraction is

\[
0.994195688\ldots.
\]

The total wrong-direction deep increment mass is

\[
106=0.0106R,
\]

while the right-direction deep increment mass is `697509`.  Their ratio is

\[
1.51969\times10^{-4}.
\]

The largest deep single-prime increment in absolute value is

\[
10753=1.0753R.
\]

The total expanding deep energy is only

\[
1.32354\times10^{-4}
\]

times the total contracting deep energy.

The full prime chronology, including the shallow excursion, has maximum

\[
|T|=714223
\]

at `p=37`, immediately before the crossing scale `K=43`.

## 5. Born/high cancellation inside the prime step

The response bucket was also split into its two exact components:

\[
\Delta_p
=
\Delta_p^{\rm born}
+
\Delta_p^{\rm high}.
\]

For the explicitly split endpoints, the fraction of component `L^1` mass removed internally by this recombination was:

| `R` | internal born/high cancellation |
|---:|---:|
| 1000 | 0.73096148 |
| 2000 | 0.70632356 |
| 5000 | 0.69763361 |
| 10000 | 0.70207777 |

Thus about seventy percent of the separate born/high component mass disappears before the fresh-prime increment is even compared with the running imbalance.

This is the main reason the final analytic claim should keep the born and high channels signed together.  Bounding those channels separately would deliberately discard the observed mechanism.

## 6. What these numerics do and do not suggest

The finite data support the following *research target*:

\[
\boxed{
\text{shallow coherent creation}
\quad\longrightarrow\quad
\text{deep sequential dissipation modulo a small frontier}.
}
\]

They do **not** support the stronger false statement that every fresh prime contracts.  Some expanding steps occur, and at several endpoints they are nonzero in number.

The formal work following the scan has already sharpened the geometry:

1. the fresh numerical step is the kernel-checked largest-prime Boolean layer;
2. restoring the matching old parent gives an exact parent/child finite difference;
3. the high channel splits into fully shallow, shallow-to-deep transition, and deep reciprocal-window cases;
4. the born and high channels must be kept together through that transition;
5. the transition shell has an exact first-failure representation rather than an independent error per prime.

Accordingly the analytic endgame is not to prove a heuristic negative correlation.  It is to prove, from the exact prime-step geometry, a signed decomposition whose interior is dissipative and whose exceptional first-failure frontier has globally controlled mass.

A representative target shape is

\[
\Delta_p^{\rm born}+\Delta_p^{\rm high}
=-D_p+F_p,
\qquad D_p\ge0,
\]

with the frontier `F_p` assigned canonically so that its total contribution is controlled without paying once for every prime.

Only a theorem of that type would turn the finite dissipation pattern into the required quantitative argument.

## 7. Reproduction

Compile with, for example,

```bash
c++ -O3 -std=c++17 research/sequential_lpr_test.cpp -o /tmp/sequential_lpr_test
```

and run

```bash
/tmp/sequential_lpr_test \
  200 300 400 500 600 800 1000 1200 1500 2000 \
  2500 3000 4000 5000 6000 7000 8000 9000 10000
```

The program writes the aggregate scan to standard output and one prime-by-prime trajectory per endpoint in the current working directory.

The committed CSV tables are frozen outputs from this finite diagnostic and should be treated exactly like the other files under `research/`: motivation and falsification data, not mathematical proof.

# Prime-conditioned moving-lag dependence versus near-zero block correlations

**October 11, 2026.** Audit of existing RH_Lean research plus a freshly rerun true-Mobius square-block correlation experiment. Exact signed prime-factor relationships are universal. Neither finite A/C nor RH is claimed.

## Earlier correlation experiments were real but tested different objects

For square block \(I_r=[r^2,(r+1)^2)\), define the actual signed block increment \(B_r=\sum_{n\in I_r}\mu(n)\), squarefree diagonal \(d_r=\sum_{n\in I_r}\mu(n)^2\), and standardized block \(z_r=B_r/\sqrt{d_r}\).

An independent genuine Mobius sieve through 99,999,999 reproduces the **previous** 8,999-block scan, r=1000..9998:
- normalized mean 0.0013560504 and standard deviation 0.99367845;
- lag-1 Pearson -0.0049075226, lag-2 Pearson +0.0051503624;
- lag-1 **Spearman** -0.0001404164, lag-2 Spearman +0.0059746908;
- lag-1 **Kendall** -0.0001019601.

These near-zero rank/linear correlations at fixed lags DO NOT mean prime-factor independence. They reflect aggregation over many distinct, age-dependent physical factor families.

Separately, the TWOAB_SCALE_TRANSFER research note reported corr(A,T)=0.999949 and a signed residual energy ratio 1.7730e-5 through R=10,000; random-sign controls at R=3,000 yielded mean energy ratio 0.7547 versus the actual 1.0573e-4. This tests signed smooth/transport alignment, not adjacent square-block independence.

The VF_MID_MEBOOT_MONTE_CARLO note tested 4,611 Pearson/Spearman-targeted or serial-correlated maximum-entropy bootstrap paths for the **prime-minus-VF block-error** series, including AR(1) phi=0.99. That is a different series and not an NNS.dep or NNS.caus experiment on the true Möbius square-block increments. No direct NNS.dep/NNS.caus test on these actual B_r was found in the repository.

## The complete signed block Gram is far from zero

Over exactly the same r=1000..9998:
\[
\sum B_r=1775,\qquad \sum B_r^2=60468247,\qquad
\sum_{i<j}B_iB_j=-28658811.
\]
Hence
\[
\boxed{1775^2=60468247+2(-28658811)=3150625.}
\]
Although lag-1 Pearson and Spearman are nearly zero, the all-lag, uncentered block interaction cancels 94.7896% of the block squared-energy diagonal. This is an EXACT algebraic reassembly, not an independent analytic proof of a uniform cancellation rate.

## The missing dependence is at multiplicatively moving square-block lags

If p is a genuine prime, m is squarefree, and p does not divide m, then
\[
\boxed{\mu(pm)=-\mu(m),\quad \mu(m)\mu(pm)=-1.}
\]
Birth clock r=floor(sqrt(m)) and descendant clock t=floor(sqrt(pm)) satisfy
\[
\boxed{t-r=(\sqrt p-1)r+O_p(1).}
\]
A fixed lag h cannot see this parent/child coupling at every scale: the relevant lag grows linearly with r.

Define the prime-conditioned *physical signed pair kernel*
\[
\mathcal C_p(r,t)
=\sum_{\substack{r^2\le m<(r+1)^2,\ t^2\le pm<(t+1)^2\\p\nmid m}}
\mu(m)\mu(pm).
\]
Then for every prime p and all r,t, with no stochastic assumptions,
\[
\boxed{\mathcal C_p(r,t)=
-\#\{m\in I_r:\mu(m)\ne0,\ p\nmid m,\ pm\in I_t\}\le0.}
\]

Actual prime-conditioned moving square-block lag counts:

| Parent square root r | p | Child lag t-r: number of links | Total signed links |
|---:|---:|---|---:|
| 317 | 2 | 131:127, 132:131 | -258 |
| 1000 | 2 | 414:448, 415:364 | -812 |
| 6000 | 2 | 2485:2472, 2486:2394 | -4866 |
| 1000 | 3 | 732:497, 733:416 | -913 |
| 6000 | 3 | 4392:2192, 4393:3152, 4394:120 | -5464 |

Every linked pair had exactly the required reversed sign. These direct links are true deterministic, conditional negative interactions, even while the **unconditioned aggregated** fixed-lag Pearson, Spearman and Kendall are near zero.

Do not mistake \(\mathcal C_p(r,t)\) for full aggregate block covariance \(B_rB_t\): that product also counts many other distinct pairs not directly linked by p. Complete Euler prime-family inclusion/exclusion creates further positive and negative faces, especially along truncated square-block boundaries.

## Meaning for the actual finite-A / finite-C problem

Neither near-zero fixed-lag correlation nor the exact negative ridge implies the required **worst-case, occurrence-preserving, all-square-run** signed bound. The object requiring arithmetic control is the signed sum across all genealogical links, nonlinked pairs, cross-family faces and moving boundary truncations, compared to historical \(R^2K_R\).

This is WHY arbitrary/random partitions can erase an observed correlation across deterministic arithmetic: the prime-conditioned relation lives along *moving multiplicative* lag curves, not stationary offsets. The existing modules BlockCovarianceDecomposition.lean, SquareRunEscapeCovariance.lean, and CanonicalGapAncestryBridge.lean already preserve the exact chronological covariance and square-root clocks. A useful theorem must exploit these exact conditional signs without dropping or double counting the remaining faces.

'Ergodicity' requires a specified dynamical system and invariant measure; no ergodicity premise is needed for the exact arithmetic.

Reproducible C++17 experiment:
[prime_dilation_moving_lag_audit.cpp](../experiments/PrimePopulationCutoff/prime_dilation_moving_lag_audit.cpp).
Compilation tested with g++ -O3 -std=c++17 -Wall -Wextra -Werror; sieved up to 108,036,000. No new Lean theorem claimed.

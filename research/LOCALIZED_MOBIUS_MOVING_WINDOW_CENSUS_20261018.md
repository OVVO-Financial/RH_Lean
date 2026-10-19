# RH_Lean localized moving-window experiment — 2026-10-18

**Status:** exact finite computation and independent spot checks; no new all-scale Möbius or RH bound.

## Exact arithmetic carrier

For integers \(H\le r<2H\) and \(|t|\le T\), define \(S_r(t)=\sum_{j=1}^{2r}\mu(r^2+t+j)\), \(\delta_r=S_r(0)\), \(\mathcal E(H)=\sum_r\delta_r^2\), and \(W(H;T)=\sum_r\sum_{t=-T}^T S_r(t)^2\). Both square endpoints are excluded for \(t=0\).

We computed the exact integer values for dyadic H=64,128,...,8192 and T=floor(H^beta), beta=1/2, 2/3, 3/4, 7/8, plus T=H/2 (duplicates omitted). Euler linear Mobius sieve was run to 268,439,568; exact prefix sums were used for all windows. Measured peak resident memory was 2,418,048 KiB (approximately 2.31 GiB), runtime ~22.4 seconds for the full run. The exact integer-valued data are in the [frozen census CSV](../experiments/mobius_moving_windows/data/window_results_H8192.csv); ratios and floating diagnostics are rounded.

## Exact data for T=floor(H^3/4)

| H | T | E(H) | W(H;T) | W/H^(13/4) | W/H^(11/4) | mean-mode % | W/diagonal |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 256 | 64 | 110,216 | 13,947,713 | 0.2078 | 3.3254 | 93.851 | 0.90583 |
| 512 | 107 | 486,935 | 104,762,016 | 0.1641 | 3.7129 | 95.426 | 1.01983 |
| 1024 | 181 | 1,723,387 | 640,384,427 | 0.1054 | 3.3738 | 95.851 | 0.92279 |
| 2048 | 304 | 7,380,415 | 4,507,589,956 | 0.0780 | 3.5301 | 96.530 | 0.96776 |
| 4096 | 512 | 30,291,950 | 30,892,995,718 | 0.0562 | 3.5964 | 97.261 | 0.98509 |
| 8192 | 861 | 126,589,560 | 218,434,508,977 | 0.0418 | 3.7801 | 97.735 | 1.03586 |

The observed values follow approximately H^(11/4) across these finite scales, substantially below the conditional H^(13/4) target. This is consistent with ordinary square-root-sized interval sums; it does **not** establish an asymptotic theorem. For T=floor(H^3/4), there are H(2T+1) windows, and the signed pair covariance equals (W-D)/2 where D is the sum of mu(n)^2 over all windows. Its normalized sign flips: W/D is below 1 at H=4096 and above 1 at H=8192.

## Translation-mode decomposition

Writing \(n_T=2T+1\) and \(\overline S_r=n_T^{-1}\sum_t S_r(t)\), the exact orthogonal decomposition is

\[W(H;T)=n_T\sum_r\overline S_r^2+\sum_{r,t}(S_r(t)-\overline S_r)^2.\]

At H=4096, T=512, the translation-mean fraction is **97.261%**, while the centered/nonconstant component is **2.739%**. The translated mean-square per shell is W/n=30,139,508.0, compared with the original shell energy E=30,291,950; their ratio is 0.99497.
At H=8192, T=861, the translation-mean fraction is **97.735%**, while the centered/nonconstant component is **2.265%**. The translated mean-square per shell is W/n=126,775,687.2, compared with the original shell energy E=126,589,560; their ratio is 1.00147.

The incidence vectors for 2r-length intervals shifted by t=-T,...,T are linearly independent, so the exact Gram-kernel rank on the full union of integer sites is 2T+1, not r/T. For 2T<2r, the translation Gram matrix is G_{tu}=2r-|t-u|. Its constant-translation Rayleigh quotient captures the fraction

\[1-\frac{(2T+1)^2-1}{3(2T+1)(2r)}\]

of the trace, a lower bound for the leading eigenvalue share. For H=8192 the block-aggregated geometric witness is 97.663%, close to the actual translation mean fraction 97.735%. The high matrix rank is therefore overwhelmingly concentrated in an almost rank-one mode at this scale.

## Fixed-squarefree-support randomized control

At H=4096, T=512, 48 independently seeded pseudorandom +/-1 sign assignments were placed on the **same squarefree sites** as genuine Möbius, preserving all mu=0 sites and every window diagonal. Results:

- Genuine Mobius: W/D = 0.985095; mean-mode fraction = 97.2611%.
- Randomized control: W/D mean = 0.992476, sample SD = 0.018706; mean-mode fraction = 97.2155%, sample SD = 0.0805 percentage points.
- Genuine W/D deviation from randomized mean = -0.39 SD. Genuine mean-mode fraction deviation = +0.57 SD.

These finite diagnostics do not show exceptional extra signed cancellation or unusually large nonconstant translation energy. They are not an asymptotic probabilistic argument and do not imply a general arithmetic independence theorem.

## Validity and quantitative sharpness of deterministic bridge

The 2-Lipschitz shift law \(|S_r(t)-\delta_r|\le2|t|\) yields the pointwise sharp **Lipschitz-envelope** inequality \(\delta_r^2\le T^{-1}\sum_{|t|\le T}S_r(t)^2+\tfrac43(T^2-1)\), for every integer T>=1. Summing gives

\[\mathcal E(H)\le\frac{W(H;T)}{T}+\frac43H(T^2-1).\]

Proof note: for a=|delta|, the smallest possible sum of squared translated values under |S_t-delta|<=2|t| is F_T(a)=a²+2*sum_{t=1}^T max(a-2t,0)². The function a²-F_T(a)/T increases up to a=2T and decreases thereafter. At a=2T its exact maximum is (4/3)(T²-1). This is a universal Lipschitz-envelope statement; it does not require adjacent-step Möbius identities. The bound was checked with exact integer arithmetic for every tested r,T, and independently exhaustively for T=1..150 and integer a=0..5T+2.

| H | optimum T for finite bound | best bound / E | bound / E at T=floor(H^3/4) |
|---:|---:|---:|---:|
| 256 | 6 | 2.240 | 14.66 |
| 512 | 7 | 2.226 | 18.06 |
| 1024 | 8 | 2.175 | 28.01 |
| 2048 | 11 | 2.138 | 36.20 |
| 4096 | 14 | 2.105 | 49.25 |
| 8192 | 18 | 2.084 | 65.97 |

At H=8192, T=861, the deterministic RHS is 65.97 times the observed shell energy. Optimizing T over all radii 1..4096 gives T=18 and still yields 2.084 E. This proves the reduction is algebraically valid but not itself a useful *numerical upper bound* at the proposed large radius. To gain an exponent it requires an independently proved upper estimate for W, not just its exact value.

For T~H^(3/4), the trivial bound from |S|<=2r is W=O(H^(15/4)), while the sufficient target is O(H^(13/4+epsilon)). The localized task therefore requires an independent power saving of H^(1/2) over its localized trivial estimate. The original full-radius T~H would have trivial W=O(H^4) and an extra translation-range cost.

## Independent reproducibility checks

- Separate prime-divisibility Möbius sieve in Python reproduced exact H=64,128,256 values E and W, independent of the C++ linear sieve.
- E(4096)=30,291,950 and sum_r delta_r=118 reproduce the prior RH_Lean Prime Census data.
- Separate segmented factorization at r=11013 independently found delta=+478 and S(276)=+502, matching the new H=8192 maxima; r=8192 and r=16383 were also checked.
- Every computed r/T satisfied the deterministic inequality using exact integer comparisons; every W was also exactly reconstructed from the common-interior, core/edge cross term, and edge-square pieces.
- Randomized controls used 48 distinct seeds from a seed-generating PRNG, not sequentially shifted seeds.

## Decision for the research program

**Retain** localized W(H;T) as a legitimate stronger, independent sufficient analytic goal and an exact computational falsifier. **Do not promote** the existence of 2T+1 geometric modes to a signed saving: W is 97%+ constant-mode energy at tested large scales, and the signed window covariance changes sign. A viable theorem must control the complete translation mean and the nonnegative variance term without assuming the target shell-energy bound, and must preserve all square-shell/cofactor boundary corrections in any multiplicative reformulation. Original native VF/#915 payment is still a separate problem.

The [independent reproduction program and CI checks](../experiments/mobius_moving_windows/README.md) accompany the frozen data. These are finite experiments, not Lean proofs of quantitative Möbius estimates or RH.

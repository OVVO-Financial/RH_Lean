# All-product Alpöge–NNS matching: the genuine remaining signed first-Selberg source

**Date:** 2026-11-21. **Status:** Exact unconditional identities (main-branch and draft #1169); finite actual-prime-power regression passed; **no RH-strength estimate on the complete source**. Draft-head Lean CI pending. This corrects the earlier isolated near-root Schur principal-overshoot narrative.

## 1. The latent cancellation in RH_Lean that must be spent FIRST

Native files:
- `RHLean/Analysis/NativePNTSignedSecondSelberg.lean`
  - `nativePNTError_mul_log_sq_eq_signedSecondSelberg`
  - `nativePNTLambdaFloorLogSignedErrorMass_eq_remainder_sub_convolution`
  - `nativePNTLambdaSignedErrorMass_mul_log_eq_components`
- `research/SELBERG_MATCHED_PRODUCT_FACE.lean`
  - `selbergMatched_complete`, `selbergMatched_schur`,
    `selbergMatched_normalized`, `selbergMatched_dyadic`
- New in PR #1169: `RHLean/Analysis/AlpogeNNSMatchedSelbergKernel.lean`
  - `alpogeNNSMatchedKernel_eq_negativePrimePower`
  - `alpogeNNSMatchedKernel_distinctPrimes_zero`
  - `alpogeNNSMatchedMass_full_eq_K2_sub_convolution`
  - `alpogeNNSNativeError_eq_matched_primePowerSource`
  - `alpogeNNSNativeError_eq_matched_mask_and_rest`
  - `alpogeNNSMatchedLowerLogs_sub_primePower_eq_firstConvolution`
  - `alpogeNNSSecondSelbergSource_eq_first_times_log`.

For EVERY integer n and every physical cutoff X,
```
K2(n) = (Lambda*Lambda)(n) - Lambda(n)*log(n).
K2(n) - (Lambda*Lambda)(n) = -Lambda(n)*log(n).
F(X) = -sum_{n<=X} Lambda(n)*log(n)*E(floor(X/n)).
```
Thus ALL distinct-semiprime terms cancel exactly, not merely the chosen near-root p*q band. This uses the ORIGINAL ordered lower Selberg remainder, not an artificially added compensator. The surviving matched F is a **prime-power-only renewal** of the actual Chebyshev error, with every power p^k retained.

For p_i in [3R/4,R), the previously isolated 2I-J source
`B=2*sum_i log(p_i)^2-(sum_i log(p_i))^2` was NOT the full source payment: the ordered convolution has exactly `-S^2` on these same physical p_i*p_j. Hence
```
B - (Lambda*Lambda*E)_selected = 2*sum_i log(p_i)^2.
```
The large negative Schur principal `-S^2` and the corresponding quadratic convolution cancel IDENTICALLY; their use as an unpaired negative principal-mode amplifier was an accounting error. The surviving 2*sum log²p is positive, with the already-CERTIFIED selected matched face theorem
```
0 <= selectedMatched(X_R)/log^2 X_R <= m_R/2,
sum_{H<=R<2H} [selectedMatched(X_R)/log^2X_R]^2 <= H^3.
```
The second estimate is `selbergMatched_dyadic`; it is a genuine UNCONDITIONAL critical-scale UPM2 payment for the exact selected matched physical products.

## 2. Exact complete source after matching

Let `E(t)=psi(t)-t`, `L=log X`, `T(X)=sum_{d<=X}Lambda(d)*E(floor(X/d))`, and define
```
F(X) = -sum_{d<=X} Lambda(d)*log(d)*E(floor(X/d)),
A(X) = S(X)*L - L_floor(X) - Def(X).
```
Here `S(X)=nativePNTSignedSelbergRemainder X`,
`L_floor(X)=sum Lambda(d)*E(X/d)*log(floor(X/d))`,
and `Def(X)=sum Lambda(d)*E(X/d)*(L-log d-log floor(X/d))`.

The complete second Selberg source gives EXACTLY
```
E(X)*L^2 = A(X)+F(X).
```
Importantly, `L_floor+Def-F=T(X)*L` by the already-certified signed-log split. Therefore
```
A(X)+F(X) = (S(X)-T(X))*L = E(X)*L^2.
```
This is a **no-double-counting and no-free-contraction audit**. It proves the second-Selberg matched source reduces to the first-Selberg identity times log X. Splitting the first/second channels into absolute values, or assigning S² as a new Schur credit, destroys the exact cancellation. But the identity itself does not estimate the size of E(X).

The original NNS zero-target Co/Div at each X is
```
A*F = Co_0(A,F)-Div_0(A,F),
(A+F)^2 = A^2+F^2+2 Co_0(A,F)-2 Div_0(A,F).
```
The one-sided RH-strength target is the sum of `[(A(X_R)+F(X_R))_+]²/log⁴X_R` over each dyadic root range. A bound on individual `A²`, `F²` at the RH scale is **false** in these tested ranges; their full signed cross covariance must be retained. Existing `PartialMomentSchurTarget` is target invariant on the centered component but does not bound the independent rank-one first moment.

## 3. Independent prime-power numeric stress test

Command:
```
python3 scripts/alpoge_matched_full_primepower_census_20261121.py
```
The revised script **independently enumerates** every actual prime and von Mangoldt prime power up to X_R and evaluates the literal Selberg symmetry pair \(\psi(X)\log X+\sum_d\Lambda(d)\psi(\lfloor X/d\rfloor)\), the factorial term via \(\log\Gamma(X+1)\), the first Selberg remainder \(S(X)\), its weighted cofactor correlation \(T(X)=\sum\Lambda(d)E(X/d)\), the floor-log term, the exact signed floor defect, and the full prime-power matched \(F(X)\). It then constructs \(A=S\log X-L_{\rm floor}-Def\) **independently of the final \(E\log^2X\) identity**, and checks both the first and second exact Selberg recurrences to floating-point precision. This is a substantially stronger source-level regression than the original reconstructed-A diagnostic.

| R | E(X_R) | full matched F | reconstructed A | selected matched | rest matched |
|---:|---:|---:|---:|---:|---:|
| 56 | -11.901555 | +24,870.389 | -25,641.713 | +89.467 | +24,780.922 |
| 317 | +12.667984 | +1,209,977.000 | -1,208,296.471 | +882.896 | +1,209,094.104 |
| 549 | -285.257239 | +3,986,879.368 | -4,032,283.289 | +1,594.469 | +3,985,284.898 |
| 1027 | -238.192404 | +15,523,584.594 | -15,569,399.338 | +3,330.913 | +15,520,253.680 |

Independent first-Selberg census at R=317 yields S=-116,094.763362 and T=-116,240.670584, so S-T=+145.907222 equals E(X)*log(X) within rounding. The independently computed A and F cancel by 99.9305% in absolute amplitude. R=1027 the cancellation is 99.8527%. The selected critical-square UPM2 paid term is a **small fraction** of full matched F: the remaining prime-power renewal and first remainder are jointly enormous. These are finite diagnostics, not evidence of a universal exponent or sign.

## 4. Exact unresolved quantitative inequality after the complete matching

Define the *fully recombined one-sided physical charge*
```
Z_R = A(X_R)+F(X_R) = E(X_R)*log(X_R)^2.
```
The relevant NNS energy target, for every eps>0, is
```
sum_{H<=R<2H} [max(Z_R,0)/log(X_R)^2]^2
  <= C_eps * H^(3+eps).
```
The selected matched near-root component is **already** unconditionally O(H³) in its own UPM2, so it is a paid term. But this does NOT imply the whole-source target. The remaining source consists of the WHOLE first-Selberg term and all remaining matched prime-power renewal, with their signed cross covariance. It cannot be bounded by summing independent UPM2 budgets on both components; the individual moments are much larger.

The external Alpöge theorem obtains the necessary square-root saving using nonlocal character–height–covolume machinery and a genuine full `AskMainBalance/topExcess/SizeWindows` construction, not the standalone principal `2I-J` calculation. For a native independent translation, an actual occurrence-preserving map must connect his paid physical family to this combined `A+F` carrier and prove the integrated one-sided estimate, not merely rename it `NNS covariance`.

**Current scope:** Algebraic source matching and critical selected-face bound are proved on the repo's existing math source; the new root-module duplication is committed and pending CI. No all-root uniform RH-strength bound is established or implied by this audit.

# Alpöge × NNS Schur: the full positive covariance is **paid**

**2026-11-21.** Source-faithful arithmetic synthesis of:
- `research/ALPOGE_SIGNED_SELBERG_INTEGRAL_SCHUR_20261120.lean` (the genuine `K2*E(1)` prime-square + semiprime matrix `D(2I-J)D`);
- `RHLean/Analysis/PartialMomentSchurTarget.lean` (arbitrary-target NNS four-moment covariance and **target-invariant Schur complement**);
- `RHLean/Analysis/NativePNTSignedSecondSelberg.lean` (complete signed Selberg recurrence `E(X)*log(X)^2` before any triangle);
- `RHLean/Analysis/AlpogeNNSBandSchur.lean` and `AlpogeNNSCompleteSelbergCovariance.lean` (new exact Schur and full signed recurrence bridges in draft #1169);
- `research/ALPOGE_ONE_SIDED_SQUARE_SEMIVARIANCE_20261120.md` (one-sided `E_+` semivariance criterion equivalent to RH as classical mathematics).

**Proof status:** New finite algebra and quantitative range bounds are unconditional. The classic analytical equivalence to RH is established in the cited mathematical note but NOT imported as an independent Lean terminal theorem. The **one-sided principal overshoot** bound on the full complement is NOT proved. A one-band sign credit alone does NOT prove RH. Exact-head Lean CI for the added files must pass before they are described as Lean-certified.

## 1. What the actual signed Selberg source tells us

For `R>=4`, `X_R=R^2-1`, let `p_1,...,p_m` be *all actual primes* in `[3R/4,R)`; `m=m_R`. Define `l_i=log p_i`, `L=sum l_i`, `barL=L/m`, and `V_R=sum (l_i-barL)^2`.

By `alpogeSelbergPrimeBand_quotient_one`, the reciprocal quotient `floor(X_R/(p_i*p_j))` equals 1 for **both** prime squares and distinct semiprimes. Hence `nativePNTError 1=-1` yields the FULL selected K2 source, with the symmetric offdiagonal half-counting:

    B_R = sum_(i,j) log(p_i)*(2*1_(i=j)-1)*log(p_j)
        = 2*sum_i (log p_i)^2 - (sum_i log p_i)^2
        = 2*V_R - m*(m-2)*barL^2.

This is an actual arithmetic identity, not a model positive matrix or an unsigned surrogate.

**NNS/Schur interpretation:** the scalar target-zero scaled Schur covariance is

    Schur_R = m*sum_i l_i^2 - L^2 = m*V_R >= 0.

The existing NNS target-invariance theorem `finiteTargetScaledSchur_target_invariant` proves that replacing target zero by any target, including the log-band MIDRANGE, does not alter `Schur_R`. The exact contraction is

    m*B_R = 2*Schur_R - (m-2)*L^2.

The sign of B_R is NOT deduced from Schur PSD: it is earned from the **negative rank-one principal component** of the 2I-J matrix and the restricted log range.

## 2. The overlooked UNCONDITIONAL critical-scale payment

Because every prime is in `[3R/4,R)`, the log weights lie in a fixed-width interval

    (3/4)*log R <= l_i <= log R,
    diameter delta = log(4/3).

The first inequality follows for R>=4 from p_i>=3R/4>=R^(3/4), since R^(1/4)>=4/3.

By Popoviciu's finite-sample range inequality (equivalently, target-invariant Schur after choosing the band midrange),

    0 <= V_R <= (m/4)*delta^2,
    0 <= 2*V_R <= (m/2)*delta^2.

The centered NNS cost is therefore <=0.041380...m. Since m<R, it is **O(R)** before normalization, with NO RH or individual Mertens estimates.

In Lean, `alpogeNNSBandScaledSchur_le_range` is the deterministic sharp target-invariant Schur bound and `alpogeNNSBandCharge_le_principal_plus_range` yields the full matrix estimate. The coarser but strict bound `alpogeNNSBandCharge_le_negative_principal` proves for all m>=3 and 0<a<=l_i<=4a/3:

    B_R <= -m*(m-8/3)*a^2 < 0.

For the actual band a=(3/4)log R, this is a genuinely signed source gain of order m^2*log^2R.

## 3. Weld to the COMPLETE signed Selberg recurrence — not merely a selected negative piece

The main-branch theorem `nativePNTError_mul_log_sq_eq_signedSecondSelberg` states EXACTLY

    E(X)*log(X)^2 =
      S(X)*log X - (Lambda*S)(X)
      + (K2*E)(X) - FloorDefect(X),

where `E(X)=psi(X)-X`. Remove **only** the actual selected band B_R from `K2*E`, defining the complete complementary right-hand side

    C_R =
      S(X_R)*log X_R - (Lambda*S)(X_R)
      + [(K2*E)(X_R)-B_R] - FloorDefect(X_R).

This retains every prime square outside the band, every semiprime outside the band, all higher quotient layers, both signs, all remainder terms and the exact floor defect. There is no term omitted or norm introduced. Thus

    E(X_R)*log^2 X_R
       = C_R - m*(m-2)*barL^2 + 2*V_R.

Put `P_R=m*(m-2)*barL^2`, the **explicit** negative principal-mode payment, and `Y_R=max(C_R-P_R,0)/log^2 X_R`. Because `0<=2V_R<=m*delta^2/2`, the complete physical upper partial moment obeys the pointwise sandwich

    Y_R <= max(E(X_R),0)
        <= Y_R + [m*delta^2/(2*log^2 X_R)].

This is an **unconditional, source-faithful one-sided inequality**. It is certified algebraically by `alpogeNNSBandOneSidedCharge_le_principal_overshoot`, then attached to the full native signed second Selberg recurrence by `alpogeNNSCompleteSelberg_oneSided_le_principalOvershoot` (new draft #1169; CI pending).

**Scale:** the bracketed remainder is O(R/log^2 R), which is STRICTLY below the natural one-sided E-error critical scale O(R^(1+eps)). Hence for every dyadic H the sum of its squares over H<=R<2H is O(H^3/log^4 H) with no RH input.

## 4. A NEW exact one-sided criterion equivalent in strength to RH

The classical one-sided semivariance theorem from the existing 2026-11-20 note proves

    RH  <=>  for all eps>0:
                sum_(H<=R<2H) max(E(X_R),0)^2
                   <= C_eps*H^(3+eps).

The pointwise sandwich above and `m_R<=R` give

    [sum Y_R^2 <= sum max(E,0)^2]
    [sum max(E,0)^2 <= 2 sum Y_R^2 + O(H^3/log^4 H)].

Therefore **as a mathematical statement**

    RH  <=>  for all eps>0:
                sum_(H<=R<2H)
                  [max(C_R - P_R,0)/log^2 X_R]^2
                <= C_eps H^(3+eps).

This is a substantive **change of the hard supplier**: every positive centered NNS covariance term from the selected genuine Selberg band is now PAID unconditionally, and the entire remaining obligation is the ONE-SIDED principal-mode OVERSHOOT of the original **complete complementary source** relative to a computable prime-band census.

The implication is not a new proof of RH: neither a uniform bound on that principal overshoot nor the full Alpöge partner/height cost has been proved in RH_Lean. The equivalence's analytic one-sided semivariance/Landau part remains paper-level, not a Lean terminal theorem.

## 5. Actual arithmetic regression (independent prime-power psi census)

Run `python3 scripts/alpoge_nns_schur_complete_source_20261121.py`. This computes actual primes to X_R, their von Mangoldt prime powers, the complete selected K2 band, the NNS Schur variance and the known one-sided inequalities. The complement C_R is reconstructed numerically from Elog^2-B (NOT independently evaluated term-by-term in this script); the complete-source equality itself is the pre-existing Lean theorem.

| R | m | B_R, selected signed | negative principal -P_R | positive Schur 2V_R | actual E(X_R) | C_R-P_R |
|---:|---:|---:|---:|---:|---:|---:|
| 56 | 3 | -44.667 | -44.711 | +0.044 | -11.902 | -771.368 |
| 317 | 14 | -5295.946 | -5296.150 | +0.204 | +12.668 | +1680.325 |
| 549 | 21 | -15144.672 | -15144.937 | +0.265 | -285.257 | -45404.187 |
| 1027 | 36 | -56616.921 | -56617.399 | +0.478 | -238.192 | -45815.222 |

At R=317, the complete principal overshoot contributes 12.666446 to E_+=12.667984 after log^2 normalization, while the positive centered term contributes just 0.001538. At R=1027, the principal overshoot is negative, so the dangerous positive E partial moment is zero; the worst Schur range payment after normalization is only 0.007745.

## 6. What to attack next (single exact witness instead of a vague missing inequality)

**Not** the already bounded centered-Schur variance. Attack the full complementary source `C_R` as one joint signed NNS/Gram object, and prove an UPPER partial-moment second bound for its excursions above `P_R` over dyadic R. Preserve the subtraction `C_R-P_R` before Cauchy, the full prime-kernel origin, actual both walls, and Alpöge's Frobenius/inertia/partner/height witnesses.

The prime-band rank-one payment is of main-term size, ≍R^2, and C_R has corresponding main-term size; a PNT estimate `o(R^2)` on the difference is NOT enough. The required square-root dyadic energy is still genuinely RH-strength. But the **centred covariance component is no longer an unpaid tax** in this source coordinate. The only nonlocal issue is the rank-one principal overshoot of the full complement.

This is the concrete source-to-NNS synthesis with explicit paid bounds; do not count the previously unbounded full UPM/LPM difference as having been proved.

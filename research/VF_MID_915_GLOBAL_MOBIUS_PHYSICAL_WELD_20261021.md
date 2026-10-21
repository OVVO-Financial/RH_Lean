# Native Mobius -> original VF #915 payment correspondence (2026-10-21)

**Status:** exact global physical coefficient identity and original anchored Co/Div algebra. No new analytic estimate, first-bad contradiction, or RH proof is asserted. Lean source: [VF_MID_915_GLOBAL_MOBIUS_PHYSICAL_WELD_20261021.lean](VF_MID_915_GLOBAL_MOBIUS_PHYSICAL_WELD_20261021.lean).

## 1. ALL-depth Boolean prime decoder, already compiled in RH_Lean

The existing VF_MID_PHYSICAL_FORCING_MOBIUS_DECODER.lean proves for every n:

    2*1_Prime(n)=mu(n)^2-mu(n)-2*D_minus(n),

where D_minus(n)=1 precisely if n is COMPOSITE and mu(n)=-1. Thus the actual open-square odd-seat charge, with original physical weight w_R=V_R/R, is

    z_R(n)=w_R-1_Prime(n)
          =w_R-mu(n)^2/2+mu(n)/2+D_minus(n).          (A)

No cubic depth-two condition, PNT approximation, or squarefree-only restriction appears. All primes, all odd-depth squarefree composites, and squareful seats are included.

| Actual n | mu | mu² | D_minus | ORIGINAL physical z_R(n) |
|---|---:|---:|---:|---|
| prime | -1 | 1 | 0 | w_R-1 |
| two-prime composite | +1 | 1 | 0 | w_R |
| three-prime composite | -1 | 1 | 1 | w_R |
| four-prime composite | +1 | 1 | 0 | w_R |
| squareful composite | 0 | 0 | 0 | w_R |

The odd-depth correction is THE precise reason that naively inserting the sign reversal mu(pc)=-mu(c) does not reverse original VF physical charge.

## 2. True fresh-prime owner response across BOTH orientations

For any prime p, any c>0 and p not dividing c,

    mu(pc)=-mu(c),    1_Prime(pc)=1_{c=1}.

Consequently,

    z_R(pc)=w_R-1_{c=1}
           =mu(pc) + [w_R+mu(c)-1_{c=1}].            (B)

Moreover the decoder gives the explicit compensation

    D_minus(pc)=(mu(c)^2+mu(c))/2-1_{c=1}.          (C)

For c>1, the entire mu(pc) signed source is undone pointwise by the physical correction (B) so that z_R(pc)=+w_R. For c=1 the sole primitive prime-root charge w_R-1 remains. This is true on both p>c and p<c; restricting to high largest-prime roots is unnecessary for the coefficient law.

The Lean full-key weighted theorem vf915GlobalDecoded_fullKeyWeightedOwnerWeld states, for ANY finite occurrence index set K, original multipliers alpha(k), and actual admissible coprime owner/cofactor maps:

    sum_{k in K} alpha(k)*z_R(p(k)*c(k))
      =sum_{k in K} alpha(k)*{
            mu(p(k)*c(k))+w_R+mu(c(k))-1_{c(k)=1}}.

The type of k can encode owner, original age, clipping, orientation, original raw parent and occurrence. Nothing is deduplicated and no absolute value is taken. Applying the theorem to ALL original #915 returned-child occurrences still requires their own admission/injection proof; the theorem does not postulate that admission.

## 3. The literal historical anchor and NNS denominator

On the ORIGINAL R odd integer seats of the OPEN square block (R²,(R+1)²), set

    Z_R = sum_n z_R(n)
        = R*w_R - P_R
        = R*w_R - (sum_n mu(n)^2)/2
                + (sum_n mu(n))/2 + sum_n D_minus(n).

The original raw VF square-endpoint defect is D_R=pi(R²)-VF_mid(R²). It satisfies

    D_(R+1)=D_R-Z_R.

The original degree-one UPM/LPM amplitude (not decompressed history!) is

    A_R=|D_R|+sum_n|z_R(n)|.

The already compiled original source satisfies

    E_R=2*D_(R+1)^2-A_R^2
       =2*(Z_R-D_R)^2-(|D_R|+sum_n|z_R(n)|)^2.     (D)

The new Lean theorems vf915GlobalDecoded_originalNNSMass and vf915GlobalDecoded_originalAnchoredExcess prove these same named original production quantities with (A) substituted sitewise.

Further, RH_Lean previously proved E_R=G_R+vfMidActiveThreeBoundaryExcess(R), with G_R the literal anchor, restoring, diagonals, and omitted-site mass, and the boundary the same three clipped physical orientations. The new theorem vf915GlobalDecoded_originalResidualAndBoundary welds THAT SAME G_R and THAT SAME clipped boundary to (D), without additional reserve capacity.

## 4. Independently reconstructed 317/1027 original VF blocks

Reproducer: scripts/vf915_global_mobius_physical_weld_317_1027.py. It checks every original open-square odd physical integer, and independently checks prime/cofactor factorization, Mobius sign reversal, full correction (B), history D_R, U/L, and original NNS denominator.

| Original physical quantity | Root 317 | Root 1027 |
|---|---:|---:|
| Per-site w_R | 0.173870484889145 | 0.144268721087924 |
| Exact odd seats | 317 | 1027 |
| Prime roots | 54 | 144 |
| High-prime composite seats | 192 | 659 |
| Smooth composite seats | 71 | 224 |
| sum mu² | 258 | 830 |
| sum mu | +6 | -2 |
| sum D_minus | 72 | 272 |
| Signed Z_R | +1.116943709859 | +4.163976557298 |
| Original D_R | -38.131636076372 | -116.133854050931 |
| Original D_(R+1) | -39.248579786232 | -120.297830608229 |
| Original NNS amplitude A_R | 128.470567418204 | 366.748438934904 |
| Original E_R | -13423.784662282891 | -105561.28136309635 |

The original production excess agrees with research/VF974_FIRST_BAD_BOUNDARY_DESCENT_OBSTRUCTION_20261018.md. These are NOT the separate cumulative Mertens values at x=317 or x=1027.

## 5. Exact remaining mathematics, not another accounting bridge

The global decoder source/endpoint/denominator and original boundary/residual are now in the SAME scalar coordinate. But the full-key matched returned-parent CAPACITY and nonpositive excess are not implied by the identities.

The module research/VF_MID_915_SOURCE_PAYMENT_CONTENT_AUDIT.lean already proves that the universal #915 payment under a first-bad hypothesis is equivalent to the no-first-bad statement (with the finite base). Therefore rewriting (D) cannot itself establish the target. A new independent sign-sensitive estimate must control the joint correction w_R+mu(c)-1_{c=1}, with every real VF weight and the historical G_R anchor, before norming.

The next acceptable theorem either (i) proves E_R<=0 on the original actual-prime first-bad source, with legal contiguous lower-run history and original denominator, or (ii) proves an independent uniform improvement to the Mertens exponent. The arithmetic coefficient identification is complete; the signed capacity estimate is not.

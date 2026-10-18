# #974 x original #915: first-bad admission and uncompensated boundary (2026-10-18)

**Status:** exact new carrier geometry, a physical same-charge/opposite-Möbius witness, an exact normalized pressure identity, and a scalar anchor-dominance obstruction. **No unconditional RH-scale first-bad payment is proved.** Lean gate and numeric regression must be checked at the PR's final head.

## 1. The new geometric audit (unconditional)

Let `R>=8`, `A=floor(R/2)+1` and `n in [R^2,(R+1)^2)`. For every prime factor `p>R` of `n`, [#974's theorem](SQUARE_BLOCK_EULER_ANCESTRY_COVARIANCE_20261017.lean) gives `c=n/p<=R`. Since `R<A^2`,

    c < A^2 <= r^2  for every historical block r>=A.

Thus the **direct sign-flipped cofactor is never a historical or current physical site in the original #915 half-run**. It belongs below the compressed `D_A` anchor. An attempted first-bad proof that spends `mu(pc)=-mu(c)` as if both charges already occur in the uncompressed historical/current NNS packet is illegal. This does not forbid a separate, *proved* nonlocal match through the original anchor.

The original native odd-site VF charge is `w_R-1_Prime(n)`, not `mu(n)`. At `R=18` actual odd composite sites 327=3*109 and 345=3*5*23 have `mu(327)=+1`, `mu(345)=-1`, yet both charge **+w_18**. This certifies that sign reversal in genuine Möbius arithmetic is not sign reversal of the original physical VF source. Squareful composites additionally contribute positive `w_R` and have `mu=0`.

## 2. Sharp residual AFTER completed legal parent matching

The existing, already compiled theorem in
[VF_MID_FIRST_BAD_FINAL_AGGREGATE_CONTRACTION.lean](VF_MID_FIRST_BAD_FINAL_AGGREGATE_CONTRACTION.lean) is

    E_R = G_R + 4 B_R - 2 H_R,

where `E_R=2*D_(R+1)^2 - (|D_R|+beta_R)^2` is the unchanged production #915 first-bad Co/Div excess, `beta_R=sum_{odd physical seats}|w_R-1_Prime(n)|`, `G_R=vfMidActiveGlobalResidualExcess R` contains identity/anchor/diagonal/squareful restoring and omitted-source capacity, and `B_R,H_R` are the signed and absolute **same-occurrence** masses of exactly three clipped boundary orientations: first-left, next-right, returned-left. Fully completed parents have zero admitted active weight; the other three oriented sectors vanish by physical masks. Never replace `H_R` by decompressed absolute history or count repeated parents as independent capacity.

Define literal upper/lower boundary masses via

    U_B=(H_R+B_R)/2, L_B=(H_R-B_R)/2.

Because `H_R` is the sum of absolute values of the same signed physical atoms, both are nonnegative. The exact unchanged production identity is

    E_R = G_R + 2 U_B - 6 L_B.

At an actual `K=2` first bad, the already-compiled `vfMidActualPrimeFirstBadAt_two_succ_nnsNormalized_gt_half` and positive original denominator give `E_R>0`, hence

    G_R + 2 U_B > 6 L_B.                     (PRESSURE)

**This is a NECESSARY condition, not an independent payment estimate.** In particular `G_R` is not known nonpositive, so one may NOT infer `U_B>3 L_B` or select a bad child solely from positive boundary mass.

The missing quantitative input is a once-only, original-weight transport matching the actual positive retained boundary and the original `G_R` anchor/restore with negative mate mass or a genuinely supercritical contiguous lower child-run. The map must preserve (owner, revealed prime, raw parent, original age, orientation, original coefficient, admissibility mask, multiplicity, and ORIGINAL NNS denominator). A same-row cofactor flip is not that map.

## 3. Algebraic no-go for spending current-local heat on an arbitrarily large anchor

Let `D` be a compressed historical scalar, `X` the signed current source and `T>=|X|` its original current absolute mass. The entirely elementary theorem proved in the accompanying Lean file is

    |D| > 6 T  ==>  2(D-X)^2 > (|D|+T)^2.

Proof: `|D-X| >= |D|-T` and

    2(|D|-T)^2 - (|D|+T)^2
      = |D|(|D|-6T) + T^2 > 0.

Therefore **no universal one-block NNS half-gate based only on current source signs can hold for large compressed history**. At a hypothetical large first-bad wall crossing, local sources may be comparatively small relative to the historical anchor. A valid proof must transfer/history-compensate the *actual* anchor as well as the clipped boundary. The previously established [exact historical NNS norm restoration](VF_MID_915_EXACT_HISTORICAL_NNS_COMPRESSION.lean) quantifies the cost of artificially decompressed history; it is not free.

This algebraic no-go does *not* refute an RH-proof based on a truly first-bad-specific nonlocal arithmetic theorem, and makes no claim of an actual first bad.

## 4. Finite genuine-prime and Möbius regression

`python3 scripts/vf974_firstbad_boundary_probe_20261018.py` independently reconstructs each original physical odd-seat source and prime/Möbius factorization. It audits the compressed `D_R`, upper square endpoint, exact root/squareful global residual `G_R`, and the signed three-boundary residual `E_R-G_R` through the already-proved equality. This **does not** independently enumerate every raw-parent boundary incidence; it does not measure the termwise `U_B,L_B`, and is not an asymptotic sign certificate.

| R | D_R | E_R | G_R | signed boundary E-G |
|---:|---:|---:|---:|---:|
| 8 | -0.82622 | -22.02883 | -8.55373 | -13.47509 |
| 18 | -3.38858 | -104.49182 | -58.31869 | -46.17313 |
| 32 | -5.94746 | -283.25658 | -161.27709 | -121.97949 |
| 56 | -11.56366 | -628.22836 | -322.90212 | -305.32624 |
| 317 | -38.13164 | -13423.78466 | -7134.99589 | -6288.78877 |
| 1027 | -116.13385 | -105561.28136 | -57248.33925 | -48312.94211 |

**Do not conflate these R values with integer endpoints x=317/1027.**

## 5. Exact next proving obligation

A genuinely new estimate must combine (a) the unmatched positive boundary `2U_B`, (b) the negative boundary payment `-6L_B`, (c) the *retained* global `G_R`, and (d) an occurrence-preserving, norm-budgeted **contiguous lower-run** recursion. The 2026-10-06 handoff explicitly forbids replacing a bad parent run by a single independently bad child endpoint. The sector-six raw cone fails already at R=8,18, so no universal child cone premise may be introduced.

An acceptable theorem either proves `E_R<=0` under the actual first-bad hypothesis with a new arithmetic ingredient, or constructs a strictly lower bad child-*run* together with an exact compensated inherited budget under a well-founded rank. Everything in the current module stops before that theorem.

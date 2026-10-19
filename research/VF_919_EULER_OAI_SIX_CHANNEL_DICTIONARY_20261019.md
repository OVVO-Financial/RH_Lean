# Six fixed-wheel covariance channels versus OAI sextic cancellation — exact bridge and remaining dictionary

**Date:** 2026-10-19. **Status:** exact real / arbitrary-complex *algebraic correspondence*; genuine OAI Hecke ideal source identification and moment saving UNPROVED. No RH, native 7/8 proof, or unconditional signed Gram estimate asserted.

## 1. Distinguish two different “sixes”

Within a VF square block [R²,(R+1)²), the low-prime wheel p<=R is fixed. Its three PHYSICAL signed streams are:
- A: integers supported entirely on primes <=R (smooth source);
- H: composite integers with exactly one greatest prime p>R, with mu(pc)=-mu(c);
- -Q: newly entering primes p>R, the c=1 source with mu(p)=-1.

Let S=A+H-Q, and KA, KH be the true squarefree diagonal. The covariance decomposition contains six symmetric pair classes:

\[
\begin{aligned}
C_{AA}&=(A^2-K_A)/2,\quad
C_{HH}=(H^2-K_H)/2,\quad
C_{PP}=(Q^2-Q)/2,\\
C_{AH}&=AH,\quad C_{AP}=-AQ,\quad C_{HP}=-HQ,\\
S^2 &= K_A+K_H+Q+2(C_{AA}+C_{HH}+C_{PP}+C_{AH}+C_{AP}+C_{HP}).
\end{aligned}
\]

These are the 6 entries of Sym²(R³) (a symmetric 3x3 real matrix), **not** the 6 phases of a sextic character χ of order dividing 6. The OAI 7/8 paper's six-fold structure comes from a sextic Hecke/Poisson arithmetic carrier and compensated marked-minus-rescaled primes, not a six-way partition of physical integer sites. There is NO known canonical bijection from the six Euler channels to six χ-values.

The six-channel identity is exact and kernel-formalized in
\`research/VF_919_EULER_FIXED_WHEEL_SIX_CHANNEL_20261019.lean\`.
The public OAI mechanism and native limitations are documented in
\`research/VF_MID_919_OAI_STAGE_SAVINGS_AND_BOOTSTRAP.md\` and
\`research/VF_MID_919_OAI_C_TO_R_CANCELLATION_WELD.md\`.

## 2. The genuine phase-preserving functor

Let w(n) be **any** complex weights attached to physical integer sites — including a hypothetical true OAI-compatible spectral probe. Define A_w, H_w, P_w by summing the original signed rational Möbius source of each site times w(n), with P_w recording +w(p), so the prime mass is -P_w. No phase replacement is made.

Then exactly:
\[
Z_w=A_w+H_w-P_w,\quad
\begin{aligned}
|Z_w|^2={}&|A_w|^2+|H_w|^2+|P_w|^2\\
&+2\Re(A_w\overline {H_w})
 -2\Re(A_w\overline {P_w})
 -2\Re(H_w\overline {P_w}).
\end{aligned}
\]

This lifts the six real signed source channels to a **Hermitian six-family Gram**. The conjugate cross pairs must remain intact; replacing a complex phase by its scalar real part *before squaring* discards information. The full Hermitian 3x3 matrix has 9 real degrees of freedom; “six” means three diagonal families plus three conjugate-paired cross families, not six independent real Fourier modes.

\`research/VF_919_EULER_OAI_PHASE_PRESERVING_SIX_GRAM_20261019.lean\` formalizes for an arbitrary w:
- exact phase-weighted actual-integer Möbius source reassembly;
- exact six-channel Hermitian identity;
- exact full-row Gram reassembly.

**This is a necessary source-preservation test, not proof of an OAI character-to-integer bijection or power saving.**

## 3. Actual six-channel numerics that a proposed dictionary MUST preserve

| pair contribution | R=317 | R=1027 |
|---|---:|---:|
| smooth–smooth AA | -28 | +28 |
| highcomposite–highcomposite HH | +2108 | +9503 |
| prime–prime PP | +1431 | +10296 |
| smooth–highcomposite AH | -134 | -2397 |
| smooth–prime AP | +108 | +2448 |
| highcomposite–prime HP | **-3618** | **-20304** |
| signed total C | **-133** | **-426** |

The negative HP channel dominates both examples. The total must be reconstructed with the true squarefree diagonal: (S²-K)/2. Positive within-shell C appears in thousands of other blocks, so a universal HP<0 component alone cannot be the theorem.

On H=4096 dyadic shells, the mixed highcomposite–prime **ENERGY** contribution -2 sum_R H_R Q_R is -4,419,744,268; the complete six-energy E(H)=30,291,950. Note the energy terms are 2*C_offdiag at the shell level, not bare pair covariances.

## 4. Precise missing arrows to compare to OAI's marked-minus-rescaled operator

Any claimed bijection should supply:

1. **Norm-and-label dictionary:** associate each actual rational integer site and its prime/composite classification with the correct OAI Eisenstein-ideal label(s), including split/inert/ramified primes, multiplicity, zero sites and true support. Norm grouping is not one-to-one; split prime ideals must NOT be collapsed.
2. **Marked/rescaled projection:** prove that the local scalar Euler-cancellation operator is represented as an explicit linear transformation of A_w,H_w,P_w **with the same physical seat weights**. One cannot equate it to -2HQ by visual similarity.
3. **Phase-respecting six-family Gram:** after transforming the coefficient streams, prove the exact source index map and retain ALL conjugate cross terms (especially H–P), not only three squares or a phase-blind real projection.
4. **Independent analytic saving:** establish a uniform bound on a restricted COMPLETE compensated character/mixed-moment tile, and pay all omitted rows and owner sources. The OAI sextic large sieve works on a different ideal carrier and cannot be borrowed as an unconditional bound for the whole physical Euler Gram.

An exact finite-stage mapping is plausible at the **weighted-operator/Gram level**, and that is the next falsifiable test. The matching cardinality “six” is not evidence of a term-by-term bijection.

## 5. Acceptance

The two fixed-wheel numerics, full 10^8 physical six-channel census and prime-square handoff tests are already native evidence. The three new weighted complex theorems are CI targets; until CI returns green, report them as **committed and pending** rather than kernel verified. The uniform arithmetic covariance cancellation estimate remains open.

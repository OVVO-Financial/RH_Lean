# Data-driven finite-C ancestry hypotheses — exhaustive R ≤ 20,000 (2026-10-11)

**Status:** exact finite integer experiments, not uniform finite C/A/RH and not newly Lean-compiled.

## Census extension

Using a new C++17 genuine-prime/Möbius sieve to n=399,999,999, we checked the historical Mertens floor kernel Q_R=2M(R-1)-M(R²-1) and strict historical K_R at **every 19,999 roots 2≤R≤20,000**, and the complete seed-inclusive gcd owner ledger at **every 19,998 roots 3≤R≤20,000**. K_R=3/2 for every root 31≤R≤20,000. The maximum C_R among R≥31 remains 0.37499231571469 at R=5,561, but there is a new near record C_13414=0.37288340947989. No finite census proves a universal cap.

| Root R | M(R²−1) | Q_R | C_R | High-prime H | Smooth S |
|---:|---:|---:|---:|---:|---:|
| 317 | -28 | +22 | 0.056665 | +890 | -918 |
| 596 | -246 | +256 | 0.350710 | +2,462 | -2,708 |
| 5,561 | -2,544 | +2,554 | 0.374992 | +124,373 | -126,917 |
| 6,000 | +2,256 | -2,256 | 0.307003 | +145,554 | -143,298 |
| 10,000 | +1,928 | -1,974 | 0.161176 | +356,027 | -354,099 |
| 13,414 | -6,136 | +6,126 | 0.372883 | +591,724 | -597,860 |
| 15,101 | +5,863 | -5,859 | 0.316791 | +739,001 | -733,138 |
| 20,000 | -1,599 | +1,651 | 0.067402 | +1,212,061 | -1,213,660 |

Independent moving-x test: **x=317 means R=18**, and S=-3, H=-1, Q=0; the physical distinct-high-prime-owner coprime/shared entries are (-436,+362), smooth/high coprime/shared (+253,-250). At x=318 Q=+1; x=323 Q=-1; x=1027 (R=33) Q=-5. Root R=317 means x=100488, NOT x=317.

## H1 — four arithmetic gcd-sector signs

Let Gamma_same_shared/coprime denote the *same high-prime* signed off-diagonal Mobius cofactor Gram, conditioned on shared gcd>1 versus gcd=1 (cofactors c,d≥2). Let D_distinct_shared/coprime denote the **seed-inclusive** ordered interaction of *different high-prime owners*, with the same gcd partition.

| Direction | Last root failing | Holds at EVERY root thereafter through 20,000 |
|---|---:|---:|
| Gamma_same_shared < 0 | 8 (zero) | **9** |
| D_distinct_shared > 0 | 371 | **372** |
| Gamma_same_coprime > 0 | 493 | **494** |
| D_distinct_coprime < 0 | 842 | **843** |

Conjecture H1: all four sign inequalities eventually hold at every root; the deliberately strong, falsifiable cutoff version predicts they hold for ALL R≥843.

| R | same shared | same coprime | distinct shared | distinct coprime |
|---:|---:|---:|---:|---:|
| 317 | -8,362 | -1,950 | -301,332 | +1,078,536 |
| 1,000 | -207,442 | +47,138 | +51,784,738 | -8,783,884 |
| 6,000 | -13,352,348 | +5,545,316 | +31,895,544,022 | -10,713,210,404 |
| 10,000 | -38,793,700 | +15,971,428 | +182,413,124,302 | -55,667,504,652 |
| 20,000 | -156,720,834 | +59,843,784 | +1,981,916,502,626 | -512,860,676,356 |

## H2 — actual-prime quotient-weighted sign domination

Define the R-independent Möbius ancestor prefix

F_shared(t) = 2 ∑_{2≤c<d≤t, gcd(c,d)>1} μ(c) μ(d).

The same-prime shared Gram admits the exact identity

Gamma_same_shared(R) = ∑_{t=2}^{R-1} h_R(t) F_shared(t),

where h_R(t)=π(⌊(R²-1)/t⌋)-π(⌊(R²-1)/(t+1)⌋) is the **genuine prime count** in the quotient band.

Write the total positive and absolute negative weighted charges as P_plus and P_minus. The positive charge is dominated in EVERY tested root.

| R | P_plus | -P_minus | ratio P_plus/P_minus |
|---:|---:|---:|---:|
| 56 | +36 | -350 | 0.102857 |
| 317 | +3,478 | -11,840 | 0.293750 |
| 1,000 | +25,412 | -232,854 | 0.109133 |
| 6,000 | +665,842 | -14,018,190 | 0.047498 |
| 10,000 | +1,718,098 | -40,511,798 | 0.042410 |
| 20,000 | +6,271,382 | -162,992,216 | 0.038477 |

The maximum ratio over **every 9≤R≤20,000** is 0.514644 at R=101. The stronger bounds P_plus ≤ (1/2)P_minus at every R≥103, ≤(1/3)P_minus at every R≥261, and ≤(1/10)P_minus at every R≥1139 hold through 20,000. Those thresholds are data-selected.

Conjecture H2: for all sufficiently large genuine-prime roots, P_plus ≤ (1/2)P_minus; the sharp cutoff prediction is all R≥103. This is a concrete conditional signed-incidence *same-prime* bound; it does NOT imply finite C.

### Crucial falsification

The tempting simplification F_shared(t)<0 for ALL t≥230 is FALSE, even though it holds for 230≤t≤20,000. An independent O(N log N) exact divisor-inversion program scanned to t=100,000,000 and found **F_shared(191,931)=+20,044**, with the last observed nonnegative value **F_shared(300,893)=+642**, followed by F_shared(300,894)=-830. This is why actual prime availability h_R(t), not unweighted prefixes or arbitrary monotone replacements, must be retained.

## Proper-descendant stress: independent budget fails at small constants

For the existing exact proper-descendant divisor-lattice term T_R=-∑_{2≤k<R} μ(k) A_R(k) V_R(k), independent divisor-stepping and n-streamed factorizations agree at the known six roots and extend to R=18,000.

| R | T_R | T_R/(R² K_R) |
|---:|---:|---:|
| 5,561 | -258,540,313 | -5.574 |
| 6,000 | +203,312,265 | +3.765 |
| 10,493 | -1,377,440,139 | -8.340 |
| 13,414 | -2,961,587,970 | -10.973 |
| 13,600 | -3,436,099,350 | -12.385 |
| 15,101 | +3,901,686,868 | +11.406 |
| 18,000 | -1,033,813,003 | -2.127 |

Thus the proposed independent estimates |T_R|≤R²K_R and even |T_R|≤10 R²K_R are **numerically false**. The +T_R and -T_R gcd sectors must be combined before placing bounds.

## Actual next theorem

Prove, falsify, or refine H1/H2 while preserving the prime quotient weights and physical c=1 seed. Then obtain an independent, *cross-sector* quantitative joint return between smooth/high and distinct-high-owner signs. H1/H2 alone do not bound Q_R, establish finite A, or prove RH. Full independent C++/Python audit scripts, exact CSVs, moving-x examples, and three plots accompany this experiment in the conversation as a reproduction ZIP.

Existing related repository groundwork: research/COFACTOR_CONDITIONAL_PRIME_AVAILABILITY_GCD_FINITE_C_2026_10_11.md and research/FINITE_C_ONE_SIDED_CROSS_OWNER_BOUNDS_2026_10_11.md.

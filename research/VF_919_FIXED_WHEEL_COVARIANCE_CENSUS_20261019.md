# Fixed-VF-wheel chronological covariance: exact 10^8 audit

**2026-10-19 | Status: EXACT FINITE CENSUS + FINITE LEAN ALGEBRA; NO asymptotic bound claimed.**

## 1. Correction to the earlier moving-wheel interpretation

For each integer root R>=2, the VF shell is I_R=[R²,(R+1)²) and the **wheel is precisely the fixed set of prime divisors p<=R**. At every site x in I_R, floor(sqrt(x))=R. New primes p>R enter as x grows; they do **not** change the wheel within this shell. High-prime composites p*c also enter, with cofactor 1<=c<=R and mu(p*c)=-mu(c); high-prime owner p is unique.

The VF non-strict wheel gains a prime p **at x=p²**, whereas the older *strict* low classification p<sqrt(x) acquires p at x=p²+1. They describe the same factorization geometry with a one-integer convention difference. In either convention p² is squareful (mu=0), and moving already-admitted terms between low/high populations does not change their physical coefficients or total signed covariance. Composite roots R do not change the wheel at R².

## 2. Three physical signed populations and six pair channels

For every partial shell [R²,X] with X<(R+1)² define:

- A_R(X): genuine signed mu(n) with **all** prime factors <=R; includes the actual smooth nonprimes.
- H_R(X): genuine signed mu(n) of **composites** with their unique greatest prime factor >R.
- Q_R(X): count of actual newly entering prime sites p>R (unit cofactor c=1), each physical Mobius weight -1.
- K_A,K_H: actual nonzero-Mobius (squarefree) diagonal in A,H. Prime diagonal is exactly Q.

Then **at every integer X**, no probabilistic assumptions:

\[
S=A+H-Q,\qquad K=K_A+K_H+Q,
\]
\[
\boxed{\begin{aligned}
C&=C_{AA}+C_{HH}+C_{PP}+C_{AH}+C_{AP}+C_{HP},\\
C_{AA}&=(A^2-K_A)/2,\quad C_{HH}=(H^2-K_H)/2,\quad C_{PP}=(Q^2-Q)/2,\\
C_{AH}&=AH,\quad C_{AP}=-AQ,\quad C_{HP}=-HQ,\\
S^2&=K+2C.
\end{aligned}}
\]

At the admission of the next integer with weight a in {-1,0,1}, **delta C=a*S_before**, without double counting same-site diagonal; for prime arrival a=-1. The sign of C, within shells and across shells, need not be negative.

This is distinct from the *global* low/high reclassification ledger of the previous PR findings. Holding a fixed VF wheel exposes the prime versus high-composite mixed term \(-HQ\) explicitly.

## 3. Exact physical examples (whole shell)

| component | R=317 | R=1027 |
|---|---:|---:|
| fixed-wheel smooth signed A | -2 | -17 |
| high-prime COMPOSITE signed H | +67 | +141 |
| new prime count Q | 54 | 144 |
| **net S=A+H-Q** | **+11** | **-20** |
| total squarefree diagonal K | 387 | 1252 |
| signed smooth pair C_AA | -28 | +28 |
| high-composite pair C_HH | +2108 | +9503 |
| prime-prime C_PP | +1431 | +10296 |
| smooth/high-composite C_AH | -134 | -2397 |
| smooth/prime C_AP | +108 | +2448 |
| **high-composite/prime C_HP** | **-3618** | **-20304** |
| **total C** | **-133** | **-426** |
| prime-arrival pair contributions | -664 | +158 |
| nonprime-arrival pair contributions | +531 | -584 |
| **largest partial-shell |S|** | **32** | **22** |
| offset of this peak after R² | 400 | 1841 |
| partial-shell states having C>0 | 248 of 635 | 53 of 2055 |

Thus 317: (-28+2108+1431-134+108-3618)=-133=(11²-387)/2.
And 1027: (28+9503+10296-2397+2448-20304)=-426=(400-1252)/2.

**A crucial observation:** the largest absolute restoring channel is H versus Q, not smooth A versus Q. The newly admitted HIGH-prime composites are extensions of fixed LOW-wheel cofactors, and their signed contribution offsets the prime-only source at the same shell.

## 4. Every-site 10^8 audit and genuine prime-square transitions

Stand-alone warning-fatal C++ linear-Mobius sieve audited 99,999,996 integer admissions n=4,...,99,999,999; **all 9,998** complete VF square shells 2<=R<10,000; all **1,229 prime-square handoffs** and **8,769 composite-square non-handoffs**. At every physical site it checked:
  - actual prime iff no fixed low-prime divides the site (smallest-prime test);
  - all high-prime owners have cofactor <=R and complete Mobius sign reversal;
  - genuine signed source partition, squarefree diagonal partition;
  - exact six covariance channels and delta-C=a*S_previous;
  - separately accumulated prime and composite arrival pair covariance;
  - nonnegative squarefree diagonal and signed pair parity;
  - partial-shell amplitude and all completed-shell/dyadic endpoint identities.

**Full-scan findings:** 3,227 complete shells have *positive* total C, and 32,010,734 intermediate shell positions have positive total C. Both signs must be retained by any genuine bound. All observed H_R were positive within this finite range but **no all-R positivity is claimed**. Maximum observed \(\max_{2\le R<10^4}\max_{X\in I_R}|S_R(X)|/\sqrt{2R+1}\) was 2.939843 at R=8135. This is FINITE and not a proof of O(sqrt(R)) for partial shells.

Historical wheel handoff: when p crosses into LOW at x=p² under VF cutoff, already-present p*c sites (c<p) reclassify with signed transfer \(-M(p-1)\) and transferred diagonal \(K(p-1)\). The new site p² itself has mu=0. The old strict convention makes the same handoff at p²+1. **Neither event creates a new signed-Mobius mass** at the handoff.

## 5. Dyadic complete-shell and partial-prefix energy

| H | E(H)=sum S_R(right)^2 | Sum_R max_X S_R(X)^2 | E(H)/H² | E(H)/H^(5/2) | positive final-C shells |
|---:|---:|---:|---:|---:|---:|
| 256 | 110,216 | 194,615 | 1.68176 | 0.10511 | 86 |
| 512 | 486,935 | 853,220 | 1.85751 | 0.08209 | 170 |
| 1024 | 1,723,387 | 3,324,657 | 1.64355 | 0.05136 | 306 |
| 2048 | 7,380,415 | 13,610,590 | 1.75963 | 0.03888 | 668 |
| 4096 | 30,291,950 | 55,099,123 | 1.80554 | 0.02821 | 1296 |

The MAXIMUM-PARTIAL energy is approximately 1.8–1.9 times full-right-end energy for these bands. Finite near-H² energy remains compatible with the 7/8 requirement H^(5/2+epsilon), and with more powerful bounds, but proves none.

**Signed six-energy at H=4096** (all integer exact):

\[
\begin{aligned}
E(4096)={}&12{,}752{,}906\quad(A^2)\\
 &+2{,}365{,}661{,}908\quad(H^2)\\
 &+2{,}085{,}172{,}706\quad(Q^2)\\
 &-268{,}542{,}628\quad(2AH)\\
 &+254{,}991{,}326\quad(-2AQ)\\
 &-4{,}419{,}744{,}268\quad(-2HQ)\\
={}&30{,}291{,}950.
\end{aligned}
\]

**This identifies the mixed \(-2H Q\) term as the dominant cancellation at this empirical scale.** It follows algebraically from the exact physical A/H/Q populations. Its magnitude and persistent sign are *not* a uniform number-theoretic upper bound.

## 6. The exact theorem still needed

The source-level candidate is to bound the **fully compensated fixed-wheel high-prime response** rather than prime-density alone:

\[
\sum_{H\le R<2H}\left(A_R+H_R-Q_R\right)^2
\ll_\varepsilon H^{5/2+\varepsilon}
\]

for the native 7/8 transfer, or a stronger *historical*, cross-shell signed bound for RH strength. The explicit signed cross term \(-2H_RQ_R\) **must remain inside the bound**; separate absolute square bounds on H_R and Q_R are of order H³/log²(H) and cannot pay H^(5/2) by themselves.

First-order PNT is allowed on the **aggregate** dyadic prime counts, but is insufficient on an individual short shell or the signed composite response. Empirical positive H_R does not justify assuming high composites always restore; neither does near-H² energy up to 10^8 prove an asymptotic estimate.

## 7. Reproduction and formalization

- Full detailed finite C++ audit produces four CSVs: partial trace at R=7,13,317,439,1027; every complete shell (9,998 rows); all 1,229 prime-square handoffs; and nine dyadic six-source Gram reports (H=16,...,4096).
- GitHub native \`scripts/vf919_euler_prime_response_census.cpp\` was expanded to check fixed-wheel primality, unique high-cofactor parity, six-channel covariance and chronological handoffs at every site, and to run through x<10^8 with warning-fatal compiler settings in CI.
- New \`research/VF_919_EULER_FIXED_WHEEL_SIX_CHANNEL_20261019.lean\` proves the fixed wheel is invariant, prime iff wheel survivor, source partition and squarefree diagonal, sixfold Green--Kubo and event increment identities. No bound from PNT is inferred.
- The earlier \`research/VF_919_EULER_PRIME_DENSITY_LEDGER_20261019.lean\` has two prime-positivity tactic fixes after its initial red CI.
- Dedicated CI compiles the new exact 36 theorems with warningAsError, checks standard axioms, runs the reproducible 4M and 100M C++ audits, and verifies research import closure. New statuses must be checked; **red/pending CI is not proof acceptance.**

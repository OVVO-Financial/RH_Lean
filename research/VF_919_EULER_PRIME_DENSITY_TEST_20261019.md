# Euler growth-rate hypothesis: true-prime census to 10^8 and exact native Lean translation

**Date:** 2026-10-19. **Status:** finite exact C++ evidence + source-exact formalized statements with a conditional bound. An unconditional all-scale growth estimate is NOT claimed. The user hypothesis tested: “the composite response increasingly dominates/cancels the arrivals because prime density decreases relative to the existing low wheel”.

## 1. What the growth rates actually compare

In each canonical shell I_R=[R^2,(R+1)^2) define
- Q_R = number of **actual newly arriving primes** in I_R.
- B_R = sum over **nonprime integer sites** in I_R of true signed mu(n); squareful sites contribute zero.
- S_R = B_R - Q_R = sum over ALL n in I_R mu(n).
- K_R = sum over ALL n in I_R mu(n)^2.

This decomposition is exact. It includes high-prime composites (not only smooth integers), fixed floor-sqrt wheels, the prime-only cofactor c=1 and both endpoints.

The relevant baseline is b(X)=0 for X<=1, b(X)=X/log(X) otherwise, with shell difference q_R^PNT=b((R+1)^2-1)-b(R^2-1). Define signed errors
U_R = B_R-q_R^PNT, V_R=Q_R-q_R^PNT. Then
  S_R=U_R-V_R
exactly. “Q_R follows x/log x” alone controls neither U_R nor their signed joint interaction.

The PNT predicts π(R)~R/log R (preexisting low PRIME count) and heuristically Q_R~R/log R (arrivals per shell). Hence **their leading growth orders coincide**; the hypothesis that Q_R / π(R) is forced to zero by PNT is incorrect. In the numerical sample, dyadic mean Q_R/π(R) rises from ~0.850 (H=256) to ~0.880 (H=4096). Also, ordinary PNT does not supply uniform one-shell Q_R asymptotics.

## 2. Exact census to 100,000,000

The independent warning-fatal C++ linear sieve used N=99,999,999 and validated ALL 9,998 completed shells 2<=R<10,000. The actual π(N)=5,761,455, M(N)=+1,928, squarefree diagonal K(N)=60,792,694. Every shell was audited against UPM−LPM, smooth/high composite decomposition, and integer parity of (S_R^2-K_R)/2.

| R | π(R) | Q_R | B_R | S_R | |S_R|/Q_R | smooth signed composite | high-prime signed composite |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 317 | 66 | 54 | 65 | +11 | 0.2037 | −2 | +67 |
| 1027 | 172 | 144 | 124 | −20 | 0.1389 | −17 | +141 |
| 2048 | 309 | 265 | 300 | +35 | 0.1321 | −24 | +324 |
| 4096 | 564 | 491 | 609 | +118 | 0.2403 | +29 | +580 |
| 8192 | 1028 | 869 | 1115 | +246 | 0.2831 | −42 | +1157 |

Counterexample to *monotonic* relative contraction: R=317 ratio 0.204, R=318 ratio 0.417, R=321 ratio 0.923, R=322 ratio 0.088. In roots 317..1027, the relative |S_R|/Q_R rose in 359 of 709 consecutive steps; 363 nonzero shell-sign changes occurred. Negative B_R at only three small roots, but this fact is not sufficient for a uniform bound.

Even with very large coherent separate terms, cancellation occurs in the full signed square:
  E(H)=sum_R(B_R-Q_R)^2
      =sum_R B_R^2+sum_R Q_R^2-2sum_R B_R Q_R.

| H | sum B_R² | sum Q_R² | -2 sum B_R Q_R | actual E(H) | E(H)/H² | E(H)/H^(5/2) |
|---:|---:|---:|---:|---:|---:|---:|
| 256 | 1,172,686 | 1,090,186 | −2,152,656 | 110,216 | 1.6818 | 0.1051 |
| 512 | 7,440,330 | 7,008,021 | −13,961,416 | 486,935 | 1.8575 | 0.0821 |
| 1024 | 47,362,993 | 46,012,166 | −91,651,772 | 1,723,387 | 1.6435 | 0.0514 |
| 2048 | 313,311,253 | 307,337,568 | −613,268,406 | 7,380,415 | 1.7596 | 0.0389 |
| 4096 | 2,109,872,186 | 2,085,172,706 | −4,164,752,942 | 30,291,950 | 1.8055 | 0.0282 |

The empirical energy looks closer to O(H²) than O(H^(5/2)); no all-H inequality follows from this finite scan. Across X>=100,000 through X=99,999,999, the maximum |M(X)|/sqrt(X) was 0.462729 at X=30,919,091; it is NOT a proof of the RH-scale envelope.

## 3. Explicit error-energy and PNT residual audit

Let E_B(H)=sum_{H<=R<2H} (B_R-q_R^PNT)^2, E_Q(H)=sum (Q_R-q_R^PNT)^2 and
G(H)=-2sum (B_R-q_R^PNT)(Q_R-q_R^PNT).
Then exactly E(H)=E_B(H)+E_Q(H)+G(H).

| H | E_B(H)/H² | E_Q(H)/H² | G(H) | E(H)/H² |
|---:|---:|---:|---:|---:|
| 256 | 1.4078 | 0.1901 | +5,500 | 1.6818 |
| 1024 | 1.5204 | 0.2744 | −158,643 | 1.6435 |
| 2048 | 1.7537 | 0.3435 | −1,415,843 | 1.7596 |
| 4096 | 1.9250 | 0.4696 | −9,882,413 | 1.8055 |

This decomposition shows that **prime density is not sufficient by itself**: controlling the signed composite error U_R is indispensable. The elementary sufficient inequality E(H)<=2(E_B(H)+E_Q(H)) is proved in Lean but is not an independent estimate of either energy.

## 4. New Lean statements (all proof obligations remain explicit)

- research/VF_919_EULER_PRIME_DENSITY_LEDGER_20261019.lean
  * actual prime p pair increment = -M(p-1)
  * actual total pair covariance = true prime admissions + true nonprime admissions
  * for arbitrary b: true prime admissions = model b + **unremoved weighted residual**
  * instantiate the explicit b(n)=n/log(n) for n>=2
  * exact prime-square handoff signed total = -M(p-1), plus algebraic invariance of the three LL/HH/LH components
- research/VF_919_EULER_MOVING_COVARIANCE_GROWTH_20261019.lean
  * define strict low prime rule p²<X
  * exact moving signed mass, diagonal, C_LL+C_HH+C_LH=total pair covariance
  * exact S_R = B_R-Q_R, and S_R=(B_R-q_R^PNT)-(Q_R-q_R^PNT)
  * exact signed B²+Q²−2BQ shell energy
  * sufficient dyadic bound E(H)<=2[E_B(H)+E_Q(H)] with explicit **unproved** error energies.

**No** PNT->signed residual estimate, uniform dyadic covariance bound, zero-free theorem or RH follows from these exact identities alone.

## 5. Reproduction and acceptance

Tracked standalone census:
  g++ -O3 -std=c++17 -Wall -Wextra -Werror scripts/vf919_euler_prime_response_census.cpp -o /tmp/euler-response
  /tmp/euler-response 2048    # CI; verifies 317,1027,H=256,1024
  /tmp/euler-response 10000   # optional 10^8 exhaustive recheck

The richer complete-shell CSVs and plots with all 9,998 roots are supplied as conversation artifacts. Their underlying full-census program euler_prime_response_test.cpp and analysis script were run under the same warning-fatal C++ compiler.

**Novel required theorem:** a uniform arithmetic restriction on the *joint* prime-model error and the signed composite response, or preferably on their compensated cross-term, strong enough to yield E(H)=O_epsilon(H^(5/2+epsilon)) and ultimately an all-scale power saving. It cannot be obtained by substituting x/log x into one-shell prime counts while discarding its signed residual.


## 6. Full moving covariance extension through x=99,999,999

The already-established strict sqrt(x) Euler ledger C++ executable was rerun at **N=99,999,999**, independently of the complete-shell density census above. It verified the signed moving low/high decomposition after **every** integer admission and every one of the **1,229** prime-square handoffs (all handoffs had delta total covariance exactly zero).

Terminal exact integer arithmetic:

| Quantity | At x=99,999,999 |
|---|---:|
| π(x) | 5,761,455 |
| M(x) | +1,928 |
| squarefree K | 60,792,694 |
| signed LOW mass L | −354,099 |
| signed HIGH mass H | +356,027 |
| C_LL | +62,684,984,482 |
| C_HH | +63,355,282,436 |
| C_LH | −126,068,804,673 |
| C_total | −28,537,755 |
| true prime-arrival C_prime | −668,067,313 |
| prime-model C_model (x/log x increments) | −629,018,218.7683 |
| weighted prime-model C_residual | **−39,049,094.2317** |
| genuine nonprime-arrival C_comp | +639,529,558 |

Arithmetic checks: L+H=+1,928; C_LL+C_HH+C_LH=−28,537,755=(1,928²−60,792,694)/2; C_prime+C_comp=−28,537,755; C_model+C_residual=C_prime.

The finite empirical maximum |M(x)|/sqrt(x) for **all x>=100,489** in this scan was 0.462728690117 at x=30,919,091. The finite maximum |M(x)|/x^(7/8) for all x>=100,489 remained 0.00476139204361 at x=119,545. No extrapolation is claimed.

**Interpretation:** prime density itself declines, but its weighted signed covariance contribution changes sign across x; the x/log x weighted residual exceeds the net covariance in absolute value at this terminal sample. It cannot be discarded or bounded by first-order PNT alone. The net cancellation involves genuine nonprime response and dynamic low/high pair cross-terms.

The complete moving-ledger CSV (integer-time samples), all 1,229 handoff rows, and independent exact full-shell C++/CSV audits are supplied in the conversation artifacts. They are evidence, not a kernel theorem or unconditional exponent gain.


## 7. Important exact dyadic-PNT scale correction

Using the native theorem \`vf919EulerDyadicPrimeArrivals_eq_prefixDifference\` and PNT on the **complete aggregate** (rather than pretending each short shell has a PNT asymptotic), one gets

\[
\sum_{H\le R<2H} Q_R
=\pi((2H)^2-1)-\pi(H^2-1)
\sim\frac{3H^2}{2\log H}.
\]

Meanwhile the count of prime coordinates already below each root satisfies, using PNT and integral comparison,

\[
\sum_{H\le R<2H}\pi(R)
\sim\sum_{H\le R<2H}\frac{R}{\log R}
\sim\frac{3H^2}{2\log H}.
\]

Thus the aggregate new-prime arrivals and cumulative low-prime *counts* have the **same leading growth**, and their ratio approaches one on dyadic bands. Falling fraction Q_R/(2R+1) is a different statement and DOES NOT bound the signed Möbius response B_R-Q_R. The hypothetical signed composite B_R≈Q_R is an additional arithmetic cancellation claim; it cannot be deduced from these unsigned first-order counts.

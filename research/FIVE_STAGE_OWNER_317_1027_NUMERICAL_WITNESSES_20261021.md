# Exact signed-owner witnesses at square-root clocks 317 and 1027

Date: 2026-10-21. This is an expansion of draft PR #995. **Integer-exact Mertens computation**, with direct integer-site classification **independently checked** against complete prime-owner cofactor Fubini. The physically weighted #915 VF ledger is separately quoted and is not the same carrier.

## 1. Distinguish clock from integer argument

R=317 means X=R²-1=100488. R=1027 means X=1054728. These are NOT ordinary Mertens evaluations M(317) and M(1027). Define H_R=sum_{n<=X, P+(n)>R}mu(n), S_R=sum_{n<=X, P+(n)<=R}mu(n), with mu(1)=1 and P+(1)=1. Every q>R is a unique high-prime owner of all q*c<=X, c<q. Thus

    H_R = - sum_{q>R prime} M(floor(X/q));
    M(X) = H_R + S_R.

## 2. Two verified cancellations, each with a different meaning

| Independently enumerated source | R=317 | R=1027 |
|---|---:|---:|
| pi(X), total prime roots through X | 9631 | 82462 |
| squarefree integers n<=X, including n=1 | 61094 | 641207 |
| odd squarefree integers n<=X | 40726 | 427473 |
| high-prime standalone roots q>R (signed) | **-9565** | **-82290** |
| high-prime composite descendants qc (signed) | **+10452** | **+89259** |
| completed high-prime source H_R | **+887** | **+6969** |
| small-prime smooth source S_R | **-915** | **-6602** |
| **complete M(X)** | **-28** | **+367** |

FIRST: -9565+10452=+887 and -82290+89259=+6969. This is prime-root versus high-prime composite-child cancellation.

SECOND: +887-915=-28 and +6969-6602=+367. This is high-prime versus small-prime smooth-source cancellation, eliminating about 98.45% and 97.30% of the respective paired absolute component sums. These are finite census findings, not uniform arithmetic inequalities.

Odd squarefree density is 40726/100488=40.5282% and 427473/1054728=40.5292%; the classical limit is 4/pi²≈40.52847%. Density does not determine signed parity balance.

## 3. Every returned owner grouped by its exact cofactor-prefix size

Let k=floor(X/q). A_R=sum_{q>R prime}|M(k)| is the positive **completed owner** return mass, not the original #915 NNS denominator. An owner has signed HIGH response -M(k).

| k | #owners R=317 | signed H, R=317 | absolute return R=317 | #owners R=1027 | signed H, R=1027 | absolute return R=1027 |
|---|---:|---:|---:|---:|---:|---:|
| 1 | 4474 | **-4474** | **4474** | 38831 | **-38831** | **38831** |
| 2 | 1571 | 0 | 0 | 13531 | 0 | 0 |
| 3..9 | 2353 | +3138 | 3138 | 20038 | +26799 | 26799 |
| >=10 | 1167 | +2223 | 2301 | 9890 | +19001 | 19909 |
| **ALL** | **9565** | **+887** | **9913** | **82290** | **+6969** | **85539** |

Concrete k=1 primes: q=50261 (R=317), q=527377 (R=1027). Such owners have no composite children; each gives mu(q)=-1. Concrete k=2 primes: q=33503 (R=317), q=351587 (R=1027). Every such owner contributes mu(q)+mu(2q)=-1+1=0, including all 1571 and 13531 k=2 families.

More generally, 1596 (R=317) and 13831 (R=1027) complete prime-owner families have M(k)=0. They therefore contribute zero without an inequality.

But the positive returned mass satisfies

    A_R >= pi(X)-pi(floor(X/2)) = 4474 or 38831,

and PNT makes this Omega(X/log X) as X increases. Hence a *positive-only*, already owner-completed returned-HIGH norm cannot have any all-scale bound O(X^(1-eta)) for fixed eta>0. **The two opposite orientations must be compensated before a global positive payment.** That is a proved obstruction to directly transplanting Gao's positive analytic returned-row estimate to the uncombined native Mobius owner family, not an obstruction to a correctly compensated analytic method.

## 4. Finite five-prime ancestry is cheap to count

For squarefree n, ordered strictly decreasing five-prime histories correspond to five-element subsets of its distinct prime factors. Thus #histories<=binomial(omega(n),5). R=317 reaches omega=6 with n=30030=2*3*5*7*11*13, giving **6**; R=1027 reaches omega=7 with n=510510=2*3*5*7*11*13*17, giving **21**.

Fixed-depth arithmetic subhistory multiplicity is O_epsilon(n^epsilon). This statement does NOT count the extra physical #915 histories labelled by original owner, age, clip, retained VF coefficient and historical anchor; full-key injection must be proved separately.

## 5. Separate original #915 VF physical-source diagnostic

The literal VF physical odd-seat charge is w_R-1_Prime(n), **not mu(n)**. The independent #974 original physical-site probe reports the following APPROXIMATE figures, separately from the integer-exact tables above:

| #915 original physical quantity | R=317 | R=1027 |
|---|---:|---:|
| Historical raw VF defect D_R | -38.13164 | -116.13385 |
| Full anchored Co/Div excess E_R | -13423.78466 | -105561.28136 |
| Global anchor/restoring residual G_R | -7134.99589 | -57248.33925 |
| Exact-identity boundary subtotal E_R-G_R | -6288.78877 | -48312.94211 |

See [VF974_FIRST_BAD_BOUNDARY_DESCENT_OBSTRUCTION_20261018.md](VF974_FIRST_BAD_BOUNDARY_DESCENT_OBSTRUCTION_20261018.md). In both examples E_R is negative, so neither is an actual first-bad witness. These checks do **not** enumerate all actual full-key #915 returned-parent histories, prove G_R<=TransportedExcess_R, or supply the missing all-scale bound.

## Reproduce

    g++ -O3 -std=c++17 -Wall -Wextra -Werror scripts/rhlean_317_1027_five_stage_witness.cpp -o /tmp/rhlean_317_1027_witness
    /tmp/rhlean_317_1027_witness

The test computes one **direct** signed site census by largest prime factor and independently computes a second census through prime-owner M(floor(X/q)) response. It asserts their equality, all signed subfamilies, the zero k=2 packet, the positive-root lower bound, and the five-prime multiplicity. No RH-strength or improved zero-free bound is asserted.
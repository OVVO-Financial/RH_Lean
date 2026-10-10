# #925 — literal integer trace at the 317 and 1027 genuine-root witnesses

**2026-10-10. Actual integer arithmetic, not modeled pi.** Every source site in
the two original half-runs and every current square block can be independently
sieved and factorized. The root values here mean **R=317 and R=1027**, i.e.
square boundaries 100489 and 1054729; do not confuse them with x=317/1027.
A full downloadable forensic CSV/gzip bundle accompanies the research run.
This document is a finite certificate and identifies the signed cancellation.
It is NOT a proof of the open first-bad Sector Six bound or RH.

## 1. Pointwise source-to-boundary arithmetic classification

Let A=floor(R/2)+1, B=R+1, and consider each original odd source site
n with A^2<n<B^2, excluding the square boundaries. Let r=floor(sqrt(n))
and keep its literal native w_r=(2r+1)/(r log(r^2+r+1/2)).
Let S_A(n) indicate survival of the genuine odd A-prime wheel.
Let T_A(n) indicate a genuine two-distinct-prime composite n=p*q,
A<p<q, on that survivor carrier. Since B<=2A, every surviving
composite is such a semiprime; n=p^2 is correctly excluded as a
square endpoint. Define the independent odd wheel density

    rho_A = product_{3<=p<=A, p prime} (1-1/p).

The **exact integer-by-integer identity**, with no prime distribution
hypothesis, is

    1_Prime(n) = S_A(n) - T_A(n),

hence

    1_Prime(n) - w_r
       = (rho_A-w_r) + (S_A(n)-rho_A) - T_A(n).       (925-ODD)

This preserves every original VF fractional weight. An old-owner
composite has (S,T)=(0,0); a true prime has (1,0); and a late
semiprime has (1,1). Every right-hand term is constructed from
genuine arithmetic occurrences, never an independently fitted
sqrt or fantasy prime event.

**Even integers have ZERO original odd-seat physical charge.**
The parity-conditioned rho above avoids assigning any extra even
source mass. The excluded square endpoints also have zero source.
T_A(n) is charged once at n=pq. The older negative prime charges
at p and q are already present in D_A; they are not separately
re-spent as restoring capacity.

## 2. Literal half-run results

All integers were enumerated with an independent exact smallest-prime-
factor sieve; these are not prime-counting approximations. Counts are
exact integers; VF and density values below are numerical real
evaluations.

| Term | R=317, A=159,B=318 | R=1027, A=514,B=1028 |
|---|---:|---:|
| Original odd physical seats | 37,842 | 396,037 |
| True primes | 6,897 | 59,438 |
| Old-owner composite physical seats | 30,003 | 329,663 |
| Distinct late prime-pair composite physical seats | 942 | 6,936 |
| Frozen A-wheel survivors | 7,839 | 66,374 |
| rho_A (odd wheel) | .218370892567 | .178511771351 |
| Sum of deterministic (rho_A-w_r) | +1,351.612201 | +11,201.433805 |
| Sum of signed (S_A-rho_A) | -424.591317 | -4,323.266391 |
| Sum of -T_A | -942 | -6,936 |
| **Exact P-V run discrepancy** | **-14.979115** | **-57.832586** |
| Genuine historical D_A | -24.269465 | -62.465245 |
| Genuine endpoint D_B | **-39.248580** | **-120.297831** |

The physical prime/composite decomposition of the **same** actual
P-V run, each site carrying its true w_r, is:

| Literal source cohort | R=317 | R=1027 |
|---|---:|---:|
| True-prime signed (1-w_r) | +5,635.627142 | +50,500.989756 |
| True old-owner-composite signed (-w_r) | -5,481.152025 | -49,530.038901 |
| True late-semiprime signed (-w_r) | -169.454232 | -1,028.783441 |
| **Full signed sum** | **-14.979115** | **-57.832586** |

The arithmetic compensation is exact at each integer, then nearly
complete across the entire genuine run (approximately 98.89% and
99.48% of the positive deterministic bias). The residual is actual
pi-VF, not an assumed uniform upper bound.

## 3. The original one-block **quadratic** cancellation (not just the linear one)

For the final current original odd carrier R^2<n<(R+1)^2, put
z_n=w_R-1_Prime(n), preserve the single historical compressed source
z_0=-D_R, and define U=sum positives and L=sum absolute negatives.
The unchanged original NNS slack is

    B=6 U L-U^2-L^2
     =(sum |z|)^2-2(sum z)^2.

For each DISTINCT physical pair (a,b), its contribution is
2|ab|-4ab. Opposite signs contribute +6|ab|; equal signs -2|ab|.
Every physical diagonal contributes -z^2. This gives an exact
occurrence-faithful ledger:

| Original current block | R=317 | R=1027 |
|---|---:|---:|
| Genuine P_R / composite C_R | 54 / 263 | 144 / 883 |
| True w_R | .173870485 | .144268721 |
| Prior D_R | -38.131636 | -116.133854 |
| Next D_(R+1) | -39.248580 | -120.297831 |
| Opposite-sign historical anchor x true primes | +10,206.541087 | +85,863.776935 |
| Opposite-sign true composites x true primes | +12,239.812429 | +94,185.497184 |
| Same-sign historical anchor x composites | -3,487.362145 | -29,588.416270 |
| Same-sign prime x prime | -1,953.286311 | -15,079.027839 |
| Same-sign composite x composite | -2,083.093532 | -16,209.650554 |
| Current physical diagonals | -44.805197 | -123.826036 |
| Historical diagonal | -1,454.021670 | -13,487.072057 |
| **EXACT physical original Co/Div slack** | **+13,423.784662** | **+105,561.281363** |

The two positive *actual* cross-family payments total +22,446.353516
at R=317 and +180,049.274118 at R=1027. These offset negative
signed pairs/diagonals of -9,022.568854 and -74,487.992755.
This specifically identifies WHICH original source interactions
produce the observed compensation, without enlarging the NNS
denominator or making a prime ancestor pay more than once.

## 4. Trace the prime-owner event for **each** physical integer

Starting at the parity-only stage, all R odd physical sites are
temporarily **unclassified** and carry a virtual prime charge w-1.
Each real composite n is reclassified **once**, at its genuine least
prime owner p<=R, into its final +w. The virtual preclassification
is NOT a claim those composites are actual primes.

For one site changing from -(1-w) to +w, if U,L are the current
positive/negative masses *before* changing that site, we prove

    delta B =
      (1-2w)                     [site diagonal]
      +(2+4w)*(L-(1-w))          [positive with remaining negatives]
      -(6-4w)*U.                 [negative with prior positives]

The actual least prime factor fixes the first removal event and the
**original historical anchor remains in U or L throughout**. Under
t previously recognized composites the next delta decreases by
(2+8w(1-w))*t relative to the first delta. This last affine form
makes explicit that the event-local algebra alone is NOT a
distributional proof: owner incidence fixes the order and total t,
but cannot guarantee a first-bad budget sign without historical
arithmetic.

The verified **actual ascending stages** are:

| Stage | R=317 | R=1027 |
|---|---:|---:|
| After owner 2 (parity only) | -10,120.580460 | -173,464.141270 |
| After owner 3 | +25,572.580287 | +211,608.388513 |
| After owner 5 | +29,927.699906 | +267,179.197484 |
| All genuine prime owners completed | **+13,423.784662** | **+105,561.281363** |

Actual owner 3 reclassifies **106** and **343** distinct composite
integers, respectively, changing provisional slack by
+35,693.160746 and +385,072.529783. Owners after the early
restoring phases also contribute negative net changes. We must
keep these FULL cross-owner products: an owner-by-owner nonnegative
payment is not a valid theorem.

In the FINAL true current block, **192** and **659** composite sites
respectively contain a genuine historical prime factor q>R,
with exact odd cofactor c=n/q<=R. Each such q is determined and
existed before R^2. A given historical q can have multiple
descendants in a longer run and its original negative historical
charge is nevertheless kept ONCE inside D_A / D_R.

## 5. New kernel proof and exact research boundary

The branch now proves the generic finite identities

- vfWilesFrozenWheelOddSeat_pointwise
- vfWilesFrozenWheelOddSeat_sum
- vfWilesOwnerReclassification_event_delta
- vfWilesOwnerReclassification_event_affine

The native factorization result on main that needs to be imported
for the actual-prime specialization is the existing
vfMidSquareBandPrefixComposite_survivor_eq_two_primes_of_subdoubling
(and the matching weighted true source census). The Mathlib-only
generic theorems need no RH assumption. They prove arithmetic
transport and exact event sensitivity, **not** the new sharp
historical signed cancellation inequality.

**What has NOT been obtained:** a uniform O(R log R) bound on
the cancellation remainder, a common floor-Li/prime stable-class
representation, or a signed original six-sector first-bad
nonpositive payment. The observed small residual cannot be
asserted for hypothetical first-bad endpoints. Full per-integer
CSV/gzip audits and replay scripts are available separately.

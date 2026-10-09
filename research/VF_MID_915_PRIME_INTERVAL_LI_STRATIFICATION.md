# #915 — Genuine prime intervals relative to √x, with exact discrete-Li matching

**October 8, 2026. Status: proof progress, NOT RH.**

This is the prime-sector refinement of the earlier actual-owner ↔ floor-Li
signed-transport interface. It directly answers: can we partition prime
owners relative to √x or arbitrary intervals, then use discrete Li on
ACTUAL prime counts in each physical interval?

**YES, exactly.** The partition can even follow the precise odd-cofactor
multiplicity of each actual composite descendant. However, the signed
errors remain genuine prime-distribution information and cannot be set
to zero by the exactness of the model.

## 1. The general √x stratification

Fix R and X=(R+1)^2-1. Every true prime q>R satisfies q²>X,
so it can divide at most one prime factor occurrence in any
n≤X. Each ODD physical site n=c*q with such a q satisfies

    c odd, 1≤c≤R,
    max(R,floor(R²/c))<q≤floor(X/c).

The intervals

    I_(R,c)=(max(R,⌊R²/c⌋),⌊X/c⌋]

are prime-counting windows, with ACTUAL population

    A_(R,c)=π(⌊X/c⌋)-π(max(R,⌊R²/c⌋)).

c=1 is the genuine current prime-seat population.
c odd≥3 is the actual composite descendant of a prime q>R; the
composite receives the ORIGINAL VF physical charge +w_R
even when c is squareful. The cofactor c is NOT reweighted by μ(c)
in this ordinary physical VF seat ledger.

For each arbitrary interval (a,b], define the exact integer Li demand

    F(a,b)=⌊Li₂(b)⌋-⌊Li₂(a)⌋

and true discrepancy E(t)=π(t)-⌊Li₂(t)⌋.
Then in EVERY cofactor stratum:

    A_(R,c)=F(I_(R,c))+E(b_(R,c))-E(a_(R,c)).

Thus all moving prime-owner intervals have been transferred to the
genuinely unmatched discrete-Li event boundary at their own endpoints.

The new Lean module
research/VF_MID_915_PRIME_INTERVAL_LI_STRATIFICATION.lean
formalizes this exact arbitrary-window decomposition,
its cofactor-specific specialization, and exact finite SUM
with original physical VF scalar weights (w_R−1 for c=1,
w_R for every odd composite c≥3).
The finite regression verifies the **additional unique large-prime
factor property** and matches its assembled charge against
literal independently scanned square-block physical sites.

## 2. Concrete prime data at R=317 and R=1027

These are exact integer results, not approximate PNT formulas.

| odd cofactor c | R=317 prime q interval | actual primes | floor-Li events | error | R=1027 prime q interval | actual primes | floor-Li events | error |
| ---: | --- | ---: | ---: | ---: | --- | ---: | ---: | ---: |
| 3 | (33496,33707] | 23 | 20 | +3 | (351576,352261] | 52 | 53 | -1 |
| 5 | (20097,20224] | 15 | 13 | +2 | (210945,211356] | 35 | 34 | +1 |
| 7 | (14355,14446] | 10 | 9 | +1 | (150675,150969] | 24 | 25 | -1 |
| 9 | (11165,11235] | 5 | 8 | -3 | (117192,117420] | 20 | 20 | 0 |
| 11 | (9135,9193] | 7 | 7 | 0 | (95884,96071] | 17 | 16 | +1 |
| 13 | (7729,7778] | 4 | 5 | -1 | (81133,81291] | 12 | 14 | -2 |

All odd cofactors c from 3 through R together:

| R | actual composite descendants with q>R | accumulated floor-Li cofactor events | signed actual-minus-Li error | positive interval errors | negative interval errors |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 317 | 192 | 204 | **-12** | +50 | -62 |
| 1027 | 659 | 648 | **+11** | +144 | -133 |

**This exposes arithmetic cancellation across cofactor intervals.**
Individual errors of both signs, including nonzero |errors| in many
short bands, nearly cancel in the complete signed aggregate:
+50-62=-12, +144-133=+11.

Using actual original composite VF weights w_R=V_R/R, the corresponding
signed cofactor residual charges are approximately:

    R=317:  w_R * (-12) = -2.086446
    R=1027: w_R * (+11) = +1.586956.

These are real signed one-block corrections, **not an all-R bound**,
not a proven hbalance payment, and not the same as the full
R/2..R historical residuals 15 and 58. Each prime-interval
Li demand must retain its multiplicity over all physically occurring
cofactors; overlapping q-intervals can count the SAME q several
times because the distinct sites c*q are themselves distinct.

## 3. Hierarchical relation to √x and previous square anchors

Take a=floor(R/2)+1. The already-compiled geometric theorem states:

- For actual q>=a² and ODD c>=3 with n=cq inside the current
  square band, necessarily c=3.
- For R>=16 every actual current 3q has its prime q within
  the explicit historical half-scale run.
- Every odd c>=5 forces the prime q<a² and hence the q-prime
  ancestor into earlier history already compressed into D_a.
- At the opposite extreme q>X/3 has no proper ODD cofactor,
  so it contributes a genuine prime site but no extra current odd
  composite site.

Thus sqrt(X) describes the unique large-prime-factor cutoff,
X/3 describes the parity-reduced inert top prime sector,
and a² describes the exact historical compression frontier.
All can be represented by the SAME generic interval floor-Li
comparison without inventing a new prime-probability model.

## 4. Further exploratory all-cofactor R-scan

As a separate numerical stress test (NOT a formal theorem), I scanned
every square block R=8,...,2000, using an exact prime sieve and
vectorized evaluation of the integer Li₂ staircase at every
cofactor-window endpoint. The 317 and 1027 cohorts and the worst-case
positive/negative windows were independently spot-checked against
45-digit mpmath Li floor calculations; there were zero floor
disagreements at the checked endpoints.

Let

    E_comp(R) = sum_(odd 3<=c<=R)
      [(π(hi_c)-π(lo_c))-(⌊Li₂(hi_c)⌋-⌊Li₂(lo_c)⌋)],

with lo_c=max(R,floor(R²/c)), hi_c=floor(X/c).
Denote the sum of all POSITIVE cofactor errors by P(R), the magnitude
of all NEGATIVE cofactor errors by N(R). Then

    E_comp(R)=P(R)-N(R),

and the algebraic cancellation against the cofactor-wise raw absolute
errors is exactly

    [P(R)+N(R)]-|E_comp(R)| = 2 min(P(R),N(R)).

This is *not* the production Co/Div cancellation. It is only the
composite-prime cofactor Fubini sector of the current VF source.

| R | actual high-prime composites | Li cohort events | P(R) | N(R) | net E_comp(R) | cofactor absolute-saving count |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 56 | 34 | 35 | 7 | 8 | -1 | 14 |
| 79 | 41 | 47 | 12 | 18 | -6 | 24 |
| 119 | 80 | 72 | 24 | 16 | +8 | 32 |
| 317 | 192 | 204 | 50 | 62 | -12 | 100 |
| 1027 | 659 | 648 | 144 | 133 | +11 | 266 |
| 1760 | 1169 | 1134 | 291 | 256 | +35 | 512 |
| 2000 | 1270 | 1294 | 293 | 317 | -24 | 586 |

Across the consecutive R=8..2000 scan:
  - 739 blocks had positive cofactor residual;
  - 1180 had negative residual;
  - 74 had exactly zero residual;
  - maximum +52 at R=1861 (actual 1215, Li 1163);
  - minimum -52 at R=1953 (actual 1219, Li 1271).

Numerically this cofactor-window error remains much smaller than the
total individual absolute window errors, and it changes sign.
However, an observed |E_comp(R)|<=52 up to R=2000 is emphatically
NOT an all-scale bound. The near-perfect cofactor compensation
must be justified by a genuine arithmetic correlation theorem
if it is to enter #915 hbalance.

## 5. NEW: telescope prime-cofactor history FIRST, then Abel-transform Li errors

A more significant consequence of stratifying relative to the native
sqrt scale is **exact historical cancellation at fixed cofactor**.

For a genuine odd cofactor c>=3 and historical square-root run a<=r<B,
its ACTUAL q>r-prime descendants can occur only for r>=c.
Thus the earliest possible native historical square block is

    r0(c)=max(a,c).

When r>=c, the condition c*q>r² forces q>r automatically. Moreover
if q>r is prime and c<=r then c*q cannot equal (r+1)²:
since q|((r+1)²), primality forces q|(r+1), hence q=r+1, but
c<=r makes c*q<(r+1)². This is formally stated as

    vfMid915PrimeCofactorSquareEndpoint_excluded
    vfMid915PrimeCofactorSquareBand_iff_physical

in the revised Lean module.

**As a result, the entire historical sequence of SHORT prime windows
for fixed c telescopes to ONE BROAD actual-prime interval:**

    sum_(r=r0(c))^(B-1)
      [π(⌊(r+1)²/c⌋)-π(⌊r²/c⌋)]
    = π(⌊B²/c⌋)-π(⌊r0(c)²/c⌋).

The actual prime count is unaffected by including the CLOSED upper
quotient face because no ACTUAL q-prime can occur on that square face.

CAVEAT: floor-Li CAN have events on those quotient faces. To preserve
correct Fubini one must also use the CLOSED quotient-face
floor-Li demand Q(⌊(r+1)²/c⌋)-Q(⌊r²/c⌋).
Those "Li-only" square-face jumps remain in the genuine signed
E(q) boundary and are NOT synthetic prime occurrences. If one used
OPEN upper q faces for the Li comparison, an additional deterministic
square-boundary correction would be mandatory.

### Literal native VF weights retained in the historical transport

The source charges the actual site c*q with ORIGINAL native w_r,
which varies across historical blocks. Writing

    E_c(r)=π(⌊r²/c⌋)-⌊Li₂(⌊r²/c⌋)⌋,

the signed ACTUAL-minus-floor-Li weighted history for fixed c is

    sum_(r=r0)^(B-1) w_r [E_c(r+1)-E_c(r)].

Abel's finite summation gives the exact identity

    = w_B E_c(B) - w_r0 E_c(r0)
      + sum_(r=r0)^(B-1) (w_r-w_(r+1)) E_c(r+1).

This is new theorem
vfMid915HistoricalCofactorTransportError_eq_endpoints_add_variation
in research/VF_MID_915_PRIME_INTERVAL_LI_STRATIFICATION.lean.
The generic finite sum identity is
vfMid915ExactWeightedAbel.

**The historical prime-owner fluctuations have genuinely been compressed
into boundary backlogs plus a smooth weight-VARIATION term, without
ever replacing the earlier anchor D_a by its enormous historical
absolute mass.**

This does NOT mean that the remaining cofactor-summed boundary
backlogs have already been bounded at RH scale. Their arithmetic signs
and cross-cofactor/time correlations remain difficult.

### Actual-prime numerical check for historical half-runs

Independent initial numerical exploration used an actual sieve and
closed-quotient interval floor-Li comparisons (SciPy Ei). It verifies
telescoping of each fixed-c prime population and the Abel identity
for the original native w_r. The new checked-in standalone Python
regression reproduces the physical uniqueness and selected cofactor
Abel identities without SciPy.

| Historical run | c | native r0 | full actual q prime interval | actual q count | floor-Li event count | signed difference |
| --- | ---: | ---: | --- | ---: | ---: | ---: |
| a=159..317 | 3 | 159 | (8427,33707] | 2556 | 2561 | -5 |
| a=159..317 | 5 | 159 | (5056,20224] | 1610 | 1621 | -11 |
| a=159..317 | 9 | 159 | (2809,11235] | 948 | 961 | -13 |
| a=514..1027 | 3 | 514 | (88065,352261] | 21604 | 21616 | -12 |
| a=514..1027 | 5 | 514 | (52839,211356] | 13532 | 13536 | -4 |
| a=514..1027 | 9 | 514 | (29355,117420] | 7891 | 7918 | -27 |

Summed over ALL odd cofactors c>=3 through R, counting EVERY
historical q>r composite occurrence once:

| Historical run | original high-prime physical sites | summed Li cofactor events | net signed count error | native VF-weighted actual composite charge | native VF-weighted Li charge | signed VF difference |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 159..317 | 23240 | 23680 | -440 | +4244.102778 | +4324.636570 | -80.533792 |
| 514..1027 | 250542 | 252429 | -1887 | +37634.432530 | +37919.220650 | -284.788121 |

These historical cofactor counts are **not** the previously used
fixed global q>R (rather than q>r) high-prime-factor population, so
one should not compare the two totals without correcting the root
cutoff. The current native root is r on each historical block.

This is a real step beyond the earlier one-block mismatch experiment:
the temporal sum over r has been ELIMINATED at each fixed cofactor
in exact arithmetic. PNT can now see a relatively broad prime window
when c is fixed and B/r0 is bounded away from 1; the remaining
large-c/high-frequency coefficients and signed interplay must still
be estimated. One cannot apply PNT to the original individual
O(r/c) short prime windows as if that were a proven local asymptotic.

## 6. Why this is useful but not an automatic RH theorem

The generic floor-Li identity is exact for all intervals. It cannot
force the actual count to be near the floor-Li demand in an interval
of length approximately 2R/c at prime argument q~R²/c.

Ordinary PNT gives asymptotics in fixed relative-scale windows;
it does not supply RH-strength errors in all these short
cofactor-selected intervals. Substituting floor-Li as if it WERE
the actual prime distribution would simply assume the missing
arithmetic saving.

Even the observation that positive and negative cofactor-band
errors nearly cancel at 317 and 1027 is not sign-definite across
all R: the aggregate residual changes sign (-12 vs +11).

The promising new target is a weighted TWO-INDEX boundary estimate:

    sum_{r=a}^R sum_{odd c>=3} w_r
       [E(⌊((r+1)^2-1)/c⌋)
        -E(max(r,⌊r²/c⌋))],

where current square-block and historical-anchor restoration are
retained exactly once. Any proof must avoid reintroducing historical
absolute mass or asserting individual short-interval gaps.

The exact previous #915 signed primitive transport already compresses
the FULL historical moving-owner packet into an endpoint backlog.
The new cofactor stratification supplies a *second, sharper* native
coordinate for seeking aggregate cancellation of prime anomalies
across both cofactor and time.

This is an investigative arithmetic route, not an inequality proof.

## Verification and files

- New Lean: research/VF_MID_915_PRIME_INTERVAL_LI_STRATIFICATION.lean
- New prime/composite regression:
  scripts/vf_mid_915_prime_interval_li_regression.py
- Original first-bad endpoint transport:
  research/VF_MID_915_FLOOR_LI_TRANSPORT_BOUNDARY.lean
- Existing actual prime/floor-Li transport:
  research/VF_MID_FLOOR_LI_TRANSPORT_CANCELLATION.lean
- Existing actual historical site compression:
  research/VF_MID_FIRST_BAD_HISTORY_COMPRESSION.lean

**Remaining #915 gate is unchanged:** prove the first-bad-specific
quantitative Co/Div payment (hbalance), not another equivalence.

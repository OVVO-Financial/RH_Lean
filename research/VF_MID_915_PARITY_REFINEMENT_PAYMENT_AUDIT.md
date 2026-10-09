# #915 — Signed quantitative audit of real middle owners and parity refinement

**Status: new exact arithmetic and NNS payment constraints; the production `hbalance` is NOT proved.**

## 1. What the x/2 threshold proves, and what it does not

Let `X=(R+1)^2`, `B=R+1`, and `q` denote a **genuine actual prime factor**.
The complete-integer factor buckets are:

- `q<=B`: small least-prime sieve owners;
- `B<q<=X/2`: at least the proper composite `2q<=X`;
- `q>X/2`: no proper multiple `cq<=X`, for any `c>=2`.

Within the middle bucket the thin layer `X/3<q<=X/2` has exactly one
proper multiple, `2q`. This is an actual even composite removed by owner
2 and is absent from the original odd-seat VF source. The older `x/3`
cutoff was correct only for the **odd carrier**, not the full integer system.

Furthermore the current square block is entirely terminal: for `R>=2`,
every integer `q>R^2` satisfies `2q>(R+1)^2`. At `R>=3`, all
`q<=X/2` are already **strictly below** `R^2`, hence historical.
Consequently the q-to-2q relationship is necessarily cross-block
for the current first-bad payment.

The actual integer mismatch remains genuinely arithmetic:
`xi_n = 1_prime(n) - (Q(n)-Q(n-1))`. A floor-Li-only event `xi_n=-1`
may be at **composite** n; do NOT assign such an event a fictional
prime owner `q=n` or an actual `2q` prime-parent edge. The split
at `X/2` is initially a split by event LOCATION, not by prime
factorization of the floor-Li benchmark.

## 2. Literal original VF cost: even 2q contributes ZERO

Already compiled in `VF_MID_915_LATE_PREFIX_WEIGHTED_DYADIC.lean`:
`vfMid915CurrentOddWeight_even_zero` and
`vfMid915ActivePhysicalSite_even_zero`. The new Lean module
`VF_MID_915_TERMINAL_TOP_THIRD_TRANSPORT.lean` has the integrated
historical sum theorem

`vfMid915MiddleDoubleHistoricalOriginalVFAbs_eq_zero`.

This charges all proposed even `2q` occurrences in the **original
native odd source** and proves their absolute contribution is ZERO.
A full integer `2q` exists geometrically, but it has no independent
negative original VF/NNS capacity. Restoring one requires an explicit
even-inclusive reference and its exact source/denominator correction.

## 3. Audit one possible even-inclusive restoration, rigorously

This is a **surrogate parity-neighbor refinement**, NOT a claim that
an odd n and its EVEN NEIGHBOR are the same multiplicative q-to-2q pair.
It tests the precise price of turning on an even partner in one native
square band without changing its signed VF source.

In the R-th square band let `w=w_R=V_R/R`, `b=1_prime(n)` on an
original odd candidate n, and `z=w-b`. Split the signed contribution
into

    z_odd = w/2 - b,
    z_even = w/2,
    z_odd + z_even = z.

For R>=3, `0<=w<=1`, so pointwise:

    |z_odd| + |z_even| = |z| + w*b.

The native current absolute source `A_R=sum_odd |z|` therefore
changes by the EXACT premium

    delta_R = w_R * P_R.

If the previously compressed historical anchor remains the same
`D_R`, the original anchored NNS square mass
`M_R^2=(|D_R|+A_R)^2` would be inflated to
`(|D_R|+A_R+delta_R)^2`, at exact cost

    PRICE_R = 2 * M_R * delta_R + delta_R^2.

This is now stated as Lean
`vfMid915ParityRefinedCurrentNNSMass_eq_original_add_exactPrice`.
No new historical absolute mass is spent.

At an actual PRIME odd site, the favorable opposite-sign NEIGHBOR-pair
local cross heat equals its **own** squared absolute-mass inflation:

    -4*(w/2-1)*(w/2) = 2w-w^2
    = (|w/2-1|+|w/2|)^2 - (w-1)^2.

At an odd composite site the local absolute-norm inflation is zero.
Summed over genuinely ACTUAL current-block primes:

    LOCAL_HEAT_R = (2w_R-w_R^2) * P_R.

These are exact Lean theorems in
`VF_MID_915_PARITY_REFINEMENT_EXACT_PRICE.lean`.
Crucially the NEIGHBOR local heat is NOT a proven occurrence-matched
multiplicative q-to-2q Co/Div return. This is only the most literal
one-band parity-refinement test.

### A quantitative **NO FREE PAYMENT** inequality

The original odd-seat absolute source necessarily satisfies

    M_R >= (1-w_R)*P_R.

Consequently, by elementary algebra,

    PRICE_R >= P_R * LOCAL_HEAT_R.

This is the theorem
`vfMid915ParityRefinedGlobalPrice_ge_primeCount_mul_localHeat`.

The inequality goes in the **opposite direction from the desired free
payment**. Even the surrogate's full local heat is swamped by the
global original-denominator restoration cost unless P is exceptionally
small. It does not rule out a genuinely global **cross-block** signed
return, which must use real matched occurrences, authentic VF native
weights at q and 2q, and the original compressed anchor. It DOES rule
out spending the surrogate local heat with no mass restoration.

### Independent actual-prime sample

| Quantity | R=317 | R=1027 |
|---|---:|---:|
| Actual current prime supply P_R | 54 | 144 |
| Native odd-seat w_R | 0.173870485 | 0.144268721 |
| Original anchored M_R | 128.470567 | 366.748439 |
| L1 parity-refinement premium w_R P_R | 9.389006 | 20.774696 |
| Full NNS squared-mass price PRICE_R | **2500.575341** | **15669.762522** |
| Sum of local neighbor-pair heat LOCAL_HEAT_R | 17.145541 | 38.552253 |
| PRICE / LOCAL_HEAT | **145.84** | **406.46** |

All numbers are calculated from genuine prime sieves and ORIGINAL
w_R and D_R, not a Li density. The independently enumerated
`scripts/vf_mid_915_top_third_sector_restoration_regression.py`
verifies the native prime/composite population, full signed VF
restoration, exact cofactor Abel cancellation, parity split, local
heat, and squared denominator price.

## 4. Why this does not complete hbalance

The original production objective remains

    2 * D_(R+1)^2 <= M_R^2

under hfirst and the genuine first-bad hypotheses alone.

Restoring the even 2q partner in a full integer representation creates
**neither an independent original VF charge nor a free negative Co/Div
capacity**. Moreover every current prime seat is above X/2, so no
current prime can have 2q inside the clock. Any successful physical
payment must be **global and historical**, preserving the cost of
returning from a full integer intermediary to the original odd
denominator. The exact signed Li/cofactor/smooth conservation does not
supply the missing first-bad inequality.

The **genuinely terminal** actual-prime discrepancy on (X/2,X] is
a strong arithmetic object, not a bookkeeping artifact. A UNIFORM
`O(sqrt(X)log X)` bound for the corresponding prime-minus-Li
discrepancy on every dyadic half interval would, by telescoping over
`X,X/2,X/4,...`, imply the global von Koch/RH-scale bound. Thus simply
assuming a short terminal-event lifetime or such a bound would be
circular.

## 5. Status and exact next target

Signed quantitative theorem actually established in the new module:

    PRICE_R >= P_R * LOCAL_HEAT_R.

This gives an explicit *obstruction*, not the desired favorable
source payment. The next unproved step is a real **historical and
current** occurrence-matched low-owner / post-root factor Fubini with
nonlocal cross terms and the original NNS squared denominator.
Any successful `hbalance` proof must get its missing signed gain from
that nonlocal arithmetic, not from zero-weight even 2q mates or an
unpaid parity refinement.

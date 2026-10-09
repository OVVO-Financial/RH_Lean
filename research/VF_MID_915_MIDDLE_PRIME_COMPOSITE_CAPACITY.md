# #915 — A new *positive* native capacity inequality for genuine 2q middle parents

## Governing parity-compressed identity — production invariant

This module's middle-prime counts are **not** an additional physical
source. For every R>=3 the complete square-block expected prime mass
V_R already lives on exactly R ODD candidate seats with
w_R=V_R/R. Every even seat is absent from the production first-bad
carrier, and contributes zero to its original signed/absolute NNS
source. In particular 2q can NEVER be credited as a new negative
partial-moment or Co/Div return.

Write D_R=pi(R^2)-VF_mid(R^2), P_R for the true current prime count,
and C_R=R-P_R. The original anchored partial masses are EXACTLY

    U_R = max(-D_R,0) + w_R*C_R
    L_R = max( D_R,0) + (1-w_R)*P_R.

Thus U_R-L_R=-D_(R+1) and the ORIGINAL denominator is

    M_R^2 = (U_R+L_R)^2
          = (|D_R|+w_R*C_R+(1-w_R)*P_R)^2.

Here M_R^2 is **squared anchored L1 partial mass**, not a
probabilistic variance. The required payment is

    (U_R+L_R)^2 - 2*(U_R-L_R)^2 >= 0.

The actual R>=62 count inequality H_R<=C_R does not give this
signed quadratic inequality. It is a combinatorial comparison between
DIFFERENT populations, not an occurrence-matched weighted return, and
no fabricated even-site charge may fill the gap.


**Statement and proof structure:** The current R-th square band has R actual
odd VF candidate seats, partitioned into P_R actual primes and C_R=R-P_R
actual odd composites. Set

    k_R = floor(R^2/2)
    H_R = pi(k_R+R)-pi(k_R).

An ACTUAL prime q contributes to H_R if and only if its genuine EVEN
semiprime 2q lies strictly in the CURRENT physical square band
(R^2,(R+1)^2). At R>=4, all these q are >R and <R^2; their
primality and chronology are true arithmetic, not Li-event surrogates.

**Proven by elementary wheel estimates for all R>=62:**

    P_R <= 8*(floor(2R/30)+1)   [real full 30-wheel on current primes]
    H_R <= 2*(floor(R/6)+1)    [real 6-wheel on middle q primes]

and the explicit integer inequality

    8*(floor(2R/30)+1) + 2*(floor(R/6)+1) <= R  (R>=62).

Consequently,

    ================================
    P_R + H_R <= R
    H_R <= C_R,
    w_R H_R <= w_R C_R.
    ================================

The last bound uses the ORIGINAL native VF scalar w_R, so it certifies
that the CURRENT positive odd-composite source has ENOUGH REAL,
NON-OVERLAPPING source mass to allocate one w_R donor for each actual
middle prime parent q whose even 2q child belongs in the current band.
This allocation is not automatically an occurrence-tagged matching and
does not independently create a legitimate Co/Div heat term.

**Finite boundary:** R=4..61 is independently prime-sieved; all satisfy
P_R+H_R<=R, with equality at R=4 and R=6. The Lean theorem has R>=62
as its explicit premise until the finite boundary is kernel checked.
The unbounded mathematical argument is independent of the numerical audit.

**Numerical examples (genuine actual primes and composites):**
Run the new
`scripts/vf_mid_915_middle_prime_composite_capacity_regression.py --extended`
for every R=4..6000, and real site scans at selected R.

## Stronger genuine *signed* historical/current payment diagnostic

One current positive odd-composite site carries +w_R. Each ACTUAL
historical prime q has its original negative prime-seat charge
-(1-w_{floor(sqrt(q))}), at its TRUE native square-root band. These
weights differ by scale, and q itself is contained in the compressed
historical D_R. The genuinely signed first-order packet to control is

    S_R = w_R*(R-P_R)
          - sum_{R^2/2<q<=R^2/2+R, q prime}
              (1-w_{floor(sqrt(q))}).

This is NOT the scalar residual of the complete D_R NNS source:
it compares a selected TRUE historical negative packet against the
entire TRUE positive current odd-composite packet. Neither any q nor
any composite is invented. It gives no permission to expand D_R's
historical absolute mass.

The new regression checks **every actual R=8..6000** and finds S_R>0
(with minimum about +0.9433 at R=21):

| R | H_R actual q parents | Historical negative charge | Original current positive charge | S_R |
|---:|---:|---:|---:|---:|
| 8 | 1 | 0.4221 | 1.9843 | +1.5622 |
| 317 | 29 | 23.6314 | 45.7279 | +22.0965 |
| 1027 | 73 | 61.9120 | 127.3893 | +65.4773 |
| 5266 | 327 | 287.2260 | 535.8118 | +248.5858 |
| 6000 | 356 | 313.3757 | 609.5042 | +296.1286 |

**This signed estimate is NOT kernel proved for all R.**
Indeed H_R<=C_R is insufficient to establish it: each negative
historical prime carries roughly ONE unit while a positive current
composite carries only about 1/log R. The fixed 6-wheel bound on H_R
is O(R), whereas the positive charge w_R*C_R is O(R/log R).
A much stronger **actual-prime distribution / owner-correlation**
bound is needed for this weighted inequality, and still more for
the full historical NNS quadratic. A finite sample cannot replace it.

**Critical limitation:** This is *first-order real physical positive source
capacity*, not the unresolved second-order first-bad NNS comparison.
The historical negative prime q lives inside the compressed D_R scalar,
and cannot be decompressed for free; the physical donor need not be a
multiplicative descendant of q. The source-to-historical-parent map,
retained weights and signs, exact compression restoration, and a
first-bad-specific global bound are still necessary before any paired
heat can be spent in production `hbalance`.

**Proof file:** `research/VF_MID_915_MIDDLE_PRIME_COMPOSITE_CAPACITY.lean`.
The repository's native wheel theorem supplies both estimates.
No RH claim.

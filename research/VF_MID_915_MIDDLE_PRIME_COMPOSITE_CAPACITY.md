# #915 — A new *positive* native capacity inequality for genuine 2q middle parents

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

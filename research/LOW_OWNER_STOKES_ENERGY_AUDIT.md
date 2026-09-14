# LOW-A: what the Stokes energy calculation does and does not prove

Base: PR #706, commit `9a19b92e08feffae2fd70527f059e9ca95e04d87`.

**Milestone 2 is not proved.** No uniform constants A and C are supplied here.
The low/high q² daughter-energy localization remains valid. The proposed
negative Dirichlet-energy approach needs an arithmetic cancellation estimate
after full signed reassembly; the Stokes identity alone does not give one.

## Two distinct prime indices

Write `B_p = p Delta_p` for the chronological Stokes charge. The exact identity is
`Corr_R = sum_p B_p`, over the complete descending prime schedule through
`X_R = R²-1`. By contrast, q in LOW-A indexes the complete daughter
`M(floor(X_R/q²))`. Filtering the latter energy by `q² < R` does not filter the
former chronology by `p² < R`.

An exact integer execution of the definitions gives, at R=56:

| Quantity | Value |
| --- | ---: |
| M(55), M(3135) | -2, 6 |
| Corr_56 | -8 |
| Daughter values for q=3,5,7 | 2, -1, -1 |
| Q_low | 6 |
| Stokes charges at p=3,5,7 | 0, 0, 0 |
| Full Stokes diagonal sum B_p² | 321418 |
| Full off-diagonal sum 2 B_p B_r, p<r | -321354 |
| Full signed energy | 64 |

These full-chronology numerical values are diagnostic calculations, not Lean
certificates. The script `scripts/LowOwnerStokesAudit/verify.py` executes the
actual carrier removal and coefficient updates, checks threshold/range-exit
and mismatch identities at every prime, and checks the final Mertens identity.
It uses exact integers and rational numbers throughout.

## Physical one-step energy growth

The Lean module `RHLean/Proof/CanonicalRoughStokesEnergyObstruction.lean`
formalizes the first-step calculation on the existing physical definitions.
For R=56 the first descending prime is 3121. Its parent set is `{1}` and its
boundary is the count of primes in [56,3135], namely 429. Consequently:

```
raw before       = -8
raw next         = -437
reciprocal next  = -8 - 429/3121 = -25397/3121
```

The reciprocal squared energy increases by the strictly positive rational
`21606585 / 9740641`. Thus even the reciprocal update is not automatically
energy-decreasing on the actual Möbius state.

The governing compiled identity is

```
reciprocal next - raw next = (1 - 1/p) B_p.
```

A quadratic telescope must retain this state-memory term. This example does
not disprove a global signed Dirichlet representation with a controlled
remainder; it disproves the shortcut that each displayed Euler step already
supplies dissipation.

## A global obstruction to separately bounding the Stokes diagonal

The following is a mathematical consequence of the first-step formula and
standard unconditional PNT/strong-Mertens estimates. The asymptotic argument in
this section is **not formalized in the new Lean module**.

Let `D_R = sum_p B_p²` on the complete descending chronology. There cannot be
fixed nonnegative A,C such that, for every admissible lower envelope K,

```
D_R <= A Q_low(R) + C R² K.
```

Proof:

1. The first prime is the largest prime at most X_R. For sufficiently large R,
   it exceeds X_R/2 and R. The exact singleton-parent theorem shows that its
   charge is `pi(X_R)-pi(R-1)`. Hence
   `D_R >= (pi(X_R)-pi(R-1))² ~ R⁴/(4 log² R)`.
2. The envelope K=R is admissible: for every y<R,
   `|M(y)-1| <= y+1`, so `(M(y)-1)² <= R(y+1)`.
3. Every low daughter cutoff is at least R: indeed q²<R implies
   `q² <= R-1`, while `X_R=(R-1)(R+1)`.
4. The unconditional estimate `M(t)=O(t/log² t)`, uniformly for t>=R as R
   grows, gives
   `Q_low(R) = O(R⁴/log⁴ R)`, since `sum_q q^(-4)` converges.
5. For this admissible K, both `A Q_low(R)` and `C R³` are
   `o(R⁴/log² R)`, contradicting step 1.

The repository supplies stronger-than-logarithmic Mertens decay in
`strongNativeMertensSubexp`; the prime-count asymptotic is part of its native
PNT development. For an external primary reference on the unconditional
Mertens estimates, see Lee and Leong,
[New explicit bounds for Mertens function and the reciprocal of the Riemann zeta-function](https://arxiv.org/abs/2208.06141).

This obstruction concerns D_R, not Corr_R². It proves that the large Stokes
diagonal must cancel with its signed cross terms before comparison with LOW-A.
The exact surviving expression is

```
Corr_R² - A Q_low(R)
  = D_R + 2 sum_{p<r} B_p B_r - A Q_low(R).
```

Controlling this joint expression uniformly remains the unresolved arithmetic
estimate. Neither the first-step counterexample nor the diagonal obstruction
supplies a finite A for it.

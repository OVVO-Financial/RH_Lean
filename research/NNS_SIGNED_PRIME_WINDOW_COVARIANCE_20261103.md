# Signed NNS Co–Div on the complete moving prime-window source

**2026-11-03 — native integer Euler/Möbius research packet.** Status:
`IDENTITY_ONLY + FINITE_REGRESSION`. The required uniform signed estimate is
**OPEN**. This packet does not establish a new exponent, RH, or an original
Eisenstein-ideal Gaussian/OAI-type intertwiner. It is an independent
arithmetic candidate beyond the source-dependent finite-slot tilt now merged
through PRs #1073–#1077; it is **not** a replacement for their proofs.

## Source and previous certified identities

Use the exact integer source already formalized in

- `research/EULER_ADMISSIBLE_PRIME_POPULATION_CODIV_20261028.lean`:
  `eulerAdmissiblePrimeDebt_eq_actual_prime_sum`,
  `eulerAdmissible_endpoint_eq_low_add_innovation`;
- `research/EULER_THREE_STRATUM_SQUARE_SAMPLING_20261028.lean`:
  `eulerThree_endpoint_eq_three_strata`,
  `eulerThree_sampledSixTermGram`;
- `research/EULER_ADMISSIBLE_WEIGHTED_CODIV_20261028.lean`:
  `eulerHybridStrictCross_eq_admissible_weighted_Co_sub_Div`;
- `research/EULER_HYBRID_TRIANGULAR_GRAM_20261027.lean`:
  `eulerHybridDiagonal` and signed strict cross.

All integer Möbius signs are the actual coefficients. Do not replace moving
prime intervals by Li, assume independent signs, or silently identify them
with original OAI ideal-character phases.

Let `X_R=R^2-1`, `Y_R=(R+1)^2-1=R^2+2R`, and
`M(y)=sum_{1<=n<=y} mu(n)`. Write

```text
T_R = sum_{R<=p<=X_R, p prime} M(floor(X_R/p))
L_R = M(X_R) + T_R
M(X_R) = L_R - T_R.
```

This is the complete actual low-prime/signed post-root cofactor source;
the prime `p=R` is admitted exactly when R is prime. The full stratum
decomposition additionally splits `-T_R` into cofactor-bearing middle
and negative upper-half prime singleton contributions. A shell samples
the change of the **whole source** as R advances.

## A new explicit root-step form of the true prime debt (paper identity)

For `R>=2` and every `1<=c<R`, define the genuine prime-window count

```text
n_R(c) = pi(floor(Y_R/c)) - pi(floor(X_R/c)).
A_R    = sum_{1<=c<R} mu(c)*n_R(c).
G_R    = (1 if R is prime else 0)*M(R-1).
B_R    = mu(R)*[(1 if R+1 is prime else 0)
              + (1 if R+2 is prime else 0)].
```

Here `pi` is **integer prime counting**, not Li or an averaged density.

**Exact identity (direct proof):**

```text
T_(R+1) - T_R = A_R - G_R + B_R.
```

To prove it, reindex the original prime-family source by its unique
cofactor `c<R`, using `p>=R>c` and `p^2>X_R`:

```text
T_R = sum_(c=1)^(R-1) mu(c)
       [pi(floor(X_R/c))-pi(R-1)].
```

On advancing the root, each shared cofactor `c<R` contributes its
moving upper prime window `n_R(c)`. Advancing the lower prime gate from
`R` to `R+1` deletes exactly `1_{R prime} M(R-1)`. The newly admitted
cofactor `c=R` contributes
`mu(R)[pi(R+2)-pi(R)]` because `floor(Y_R/R)=R+2`.
These are all the terms; there is no hidden boundary face.

**A genuinely paid correction:** `|B_R|<=2`, hence
`sum_(H<=R<2H) B_R^2<=4H`. Define
`U_R=(L_(R+1)-L_R)-A_R+G_R`.
Since `M(Y_R)-M(X_R)=U_R-B_R`, the elementary
`(x-y)^2 <= 2x^2+2y^2` proves, in both directions,

```text
sum_(H<=R<2H) [M(Y_R)-M(X_R)]^2
       <= 2*sum_(H<=R<2H) U_R^2 + 8H,

sum_(H<=R<2H) U_R^2
       <= 2*sum_(H<=R<2H) [M(Y_R)-M(X_R)]^2 + 8H.
```

Thus the two energy targets are equivalent at any target exponent
strictly greater than 1. The **new-cofactor birth** is harmless.
The `G_R` root-prime deletion is **not** harmless by a standalone
current-bound estimate: using only `M(R-1)=O(R^(7/8+eps))` gives at
best `sum G_R^2=O(H^(11/4+eps))`, above the
`H^(5/2-eta)` target. Keep `G_R` coupled to `A_R` and the low source.

## The source-faithful NNS Co–Div matrix

The weights `n_R(c)` are nonnegative **actual prime-window counts**.
For the root range `H<=R<2H`, set

```text
D_H = sum_R sum_(1<=c<R) mu(c)^2*n_R(c)^2
Co_H = sum_R sum_(1<=c<d<R, mu(c)*mu(d)=+1) n_R(c)*n_R(d)
Div_H= sum_R sum_(1<=c<d<R, mu(c)*mu(d)=-1) n_R(c)*n_R(d).
```

Zero Möbius coefficients contribute to neither off-diagonal population.
The **exact weighted NNS identity**, before any triangle inequality, is

```text
sum_(H<=R<2H) A_R^2 = D_H + 2*(Co_H-Div_H).
```

This is an actual arithmetic Gram: no centering, random sign model,
independence, row-averaging or missing prime gate has been assumed.

### Measured evidence (exact integer arithmetic)

Run
`python3 scripts/nns_signed_prime_window_census_20261103.py`.
This verifies all identities against the literal sieve and frozen counts.

| H | D_H | Co_H | Div_H | signed 2(Co-Div) | sum A_R^2 |
|---:|---:|---:|---:|---:|---:|
| 128 | 301,212 | 1,149,247 | 1,284,583 | -270,672 | 30,540 |
| 256 | 1,850,483 | 9,079,821 | 9,957,003 | -1,754,364 | 96,119 |
| 512 | 11,703,523 | 71,845,073 | 77,489,674 | -11,289,202 | 414,321 |

At `H=512`, the signed pairs cancel **96.46% of the weighted
cofactor diagonal**. This is the leading numerical reason to attack
the genuine weighted Co–Div rather than a raw `r_min` gate.

The same script verifies the complete LOW/MIDDLE/TOP **six-term** root
Gram. Its dominant middle–singleton signed payment is
`-3,552,638` at `H=512` against positive middle/top energies
`2,371,730+1,595,492`; the full shell energy is `486,935`.
The two source coordinate systems are exact but their individual
diagonals are NOT interchangeable.

Historical endpoint regression at `R=317`:
`D=96,346, Co=346,668, Div=394,830, Q=22`.
At `R=1027`:
`D=1,011,407, Co=5,257,036, Div=5,762,927, Q=-375`.
Here `D` is the **historical Abel diagonal**
`sum_b M(b)^2(floor(X/b^2)-floor(X/(b+1)^2))`,
**not** `sum_b mu(b)^2 floor(X/b^2)`.
The exact endpoint check is `Q=2M(R-1)-M(X_R)`.

All data are finite; neither a fitted exponent nor an observed sign
is accepted as a uniform theorem. In particular the full shell
off-diagonal is sometimes positive, so global `Div>=Co` is false
as a blanket shell assertion.

## First genuinely NEW analytic estimate required

The source-faithful one-sided **complete compensated** target is:
there exist fixed `eta>0`, and for every `eps>0` a constant
`C_eps` independent of `H`, such that

```text
sum_(H<=R<2H) [
  (L_(R+1)-L_R) - A_R + G_R
]^2 <= C_eps * H^(5/2-eta+eps)
```

for all sufficiently large H. An equivalent signed NNS payment
inequality is

```text
2*sum_R (L_(R+1)-L_R)*(A_R-G_R)
 >= sum_R (L_(R+1)-L_R)^2
  + sum_R (A_R-G_R)^2
  - C_eps*H^(5/2-eta+eps).
```

Here `Co_0(x,y)-Div_0(x,y)=xy`, so the left-hand side is the
**full LOW/cofactor-prime-window signed NNS payment**, with the
root-prime gate kept in the second channel. The complete two-channel
energy includes internal same-/opposite-sign cofactor correlations;
one cannot replace it by a mean sign ratio or by the middle/singleton
cross term alone.

It is legitimate to try to prove separate upper bounds for
`sum (A_R-G_R)^2` and `sum (Delta L_R)^2`, using Cauchy to
recombine them. It is also legitimate to use a *joint* one-sided
covariance inequality, which may be strictly easier. Neither route
currently has the required uniform arithmetic proof.

If proved for any fixed `0<eta<1/2`, the shell Green–Kubo identity,
dyadic Cauchy and exact last-shell transfer give

```text
M(x) = O_eps(x^(7/8 - eta/4 + eps)).
```

To beat the existing LOW-first source-dependent
`delta_slot=7*rmin/192`, it suffices that
`eta>4*delta_slot=7*rmin/48`, with the net exponent loss paid.
No numerical bound on `rmin` is needed to formulate the target.

## First independent arithmetic attack

Work on the actual weighted prime-window incidence
`n_R(c)`. The diagonal is large, and the data show substantial
opposite-sign off-diagonal payment. The first missing inequality is
a **uniform upper bound on the FULL compensated covariance**, not
a nonnegative-size estimate for each stratum. Preserve common primes,
shared gcd, incomplete CRT periods, the moving cutoff, `p=R`
admission, the singleton-to-cofactor transition, and the actual
Möbius cofactor signs. A statement for coprime complete CRT periods
alone is not uniform on the growing root windows.

A stand-alone bound for `G_R` at the inherited 7/8 exponent does
not fit the target; seek a signed cofactor/prime-gate interaction
or a separate genuinely improved prime-restricted mean square.
The new bounded `B_R` birth face is already paid and should not
be reintroduced as an obstruction.

**Original OAI-source caveat:** This is the **native integer**
admissible-prime channel. If reusing it inside the fully integrated
`compensatedPhysicalProbe`, first prove a faithful occurrence map
preserving the original ideal labels, Hecke phases, masks, heights,
W0/W1 shears, selected prime factors, normalization and separate
negative principal signal. The OAI `D+C_off-V_off` moment is not
automatically the same numerical matrix as this integer source.
No such unproved intertwiner is assumed here.

## Verification status and acceptance gate

The script checks finite arithmetic and deterministic identities.
The displayed moving-prime formula has an elementary paper proof,
but is **not yet a kernel-checked Lean declaration** in this PR.
For promotion: formalize the exact prime-gate identity using the
existing native finite objects, add warning-fatal exact-head Lean
and standard-axiom audits, and have the independent Referee check
the proof and census. **Do not merge or report VERIFIED_ETA from
a finite regression, paper equivalence, or conditional consumer.**

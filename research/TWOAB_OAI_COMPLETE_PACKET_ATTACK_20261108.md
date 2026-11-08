# 2ab complete-parent renewal bands: reuse the certified OAI cancellation

Date: 2026-11-08. Research scope: exact original integer-Mobius source and the existing strict OAI Mertens exponent. This is a **proper-subpopulation bound**, not a new global exponent or a proof of RH.

## 1. Original source, full descendants and exact telescope

Put `X_R=R^2-1`, `R>=2`. Define the true reciprocal hyperbola-fibre mass

```text
t_R(z) = sum_(X_R/(z+1)<n<=X_R/z) mu(n)
       = M(floor(X_R/z)) - M(floor(X_R/(z+1))), 1<=z<R.
```

Existing Lean:
- `squareRootReplacementTailMoebiusCoefficient_eq_mertensIncrement` in `RHLean/Proof/RootSmoothCrossRegionGram.lean`;
- `squareRootReplacementTailCoefficient_eq_neg_tailMoebiusKernel` and `sum_shiftedMertens_div_eq_one_sub` in `RHLean/Proof/RecursivePrimeReplacement.lean`;
- `mertensEndpoint_eq_recombinedReplacementRow` is the exact complete endpoint, not an estimate.

For each parent z include ALL its quotient descendants before applying a norm:

```text
P_R(z) = t_R(z) * sum_(1<=k<=z) M(floor(z/k))
       = t_R(z)                                  (Mobius * 1 = unit).
```

Consequently, for every 1<=A<=B<R,

```text
sum_(A<=z<=B) P_R(z)
   = M(floor(X_R/A)) - M(floor(X_R/(B+1))).
```

The new Lean file `research/TWOAB_RENEWAL_COMPLETE_BAND_20261108.lean` expresses and proves these exact finite statements on the source-repository carriers. The separate OAI consumer uses the already-established uniform-for-every-positive-loss theorem

```text
M(n) = O_eps(n^(beta_*+eps));  beta_* = 7/8 - 1/(48*N_*),
N_* = explicitSlotCount > 0 fixed independent of cutoff.
```

Thus, for one constant C_eps independent of R,A,B,

```text
|sum_(A<=z<=B) P_R(z)|
 <= C_eps [floor(X_R/A)^(beta_*+eps)
           + floor(X_R/(B+1))^(beta_*+eps)].
```

For A ~ R^alpha, B=R-1, 0<alpha<=1, this inherits a bound
`O_eps(R^((2-alpha)*(beta_*+eps)))`. In particular alpha=1/2
transfers the original 7/8 input to power 21/16 in R (before the
strict November 8 saving), whereas the full endpoint baseline is
7/4. This is a strict bound on a **completed signed band**, not a
new estimate on M(X_R).

## 2. Explicit bounded geometry near the root

The exact quotient multiplicity is

```text
K(z,y) = #{1<=k<=z : floor(z/k)=y}.
```

For 1<=y<=z<R with R<=2*y, the only possible k is 1; hence
`K(z,y)=1[z=y]`. When z<y, K=0. The new finite Lean packet proves
that

```text
W_R(y) = 1[y=R-1] + t_R(y)  (ceil(R/2)<=y<R).
```

Moreover `floor(X_R/y)-floor(X_R/(y+1))<=4` on this range, so
`|W_R(y)|<=5`. This last elementary numeric inequality is a
paper corollary; the Lean file proves the exact coefficient identity
but does not claim to have compiled this numeric bound.

**Do not bound the near-root diagonal independently**. Its completed
parents also have strict quotient descendants with y<ceil(R/2).

## 3. Exact independent integer diagnostics (not an infinity proof)

All observations use the actual ordinary Mobius sieve and exact floors.
They test both the original replacement-coefficient identity and the
new band telescoping identity, with no artificial random signs.

| R | A | Complete band sum P | Uncompleted diagonal sum t_R(z) M(z) |
|---:|---:|---:|---:|
| 317 | 17 | -5 | not recorded |
| 1009 | 31 | 18 | not recorded |
| 1027 | 32 | 26 | 1066 |
| 3162 | 56 | 75 | 3544 |
| 5561 | 74 | 156 | -8643 |
| 1027 | 514 | 13 | not recorded |
| 3162 | 1581 | -33 | not recorded |
| 5561 | 2781 | -5 | not recorded |

The corresponding diagonal absolute sums at A=32,56,74 are
6018, 30260, 67405. These are diagnostics of the cost of splitting
the original pair of HIGH/LOW channels and their descendant returns,
not estimates of growth exponents.

## 4. Exactly what remains unpaid, with no new generic covariance label

This theorem recombines all descendants for each original parent; therefore
the large deep-fibre tail `1<=z<A` is complementary and is NOT controlled
by the completed band theorem. It contains the longest hyperbola intervals,
especially z=1, and can carry the high-prime/prime-power/cofactor main mode.

The reconstructed identity with `A=1,B=R-1` reduces to the full
Mertens endpoint and is tautological. Its use alone cannot improve
the already-certified exponent or deliver an all-scale contraction.

The sharp OAI localization gap is distinct: the certified OAI weighted
moments apply to particular smooth test profiles, selected ideal-labelled
coefficients, compensated masks and height/conductor parameters. They
are not automatically valid uniformly for a moving sharp cutoff
`floor(X_R/z)` or all canonical cofactor masks. See
`research/OAI_PAIRED_SHARP_MOMENT_TRANSFER_20261028.md` and
`research/VF_MID_919_OAI_C_TO_R_CANCELLATION_WELD.md`.

A meaningful next mathematical advance should derive, using the
already-proved OAI cancellation on the **same actual admissible analytic
source**, a true weighted sharp/smooth comparison for the complete
deep-fibre remainder (including coherent mode, terminal parent and
principal signal). Keep the anti-diagonal complex energy,
selected/unselected ideal phases and original masks.

To beat `beta_*`, the **complete endpoint** must improve, not merely
the completed good band. Numerically attractive cancellation in
a proper subpopulation is never an RH certificate.

## 5. Formal proof status and review

Files:
- `research/TWOAB_RENEWAL_COMPLETE_BAND_20261108.lean`: exact finite packet, band telescope, near-root kernel diagonal, coefficient bridge;
- `research/TWOAB_RENEWAL_OAI_CONSUMER_20261108.lean`: unconditional **reuse** of the strict November 8 Mertens exponent for the true completed packets;
- `.github/workflows/twoab-complete-renewal-bands.yml`: warnings-fatal Lean compilation and declaration/axiom checks.

The new files require pinned warning-fatal CI and human review before any
claim of being compiled on main. Even when green they provide **no**
additional Mertens exponent and do not assert a new analytic source theorem.

FAR-4 terminal audit and exact finite diagnostic

Audited baseline: `22b1251f131bbaab780bb95a04e6fda6808df2fa`, the merge of
PR #683. The baseline has the factor-four raw terminal induction and FAR-3
equivalence. It does not yet contain FAR-4 or a STOKES-4 Gram theorem.

For a literal daughter coefficient `a`, the existing deterministic shell gives

```
Q_R <= (37/36) A K sum_q s_q^2 + 148 sum_q (s_q+1)^2
    <= (37/36)(17/72) A R^2 K + 296 R^2.
```

All owners are odd primes below `R`, `Y_q=floor((R^2-1)/q^2)`, and
`s_q=floor(sqrt(Y_q))`. The daughter is the whole signed `M(Y_q)` before
squaring. The two finite sum inequalities are existing source theorems in
`SignedTransportAmplificationAudit.lean` and
`PhysicalQ2ExceptionalTerminalSynthesis.lean`.

Consequently the raw step closes by strong induction with

```
kappa = a * (37/36) * (17/72) < 1,
A = (C + 296*a)/(1-kappa).
```

The same lower critical envelope `K` restricts to every smaller child root.
Its definition includes `y=0`, so `K>=1`; hence `296*a*R^2` is absorbed
additively. The proof establishes the envelope with a fixed constant. It does
not require a power saving from `kappa` raised to the recursion depth.

For FAR-4, Young's inequality with epsilon `1/40` and the existing `10 R`
root boundary supply the raw step with

```
a = 41/10,
C = 4100 + (41/40)*CF,
kappa = 25789/25920,
1-kappa = 131/25920,
A = (25920/131)*(C + 6068/5).
```

The chosen `C` also covers every `2<=R<56` via the pre-existing bound
`3136 R^2 K`. Thus neither finite roots nor the unsigned shell consume another
multiplicative margin. The shifted endpoint interface uses `2*A+1` as before.

The source change generalizes the existing induction, preserves its original
factor-four interfaces, and adds `FrozenTopFarFourEnergyStatement`, its exact
`41/10` recurrence implication, and its equivalence to endpoint amplification.
FAR-4 remains an explicit unproved hypothesis in the terminal theorem.

The diagnostic script independently enumerates the physical states, retains
their Boolean face tags and Möbius signs, removes the actual top/internal-mate
images, and checks the root correction. It also enumerates the far-prime
pairs, their exact `(q,d,p)` tags, strict second-contact crossings, post-root
partner columns, first-prime loss/birth boundaries, and literal signed
Mertens daughters.

| R | X | M(X) | B | F | Q | Minimum K | F^2/(4Q) | Required nonnegative CF |
|---|---|---|---|---|---|---|---|---|
| 56 | 3135 | 6 | 3 | -3 | 29 | 3/2 | 9/116 | 0 |
| 100 | 9999 | -23 | -1 | 22 | 239 | 3/2 | 121/239 | 0 |

The exact signed far census is

```
F = unit - descended - crossing - internalMate - topImage.
R=56:  F = 427 - 160 - 309 - (-30) - (-9) = -3.
R=100: F = 1201 - 470 - 834 - (-149) - 24 = 22.
```

| R | Physical states | Residual states | Descended triples | Crossing triples |
|---|---|---|---|---|
| 56 | 37,523 | 36,288 | 204 | 779 |
| 100 | 149,925 | 146,969 | 660 | 2,646 |

The post-root partner checks cover all 983 and 3,306 nonunit triples,
respectively. The descended/crossing census includes owner 2; the terminal
energy `Q` uses only odd owners. No equality between these different owner
schedules, between a far slice and a whole daughter, or between coefficient
square mass and Mertens energy is assumed.

The zero-boundary threshold for `F^2/(4Q)` is 1, not 4. For the actual statement,
the finite excess diagnostic is `max(0,F^2-4Q)/(R^2*K_min)`. A ratio above 1
would require a positive additive coefficient; it would not itself refute
FAR-4. Two roots cannot establish a uniform constant.

All implemented finite identities passed. The proposed two-boundary signed
Gram identity is not specified as a compiled equality and is not verified by
this experiment. The geometric availability of factor four remains unproved.

Reproduce the finite enumeration:

```
python3 scripts/far_four_diagnostic.py --roots 56 100 --output-dir /tmp/far_four
```

The JSON output records every physical and residual state as
`[face_product, cofactor, quotient, signed_weight]`, the descended/crossing
triples, and their partner incidences. A squarefree face product encodes its
unique set of prime factors; it does not collapse different physical states.

Validation status: the source assumption audit, root manifest, public export
closure, paper/Analysis boundary, proof inventory, and syntactic declaration
graph checks pass. These are not Lean elaboration checks. The local Lean/Lake
installation fails during application-path detection before loading the
project. The new declarations have therefore not been compiler-verified.
Automatic approval review blocked the push for lack of explicit authorization
to upload repository source in this turn. No PR or hosted build was started.

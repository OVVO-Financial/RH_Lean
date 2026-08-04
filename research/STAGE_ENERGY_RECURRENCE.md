# Stage energy recurrence: `E_q <= A E_{q^-} + C x`

The one-prime drill-down, the measured defect frontier, and the division of the
remaining work.

---

## 0. The one-prime calculation (steps 1–3), settled

Everything in this section is exact and was checked independently:
`scripts/TwoAnchorSlackCoverage/ternary_refinement_check.py` and
`scripts/TwoAnchorSlackCoverage/quotient_ladder_check.py`.

### Step 1 — the refinement is exact, and crudely bounded

With `a_n` the parent weight carrying the local `q`-factor stripped,
`X_0 = sum_{q∤n} a_n`, `X_1 = sum_{q‖n} a_n`, `X_2 = sum_{q²|n} a_n`, the local
Möbius factor `(1,-1,0)` gives the parent value `P = X_0 - X_1`. Substituting
`X_0 = P + X_1` in the stated `C/S/W` coefficients reproduces the matrix `M_q`
exactly, and

```text
C + S + W = X_0 - X_1 = P      exactly, for every q.
```

Coefficient of `X_0`: `(q-1)²/q² + (2q-1)/q² = 1`. Of `X_1`:
`(q-1)²/q² - (2q-1)(q-1)/q² - 1/q = -1`. Of `X_2`:
`(q-1)²/q² - (2q-1)(q-1)/q² + (q-1)/q = 0`. So the refinement is
value-preserving — an independent confirmation that the coefficients are right.

The squared row norms of `M_q` are

```text
|row_C|² = 6 (q-1)⁴/q⁴                                   < 6    since (q-1)⁴ < q⁴
|row_S|² = (2q-1)²(2q²-6q+6)/q⁴                          < 8    since 32q³-50q²+30q-6 > 0
|row_W|² = (q²-2q+2)/q²                                  < 1    since 2q-2 > 0
```

each a polynomial certificate valid for **every `q ≥ 2`**, with suprema exactly
`6, 8, 1` as `q → ∞`. Hence

```text
|C|² + |S|² + |W|² ≤ 15 (|P|² + |X_1|² + |X_2|²).
```

At `q = 11` the true total is `10.41`, so `15` is generous — deliberately.
Formalized in `RHLean/Proof/TernaryRefinementBound.lean` as `refinement_exact`
and `frobenius_poly`, in cleared (division-free) form.

### Step 2 — the hidden classes are objects at smaller cutoffs

For odd `q`, `a_{qm} = a_m` and `a_{q²m} = a_m` in the `q`-stripped convention, so

```text
X_1(L,x] = X_0 on (⌊L/q⌋, ⌊x/q⌋]
X_2(L,x] = the total raw sum on (⌊L/q²⌋, ⌊x/q²⌋]
```

Verified exactly for `q = 11, 13, 17` at four cutoffs each, alongside the check
that `P = X_0 - X_1` equals the true prime-`2` fibre partial sum.

### Step 3 — the answer is yes, via a geometric quotient ladder

`X_0 = P + X_1` and `X_1(L,x] = X_0(L/q, x/q]` unroll to the **telescope**

```text
X_0(L,x] = sum_{k>=0} P(⌊L/q^k⌋, ⌊x/q^k⌋]
```

verified exactly at depth `5`–`6` in every case tested. So the hidden channel is
not a new object: it is a sum of *value* objects down the ladder of quotient
cutoffs. Two consequences decide the question:

* the reduction is **not** to the two cutoffs `{x/q, x/q²}` but to the whole
  geometric ladder `{⌊x/q^k⌋, ⌊L/q^k⌋}`;
* the depth costs **no logarithmic factor**. Under a strong-induction hypothesis
  `|P(y)| ≤ K√y` at smaller scales, the ladder is dominated by
  `K√x · sum_k q^{-k/2}`, an absolute constant: `1.4317` at `q = 11`, `1.3838` at
  `13`, `1.3202` at `17`, decreasing to `1` as `q` grows. Measured partial
  envelopes on `(30030, 510510]` are `1.4306`, `1.3832`, `1.3191` — already at
  the limit.

This matters because a per-stage `log x` factor would have been fatal: with
`j = O(log x / log log x)` stages, `(log x)^j = x^{Θ(1)}`, not `x^{o(1)}`. The
geometric ladder avoids it.

The ladder is also nearly cancellation-free: `sum_k |P|` versus `|sum_k P|` is
`174.00` versus `169.50` at `q = 11`, `132.00` versus `124.50` at `13`,
`134.25` versus `131.25` at `17`. The triangle inequality is not lossy here, so
the reduction does not depend on unproved cancellation between rungs.

**Verdict.** Raw `l²` is not the wrong invariant. The hidden `q`- and
`q²`-divisible energies do reduce to the same legal energy at smaller cutoffs,
provided the reduction is taken down the full geometric ladder and closed by
strong induction in `x`. What remains is to carry the channel index through the
reindexing uniformly — the ladder identity above is proved for a single channel.

---

The measured defect frontier, the bulk-versus-boundary verdict it delivers, and
the division of the remaining work.

## Status

| layer | classification |
|---|---|
| iterated energy estimate from the one-stage recurrence | **exact algebra**, formalized |
| `D_n = 3^n` from three-way Cauchy-Schwarz | **exact algebra**, formalized (no longer assumed) |
| ternary shell recurrence and evaluation at one | **exact algebra**, formalized |
| anchor coverage | **exact algebra**, formalized |
| the `(A, C)` defect frontier on `(30030, 510510]` | **reported exhaustive scan**, audited for internal consistency |
| the `29#` bottleneck frontier | **reported, one resolved state — not a scan** |
| `E_q(x) <= 4 E_{q^-}(x) + C x` on legal enriched states | **open** — the decisive theorem |

Nothing here is connected to the protected theorem graph. The Lean modules
contain no analytic premise and no asymptotic specialization.

---

## 1. The measured defect frontier

For

```text
C_q(A) = sup_x ( E_q(x) - A E_{q^-}(x) )_+ / x
```

scanned over **every** prefix of `(30030, 510510]` with exact ternary-state
updates and raw `l^2` energies:

| new prime `q` | zero-defect threshold `A*_q` | `C_q(1)` | `C_q(1.25)` | `C_q(1.5)` | `C_q(2)` |
|---:|---:|---:|---:|---:|---:|
| `11` | `1.569005` | `3.04208` | `0.0017606` | `4.32e-5` | `0` |
| `13` | `1.384105` | `1.01628` | `0.0003161` | `0` | `0` |
| `17` | `2.857660` | `0.006365` | `0.0008501` | `6.53e-5` | `1.45e-5` |

`A*_q` is the smallest multiplier with `E_q(x) <= A*_q E_{q^-}(x)` at every
prefix. The large `A*_17 = 2.857660` occurs at `x = 30040` with `m_2 = 6` — an
extreme short-prefix boundary event; the mature-prefix maximum at that stage was
`1.289167`.

Simultaneous constants over `q = 11, 13, 17`:

```text
(A, C) = (3, 0)                     works outright
(A, C) = (1.5, 6.53e-5)             a substantially tighter mixed estimate
(A, C) = (2, 1.45e-5)               zero defect at 11 and 13; the residue is the short 17-prefix
```

**Audit.** These values are reported, not recomputed here (see §4). What can be
checked without the energies is their mutual consistency, and it holds exactly:
`C_q(A)` vanishes at precisely the entries with `A >= A*_q`, and the simultaneous
maxima `max_q C_q(A)` reproduce the quoted `6.53e-5` and `1.45e-5`.
`scripts/TwoAnchorSlackCoverage/defect_model.py` carries the table and runs the
audit.

---

## 2. Bulk versus boundary: the verdict

This is the finding that changes the analytic target. At `A = 1` the worst
defects split as

```text
q = 11:   1552956  (bulk)  - 1559 (cross)  + 47  (terminal tail)  = 1551444
q = 13:    494739  (bulk)  + 3421 (cross)  -  28 (terminal tail)  =  498132
```

Both reconstruct their totals exactly. The bulk share is `100.097%` at `q = 11`
and `99.319%` at `q = 13` — at `q = 11` the bulk alone *overshoots* the defect and
the negative cross term partially offsets it.

So the earlier hypothesis is settled, negatively:

> Raw `l^2` energy has **no contractive periodic bulk at `A = 1`**. The
> multiplicative constant must absorb genuine bulk inflation; it is not an
> incomplete-terminal-period artifact.

The terminal tail contributes `47` out of `1551444` and `-28` out of `498132`.
The boundary is negligible in the bulk regime — it reappears only as the short-prefix
events that set `A*_17`, and those are killed either by the maturity restriction
or by an arbitrarily small additive `C`.

Once `A` reaches roughly `1.5` to `2` the remaining positive defects on this
block are of order `10^-5` and concentrated at short prefixes.

---

## 3. The `29#` bottleneck

At the resolved `29#` bottleneck the post-`7` inflation factors are

```text
q  =    11       13       17       19       23       29
      3.6244   2.3790   1.7798   1.5528   1.3837   1.2660
```

monotonically declining after `q = 11`, so `(A, C) = (4, 0)` works at that state
through `q = 29`. The corresponding additive constants at candidate multipliers:

| `A` | largest tested `C` |
|---:|---:|
| `1` | `133.93` |
| `1.25` | `68.07` |
| `1.5` | `46.67` |
| `2` | `23.80` |
| `3` | `9.15` |
| `4` | `0` |

**This row is one fully resolved state, not an exhaustive scan of the `29#`
block.** It bounds nothing on its own; it says where the constant sits at the
single point that the all-prefix scan identified as the block's normalized
bottleneck.

---

## 4. Best current target, stated correctly

```text
E_q(x) <= A E_{q^-}(x) + C x        for absolute A, C, on legal inherited states.
```

The data says `A = 4` suffices at every state tested and `C = 0` is consistent
with all of it. But **the constant is not sacred**: any absolute `A` closes the
same exponent argument, so `A = 8` or `10` is just as good a theorem. What must be
absolute is `A`, not its value.

### The additive form is not a homogeneous operator inequality

A homogeneous Gram inequality reads `T_q^* H_q T_q ⪯ A H_{q^-}` and scales with
the vector. An estimate carrying `C x` cannot hold for every scalable `v`: dilating
`v` scales the quadratic terms and leaves `C x` fixed, so the additive constant
dilutes like `lam^-2` and vanishes in the limit. `homogeneous_of_affine` in
`RHLean/Proof/AbstractEnergyRecurrence.lean` makes that an exact statement — an
affine bound surviving every dilation *forces* the homogeneous bound `f <= A g`.

So the inequality must be stated either

* only on the normalized legal arithmetic states arising at prefix `x`; or
* by decomposing the refinement into a homogeneous bulk map and a bounded
  boundary vector,

```text
T_{q,x} v = T_q^bulk v + b_{q,x},
‖T_q^bulk v‖_{H_q}^2 <= A_0 ‖v‖_{H_{q^-}}^2,      ‖b_{q,x}‖_{H_q}^2 <= C_0 x.
```

The cross term is absorbed by Young's inequality,
`2|<T^bulk v, b>| <= η ‖T^bulk v‖^2 + η^-1 ‖b‖^2`, giving

```text
E_q(x) <= (1 + η) A_0 E_{q^-}(x) + (1 + η^-1) C_0 x
```

for every `η > 0` — exactly the shape `energy_le` iterates. This is
`energy_affine_step`, proved in any normed group from the triangle inequality
alone. The multiplicative constant is an operator bound, the additive one is a
boundary bound, and neither is asked to do the other's work.

### The local theorem to prove

For every `q >= 11`, every legal inherited state and every pinned prefix,
`E_q(x) <= A E_{q^-}(x) + C x` with absolute `A, C`. A practical route:

1. write the prefix length as `N = m q^2 + r`, `0 <= r < q^2`;
2. diagonalize the complete-period refinement on `Z/q^2 Z` and bound its largest
   Gram eigenvalue uniformly;
3. treat the terminal incomplete `r`-segment as the boundary vector `b_{q,x}`;
4. use the legal-state normalization and `q^2 << x` in the relevant primorial
   regime to bound its energy and the bulk-boundary cross term;
5. conclude the coarse recurrence with any absolute constants.

The concrete Gram target is then `G_q^periodic <= A H_{q^-}` together with
`<R_{q,x}^boundary v, v> <= C x` for legal `v`, with `A` around `4` indicated by
the scan and any absolute value acceptable.

### Why a coarse constant is enough

From `E_7(x) <= B x`, iterating `j` later primes gives `E_j(x) << A^j x`. Since the
physical value is a sum of at most `3^j` channels, `|P_2(x)|^2 <= 3^j E_j(x) << (3A)^j x`.
On the `p#` scale `j = O(log x / log log x)`, so `(3A)^j = x^{o(1)}` and

```text
|P_2(x)| <<_eps x^{1/2 + eps}.
```

The decisive statement is therefore just: **one new prime causes at most absolute
bounded quadratic damage on legal states.**

This last paragraph is analysis, not algebra, and is deliberately **not** in the
Lean modules: `energy_le` supplies the iteration and `eval_le_three_pow` the
`3^j` channel count, but the range of `j` and the `x^{o(1)}` conclusion belong to
the analytic layer.

### Why the multiplicative side is the whole problem

Formalized in `RHLean/Proof/AbstractEnergyRecurrence.lean`: refinement replaces a
component by three children summing to it, so Cauchy-Schwarz gives
`E_j <= 3 E_{j+1}` — a bound on the **parent** by the children. Iterating from the
unresolved stage, where the single component is the fibre value, yields

```text
|P_2|^2 = E_0 <= 3^n E_n,
```

so `D_n = 3^n` is now discharged rather than assumed (`le_pow_three_mul`,
`eval_le_three_pow`). The direction matters: the tensor structure bounds
`E_{j+1}` from below and never from above, since three children with a small
signed sum can have arbitrarily large squares. Every upper bound
`E_{j+1} <= A E_j + C x` is therefore arithmetic content about the legal states and
cannot be recovered from the shell combinatorics. The measured bulk inflation is
consistent with that: there is nothing structural forcing `A <= 1`, and the data
says `A > 1` genuinely.

---

## 5. Lean layer: what is proved

Four independent pieces, all exact algebra, none carrying an estimate.

1. **Anchor coverage** — `RHLean/Proof/TwoAnchorSlackCoverage.lean`:
   `a b <= 0 => a(y-a) <= 0 or b(b-y) >= 0` (`covers_of_mul_nonpos`), with the
   exact failure set and the cross-term price.
2. **Ternary shell recurrence** — `RHLean/Proof/DegreeShellTransfer.lean`:
   `E_d^{(j+1)} = C_q E_d^{(j)} + (S_q + W_q) E_{d-1}^{(j)}` (`shellStep`,
   `shellStepThree`).
3. **Evaluation at one** — same module:
   `evalOne (step_q E) = (C_q + S_q + W_q) (evalOne E)`
   (`sum_shellStepThree_window`), iterated by `sum_shellSteps`.
4. **Abstract energy recurrence** — `RHLean/Proof/AbstractEnergyRecurrence.lean`:
   from `E_{j₀} <= B x`, `E_{j+1} <= A_j E_j + C_j x` and `0 <= A_r`,

   ```text
   E_n <= (prod_{r=j₀}^{n-1} A_r) B x + x sum_{s=j₀}^{n-1} C_s prod_{r=s+1}^{n-1} A_r
   ```

   (`energy_le`), and with `|Λ_n V_n|^2 <= D_n E_n` the closed form (`eval_le`),
   `D_n = 3^n` discharged by `eval_le_three_pow`.

The asymptotic specialization `n = O(log x / log log x)` is deliberately outside
these modules: it is an analytic step, and stating it beside the algebra would
turn a lemma into a conditional theorem.

---

## 6. What is still blocked here

`E_q(N)` is the squared `l^2` mass of the resolved components,
`E_j(N) = sum_{σ ∈ {C,S,W}^j} |Z_σ(N)|^2`, and the definition of `Z_σ` is not
recorded in this repository. The published prime-`3` triples

```text
+869.667 - 2295.417 + 751.500 = -674.25      (19# trough)
+1102.333 - 1282.083 + 905.750 = +726        (19# crest)
```

do not determine the three operators, and guessing them would produce numbers that
look like a check and are not one. Any one of the following unblocks independent
recomputation here:

* the operators `C_q`, `S_q`, `W_q` as they act on a packet;
* the definition of `Z_σ(N)`;
* a reference implementation of `resolve(q, N)` returning the `3^j` components.

The harness in `scripts/TwoAnchorSlackCoverage/defect_model.py` is written against
that callback: the frontier formulas

```text
C_min(A) = max_N (E_q - A E_{q^-})_+ / x,     A_min(c) = max_N (E_q - c x) / E_{q^-}
```

are one-pass and inverse to each other, so the whole trade-off curve costs the
same sweep as the single number `A*_q = A_min(0)`.

## The division

```text
Lean        proves a coarse recurrence suffices, that D_n = 3^n, and the
            legitimate form of the one-stage step                     — done
computation determines realistic A and C                              — frontier measured
analysis    proves G_q^periodic <= A H_{q^-} plus a boundary form     — open, decisive
```

The empirical evidence supports feasibility at `A = 4`, and any absolute `A` would
do. The universal inequality remains the open theorem, and nothing above assumes
it.

## Scope

This would supply the central cancellation engine for the prime-`2` fibre
induction, and nothing beyond it. A complete Mertens proof still needs

* the complementary fibres — the distinguished fibre carries `79.15%` of the
  block excursion at the `29#` bottleneck, not all of it; and
* the two-anchor slack-preservation bridge of
  [`TWO_ANCHOR_SLACK_COVERAGE.md`](TWO_ANCHOR_SLACK_COVERAGE.md), which converts a
  per-block estimate into the frozen-prefix invariant, at the measured cost
  `K_anchor/K_*` of `1.22` to `3.31` on the last four blocks.

Neither is implied by the one-prime estimate.

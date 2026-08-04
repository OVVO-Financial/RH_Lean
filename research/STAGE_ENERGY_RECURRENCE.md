# Stage energy recurrence: `E_q <= A E_{q^-} + C x`

The three-layer division of the remaining work, the empirical constants measured
so far, and what each layer can and cannot proceed on.

## Status

| layer | classification |
|---|---|
| iterated energy estimate from the one-stage recurrence | **exact algebra**, formalized |
| ternary shell recurrence and evaluation at one | **exact algebra**, formalized |
| anchor coverage | **exact algebra**, formalized |
| `B`, `A_q` measured on `(30030, 510510]` and at the `29#` bottleneck | **reported finite computation** |
| the defect-model separation (bulk versus boundary) | **blocked**, see §4 |
| `E_q(x) <= A E_{q^-}(x) + C x` on legal enriched states | **open** — the decisive theorem |

Nothing here is connected to the protected theorem graph. The Lean modules
contain no analytic premise and no asymptotic specialization.

---

## 1. Measured constants

On every prefix of the block

```text
(30030, 510510]
```

(labelled `(5#, 17#]` in the source note and `(13#, 17#]` under the primorial
indexing used elsewhere in this repository — the integer interval is the same),
the exhaustive computation through stages `q <= 17` gives the raw-energy base
constant through `7`

```text
B_{<=7}^emp = 29.850695
```

and the later-stage inflations

| stage | mature prefixes `m_2 >= 1000` | all prefixes |
|---|---:|---:|
| `A_11` | `1.179208` | `1.5690` |
| `A_13` | `1.125960` | `1.3841` |
| `A_17` | `1.289167` | `2.8577` |

At the much larger `29#` bottleneck the largest post-`7` inflation was

```text
A_11 = 3.624432
```

after which the factors decline steadily to `1.265988` at `29`.

The accurate status is therefore

```text
A_q^emp < 3.7   across the presently tested post-7 stages,
```

**not** a universal theorem. These values are carried as reported: they cannot be
recomputed here, for the reason in §4.

Two features of the table matter for the proof programme. The maturity
restriction moves `A_17` from `2.8577` to `1.289167`, so short-prefix boundary
cases are already known to dominate the unrestricted constant at that stage; and
the single large value `A_11 = 3.624432` at the `29#` bottleneck sits at the one
stage immediately after the base, which is where an incomplete-period defect
would be expected to show. Whether it is bulk behaviour or a boundary artifact is
exactly the open computational question.

---

## 2. Lean layer: what is now proved

Four independent pieces, all exact algebra, none carrying an estimate.

**1. Anchor coverage** — `RHLean/Proof/TwoAnchorSlackCoverage.lean`

```text
a b <= 0  =>  a (y - a) <= 0  or  b (b - y) >= 0
```

`covers_of_mul_nonpos`, with `covers_of_nonpos_of_nonneg` as the general form,
`not_covers_iff_of_pos` / `not_covers_iff_of_neg` for the exact failure set, and
`anchor_excess_eq_cross` for the price of discarding a favourable cross term.

**2. Ternary shell recurrence** — `RHLean/Proof/DegreeShellTransfer.lean`

```text
E_d^{(j+1)} = C_q E_d^{(j)} + (S_q + W_q) E_{d-1}^{(j)}
```

`shellStep` with `shellStepThree` keeping the three classes separate, and
`supported_shellStep` for the degree-support bookkeeping.

**3. Evaluation at one** — same module

```text
evalOne (step_q E) = (C_q + S_q + W_q) (evalOne E)
```

`sum_shellStepThree_window`, with `sum_shellSteps` iterating it to the ordered
operator product over a list of primes.

**4. Abstract energy recurrence** — `RHLean/Proof/AbstractEnergyRecurrence.lean`

From `E_{j₀} <= B x`, `E_{j+1} <= A_j E_j + C_j x` and `0 <= A_r`,

```text
E_n <= (∏_{r=j₀}^{n-1} A_r) B x + x ∑_{s=j₀}^{n-1} C_s ∏_{r=s+1}^{n-1} A_r
```

is `energy_le`, and combining it with `|Λ_n V_n|^2 <= D_n E_n` gives

```text
|Λ_n V_n|^2 <= D_n x [ B ∏_r A_r + ∑_s C_s ∏_{r>s} A_r ]
```

as `eval_le`. The asymptotic specialization `D_n = 3^n` with
`n = O(log x / log log x)` is deliberately **not** in the module: it is an
analytic step, and stating it alongside the algebra would turn a lemma into a
conditional theorem. `inflation_le_pow` is the only collapse provided, and it is
still an inequality between finite products.

---

## 3. Computational layer: the defect model

The next computation is not another scan. It is the local defect model

```text
Δ_q(N) = E_q(N) - A E_{q^-}(N),   normalized by x = L + N,
```

asking for the smallest `A` at which `sup_N Δ_q(N)/x` stays bounded. On a finite
prefix range both directions of that question have a **one-pass closed form**, so
no search over `A` is required:

```text
C_min(A) = max_N ( E_q(N) - A E_{q^-}(N) ) / x(N)
A_min(c) = max_N ( E_q(N) - c x(N) ) / E_{q^-}(N)
```

They are inverse to each other, `C_min(A_min(c)) <= c`, and `A_min(0)` is exactly
the pure multiplicative constant `max_N E_q/E_{q^-}` reported as `A_q^emp`. So
the whole `(A, C)` trade-off curve costs the same sweep as the single number
already measured.

That curve is the bulk-versus-boundary discriminator. If a small additive budget
collapses `A_min(c)` sharply, the inflation is carried by a few prefixes; if the
curve is flat, it is bulk behaviour. `scripts/TwoAnchorSlackCoverage/defect_model.py`
implements both formulas, the maturity filter (`m_2 >= 1000`), and the split of
each prefix into complete `q^2` periods and a terminal remainder, with a synthetic
self-test showing the discriminator separating a bulk stage from a boundary spike:
a spike reading `A = 4.0` collapses to `1.49` at budget `c = 0.01`, while a true
bulk stage at `1.4` only moves to `1.37`.

---

## 4. What blocks the recomputation

`E_q(N)` is the squared `l^2` mass of the resolved components,

```text
E_j(N) = ∑_{σ ∈ {C,S,W}^j} |Z_σ(N)|^2,
```

and the definition of `Z_σ` is not recorded in this repository. The `C/S/W`
classes are described as "constant", "strong nonzero `q`-multiple" and "weak
nonmultiple", and the published data fixes two prime-`3` triples

```text
+869.667 - 2295.417 + 751.500 = -674.25      (19# trough)
+1102.333 - 1282.083 + 905.750 = +726        (19# crest)
```

but two triples do not determine the three operators, and guessing them would
produce numbers that look like a check and are not one. What is needed is one of:

* the three operators `C_q`, `S_q`, `W_q` as they act on a packet; or
* the definition of `Z_σ(N)` directly; or
* a reference implementation of `resolve(q, N)` returning the `3^j` components.

Any of the three unblocks the whole diagnostic — the harness is written against
that callback and needs no other change.

---

## 5. Analytic layer: the decisive theorem

```text
E_q(x) <= A E_{q^-}(x) + C x     on legal enriched states after 3, 5, 7.
```

The route is to split the one-prime refinement Gram form into its periodic and
boundary parts,

```text
G_{q,x} = G_q^periodic + R_{q,x}^boundary,
```

and prove separately

```text
G_q^periodic ⪯ A H_{q^-},        <R_{q,x}^boundary v, v> <= C x   for legal v.
```

The first is where the exact complete-fibre contraction laws apply; the second is
where the incomplete terminal period lives, and is the same object the defect
model measures. A `(A, C)` pair proved there feeds `energy_le` and `eval_le`
unchanged.

## The division

```text
Lean       proves that a coarse recurrence is sufficient      — done, four pieces
computation determines realistic A and C                      — harness ready, input blocked
analysis   proves the periodic-plus-boundary Gram bound       — open, decisive
```

The empirical evidence supports feasibility. The universal `(A, C)` inequality
remains the open theorem, and nothing above assumes it.

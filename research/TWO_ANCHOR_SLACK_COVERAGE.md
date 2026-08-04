# Anchor coverage of the square-root slack invariant

Tightening of the two statements flagged in issue #184: what the `29#` bottleneck
actually forces, and what opposite-sign endpoints actually give.

## Status

| layer | classification |
|---|---|
| slack identities, anchor lemma, coverage and sharpness | **exact algebra**, formalized |
| primorial endpoint values, `K_*`, coverage counts, `K_anchor` | **exact finite computation** |
| degree-shell head/tail arithmetic, leaf counts | **exact finite computation** |
| shell/packet estimate that would discharge the obligation | **open** |
| any `M(x)` bound | **not claimed** |

Nothing here is connected to the protected theorem graph. The Lean modules
`RHLean/Proof/TwoAnchorSlackCoverage.lean` and
`RHLean/Proof/DegreeShellTransfer.lean` contain no analytic premise: the
arithmetic obligation appears only as a hypothesis.

Recomputation: `scripts/TwoAnchorSlackCoverage/verify.py` (anchor algebra,
the complete block `(13#, 17#]`, the reported diagnostics) and
`scripts/TwoAnchorSlackCoverage/block_scan.c` (every prefix through `29#`).
Every finite value quoted in issue #184 that these reproduce is marked
**reproduced** below; the two that could not be checked from published data are
marked explicitly.

---

## 1. Left and right filling are one lemma

Write `a = M(L)`, `b = M(U)`, `y = M(x)`, `S_K(x) = K^2 Q(x) - M(x)^2`. The two
exact identities are

```text
S_K(x) = S_K(L) + K^2 (Q(x)-Q(L)) - 2 a (y-a) - (y-a)^2,
S_K(x) = S_K(U) - K^2 (Q(U)-Q(x)) + 2 b (b-y) - (b-y)^2.
```

The favourable-cross conditions `a(y-a) <= 0` and `0 <= b(b-y)` are the *same*
condition on an anchor value `c`, and after discarding the cross term the two
obligations are the *same* inequality:

```text
c covers y       <->   c (y - c) <= 0
obligation at c  :     c^2 + (y - c)^2 <= K^2 Q(x)
```

because `0 <= b(b-y)` is `b(y-b) <= 0` and `(b-y)^2 = (y-b)^2`. So there is no
forward theorem and a separate backward theorem: there is **one anchor lemma**
applied to a set of frozen values. Left and right are only bookkeeping about
which side of `x` the frozen value sits on.

Three consequences, all formalized:

**Coverage is a statement about signs only.** A positive anchor covers the whole
half-line `y <= c`; a negative anchor covers `c <= y`; a zero anchor covers
everything. Hence

```text
M(L) M(U) <= 0   =>   every interior value has a covering anchor,
```

which is the `29#` statement of the issue, and more generally any anchor set
containing a nonpositive and a nonnegative value covers `R`.

**The price of the reduction is exactly the discarded cross term.**

```text
(c^2 + (y-c)^2) - y^2 = -2 c (y - c).
```

The anchor obligation is never weaker than the truth `y^2 <= K^2 Q(x)`, and the
gap is precisely the cross term one threw away. It vanishes only at `c = 0` and
at `c = y`. This is the quantitative content that "use the favourable anchor"
does not by itself supply.

**No single anchor is universal.** For every `c != 0` the half-line beyond `c` is
uncovered. This is what rules out right-anchor orientation as a pointwise
mechanism — and it rules out left-anchor orientation equally. The `29#`
bottleneck is a witness, not the reason.

---

## 2. What the bottleneck forces

At `x_* = 1109331447` (**reproduced**: `M = -15335`, `Q = 674392719`,
`K_* = 0.590510118734035`, the exact all-prefix maximum of `|M|/sqrt Q` on the
block):

```text
A(x_*) = M(x_*) - M(23#) = -18851      -2 M(L) A = +132560232   favourable
B(x_*) = M(29#) - M(x_*) = +10323       2 M(U) B = -103477752   unfavourable
```

Both **reproduced**. The correct reading:

* **Backward filling is not falsified.** The backward identity is an identity; it
  closes at `x_*` with no sign hypothesis whenever `S_K(U)` dominates
  `K^2 r(x) + B^2 - 2 M(U) B`. An unfavourable cross term is a demand on the
  endpoint reserve, not a contradiction. A backward-only programme therefore
  remains logically available if it produces a quantitative reserve — this is
  `slack_nonneg_of_endpoint_reserve`.
* **Right-anchor orientation is falsified as the pointwise mechanism**, at the
  actual extremizer, by `bottleneck_not_covered_right`.
* The bottleneck is at `14.19%` of the block (**reproduced**), and is neither the
  global trough (`M = -25071` at `x = 3773166681`, ratio `0.5234713516`) nor the
  crest (`M = 21791` at `x = 5439294781`, ratio `0.3789484274`). Both ratios
  **reproduced**; the two extremal locations are new here.

So the flexible statement in the issue is the right one: *use the favourable
anchor when available, and endpoint reserve otherwise.*

---

## 3. Opposite-sign endpoints are not the generic case

The issue notes that one cannot yet assume consecutive primorial endpoints have
opposite signs. The exact scan settles it: they do not.

| pair | `M(prev) M(next)` | anchor pair |
|---|---:|---|
| `2# x 3#` | `0` | opposite (covered) |
| `3# x 5#` | `+3` | **same sign** |
| `5# x 7#` | `+3` | **same sign** |
| `7# x 11#` | `+1` | **same sign** |
| `11# x 13#` | `-16` | opposite (covered) |
| `13# x 17#` | `-400` | opposite (covered) |
| `17# x 19#` | `-6950` | opposite (covered) |
| `19# x 23#` | `+977448` | **same sign** |
| `23# x 29#` | `-17622192` | opposite (covered) |

with `M(2#..29#) = 0, -1, -3, -1, -1, 16, -25, 278, 3516, -5012` (all exact).

Four of the nine consecutive pairs are same-sign, **including the block
immediately preceding the `29#` block**. On `(19#, 23#]` the anchors are
`M(19#) = 278` and `M(23#) = 3516`, both positive, so the uncovered set is
exactly `{x : M(x) > 3516}`, and the scan finds

```text
left only 0,  right only 95958912,  both 109500980,  uncovered 7933289
```

out of `213393181` prefixes — about `3.7%` of the block, containing the block
crest `M = 5971` at `x = 220260118`. The gap case is therefore real, large, and
adjacent, not a hypothetical.

**Consequence for the proof program.** Of the three repairs listed in the issue,
option 1 — an anchor-bracketing property for consecutive primorial endpoints — is
**false as stated**. Option 3 works at the level of signs: `M(17#) = -25` has the
opposite sign to `M(23#) = 3516`, so admitting the anchor from one further
completed block restores total coverage of `(19#, 23#]`. Option 2 remains the
fallback wherever no completed endpoint of either sign is available.

---

## 4. Coverage is cheap; the constant is not

Sign coverage says nothing about the size of `K`. The exact question is

```text
K_anchor = max_x sqrt( min over covering c of (c^2 + (M(x)-c)^2) / Q(x) )
```

versus the true `K_* = max_x |M(x)| / sqrt(Q(x))`. Both are computed exactly.

| block | `K_*` | `K_anchor` (block endpoints) | ratio | uncovered |
|---|---:|---:|---:|---:|
| `(13#, 17#]` | `0.593775408250` | `0.725254249583` | `1.2214` | `0` |
| `(17#, 19#]` | `0.536418786646` | `1.026583968026` | `1.9138` | `0` |
| `(19#, 23#]` | `0.595311149129` | `1.968097029386` | `3.3060` | `7933289` |
| `(23#, 29#]` | `0.590510118734` | `1.022394622291` | `1.7314` | `0` |

The `(19#, 23#]` figure is over its covered prefixes only; the uncovered ones have
no anchor obligation to satisfy at all.

So on the `29#` block the cross-term-free reduction is valid at every prefix but
costs a factor `1.73` in the constant, and the loss is largest near the left
endpoint (attained at `x = 228044335`, only `0.08%` into the block), where `Q(x)`
is still close to `Q(L)` while the fixed anchor value `M(L)^2` is already being
charged.

The trade-off is exactly the identity of section 1: the excess equals the
discarded cross term `-2c(y-c)`, so it shrinks with `|c|`. Anchoring further back
therefore *lowers* the constant — the `(13#, 17#]` scan with all frozen primorial
endpoints admitted returns exactly `K_*`, because `M(2#) = 0` is a frozen anchor
and a zero anchor is lossless. **That figure is degenerate and must not be quoted
as progress:** with `c = 0` the excursion `A(x) = M(x) - c` is the whole Mertens
value, so the shell estimate that has to bound it is the original problem. The
useful anchors are those for which `A(x)` is a shell increment; those are the
block endpoints, and their cost is the table above.

The honest statement is therefore:

> Anchor selection is a coverage device, not an estimate. It converts a signed
> orientation obligation into a magnitude obligation at a known, bounded price —
> a factor `1.22` to `1.73` in `K` on mature blocks — and it leaves the entire
> analytic difficulty in the shell estimate for `A(x)`.

---

## 5. Square-root scaling: boundedness, not a universal constant

At `x_*` the exact fibre data are (**reproduced**, from a `29#`-wide sieve)

```text
P_2(x_*) = -14921.25 = -59685/4         A_2 = 718357949
m_2      = (3/4) A_2 = 538768461.75     |P_2|/sqrt(m_2) = 0.642841823379
alpha_2  = |P_2|/m_2                    alpha_2 sqrt(x_*) = 0.92243
P_2 / (M(x_*) - M(23#)) = 0.7915362580  (the fibre carries 79.15% of the excursion)
```

Both normalizations are exact rationals and are pinned in Lean-checkable form:

```text
0.6428^2 m_2 < P_2^2 < 0.6429^2 m_2,     0.9224^2 < alpha_2^2 x_* < 0.9225^2.
```

The coefficients quoted at the `19#` trough (`~0.96`) and crest (`~0.33`) are
**not recomputed here** — the published data for those points does not include
`m_2`, so they are carried as reported values. The structural conclusion does not
depend on them: three locations, three different constants, all of square-root
order. The theorem to seek is therefore

```text
|P_2(x)| <= C sqrt(m_2(x))
```

with `C` absolute — boundedness, not convergence to a universal constant. This is
also what the block-level scans support: `K_*` is `0.5938`, `0.5364`, `0.5953`,
`0.5905` on the last four blocks — stable in magnitude, not converging to a
distinguished value.

One further reproduction: the `(17#, 19#]` diagnostic points of the earlier
addendum are confirmed. The block trough is at `x = 7109110` with `M = -1078`,
i.e. block increment `M(x) - M(17#) = -1053` exactly as reported, and the crest is
at `x = 6481601` with `M = 1060`.

---

## 6. Degree shells: the tail is not discardable

The ten reported shell nets at `x_*` sum to `-59685/4` exactly, which is an
independent consistency check against the sieved fibre value. Their partial sums

```text
+510599 -> -841738 -> +173005 -> +253101 -> -92475 -> -34199
        -> -12672  -> -13860  -> -14960  -> -14921
```

give

```text
head E_0..E_4 = -92475.462      |head| / |P_2| = 6.1976
tail E_5..E_9 = +77554.212      |tail| / |P_2| = 5.1976
```

So a theorem that keeps degrees `0..4` and discards the rest overshoots the net
by a factor `6.2`; the discarded tail is itself `5.2` times the answer. The
correct structural statement is a dominant low-degree oscillation **plus** a
smaller stabilizing tail that must be retained.

Two corrections to the diagnostic wording:

* The claim "degrees `0..4` contain approximately `95%` of the total grouped
  absolute mass" cannot be checked against the published numbers. With the
  published shell nets the head share of `sum_d |E_d|` is `97.5741%`. The `95%`
  figure must refer to the per-degree leaf `l1` mass, which was not published;
  the two quantities are different and should not be conflated.
* The survivor factors `rho_3 = 0.9773`, `rho_5 = 0.1534`, `rho_7 = 0.2038`,
  continuing `0.4289, 0.5768, 0.6967, 0.7681, 0.8084, 0.8367`, are **reproduced**
  exactly as ratios of consecutive grouped `l1` masses,
  `rho_q = A_{<=prev} / A_{<=q}`. Since `|P_2|` is fixed, `rho_q` is the
  reciprocal of the `l1`-mass growth of the chosen grouping — a property of the
  representation, not an operator contraction factor. The conclusion drawn in the
  issue survives and is strengthened: a norm that demands contraction from each
  individual prime is not merely unavailable, it is measuring the wrong thing.

**The tree is ternary.** Grading `{C,S,W}^9` by the number of non-`C` coordinates
gives shells of size `choose(9,d) 2^d`, summing to `3^9 = 19683`. A Boolean
subset model keeps `choose(9,d)`, summing to `2^9 = 512`, and so discards `19171`
components. Möbius inversion must be run in the ternary incidence algebra, or the
`W`-modes regrouped exactly first, or `C, S, W` retained as three transfer
operators.

---

## 7. The transfer recursion, formalized

The third route is the one carried into Lean. With `T_q = S_q + W_q` acting as
genuine additive operators on the shell family,

```text
E_d^{(j)} = C_q E_d^{(j-1)} + T_q E_{d-1}^{(j-1)},
F_j(z)    = (C_q + z T_q) F_{j-1}(z),
P_2       = F_j(1).
```

`RHLean/Proof/DegreeShellTransfer.lean` proves:

* each adjunction raises the degree support by exactly one (`supported_shellStep`);
* on any window containing the support, totalling the adjoined family is
  `(C + T)` applied to the total (`sum_shellStep_window`) — this is evaluation at
  `z = 1`;
* iterated over a list of primes, the total is the ordered operator product
  `prod_q (C_q + T_q)` applied to the initial total (`sum_shellSteps`).

That is the algebraic skeleton of the target

```text
| ev_{z=1} prod_{q <= p} (C_q + z(S_q + W_q)) F_0 |  <<  sqrt(m_2(x)).
```

The analytic content — a bound on that product — is untouched, and the survivor
data above says it cannot be obtained prime by prime.

---

## 8. Open obligations

1. The shell estimate for `A(x) = M(x) - M(L)` uniform over every prefix of a
   block, which is what the anchor lemma reduces the problem to and does not
   supply.
2. A quantitative endpoint reserve for the same-sign blocks — `(19#, 23#]` is the
   concrete test case, with `7933289` prefixes covered by no block endpoint.
3. A uniform bound on the transfer product, retaining the full degree range: the
   head/tail split forbids truncation and the survivor factors forbid a
   prime-by-prime contraction argument.
4. Whether `K_anchor` stays bounded as blocks grow. It is `1.22`, `1.91`, `3.31`,
   `1.73` times `K_*` on the last four blocks; the reduction is only useful if
   that ratio does not grow.

## Falsification criteria

* Exhibit a primorial block whose `K_anchor` (block endpoints, uncovered prefixes
  excluded) exceeds any proposed absolute `K` — the anchor reduction is then not
  the right device.
* Exhibit a block in which the uncovered set is not controlled by the reserve of
  any completed endpoint — option 2 then fails as well.
* Exhibit a prefix where `|M(x)| > K sqrt(Q(x))` for the proposed `K` — the
  invariant itself fails.

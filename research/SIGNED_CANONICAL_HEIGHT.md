# Signed canonical height: corrected clock, low-imbalance counting, remaining target

Verification and formalization of the corrected signed-height attack. Every claim in
sections 1–4 of the source note was checked; all hold. The recomputation is
`scripts/TwoAnchorSlackCoverage/signed_height_check.py` and the formalization is
`RHLean/Proof/SignedCanonicalHeight.lean`.

## Status

| layer | classification |
|---|---|
| corrected clock identity, and refutation of the `1_{h<=n}` variant | **exact**, formalized |
| transport-born / born-smooth versus `sign(Y_*)` | **exact**, boundary located |
| low-imbalance counting theorem | **exact**, formalized |
| low-band local energy | **exact**, formalized |
| balanced-regime endpoint characterization and symmetric coefficient | **exact**, formalized |
| exact balanced/extreme split of the high-band block increment | **exact**, formalized |
| high canonical-imbalance population `Z(m) > n^{1+delta}` | **open** — the remaining target |

Nothing is connected to the protected theorem graph.

---

## 1. The corrected clock

For squarefree `m > 1`, `q = P⁺(m)`, `c = m/q`, `e(m) = ceil(sqrt(m+1)) - 1`,
`h(m) = q - 1`:

```text
mu(m) 1_{e <= n} = -mu(c) 1_{e <= n < h} + mu(m) 1_{max(e,h) <= n}.
```

**Verified**: zero failures over all squarefree `m < 4000` and all `n < 200`. The
variant with `1_{h <= n}` fails `4099` times on the same range, first at exactly the
stated counterexample

```text
m = 30,  q = 5,  c = 6,  e = 5,  h = 4,  n = 4:   left 0,  variant -1.
```

Since `mu(m) = -mu(c)` for squarefree `m` with `q` its largest prime factor, the whole
content is an indicator identity, and `clock_indicator` proves it for arbitrary
`e, h, n`. `false_clock_at_thirty` pins the refutation.

### The entry clock is the integer square root

```text
ceil(sqrt(m+1)) - 1 = floor(sqrt(m))
```

with zero mismatches over all `m < 2 * 10^6`. Both sides equal the unique `e` with
`e^2 <= m < (e+1)^2`. So `e(m) = Nat.sqrt m`, and block membership `m ∈ B_n` is
exactly `Nat.sqrt m = n` — no real-valued square root is needed anywhere.

### The two classes

`e < h` is transport-born, `h <= e` is born-smooth. Unwinding, transport-born is
`c <= q - 2` while `Y_*(m) > 0` is `c <= q - 1`, so the two agree except exactly at
`c = q - 1`. **Verified**: over all squarefree `m < 200000` there are `36` mismatches
and every one has `c = q - 1`. The "harmless integer boundary at entry" is precisely
that locus.

---

## 2. The low-imbalance counting theorem

```text
#{ m ∈ B_n : mu(m) != 0, Z(m) <= H }  <=  1 + floor(H/n).
```

**Verified** for every `n` in `[2, 700)` at `H ∈ {0, n/2, n, 2n, 5n, 17n}`; it holds
in all cases.

The proof is a statement about factor pairs, with no reference to `mu`, to primality,
or to which factor is larger, and it is formalized in that sharper form. Writing a
pair as `(u, u+d)`:

* **`two_mul_le`** — `2n <= 2u + d`. From `(2u+d)^2 - 4u(u+d) = d^2 >= 0` and
  `u(u+d) >= n^2`.
* **`gap_mul_le`** — hence `2dn <= d(2u+d) <= 2H`, so `d * n <= H`: only
  `1 + floor(H/n)` gaps can occur.
* **`u_unique`** — for a fixed gap, consecutive products differ by
  `(u+1)(u+1+d) - u(u+d) = (u+v) + 1 >= 2n + 1`, which exceeds the block diameter
  `2n`. So at most one `u` per gap.
* **`card_le`** — the two combine: the gap map is injective on admissible pairs and
  lands in `{0, ..., floor(H/n)}`.

A squarefree `m` supplies the single pair `(c, q)`, and distinct `m` have distinct
products, so the bound applies to `#F_n^can(H)` a fortiori.

Note what the proof does **not** use: no bound on `c` versus `q`, no squarefreeness,
no primality. It is pure factor-pair geometry in the block, which is why it is
unconditional.

---

## 3. The low-band energy

With `d_n^low` the signed block sum over `Z(m) <= Λn` and `S_n^low` its prefix sum,
the counting theorem gives `|d_n^low| <= C_Λ` with `C_Λ = 1 + floor(Λ)` and hence
`|S_n^low| <= C_Λ n`.

**Verified** for `Λ ∈ {0, 1, 2, 5}` over all `n` in `[2, 700)`: both bounds hold at
every `n`.

`window_energy_le` formalizes the consequence: from `|S_n| <= C n` and `H <= N`,

```text
sum_{n=N}^{N+H-1} |S_n|^2 <= 4 C^2 H N^2,
```

since each term is at most `C^2 (N+H-1)^2 <= 4 C^2 N^2`. The whole fixed
low-imbalance band therefore satisfies the desired local square-prefix energy bound
unconditionally, with no transport-lifetime factor. Taking `Z(m) <= n^{1+delta}` gives
`|d_n| <= 1 + n^delta` and local energy `<< H N^{2+2delta}`, so any `N^epsilon`-wide
gap band is absorbed into the final epsilon-loss.

---

## 4. The balanced regime

`RHLean/Proof/BalancedCanonicalGap.lean` works the fixed-gap representation of §2 in
the **balanced regime** `0 < d < u`, and `scripts/TwoAnchorSlackCoverage/balanced_gap_check.py`
re-tests every statement by direct enumeration (all pairs with `u <= 700`, `d <= 4000`).
All checks pass.

**Scale localization.** `n^2 < 2u^2` and `u <= n <= u+d < 2n`. Both endpoints sit
within a bounded factor of the block index, so the square-block map is a translation
up to bounded distortion.

**Height sandwich.** `2dn <= 2Z < 3dn`, i.e. `2Z` and `dn` agree to within the
explicit constants `2` and `3`. This upgrades §2's one-sided `dn <= H` to a genuine
two-sided comparison, which is what lets a height threshold be read as a gap
threshold and back. Measured over the enumeration, `2Z/(dn)` runs over
`[2.0014, 2.6667]`: the lower constant `2` is essentially attained and the true
supremum is `8/3`, so the proved upper constant `3` is safe but not sharp.

**Endpoint-prime characterization.** In the balanced regime, being the canonical
largest-prime split is *equivalent* to at least one endpoint being prime. The
largest-prime condition — normally a global statement about `P⁺` — collapses to a
primality test on two numbers. The balance hypothesis is doing real work: outside
`0 < d < u` the equivalence fails, and not only degenerately. The first coprime
witness is `u = 2`, `v = 9`, `d = 7`, where `u` is prime but `9` carries the larger
prime factor `3`, so neither endpoint dominates.

**The symmetric coefficient.** Writing `beta(u,d) = mu(u) mu(u+d) 1_{u or u+d prime}`,
the canonical source coefficient equals `beta` throughout the balanced regime, and

```text
beta = -mu(u) 1_{u+d prime} - mu(u+d) 1_{u prime} - 1_{u prime} 1_{u+d prime}.
```

These are exactly the two signed channels of §5 below, with the prime-prime overlap
subtracted once — verified across all four prime/composite cases and by enumeration.
The two channels are therefore not merely coupled by choice; they are two halves of a
single symmetric object plus a diagonal correction.

**Exact reconstruction.** The finite high-band block increment splits with no
remainder into its balanced part (`d < u`, evaluated by `beta`) and its extreme part
(`u <= d`). The split is an identity, not an estimate: nothing is discarded, and the
extreme part remains to be handled.

### Both decompositions are exact; the raw pieces fail, and one term is why

This is the measurement that constrains how the balanced results can be used.
`scripts/TwoAnchorSlackCoverage/balanced_split_frontier.py` computes the prefix sum
of every piece of both decompositions over blocks `n <= 1900` (`m < 3.6 * 10^6`). The target's prefix form is `|sum_{n<=N} d_n| << N^{1+eps}`, so the diagnostic is
`|prefix| / N`. A stable ratio is compatible with the target on the tested range;
sustained upward drift rejects the proposed piecewise mechanism at that range. It
does not by itself prove an asymptotic theorem.

| piece | `N=300` | `600` | `900` | `1200` | `1500` | `1900` | `max |·|/N` |
|---|---|---|---|---|---|---|---|
| `A = -mu(u) 1_{u+d prime}` | −0.197 | −0.140 | 0.064 | 0.005 | −0.099 | −0.035 | **0.309** |
| `B = -mu(u+d) 1_{u prime}` | −0.130 | 0.100 | 0.054 | −0.137 | 0.115 | −0.245 | **0.245** |
| `C = -1_{u prime} 1_{u+d prime}` | −3.437 | −5.628 | −7.550 | −9.263 | −10.901 | −12.874 | 12.874 |
| `A + B` (Möbius channels) | −0.327 | −0.040 | 0.119 | −0.132 | 0.017 | −0.280 | **0.394** |
| `beta = A+B+C` = balanced half | −3.763 | −5.668 | −7.431 | −9.395 | −10.884 | −13.154 | 13.154 |
| extreme half | 3.793 | 5.457 | 7.358 | 9.349 | 10.758 | 13.182 | 13.228 |
| **total (the truth)** | 0.030 | −0.212 | −0.073 | −0.046 | −0.126 | 0.027 | **0.430** |

> **Methodological note.** Do not fit a log-log exponent to these series. Every piece
> except `C` changes sign repeatedly, and `log |prefix|` plunges at each crossing, so
> least squares on `log |prefix|` against `log n` reports growth that is not there. An
> earlier pass of this record did exactly that and recorded `1.338` for `B` and
> `1.406` for `A + B`; both are artifacts. The measured trajectories of `B` and
> `A + B` remain small on this range. Only `C` is monotone on the sampled range,
> and its fitted `1.714` is a descriptive finite-range exponent, not a theorem.

Three things follow.

1. **The balanced/extreme split destroys the observed cancellation.** Each half
   reaches `13.2 N` and is still climbing on the tested range, against the truth's
   `0.43 N`, and each is about `500x` its own sum at `N = 1900`. This fails the
   predeclared finite stop criterion for separate estimates; it is not a proof that
   every conceivable asymptotic treatment of the pieces is impossible.

2. **The measured obstruction is exactly one piece, and it is a count.** `C` is
   minus the number of balanced coprime prime-prime pairs in the block and contributes
   `-24461` of the balanced half's `-24993` at `N = 1900`. It is monotone on the
   sampled range; a descriptive fit there is approximately `N^{0.71}` per unit `N`.

3. **The measured Möbius channels remain small.** The observed maxima of `A`, `B`
   and `A + B` are `0.309`, `0.245` and `0.394`, the same scale as the total's
   observed `0.430`. On this range, the excess of the two halves is carried by `C`
   and `-C`; this statement is diagnostic rather than asymptotic.

So `beta_symmetric_identity` and `highBandBlockIncrement_eq_balanced_add_extreme` are
exact rewritings that do not by themselves license a term-by-term estimate — but they
localize the measured excess in a single explicit, Möbius-free counting function.

### The same statement in the energy norm: the cross term is the whole estimate

`RHLean/Proof/CanonicalGapPrefixGram.lean` supplies the exact prefix-energy ledger

```text
E(bal + ext) = E(bal) + 2 Cross(bal, ext) + E(ext),
```

together with the closed-form Gram kernel `#{r < H : i <= r and j <= r} = H - max(i,j)`.
This is the right frame for the target, which is an energy bound, and the frontier
above says exactly what the ledger's three terms must look like.
`scripts/TwoAnchorSlackCoverage/prefix_gram_cross.py` evaluates all of them on real
windows of blocks `[N, N+H)`. The identity holds exactly in every window — it is
checked, not assumed — and the sizes are:

| `N` | `H` | `E(bal)` | `E(ext)` | `2 Cross` | `E(total)` | `rho` | `E(bal)/HN²` | `E(total)/HN²` |
|---|---|---|---|---|---|---|---|---|
| 400 | 100 | `2.42e7` | `2.92e7` | `-5.26e7` | `7.9e5` | `-0.989` | 1.51 | 0.050 |
| 700 | 175 | `1.79e8` | `1.92e8` | `-3.68e8` | `3.1e6` | `-0.992` | 2.09 | 0.036 |
| 1000 | 250 | `1.17e9` | `9.11e8` | `-2.06e9` | `2.0e7` | `-0.998` | 4.69 | 0.079 |
| 1400 | 350 | `6.48e9` | `7.56e9` | `-1.40e10` | `5.6e7` | `-0.999` | 9.44 | 0.082 |

`rho = Cross / sqrt(E(bal) E(ext))` is the prefix correlation between the two halves.
It approaches `-1` across the measured windows.

The last two columns settle the declared finite test. The target scale is
`E << H N^{2+eps}`. On the measured windows, `E(total)/HN²` stays at the `10^-2`
scale, which is compatible with the target, while `E(bal)/HN²` runs
`1.51, 2.09, 4.69, 9.44` and rises sharply. Thus the data reject estimating the
balanced half alone; by the same calculation the extreme half is not a viable
separate target either. These are finite diagnostics, not asymptotic proofs.

Three consequences for using the ledger:

* `Cross` cannot be dropped. It is the dominant term, not a remainder — it is larger
  in magnitude than `E(total)` by two to three orders of magnitude.
* `Cross` cannot be handled by Cauchy–Schwarz. `|Cross| <= sqrt(E(bal) E(ext))` is
  true and nearly an equality here, and applying it gives
  `E(total) <= (sqrt(E(bal)) + sqrt(E(ext)))²`, a bound built from two quantities that
  are each already over budget. Any estimate of `Cross` that does not reproduce both
  its sign and its near-extremal magnitude throws away the entire cancellation.
* Therefore the ledger is an exact accounting of *where* the cancellation lives, and
  it localizes it entirely in the cross term. That is genuine information. It is not
  a reduction: it does not produce a smaller object to estimate.

### The excess is a main term, and subtracting it helps but does not suffice

Everything above rejects separate estimation of the **raw** halves under the
declared finite diagnostic. It does not say whether the excess is structured. It is, and `scripts/TwoAnchorSlackCoverage/balanced_main_term_repair.py`
identifies it in closed form.

> **Read this section with the next one.** What follows measures the prefix norm at
> `n <= 1900`, where subtracting the main term does bring the balanced half inside
> budget. The energy norm at `N` up to `40000` — the diagnostic the target actually
> uses, in the next section — shows the normalized subtracted-half ratio rising again.
> The main term is real and removing it helps by a large factor, but it fails the
> declared finite energy test.

Split the balanced pair population by primality of the endpoints and let `N_pp(n)`
count the balanced coprime prime-prime pairs with product in `B_n`. With
`beta = mu(u) mu(u+d) 1_{u or u+d prime}`:

| case | value of `beta` | contribution |
|---|---|---|
| both prime | `+1` on every pair | `+N_pp` |
| `u` prime, `u+d` composite | `-mu(u+d)`, and `sum_{composite} mu = sum_{all} mu - sum_{prime} mu ~ +N_pp` | `-N_pp` |
| `u+d` prime, `u` composite | symmetric | `-N_pp` |

so the predicted main term of the whole balanced half is `-N_pp`, which is exactly the
overlap term `C`. And `N_pp` can be replaced by a prime-density prediction `Cpred`
that uses no Möbius input at all: for each prime `u <= n` the admissible window for
`u+d` is an explicit interval, and primes in it have density `1/log`. Measured:

| series | prefix at `N = 1900` | `max |·|/N` | verdict |
|---|---|---|---|
| balanced half, raw | `-24993` | 13.154 | fails |
| `C = -N_pp` | `-24461` | 12.874 | fails |
| `Cpred`, density prediction of `C` | `-25119` | 13.220 | fails |
| `balanced - C` (exact count subtracted) | `-532` | 0.394 | **passes** |
| `balanced - Cpred` (density subtracted) | `+126` | 0.444 | **passes** |

The raw half reaches `13.2 N`; after subtracting the main term, the maximum
observed ratio is `0.39 N`, the same finite scale as the total's `0.43 N`. Both the
exact count and its Möbius-free density prediction reproduce this short-range repair.
Since the two halves sum to the total, the same deterministic subtraction may be
transferred between them without changing the exact reconstruction.

So on this range and in this norm the subtracted halves are inside budget. **That does
not survive the energy norm at larger `N`** — see the next section, where the same
subtraction gives `0.071, 0.253, 0.973, 1.009, 4.434` for `N = 1000` to `40000`,
with a descriptive finite-range fit near `N^{1.08}`. The prefix diagnostic at
`n <= 1900` is too short and too weak to reveal that later rise.

What stands is the structural part: the common main term is the explicit
prime-pair count `N_pp`, not a Möbius correlation, and subtracting it is a finite
deterministic step that removes most — but not all — of the measured excess.

This also explains the finite table: `A`, `B` and `A + B` exclude the overlap
term and remain small on the sampled range. The measured excess is not in those
Möbius channels.

### Explicit main term versus window mean

[`research/CANONICAL_GAP_PREFIX_GRAM_SCAN.md`](CANONICAL_GAP_PREFIX_GRAM_SCAN.md)
removes the coherent increment mode a different way: by subtracting each sequence's
**window mean**, the Brownian-bridge construction. Its finite verdict is that this works on the tested short windows but fails the
declared criterion on the tested long windows — at `H = N` the separate bridge energies
`Q^o_BB/(HN^2)` are `0.65`, `11.1`, `27.5` at `N = 1000, 5000, 10000`, i.e. over
budget and climbing.

That is a statement about mean subtraction specifically, and the distinction matters.
The window mean can only remove a drift that is linear across the window, while the
main term identified above varies nonlinearly across `[N, 2N)`. So the two repairs are
not interchangeable. `scripts/TwoAnchorSlackCoverage/main_term_vs_bridge.c` runs both
on the same windows:

| window | `H/N` | raw `Q_BB/(HN²)` | bridge | minus `Cpred` | `Q_tot/(HN²)` |
|---|---|---|---|---|---|
| `[1000,2000)` | 1.00 | 104.75 | 0.65 | 0.071 | 0.10884 |
| `[5000,10000)` | 1.00 | 1232.00 | 11.14 | 0.253 | 0.08159 |
| `[10000,20000)` | 1.00 | 3552.50 | 27.50 | 0.973 | 0.09036 |
| `[20000,40000)` | 1.00 | 11071.62 | 105.21 | 1.009 | 0.08561 |
| `[40000,80000)` | 1.00 | 33339.64 | 266.31 | 4.434 | 0.09115 |

The raw and bridge columns reproduce the prefix-Gram scan's own figures to every
digit it reports (`104.754`, `1232.004`, `3552.497`, and `0.645512`, `11.142857`,
`27.502757`), from an independent implementation — so the comparison is like-for-like.

**The main term does not rescue the split on the tested range.** The normalized
sequences are monotone at the sampled points, so descriptive log-log fits give raw
`1.562`, bridge `1.641`, and minus-`Cpred` `1.078`. These fits summarize the finite
data; they do not prove asymptotic exponents. The explicit main term is the better
repair by a wide margin — `60x` smaller than the bridge at `N = 40000` — but its
normalized ratio still rises and therefore fails the route's declared stop criterion.

An earlier version of this section claimed the minus-`Cpred` column flattened, on the
strength of `0.973 → 1.009` from `N = 10000` to `20000`. The next point is `4.434`.
That plateau was noise in a rising sequence, not convergence; the step ratios are
`3.55, 3.85, 1.04, 4.39`, and reading the one small ratio as a trend was wrong.

So the prefix-Gram scan's verdict stands, and applies more widely than to mean
subtraction alone: **separate diagonal estimates are the wrong primary target**, for
the raw halves, for the bridge, and for this main-term-subtracted version. What the
comparison establishes is narrower than a repair — the failure rate depends strongly
on how the coherent mode is removed, and an arithmetic main term removes far more of
it than an empirical window mean does.

Whether a sharper main term would do better is untested. `Cpred` is crude — `1/log` at
the interval midpoint — and its own modelling error grows with `N`, so some of the
residual fit may partly reflect the model rather than the arithmetic. But that is a
conjecture about an uncomputed quantity. The measured fact is only that this residual
ratio rises over the sampled range.

---

## 5. The terminal statement, and why `Λ` is not a lever

PR #196 closed the formal reduction:
`ProjectedRenewalQuadraticBoundedStatement Λ ↔ RiemannHypothesisStatement`, given
`ClassicalMertensRHCriterion`. Kernel-checked in
[`RHLean/Proof/TerminalAxiomAudit.lean`](../RHLean/Proof/TerminalAxiomAudit.lean):
all three carrying theorems print `[propext, Classical.choice, Quot.sound]` and
nothing else.

Two consequences worth stating flatly.

**The remaining step is RH, not an approach to RH.** The equivalence is proved, so
`ProjectedRenewalQuadraticBoundedStatement` is neither easier nor harder than the
Riemann Hypothesis. No weaker formal bridge remains in the current chain: once the classical
criterion is supplied, proving this proposition proves RH.

**`Λ` is not an optimization parameter.** It should be treated as fixed at `0`, not as
one endpoint in a search over cutoffs. The equivalence holds for *every* `Λ ≥ 0`, so
every instance is exactly RH and none is easier; there is nothing to search over. The
measurement in
`scripts/TwoAnchorSlackCoverage/terminal_lambda_dependence.c` confirms this
operationally: it finds no sustained improvement from increasing `Λ`, and large
values are materially worse on both tested windows:

| `Λ` | `Q/(HN²)`, `N=1000` | `Q/(HN²)`, `N=4000` |
|---|---|---|
| 0 | 0.0609 | 0.0638 |
| 1 | 0.0609 | 0.0638 |
| 2 | 0.0614 | 0.0636 |
| 5 | 0.0828 | 0.0734 |
| 10 | 0.1455 | 0.1015 |
| 25 | 0.9248 | 0.4804 |

The reason is structural. `S^high = S_total − S^low`, and the low band's own prefix is
`O(Λn)` — that is exactly the content of the unconditional counting theorem of §2.
Subtracting a quantity permitted to be as large as `Λn` from a near-cancelling total
can introduce a coherent drift that the total itself does not have. The low
band was already harmless; removing it costs.

So the low/high split, and the counting theorem that controls the low band, do not
reduce the terminal difficulty. They were worth proving — they establish the low band
is not where the problem lives — but they buy nothing further. **The cleanest form of
the remaining statement is `Λ = 0`**, where `canonicalHighPrefix 0 n` is the full
square-block Möbius prefix and the statement reads

```text
sum_{h<H} |M((N+h+1)^2 - 1)|^2  <<_eps  H N^{2+eps},
```

which is the square-endpoint energy formulation connected by the proved bridge to
the classical Mertens criterion. The displayed local-energy estimate is not itself a
separately proved pointwise bound.

---

## 6. What remains

The high canonical-imbalance population `Z(m) > n^{1+delta}`, retaining both signs:

```text
Y_* > 0   one-large-prime transport: small core, larger prime;
Y_* < 0   born-smooth extensions, recursively generated by smaller-prime ancestry.
```

with local target

```text
sum_{r=0}^{H-1} | sum_{n=N}^{N+r} d_n^high |^2  <<_eps  H N^{2+eps}.
```

This permits cancellation between the two signs and between distant height shells. An
absolute estimate for every vertical-difference shell separately is **stronger than
necessary** and is not justified by the low-height counting theorem.

In the fixed-gap representation, at most one `u` contributes per gap per block, and
the two channels are

```text
Y_* > 0:   -mu(u) 1_{u+d prime}
Y_* < 0:   -mu(u+d) 1_{u prime}   when u+d is composite with all prime factors below u
```

the side condition being automatic for composite `u + d < 2u`. The block index is
`n = floor(sqrt(u(u+d)))`. So the high band is a curved pushforward of averaged
Möbius-prime shifted correlations. Existing averaged-shift results give qualitative
cancellation over sufficiently many shifts but not the square-root-strength local
energy needed here, so the two signed channels must remain coupled.

§4 sharpens what "remains" means. The balanced part of the high band is now written
exactly, in closed form, as the symmetric coefficient `beta` — no side conditions and
no case analysis survive. So the open problem is no longer "identify the high-band
channels"; it is the single estimate

```text
sum_{r=0}^{H-1} | sum_{n=N}^{N+r} beta-block-sum(n) |^2  <<_eps  H N^{2+eps},
```

for the balanced part, plus a separate treatment of the extreme part `u <= d`. The
extreme part is not covered by any of the balanced results: the endpoint-prime
characterization genuinely fails there (`u = 2`, `v = 9`), so its coefficient is still
the unreduced `canonicalCoefficient`.

That sizing has now been done, and it is negative: the extreme part is **not** small,
and neither is the balanced part. Each carries a prefix of about `25000` at `N = 1900`
where the true total is `52`. So the sentence above is the wrong target — the balanced
estimate and a separate extreme estimate cannot be combined, because their measured normalized prefixes carry roughly an additional
`n^{0.6}` factor over this finite range. What must be estimated is the coupled object. The balanced results narrow
*what* has to cancel — the overlap term `C` is a prime-pair count, and `A` already
meets the target on its own — but they do not produce a piece that can be bounded
alone. See the table in §4.

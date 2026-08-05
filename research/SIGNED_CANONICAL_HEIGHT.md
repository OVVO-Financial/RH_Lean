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

### Both decompositions are exact and neither may be estimated piecewise

This is the measurement that constrains how the balanced results can be used.
`scripts/TwoAnchorSlackCoverage/balanced_split_frontier.py` computes the prefix sum
of every piece of both decompositions over blocks `n <= 1900` (`m < 3.6 * 10^6`). The
target's prefix form is `|sum_{n<=N} d_n| << N^{1+eps}`, so the diagnostic is
`|prefix| / N`: bounded means the piece is within the target, upward drift means it is
not.

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
> `1.406` for `A + B`; both are artifacts, and the trajectories above show both are
> bounded. Only `C` is monotone, and only for `C` is the fitted `1.714` meaningful.

Three things follow.

1. **The balanced/extreme split destroys the cancellation.** Each half reaches
   `13.2 N` and is still climbing, against the truth's `0.43 N`, and each is about
   `500x` its own sum at `N = 1900`. Bounding the two halves separately and adding
   them cannot reach the target, and no sharpening of the individual bounds recovers
   it, because the halves genuinely are that large.

2. **The obstruction is exactly one piece, and it is a count.** `C` is minus the
   number of balanced coprime prime-prime pairs in the block: monotone, with no
   cancellation available, contributing `-24461` of the balanced half's `-24993`. It
   grows like `N^{0.71}` per unit `N`.

3. **The Möbius content is already fine.** `A`, `B` and `A + B` are all bounded, at
   `0.309`, `0.245` and `0.394` — the same scale as the true total's `0.430`. So the
   balanced half fails *only* because it carries `C`, and the extreme half fails only
   because it carries `-C`.

So `beta_symmetric_identity` and `highBandBlockIncrement_eq_balanced_add_extreme` are
exact rewritings that do not by themselves license a term-by-term estimate — but they
localize the entire failure in a single explicit, Möbius-free counting function.

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
It converges to `-1`.

The last two columns settle the question. The target is `E << H N^{2+eps}`.
`E(total)/HN²` sits at the `10^-2` level with no upward drift across the whole range,
so **the total meets the target**. `E(bal)/HN²` runs `1.51, 2.09, 4.69, 9.44` and keeps
climbing, so **the balanced half fails the same target on its own**, and by symmetry so
does the extreme half.

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

### The excess is a main term, and subtracting it repairs the split

Everything above rules out estimating the **raw** halves. It does not say the split is
useless, because it does not say whether the excess is structured. It is, and
`scripts/TwoAnchorSlackCoverage/balanced_main_term_repair.py` identifies it in closed
form.

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

The raw half drifts to `13.2 N`; after subtracting the main term it is bounded at
`0.39 N` — indistinguishable in scale from the true total's `0.43 N`. Both the exact
count and its Möbius-free density prediction work, which matters: the repair does not
need the prime-pair count itself, only an asymptotic for it. Since the two halves sum
to the true total, subtracting from the balanced half and adding to the extreme half
repairs both at once.

**So the split is usable — after main-term subtraction, and only then.** The correct
statement of the obstruction is not "the halves cannot be estimated" but "the halves
carry a common prime-pair main term of size `n` per block which must be removed before
either is estimated." That main term is explicit, it is a prime count rather than a
Möbius correlation, and removing it is a finite deterministic step. What remains after
removal is a centred object bounded by `0.44 N` on the measured range — inside budget,
and at the same scale as the truth itself.

This also explains why `A`, `B` and `A + B` are individually fine: none of them is
the overlap term. The Möbius channels of the balanced half never carried the problem.

---

## 5. What remains

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
estimate and a separate extreme estimate cannot be combined, because both are `n^{0.6}`
too large. What must be estimated is the coupled object. The balanced results narrow
*what* has to cancel — the overlap term `C` is a prime-pair count, and `A` already
meets the target on its own — but they do not produce a piece that can be bounded
alone. See the table in §4.

# Dyadic Möbius pairing of the signed exact-activity residual

Focused pen-and-paper analysis of Attack A. Every statement is classified as one
of **exact identity**, **plausible analytic estimate**, or **open step**. The
exact identities are verified to machine precision by
[`../scripts/DyadicMobiusSignedResidual/`](../scripts/DyadicMobiusSignedResidual/README.md).

No use is made of the midpoint-lifetime approximation, of a Mellin rank-one
model, or of any assumed cancellation for Möbius sums.

---

## 0. Objects and notation

Fix an integer `t >= 1`. Throughout write

```text
S = (t+1)^2 ,        X = S - 1 = t(t+2) .
```

For a positive cofactor `c` the exact active-prime interval endpoints
(PR #101, `ExactActivityPrimeIntervals.lean`) are

```text
L(t,c) = max( t+2 , ceil(S/(2c)) ) ,
U(t,c) = floor( X / c ) .
```

We abbreviate `U_c = U(t,c) = floor(X/c)`, so `U_2c = floor(X/(2c))`,
`U_4c = floor(X/(4c))`, and `a(c) = ceil(S/(2c))` (the *hyperbolic* lower
endpoint). The active interval is `I(t,c) = [L(t,c), U_c]`.

For a deterministic cumulative baseline `F : R -> C` put `E := pi - F` (the
exact prime-count error against the baseline). For a cumulative `G` write the
interval increment

```text
Δ_G(t,c) := G(U_c) - G(L(t,c) - 1) ,
```

so `Δ_pi(t,c) = pi(U_c) - pi(L(t,c)-1)` is the exact active-prime count and, by
linearity in the cumulative,

```text
Δ_F(t,c) := (pi - F)-increment = Δ_pi(t,c) - Δ_{F}(t,c) = Δ_E(t,c) .
```

The signed exact-activity residual on all squarefree cofactors is

```text
R_F(t) = Σ_{c <= t, squarefree} μ(c) · Δ_E(t,c) .
```

(The band-restricted object `R_F(t;C) = Σ_{C<=c<2C} μ(c) Δ_E(t,c)` is the
same sum with a dyadic cutoff; the pairing below moves mass between adjacent
bands, so it is cleanest to state the identity for the full cofactor range and
reinstate a smooth cutoff afterwards — see §5.)

The finite horizon `N` of the transport process enters only as the constraint
`t <= N`; for a *fixed* `t <= N` the exact interval is exactly `[L(t,c), U_c]`
with no further truncation (this is the content of
`isDyadicBoundaryActive_iff_product_bounds`). So the analysis below is at fixed
`t` and is horizon-free.

---

## 1. Exact interval algebra (all cases)

### 1.1 Reciprocal endpoint identity — EXACT

For all integers `S >= 1`, `m >= 1` one has `ceil(S/m) - 1 = floor((S-1)/m)`.
Applying this with `m = 2c`:

```text
a(c) - 1 = ceil(S/(2c)) - 1 = floor((S-1)/(2c)) = floor(X/(2c)) = U_2c .      (R)
```

**The hyperbolic lower endpoint of the parent `c` is exactly one more than the
upper endpoint of the child `2c`.** Consequently

```text
L(t,c) - 1 = max( t+1 , a(c) - 1 ) = max( t+1 , U_2c ) .                       (L)
```

Likewise `L(t,2c) - 1 = max(t+1, U_4c)`.

### 1.2 Regime threshold — EXACT

Because `floor(X/(2c)) >= t+1  <==>  X >= (t+1)(2c)  <==>  t(t+2) >= 2c(t+1)`,
and `2c <= t` forces `2c(t+1) <= t(t+1) < t(t+2)` while `2c >= t+1` forces
`2c(t+1) >= (t+1)^2 = t(t+2)+1`, we get the clean dividing line

```text
U_2c >= t+1   <==>   2c <= t ,        U_4c >= t+1   <==>   4c <= t .           (T)
```

Equivalently `L(t,c)` is *hyperbolic* (`= a(c) > t+2`) exactly when `2c <= t`,
and is the *prefix* value `t+2` exactly when `2c >= t+1`.

### 1.3 Non-emptiness — EXACT

`L(t,c) <= U_c  <==>  c <= t`. (For `c > t` the prime part `Δ_pi` counts an empty
interval.) So `R_F(t)` ranges over `1 <= c <= t`, and the pairing partner `2c`
is *in range* iff `2c <= t`, i.e. `c <= t/2`.

### 1.4 Exact interval difference of the `c`- and `2c`-channels

Using (L) and the threshold (T), the parent and child intervals are, in every
case, **adjacent disjoint reciprocal slabs meeting exactly at the shared node
`U_2c`**:

| regime (odd `c <= t`) | parent `I(t,c)` | child `I(t,2c)` | shared node |
|---|---|---|---|
| `4c <= t`        (I)  | `[U_2c + 1, U_c]` | `[U_4c + 1, U_2c]` | `U_2c` |
| `t/4 < c <= t/2` (II) | `[U_2c + 1, U_c]` | `[t+2, U_2c]`      | `U_2c` |
| `t/2 < c <= t`  (III) | `[t+2, U_c]`      | empty (`2c > t`)   | —      |

There is **never any overlap**: the symmetric difference of `I(t,c)` and
`I(t,2c)` is their disjoint union `[·, U_c]`, and the union is a *contiguous
reciprocal annulus* with cut point `U_2c`. This is the exact form of the
"reciprocal nesting" noted in the handoff.

### 1.5 The paired difference — EXACT

Let `G` be any cumulative, and write the interval increment
`E_G[a,b] := G(b) - G(a-1)` (`= 0` when `a > b`). From the table and (L), the
signed pair is the **difference of two adjacent multiplicative shells**:

```text
(I)   4c <= t :      Δ_G(t,c) - Δ_G(t,2c) = E_G[U_2c+1, U_c] - E_G[U_4c+1, U_2c] ,
(II)  t/4<c<=t/2 :   Δ_G(t,c) - Δ_G(t,2c) = E_G[U_2c+1, U_c] - E_G[t+2,   U_2c] ,
(III) t/2<c<=t :     Δ_G(t,c)              = E_G[t+2,   U_c]           (unpaired).
```

Equivalently, on point evaluations, this is
`G(U_c) - 2 G(U_2c) + G(U_4c)` (I), `G(U_c) - 2 G(U_2c) + G(t+1)` (II),
`G(U_c) - G(t+1)` (III).

**The pair does not collapse to a shorter interval.** It is a *signed contrast
of two adjacent reciprocal shells*
```text
(S/2c, S/c]   minus   (S/4c, S/2c]        (up to floors),
```
meeting exactly at the shared node `U_2c`. The two shells have **unequal
lengths** (a factor of two): the upper shell has length `≈ S/(2c)`, the lower
`≈ S/(4c)`. This is a one-scale reciprocal difference operator, **not** a
mean-zero (Haar) wavelet — a point made precise in §4.5. In region I the bottom
node is the next reciprocal point `U_4c`; in region II it is clamped to the
finite-horizon value `t+2`; in the unpaired region III there is no lower shell.

Note the point-evaluation `E(t+1)` (the diagonal endpoint) is genuinely absent
from region I. This is a *pointwise* cancellation of that one boundary value; it
is not the same as cancellation at the principal Fourier frequency, which does
**not** occur (§4.5).

---

## 2. The exact global decomposition — EXACT

Every even squarefree cofactor is `2c'` with `c'` odd, and `μ(2c') = -μ(c')`
(`MoebiusDoubling.lean`); multiples of `4` have `μ = 0`. Folding the even
cofactors onto their odd halves and using §1.5 gives the identity

```text
R_F(t) =  Σ_{odd c <= t/4}      μ(c) [ E(U_c) - 2 E(U_2c) + E(U_4c) ]     (I)
        + Σ_{odd t/4<c<=t/2}    μ(c) [ E(U_c) - 2 E(U_2c) + E(t+1)  ]     (II)
        + Σ_{odd t/2<c<=t}      μ(c) [ E(U_c) -   E(t+1)            ] .    (III)
```

This is proved to machine precision for a *random* real `E` (hence it is a pure
Möbius/endpoint identity) in the companion script. Structurally it is the exact
residual-side analogue of the `t`-summed transport compression already
formalized in `DyadicTransportCompression.lean`: even cofactors reduce to
`-`(odd at half scale), leaving an **odd boundary channel** `t/2 < c <= t` — the
same `B/2 < c <= B` boundary that appears there, now carrying reciprocal second
differences of `E` instead of packet suffixes.

### 2.1 The principal endpoint — EXACT

The value `E(t+1)` (the genuine prime error at the diagonal `t`) appears only in
regions II and III. Collecting its coefficient,

```text
[ coeff of E(t+1) in R_F(t) ]  =  M_odd(t/4, t/2]  -  M_odd(t/2, t] ,          (P)
     where  M_odd(a,b] := Σ_{a < c <= b, c odd} μ(c) .
```

(Identity (P) is verified exactly, integer arithmetic, in the script.) So the
**contribution of the diagonal point evaluation `E(t+1)` is exactly `E(t+1)`
times a difference of two short odd-Möbius sums**. This is one concrete
realization of the handoff warning: the Möbius signs must be retained — discarding
them (sign-blind Cauchy–Schwarz in `c`) destroys the cancellation in (P) and
reintroduces the full `E(t+1)` at strength `~ t`.

Caution: (P) concerns only the single value `E(t+1)`. It is **not** the principal
Fourier frequency of the pairing, which is a different object and does **not**
cancel — see §4.5.

---

## 3. Bilinear (Vaughan) form of the prime part — EXACT

The prime part of `Δ_pi(t,c)` is, by the three product inequalities equivalent to
interval membership (`exactActivityPrimeBounds_iff_product_bounds`),

```text
Δ_pi(t,c) = #{ p prime : p >= t+2 ,  S <= 2cp ,  cp <= X } .
```

Hence the prime part of `R_F(t)` is the Möbius × primes bilinear sum over a
hyperbolic band:

```text
Π(t) = Σ_{ c,p : S/2 <= cp < S ,  p >= t+2 } μ(c) · 1[p prime] ,               (B)
```

and `R_F(t) = Π(t) - (baseline analogue of Π with 1[p prime] -> dF)`. The band
`cp ∈ [S/2, S)` with `p > sqrt(S) = t+1` forces `c < t+1`. This is a Vaughan-type
object at the **balanced point** `c, p ≍ sqrt(S) = N`, `cp ≍ N^2`. The dyadic
pairing of §2 rewrites, inside this object, single-slab prime indicators as
adjacent-slab differences and removes the diagonal point evaluation `E(t+1)`
from the deep region — but it does **not** introduce any Fourier variable, and it
does **not** annihilate the principal (zero) frequency (§4.5).

---

## 3.5 Exact low-Mertens representations — EXACT

Fix a dyadic band `C <= c < 2C` and swap the two finite sums (over `c` and over
the prime variable `n`). Write `e_F(n) = 1_P(n) - (F(n) - F(n-1))` so that
`Δ_F(t,c) = Σ_{n ∈ I(t,c)} e_F(n)`. For a fixed `n`, membership `n ∈ I(t,c)` is
`n >= t+2` together with `ceil(S/(2n)) <= c <= floor((S-1)/n)`. Hence, with
`M(x) = Σ_{m<=x} μ(m)`,

```text
R_F(t;C) = Σ_{n >= t+2, A_n <= B_n} e_F(n) · [ M(B_n) - M(A_n - 1) ] ,        (F)
   A_n = max( C, ceil(S/(2n)) ) ,   B_n = min( 2C-1, t, floor((S-1)/n) ) .
```

This is the sharp exact low-Mertens form (the correct version of Attack C at
fixed `t`). The Möbius coefficient of a fixed prime `n` is a short Mertens sum
over the reciprocal `c`-window `S/(2n) <~ c <~ S/n`, of length `≈ S/(2n)`. This
`c`-support must not be confused with the endpoint motion
`U_d - U_{d+1} = O(S/d^2 + 1)`, which is the *reciprocal derivative in `c`* and
governs Abel summation, a different (and weaker) transformation that does not use
`μ(2c) = -μ(c)`.

The paired block (odd `c ∈ [C,2C)` with `2c <= t`) has the analogous exact
odd-Mertens form. With `M_odd(x) = Σ_{m<=x, 2∤m} μ(m)` and
`D_* = min(2C-1, ⌊t/2⌋)`,

```text
P_F(t;C) = Σ_{n >= t+2} e_F(n) · (                                            (G)
     [ M_odd(B_+) - M_odd(A_+ - 1) ]   over the reciprocal c-annulus [S/2n, S/n]
   - [ M_odd(B_-) - M_odd(A_- - 1) ] ) over the reciprocal c-annulus [S/4n, S/2n]
   A_± = max(C, ceil(S/((2 or 4)n))),  B_± = min(D_*, floor((S-1)/((1 or 2)n))),
```
each empty interval read as zero. Form (G) exhibits the coefficient of each
`e_F(n)` as a **difference of odd-Möbius sums on two adjacent reciprocal
`c`-annuli** — the low-Mertens image of the two-shell contrast of §1.5.

*Proof of (F).* Write `Δ_F(t,c) = Σ_{n ∈ I(t,c)} e_F(n)` and substitute. By
`exactActivityPrimeBounds_iff_product_bounds`, for integer `c` and `n`,
`n ∈ I(t,c) ⇔ n ≥ t+2 ∧ 2cn ≥ S ∧ cn ≤ S-1`. For fixed `n ≥ t+2` this is
`⌈S/(2n)⌉ ≤ c ≤ ⌊(S-1)/n⌋` (the two product inequalities inverted in `c`).
Intersecting with the band `C ≤ c ≤ min(2C-1,t)` gives `A_n ≤ c ≤ B_n`, and
`Σ_{A_n ≤ c ≤ B_n} μ(c) = M(B_n) − M(A_n−1)`. Interchanging the two finite sums
yields (F). ∎

*Proof of (G).* Apply the same inversion separately to the two terms of
`P_F(t;C) = Σ_{odd c} μ(c) Δ_F(t,c) − Σ_{odd c} μ(c) Δ_F(t,2c)`. For the parent,
`n ∈ I(t,c)` gives the `c`-range `[A_+,B_+]`; for the child, `n ∈ I(t,2c)` gives
`2cn ≥ S ∧ 2cn ≤ S-1+... ` i.e. `⌈S/(4n)⌉ ≤ c ≤ ⌊(S-1)/(2n)⌋`, the range
`[A_-,B_-]`. Summing `μ` over *odd* `c` in each range gives the two `M_odd`
differences; subtract. ∎

Both proofs are elementary Fubini + the endpoint inversion; the machine-precision
agreement in the companion script is a regression check, not the proof.

---

## 4. Regime map and where the difficulty lives

The three regions probe genuinely different ranges of `E`, matching Attack D:

* **Region I (`c <= t/4`, small cofactors).** Shells `(U_2c, U_c]` have length
  `≈ X/(2c)`, up to `≈ X/2 ≈ N^2/2`; the largest prime probed is
  `U_1 = X ≈ N^2`. This is a **long-interval / Type-I (Dirichlet hyperbola)**
  regime (small `c`). It is *not* a smoothing: the two shells differ in length by
  a factor of two, so this region carries the bulk of the constant mode `≈ S/4c`
  (§4.5). Small `c` makes the bilinear machinery more standard, but the
  constant-mode interaction (K) must still be handled.

* **Region II (`t/4 < c <= t/2`, transition).** Two-shell contrast with the lower
  shell clamped to the finite-horizon prefix `[t+2, U_2c]`.

* **Region III (`t/2 < c <= t`, large cofactors, unpaired).** The intervals are
  short prefixes `[t+2, U_c]` with `U_c ∈ [t+1, 2t+2]`, so region III probes `E`
  across the whole of `[N, 2N]`. By (B) this is a **balanced Type-II** object
  `c ≍ p ≍ N`, `cp < S`; at `H = 1`, `C ≍ N` it embeds
  `∫_N^{2N} |E(x) - E(N)|^2 dx`, an RH-strength quantity (handoff §6). Pairing
  cannot touch it — the partner `2c` is out of range.

**But the RH-strength difficulty is not confined to region III.** The paired
regions I and II each carry a nonzero constant mode `≈ S/(4c)` (§4.5), and this
mode probes `E` over the long union interval `[S/4c, S/c]` — which at the
`c ≍ t/2` end reaches down to `[N, 2N]` as well. So the principal-mode obstruction
is present in *both* the paired sum and the tail. Pairing reorganizes it into an
unequal adjacent-shell contrast; it does not move it into the tail. The correct
one-line summary is:

> **Pairing gives an exact two-shell decomposition, but neither the paired term
> nor the odd tail is automatically principal-mode free.**

**Finite evidence** (companion script, `H = 40`, real `E`): at `N = 2800` the
*odd tail* has `RMS ≈ 78`, while the *paired sum* is larger, `RMS ≈ 240`. Split
by (N) below, the paired sum's constant-mode part has `RMS ≈ 882` and its centered
part `RMS ≈ 988`: **each is individually larger than the paired sum**, which is
small only through a delicate cancellation between them. The constant mode is thus
not a small correction — it is the dominant raw component. These are finite
diagnostics only.

---

## 4.5 The principal frequency does not cancel algebraically — EXACT

The two-shell weight of a single pair is `W_{t,c}(n) = 1_{I(t,c)}(n) - 1_{I(t,2c)}(n)`.
Its zero-frequency (constant) mode is the length difference of the two shells,

```text
Ŵ_{t,c}(0) = |I(t,c)| - |I(t,2c)| .
```

In the deep range `c <= t/4` the shells have lengths `≈ S/(2c)` and `≈ S/(4c)`, so

```text
Ŵ_{t,c}(0) ≈ S/(4c)  >  0     (verified: mean ratio 1.0000, strictly positive).
```

**The raw Möbius pair is therefore not a mean-zero (Haar) wavelet.** Pairing
converts a single-slab count into an unequal-length two-shell contrast that
retains a substantial constant mode. Consequently the principal Fourier frequency
of the pairing does **not** vanish from parent–child cancellation alone; any
saving at `α = 0` must come from the discrete baseline subtraction (`e_F` already
has the smooth main term removed), from the outer Möbius sum over many `c`, or
from interaction with the complementary main term `L + Ĥ^F`. This is exactly why
the project architecture places the *signed principal major arc* as a separate
step immediately after exact dyadic pairing, not as something the pairing
disposes of.

(This corrects any reading of §1.5/§2.1 in which "removing the diagonal point
`E(t+1)`" is mistaken for "handling the principal arc." The former is a pointwise
identity; the latter is a Fourier statement that is false for the raw pair.)

### 4.6 Exact constant-mode / centered split of a pair — EXACT

Write `ℓ_1 = |I(t,c)|`, `ℓ_2 = |I(t,2c)|`, and the shell averages
`A_c = Δ_F(t,c)/ℓ_1`, `A_{2c} = Δ_F(t,2c)/ℓ_2` (for nonempty shells). Then

```text
Δ_F(t,c) - Δ_F(t,2c) = (ℓ_1 - ℓ_2) · A_{2c}   +   ℓ_1 · (A_c - A_{2c}) .         (N)
```

The first term is the **surviving constant mode** (`ℓ_1 - ℓ_2 ≈ S/(4c)` times the
child-shell average discrepancy); the second is the **genuinely centered
two-shell comparison** (mean-zero against the length-normalized kernel
`1_{I(t,c)}/ℓ_1 - 1_{I(t,2c)}/ℓ_2`). Equivalently, using the average
`ē_F = (Σ_{J} e_F)/|J|` over the union `J = I(t,2c) ∪ I(t,c)`,

```text
Δ_F(t,c) - Δ_F(t,2c) = (ℓ_1 - ℓ_2) ē_F(J)
                     + Σ_{n∈I(t,c)}(e_F(n) - ē_F(J))
                     - Σ_{n∈I(t,2c)}(e_F(n) - ē_F(J)) .                          (H)
```

Both (H) and (N) are elementary and are verified to machine precision. **Warning
(finite evidence):** the two terms of (N) are individually *larger* than their
difference — at `N = 2800`, `Σ_c μ(c)(ℓ_1-ℓ_2)A_{2c}` has `RMS ≈ 882` and
`Σ_c μ(c) ℓ_1 (A_c-A_{2c})` has `RMS ≈ 988`, versus `RMS ≈ 240` for the paired
sum. So the split trades one moderate object for two larger, strongly
anti-correlated ones. It is analytically valuable as a *diagnostic* — it names
exactly what pairing does and does not cancel — but bounding the two pieces
separately is strictly stronger than bounding the paired sum, and would discard
their cancellation.

---

## 5. The sharpest resulting theorem to attack

Target (as in the handoff §7), with the `c`-sum kept inside the square and the
Möbius signs retained:

> **Target (plausible; RH-adjacent).** For `1 <= H <= N`, `1 <= C <= N`,
> ```text
> Σ_{t=N}^{N+H-1} | Σ_{C<=c<2C, c<=t} μ(c) Δ_E(t,c) |^2  ≪_ε  H N^{2+ε} .
> ```

The pairing identity of §2 (equivalently form (G)) splits the target, by the
triangle inequality, into the paired block and the unpaired odd tail:

The pairing splits the target into **paired block + unpaired odd tail**, and the
constant-mode split (N) further separates the paired block. Rather than one
estimate, formulate the three distinct sub-targets that the corrected geometry
exposes.

* **(J) Centered shell estimate — OPEN (the "may eventually be arc-amenable"
  part).**
  ```text
  Σ_{t=N}^{N+H-1} | Σ_{c∼C, odd} μ(c) ℓ_1(t,c) ( A_c - A_{2c} ) |^2  ≪_ε  H N^{2+ε}.
  ```
  This is the genuinely mean-zero two-shell comparison. Its length-normalized
  kernel `1_{I(t,c)}/ℓ_1 - 1_{I(t,2c)}/ℓ_2` integrates to zero, so this is the
  component for which a Fourier / Vaughan / large-sieve treatment may eventually
  be appropriate — *after* an exponential representation is built (see cautions).

* **(K) Constant-mode interaction estimate — OPEN (the principal obstruction).**
  ```text
  Σ_{t=N}^{N+H-1} | Σ_{c∼C, odd} μ(c) ( ℓ_1(t,c) - ℓ_2(t,c) ) A_{2c} |^2  ≪_ε  H N^{2+ε}.
  ```
  Here `ℓ_1 - ℓ_2 ≈ S/(4c)` is the surviving principal mode. It must be studied
  **jointly with the baseline and probably with the complementary main term
  `L + Ĥ^F`** (handoff Attack G's joint-operator / joint-Gram suggestion), **not**
  sent through a generic minor-arc argument. Empirically (K) is the *dominant*
  raw component of the paired block (§4.6).

  *Caveat (from §4.6):* (J) and (K) individually exceed the paired sum and are
  strongly anti-correlated; proving both separately is sufficient but strictly
  stronger than the paired-block target, and discards their cancellation. So (J)
  and (K) are the right *diagnostic* decomposition, and the deeper question is
  whether that cancellation can be exploited rather than thrown away.

* **(Tail) Unpaired balanced tail — OPEN (RH strength).** The region-III sum
  ```text
  Σ_{t=N}^{N+H-1} | Σ_{odd t/2<c<=t} μ(c) ( E(U_c) - E(t+1) ) |^2
  ```
  is balanced Type-II `c ≍ p ≍ N`, `cp < S`. At `H = 1` it embeds
  `∫_N^{2N} |E(x)-E(N)|^2 dx ≪ N^{2+ε}` of RH strength. Pairing cannot remove it.

  The diagonal point piece (P), `E(t+1)·(M_odd(t/4,t/2] - M_odd(t/2,t])`, is the
  one genuinely smaller, well-posed sub-object here — again only because the
  Möbius signs are kept.

Two cautions on the intended machinery (both were over-optimistic in the first
draft of this note):

* No Fourier variable is present in (F)/(G)/(N); before any large-sieve or
  minor-arc step one must first *build* an exponential representation of the
  moving interval indicators, and replace `1_P` by a `Λ`-weighted sum (Vaughan)
  at the cost of a `log`/partial-summation whose coefficients depend
  discontinuously on `n` and `t`.
* A uniform square-root cancellation bound for Mertens exponential sums,
  `Σ_{d∼X} M(d) e(αd) ≪ X^{1/2+ε}`, is **not** a standard unconditional input
  (near `α = 0` it is entangled with the size of `M` itself) and must not be
  assumed.

**Honest conclusion.** Dyadic Möbius pairing is an *exact* reduction. Its
concrete, rigorous gains are: (i) the two-shell contrast identities of §1.5; (ii) the exact low-Mertens forms (F) and (G) (with elementary proofs); and
(iii) the exact constant-mode / centered split (H)/(N). What it does **not** do:
it does not produce a mean-zero wavelet — each pair keeps a constant mode
`≈ S/(4c)` (§4.5–§4.6) — it does not by itself introduce a Fourier decomposition,
and it does not confine the RH-strength difficulty to the tail. **Neither the
paired block nor the odd tail is automatically principal-mode free.** The correct
next analytic step is the constant-mode interaction (K), studied jointly with the
baseline and the complementary main term, not a minor-arc estimate.

---

## 6. Explicit answers to the Attack-A questions

* *Exact symmetric difference of `I(t,c)` and `I(t,2c)`?* — Disjoint adjacent
  reciprocal slabs meeting at `U_2c = floor(X/(2c))`; symmetric difference =
  disjoint union = contiguous annulus with cut point `U_2c` (§1.4).
* *Does repeated pairing compress to odd boundary channels?* — Yes, and it
  terminates immediately: `μ(4c)=0`, so the dyadic ray dies after two terms; the
  survivors are exactly the odd boundary `t/2 < c <= t` (§2), the residual-side
  analogue of `dyadicCofactorBoundary`.
* *How large are the boundary intervals?* — Region III intervals are short
  prefixes `[t+2, floor(X/c)]` of length up to `≈ t` (`U_c` up to `2t+2`); the
  paired-region slabs range up to length `≈ N^2/c`.
* *Does the parent–child difference become boundary intervals or a dyadic
  annulus?* — A **dyadic annulus**: a signed contrast of two adjacent unequal
  reciprocal shells (§1.5), not a short boundary interval. Its low-Mertens image
  is (G).
* *Does the principal major arc cancel between parent and child?* — **No, not at
  the Fourier level.** The *point evaluation* `E(t+1)` is removed from the deep
  region (a pointwise identity, coefficient (P)), but the pair's zero-frequency
  mode is `≈ S/(4c) ≠ 0` (§4.5), so the principal arc is not annihilated by
  pairing. It must be handled by the baseline/complementary-term interaction.
* *Is the RH-strength difficulty isolated into the tail by pairing?* — **No.**
  The paired block keeps a constant mode `≈ S/(4c)` (§4.5–§4.6); empirically it is
  *larger* than the tail. Pairing reorganizes the obstruction into an unequal
  two-shell contrast (targets (J),(K)); it does not confine it to the tail (Tail).
* *Can Vaughan be applied only to the shorter boundary sums?* — Only after the
  constant-mode interaction (K) is handled jointly with the baseline and after
  building a Fourier representation; the "Vaughan + standard large sieve" framing
  is premature. The balanced tail (Tail) is not shortened by pairing.

---

## 7. Suggested next Lean layer

Mirror the transport-side compression on the residual side: define, at fixed `t`,
the parent/child residual contribution and prove the pointwise three-region
identity of §1.5 (pure endpoint algebra + `moebius_two_mul_of_odd`), then the
`Σ_c` decomposition of §2, the principal-endpoint coefficient (P), the finite
Fubini swaps giving the low-Mertens forms (F) and (G), and the constant-mode /
centered split (H)/(N). All of these are finite exact identities with no analytic
content and are exactly the layer that can be formalized now. The mean-square
targets (J), (K), (Tail) stay as explicit open propositions used only through a
conditional bridge — exactly as recommended for the earlier variance target.
Formalizing (F)/(G) also makes it impossible to silently reuse the two conflated
reciprocal derivatives (`c`-support `≈ S/(2n)` versus endpoint motion `O(S/c^2)`),
since both appear explicitly.

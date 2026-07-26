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

Let `G` be any cumulative. From the table and (L),

```text
(I)   4c <= t :      Δ_G(t,c) - Δ_G(t,2c) = G(U_c) - 2 G(U_2c) + G(U_4c) ,
(II)  t/4<c<=t/2 :   Δ_G(t,c) - Δ_G(t,2c) = G(U_c) - 2 G(U_2c) + G(t+1) ,
(III) t/2<c<=t :     Δ_G(t,c)              = G(U_c) -   G(t+1)   (unpaired).
```

**The pair does not collapse to a shorter interval.** It collapses to a
*discrete second difference of `G` on the geometric reciprocal grid*
`{ X/(2^j c) }_{j=0,1,2}` — a one-scale **reciprocal Laplacian**. The shared node
`U_2c` acquires weight `-2`; a single-slab prime count is replaced by the
*difference of the discrepancies of two adjacent reciprocal slabs*. In region I
the bottom node is the next reciprocal point `U_4c`; in region II it is clamped
to the principal endpoint `t+1`; in the unpaired region III it is the principal
endpoint `t+1` with weight `-1`.

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
**principal major-arc content of `R_F(t)` is exactly `E(t+1)` times a difference
of two short odd-Möbius sums**. This is the concrete realization of the handoff
warning: the Möbius signs must be retained through the principal arc — discarding
them (sign-blind Cauchy–Schwarz in `c`) destroys the cancellation in (P) and
reintroduces the full `E(t+1)` at strength `~ t`.

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
pairing of §2 is exactly the identity that, inside (B):

* **cancels the `p`-lower-endpoint (principal-arc) mass** in the paired regions
  (I, and the top node of II), and
* replaces single-slab prime indicators by **adjacent-slab differences**.

---

## 4. Regime map and where the difficulty lives

The three regions probe genuinely different ranges of `E`, matching Attack D:

* **Region I (`c <= t/4`, small cofactors).** Slabs `(U_2c, U_c]` have length
  `≈ X/(2c)`, up to `≈ X/2 ≈ N^2/2`; the largest prime probed is
  `U_1 = X ≈ N^2`. This is a **long-interval / Type-I (Dirichlet hyperbola)**
  regime with an extra reciprocal second-difference smoothing. Small `c` makes
  it the most accessible to standard bilinear/large-sieve methods.

* **Region II (`t/4 < c <= t/2`, transition).** Mixed second differences with the
  bottom node clamped to `t+1`.

* **Region III (`t/2 < c <= t`, large cofactors, unpaired).** The intervals are
  short prefixes `[t+2, U_c]` with `U_c ∈ [t+1, 2t+2]`, so region III probes `E`
  across the whole of `[N, 2N]`. By (B) this is the **balanced Type-II core**
  `c ≍ p ≍ N`, `cp < S`. This is the RH-strength piece identified in the
  handoff (§6): at `H = 1`, `C ≍ N` it embeds
  `∫_N^{2N} |E(x) - E(N)|^2 dx`. Pairing **cannot** remove it — the partner `2c`
  is out of range — it can only *isolate* it and, via (P), *factor out* its
  principal component with the Möbius signs intact.

**Finite evidence** (companion script, `H = 40`): all three regions are well
below the target `≪ N`; e.g. at `N = 2800`, `RMS(I) ≈ 226`, `RMS(II) ≈ 41`,
`RMS(III) ≈ 109`, `RMS(R_F) ≈ 337`, versus target `~ N = 2800`. Region I
dominates at these small scales (it holds most cofactors); region III is thin but
is the analytically hard one. These are finite diagnostics only.

---

## 5. The sharpest resulting theorem to attack

Target (as in the handoff §7), with the `c`-sum kept inside the square and the
Möbius signs retained:

> **Target (plausible; RH-adjacent).** For `1 <= H <= N`, `1 <= C <= N`,
> ```text
> Σ_{t=N}^{N+H-1} | Σ_{C<=c<2C, c<=t} μ(c) Δ_E(t,c) |^2  ≪_ε  H N^{2+ε} .
> ```

The pairing identity of §2 reduces this to three independent sub-estimates.
Introduce a smooth dyadic cutoff `w(c/C)` (so the cross-band pairing is
harmless up to `O(1)` boundary channels per band):

* **(A) Paired second-difference estimate — PLAUSIBLE.** For the region-I/II
  family
  ```text
  Σ_{t=N}^{N+H-1} | Σ_{odd c ≍ C} μ(c) ( E(U_c) - 2E(U_2c) + E(U_{4c or t+1}) ) |^2
        ≪_ε  H N^{2+ε} .
  ```
  Here the extra reciprocal second difference is a genuine smoothing. The route
  is: expand the prime part by Vaughan's identity, keep `Σ_c μ(c)` intact, and
  apply the large sieve to the resulting bilinear forms; the second difference
  supplies an extra `(scale)^{-1}`-type saving on each slab pair. For small `C`
  (region I) this is a Type-I / hyperbola sum and should be provable
  unconditionally. **This is the part Vaughan + large sieve can plausibly close.**

* **(B) Principal major-arc term — PLAUSIBLE (conditional strength known).** By
  (P) the `E(t+1)` contribution is
  ```text
  E(t+1) · ( M_odd(t/4,t/2] - M_odd(t/2,t] ) .
  ```
  Its mean square over `t ∈ [N, N+H)` is `≤ max_t|E(t+1)|^2 · Σ_t |ΔM_odd|^2`.
  Unconditionally `M_odd(·) = o(t)`; on RH `≪ t^{1/2+ε}`. This term is *not* the
  obstruction — the obstruction is that it must be handled **before** any
  Cauchy–Schwarz in `c`, which the pairing makes possible.

* **(C) Unpaired balanced tail — OPEN (RH strength).** The region-III sum
  ```text
  Σ_{t=N}^{N+H-1} | Σ_{odd t/2<c<=t} μ(c) ( E(U_c) - E(t+1) ) |^2
  ```
  is the balanced Type-II core `c ≍ p ≍ N`, `cp < S`. At `H = 1` it is
  equivalent to a short-interval variance bound
  `∫_N^{2N} |E(x)-E(N)|^2 dx ≪ N^{2+ε}` of RH strength, and cannot be expected
  from Vaughan + large sieve alone. **This is the irreducible residual core.**

**Honest conclusion.** Dyadic Möbius pairing is an *exact* reduction. It
performs three concrete gains — (i) algebraic cancellation of the principal
low endpoint in the paired regions, (ii) conversion of single-slab prime counts
into smoother reciprocal second differences, (iii) exact factorization of the
surviving principal-arc mass into `E(t+1)` times short Möbius sums with signs
intact — and it *isolates* the RH-strength difficulty into the thin unpaired
odd tail `t/2 < c <= t`. It does **not** by itself defeat that tail. The
sharpest theorem cleanly attackable by Vaughan's identity and the large sieve is
(A) together with (B); (C) is the genuinely open, RH-adjacent residual.

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
* *Does the principal major arc cancel between parent and child?* — In the paired
  regions I (and the top node of II) the principal endpoint `t+1` is eliminated
  by pairing. The surviving principal mass is exactly (P): `E(t+1)` times a
  difference of short odd-Möbius sums — small precisely because the signs are
  kept.
* *Can Vaughan be applied only to the shorter boundary sums?* — Yes for (A)/(B).
  The residual balanced tail (C) is not shortened by pairing and remains RH
  strength.

---

## 7. Suggested next Lean layer

Mirror the transport-side compression on the residual side: define, at fixed `t`,
the parent/child residual contribution and prove the pointwise three-region
identity of §1.5 (pure endpoint algebra + `moebius_two_mul_of_odd`), then the
`Σ_c` decomposition of §2 and the principal-endpoint coefficient (P). All of
these are finite exact identities with no analytic content; the mean-square
targets (A)–(C) stay as explicit open propositions used only through a
conditional bridge, exactly as recommended for the earlier variance target.

# Gram/Lyapunov dichotomy and trajectory pinning at primorial extensions

## Status

**Two exact theorems closing single-wheel Gram feasibility as a discovery method,
plus two corrections to previously recorded classifications.**

This note answers the acceptance rule declared at the end of the off-diagonal
quotient-tautology audit (PR #177), which required the next candidate family to be

1. **annihilator-independent** — output domination must not come from solving a
   quotient-defining relation for the target coordinate; and
2. **quotient-stable** — with a declared transition rule, verified on the
   31-dimensional `210 -> 2310` quotient.

The answer is that condition 1 is **unsatisfiable in combination with the formal
non-circularity condition already in force**, and that condition 2 **cannot
discriminate**, because the excluded mechanism regenerates at every primorial
level. Separately, a budget-side theorem shows that *every* admissible form —
diagonal, off-diagonal, tautological or not — agrees with the target square to
within a bounded factor along the realized arithmetic trajectory.

Everything below is recomputed from scratch by
[`scripts/GramLyapunovDichotomy/verify.py`](../scripts/GramLyapunovDichotomy/verify.py)
using exact integer and rational arithmetic and the Python standard library only.
That verifier also re-derives, and confirms, the published rows of PR #176 and
PR #177 rather than importing them.

## 0. Setting and notation

For a primorial extension `W -> pW` with `W = p_1 ... p_{k-1}` and `p = p_k`,
index the child cube by masks `D subseteq {p_1,...,p_k}`, encoded as
`0,...,2^k - 1`, and write the prefix flip sums

```text
s_D(U) = sum_{W < n <= U} mu(n) chi_D(mask(n)),        W < U <= pW,
```

where `mask(n)` records which wheel primes divide `n` and
`chi_D(m) = (-1)^{|D and m|}`. The target output is the ordinary Möbius residual

```text
s_0(U) = R_U = M(U) - M(W).
```

Because `s = sum_m c_m chi_m` with `c_m` supported on realized masks, every
attainable state lies in the **compatibility space**

```text
V = { s : <chi_m, s> = 0 for every unrealized mask m }.
```

The Gram/Lyapunov program seeks PSD forms `G_child`, `G_parent` with

- **output domination:** `Q_child(s) >= s_0^2`;
- **extension compatibility:** `Q_child(T x) <= (p-1) Q_parent(x)`;
- **seed budget:** `Q_parent(x_U) <= 2 phi(W)` at every cut,

where `T` is the exact signed `A/B` operator `s_C = A_C - B_C`,
`s_{C u {p}} = A_C + B_C`. Chaining the three gives `R_U^2 <= 2 phi(pW)`.

The formal non-circularity condition already in force since PR #176 is that the
child form must have **zero direct target square**, `(G_child)_{00} = 0`,
excluding the trivial solution `G_child = e_0 e_0^T`.

## 1. Theorem (zero-direct-square dichotomy)

> Let `G` be real symmetric positive semidefinite on `R^m` with `G_{00} = 0`, and
> let `V subseteq R^m` be a subspace. Then `Q(s) >= s_0^2` for all `s in V` holds
> for some such `G` **if and only if** `e_0 notin V`. In that case the target
> coordinate is a linear function of the remaining coordinates on `V`.

**Proof.** Positive semidefiniteness forces every principal `2x2` minor
`[[0, G_{0j}], [G_{0j}, G_{jj}]]` to have determinant `-G_{0j}^2 >= 0`, hence
`G_{0j} = 0` for all `j`, i.e. `G e_0 = 0`. Therefore `Q(s) = Q(Ps)` where
`P = I - e_0 e_0^T`, so `Q` is blind to the target coordinate.

If `e_0 in V`, take `s = e_0`: domination reads `0 >= 1`, false. So domination
forces `e_0 notin V`.

Conversely, if `e_0 notin V` then `V and span(e_0) = 0`, so `P` restricted to `V`
is injective and there is a covector `l` with `l_0 = 0` and `s_0 = <l, s>` for all
`s in V`. Then `G = l l^T` is PSD, has `G_{00} = l_0^2 = 0`, and satisfies
`Q(s) = s_0^2` on `V` with equality. `∎`

### 1.1 Corollary — the declared acceptance rule is unsatisfiable

The existence of *any* zero-direct-square PSD form dominating the target on `V`
is **equivalent** to the annihilator of `V` containing a vector with nonzero
target coefficient, i.e. to the compatibility relations determining the target
coordinate. Annihilator independence and zero direct target square therefore
cannot both hold. The family declared admissible by PR #177 is empty.

The dichotomy does not say every such `G` is the rank-one form `l l^T`; the whole
convex class between `l l^T` and `lambda (I - e_0 e_0^T)` qualifies. It says the
class is *non-empty for exactly one reason* — the annihilator — and that reason
is the one PR #177 tried to legislate away.

## 2. Theorem (the annihilator always exists at primorial extensions)

> For consecutive primorials `W -> pW`, the divisibility mask equal to the full
> **old** wheel `{p_1,...,p_{k-1}}` is realized by no squarefree integer in
> `(W, pW]`.

**Proof.** If `n in (W, pW]` has mask containing the old wheel then `W | n`, so
`n = jW` with `2 <= j <= p`. Squarefreeness of `n` forces `gcd(j, W) = 1` and `j`
squarefree. Since `W` is the primorial of the first `k-1` primes, every integer
`j >= 2` coprime to `W` has least prime factor at least `p`; with `j <= p` this
gives `j = p`. Then `n = pW`, whose mask is the full **new** wheel, not the old
one. `∎`

Every Walsh character satisfies `chi_m(0) = +1`, so a single unrealized mask
already gives `e_0 notin V`. Combining with Theorem 1:

### 2.1 Corollary — the tautology regenerates at every level

At every primorial extension there exists a rank-one PSD form with zero direct
target square satisfying `Q(s) = s_0^2` exactly on all of `V`. Verified
independently at three consecutive extensions:

| extension | masks realized | missing masks | `dim V` | tautology exists |
|:--|--:|:--|--:|:--|
| `30 -> 210` | 14/16 | `7 = {2,3,5}`, `10 = {3,7}` | 14 | yes |
| `210 -> 2310` | 31/32 | `15 = {2,3,5,7}` | 31 | yes |
| `2310 -> 30030` | 61/64 | `31 = {2,3,5,7,11}`, `54`, `57` | 61 | yes |

In each row the missing full-old-wheel mask is the first entry, as Theorem 2
predicts, and the full-new mask is realized by `n = pW` itself.

**Consequence.** The `210 -> 2310` test declared decisive by PR #177 does not
discriminate: the mechanism it was meant to eliminate is present there too.

## 3. Correction to PR #177

PR #177 states that the only missing squarefree mask in `(210, 2310]` is
`31 = {2,3,5,7,11}`, and
[`scripts/OffDiagonalQuotientTautology/verify.py`](../scripts/OffDiagonalQuotientTautology/verify.py)
accordingly defines `V_210` by `<chi_31, t> = 0`.

That is the wrong mask. Mask `31` **is** realized — by `n = 2310`. The genuinely
missing mask is `15 = {2,3,5,7}`, the full old wheel, exactly as Theorem 2
requires. The dimension `31 = 32 - 1` is correct for either choice, so the error
is invisible to the dimension assertion in that verifier.

Two consequences, stated separately because they differ in severity:

- **Numerically benign.** The published failure value `-2` for the naively lifted
  functional occurs in the error set on both the incorrect quotient
  (`{-2,-1,0,2}`) and the correct one (`{-2,0,1,2}`). The headline number
  survives.
- **Logically fatal to the conclusion drawn.** The naive slice-by-slice lift was
  never the right test of quotient stability. Regenerating the functional from
  the correct annihilator at the new level gives exact equality on `V_210`
  (§2.1). The recorded verdict "the mechanism is not quotient-stable" is
  therefore withdrawn: the mechanism *is* stable under regeneration, and is
  eliminated by Theorem 1 instead — on far stronger grounds.

## 4. Theorem (trajectory pinning)

Theorem 1 governs domination on all of `V`. The realized states are a finite
subset of `V`, and on a finite set non-annihilator zero-square forms do exist:
at `30 -> 210` the spread form `lambda (I - e_0 e_0^T)` dominates pointwise on all
180 realized states already at `lambda = 1/15`, versus `lambda = 7` required on all
of `V`. The budget closes that regime instead.

> Suppose `G_child`, `G_parent` satisfy output domination, extension
> compatibility, and the seed budget. Then for every cut `U`,
>
> ```text
> R_U^2  <=  Q_child(s_U)  <=  (p-1) * 2 phi(W)  =  2 phi(pW).
> ```

**Proof.** The left inequality is output domination at `s_U`; the right is
extension compatibility at `x_U` followed by the seed budget, using
`phi(pW) = (p-1) phi(W)`. `∎`

So on the realized trajectory the Lyapunov value is confined to a band of
multiplicative width `2 phi(pW) / max_U R_U^2`:

| block | `max |R|` | `2 phi(W)` | band factor |
|:--|--:|--:|--:|
| `(2,6]` | 2 | 4 | 1.000 |
| `(6,30]` | 2 | 16 | 4.000 |
| `(30,210]` | 5 | 96 | 3.840 |
| `(210,2310]` | 15 | 960 | 4.267 |
| `(2310,30030]` | 71 | 11520 | 2.285 |
| `(30030,510510]` | 274 | 184320 | 2.455 |

**Interpretation.** Every band factor computed is below 5. Any admissible form,
whatever its rank or sparsity pattern, therefore equals the target square to
within a bounded factor *on the states that actually occur*. It cannot encode a
quantity with independent arithmetic content along the trajectory; it is the
target bound carrying bounded slack. Whatever proof power the reformulation has
must come entirely from the operator structure of the extension inequality, not
from the invariant being a different object.

The band factors are exact for the blocks tested. No claim is made about their
behaviour for large `k`; in particular they are **not** observed to tend to 1,
and any such assertion would be unsupported.

## 5. Normalization audit of the PR #176 separating certificate

PR #176 classifies the non-circular mask-specific diagonal family as **CLOSED BY
EXACT RATIONAL SEPARATING CERTIFICATE**, on the strength of

```text
required parent budget >= 368/3 ~ 122.67   versus   allowed 2 phi(30) = 16.
```

The exact rational certificate itself is confirmed by the verifier and is not in
dispute. The **classification** is.

The constant `2` in the seed budget `2 phi(W)` is inherited from the ellipse
diagnostic of Issue #171, not from anything the descent requires. Write the
budget as `b(W) = c * phi(W)`. Because `phi(pW) = (p-1) phi(W)` at a primorial
extension, the extension law `b(pW) = (p-1) b(W)` holds for **every** constant
`c`; the verifier checks this at `30 -> 210 -> 2310 -> 30030`. The chained
conclusion is then

```text
R_U^2 <= c * phi(W_k),      hence     |R| <~ sqrt(c * phi(W_k)),
```

which is square-root-of-block-length, i.e. RH-strength, for any fixed `c`.

Restated in that gauge, the PR #176 certificate says

```text
c >= (368/3) / phi(30) = 46/3 ~ 15.33,
```

not that no such family exists. **It refutes the constant 2, not the diagonal
family.** The family remains open at `c = 46/3`, subject to sufficiency, which
the certificate does not address (it is a lower bound only).

Note carefully what this argument is *not*. Rescaling the whole family by a
factor `t` is a pure gauge change — it multiplies the required and the allowed
budget alike and leaves `368/3 > 16` intact. The point here is different: it is
that the *target* invariant may be stated with any fixed constant without
weakening the RH-relevant conclusion, and the certificate is a statement about
which constants are admissible.

### 5.1 Corrected falsification criterion

A separating certificate closes a Gram family only if the required constant
`c_k` is shown to be **unbounded** along the extension chain. A single finite
value of `c_k` at one wheel closes nothing. Any future certificate must report
`c_k` at a minimum of two consecutive extensions and state the growth it claims.

**This growth test was not run in this cycle.** Reproducing the PR #176 dual
construction at `210 -> 2310` is a fresh exact linear program over a 32-coordinate
child cube and a 32-coordinate enlarged parent state; it is recorded as the next
task, not as a result.

## 6. Scale audit of the enlarged extension state

Independent of the above, the state on which the seed budget is imposed is not a
parent-wheel prefix state. With `A_C(U)` summed over the child interval `(W, U]`
and `B_C(U)` over its dilate `(W/p, U/p]`, exact computation over all 180 cuts of
`(30, 210]` gives

```text
max_C,U |A_C(U)| = 92        (child scale, block length up to 180)
max_C,U |B_C(U)| = 11        (parent scale)
```

against a declared budget of `16` for the combined 16-dimensional state. The
`A` block is a child-scale quantity, so `2 phi(30)` is not the parent invariant
being assumed — it is a normalization imposed on a mixed-scale object. This does
not by itself invalidate the framework, but it is the precise sense in which the
induction is **not closed**: the object bounded at the parent level is not the
object the parent level bounds.

## 7. Classification

- zero-direct-square dichotomy (Theorem 1): **PROVED EXACTLY**;
- missing full-old-wheel-mask lemma (Theorem 2): **PROVED EXACTLY**, verified at
  three consecutive extensions;
- unsatisfiability of the PR #177 acceptance rule: **PROVED EXACTLY**;
- regeneration of the tautology at every primorial level: **PROVED EXACTLY**;
- PR #177 misidentification of `V_210`: **CONFIRMED COMPUTATIONAL ERROR**,
  numerically benign, logically fatal to the recorded verdict;
- trajectory pinning (Theorem 4): **PROVED EXACTLY**, band factors exact for the
  six blocks tabulated, no asymptotic claim;
- PR #176 reclassification from CLOSED to **OPEN AT A LARGER CONSTANT**:
  **PROVED EXACTLY** as a statement about the certificate's scope;
- growth of the required constant along the chain: **NOT TESTED**;
- protected RH theorem graph: **UNCHANGED**.

## 8. Consequence for the route

Single-wheel Gram feasibility is closed as a discovery method. Feasibility is
attainable at every level for a reason that is now completely understood
(Theorem 2 + Theorem 1), and every admissible form is pinned to the target square
on the realized trajectory (Theorem 4). No further one-wheel feasibility search —
diagonal, off-diagonal, sparse, or symmetry-reduced — can produce evidence of
arithmetic contraction.

The remaining content of obligation A is entirely the **state-closure and
uniformity** problem: exhibit an induction state that is preserved by prime
extension, on which the parent bound and the child bound are statements about the
same object. Section 6 shows the current enlarged state is not that object.

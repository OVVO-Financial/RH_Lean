# Prime-extension state closure

## Status

**Solved — and the solution shows state closure was never the bottleneck.**

The previous cycle recorded the open dependency as:

> Solve the prime-extension state-closure problem: an induction state on which
> the parent and child bounds concern the same object, bridging wheel-depth
> recursion and per-block budget.

A state with that property exists, is elementary, and is exhibited below. It is
**not** an enlargement of the `(A, B)` packet state; it is a change of index.
Having it does not advance the program, and this note explains precisely why —
which is itself the useful outcome, because it relocates the open problem.

All identities are verified exactly by
[`scripts/PrimeExtensionStateClosure/verify.py`](../scripts/PrimeExtensionStateClosure/verify.py)
(exact integer arithmetic, standard library only).

## 1. Why the previous state failed

For the extension `W -> pW`, the packet state has components on different
intervals: `A_C(U)` sums over the child block `(W, pW]`, `B_C(U)` over the
dilate `(W/p, U/p]`, and `W/p` is never the previous primorial. Two failures,
recorded in `DIAGONAL_REQUIRED_CONSTANT_GROWTH.md` §7:

- **scale** — `A` is child-scale (`max|A_C| = 92` versus `max|B_C| = 11` over
  `(30, 210]`, under a budget declared as `16`);
- **direction** — the extension law recurses in *wheel depth at fixed interval*
  while the budget is a statement *per block*.

The diagnosis was right, but the prescription — enlarge the packet state — was
wrong. The fix is to stop indexing by block.

## 2. The scale-indexed state

For a squarefree wheel `W` take as state the **whole rough summatory function**

```text
T_W : y |-> sum_{n <= y, (n,W)=1} mu(n),
```

and as the assertion at level `W` the sup bound over a scale range

```text
S(W, X, Phi):      |T_W(y)| <= Phi(y)      for all y <= X.
```

`S(W, X, ·)` and `S(pW, X, ·)` are the *same predicate* applied to the *same
kind of object* over the *same range of scales*. There is no interval mismatch
and no scale mismatch. That is exactly the property the packet state lacked.

### 2.1 The exact transfer law

```text
T_{pW}(x) = T_W(x) + T_{pW}(floor(x/p)),
```

for `p` prime and `pW` squarefree, and iterating (the sum is finite, terminating
once `p^j > x`),

```text
T_{pW}(x) = sum_{j >= 0} T_W(floor(x / p^j)).
```

The one-step form is `roughMertens_wheel_recursion` applied to the wheel `pW`
and rearranged; the merged Lean theorem already supplies it. Both are verified
exactly over `(W, p) in {(6,5), (30,7), (210,11), (2310,13)}` and all `x` in the
checked range.

The one-step law is now formalized as `roughMertens_prime_extension` in
`RHLean/Analysis/EulerCRTRoughnessRecursion.lean`. The geometric form is not.

### 2.2 The descent, and the exact telescope

Reading the recursion downward, `T_W(x) = T_{pW}(x) - T_{pW}(floor(x/p))`, and
removing every wheel prime gives the exact telescope

```text
M(x) = sum_{d | W} mu(d) T_W(floor(x/d)),
```

verified exactly for `W in {6, 30, 210, 2310}`. This is the closed induction: at
every level the object is a rough summatory function, and the step is exact.

## 3. Why the closure does not help

Two independently sufficient reasons. Either alone blocks the route.

### 3.1 The generic descent costs a factor 2 per prime

The triangle inequality on the telescope gives only

```text
|M(x)| <= 2^k * sup_{y <= x} |T_{W_k}(y)|.
```

Measured at `x = 20000`, where `|M(x)| = 26`:

| wheel `W_k` | `k` | `sup_{y<=x} |T_{W_k}(y)|` | `2^k · sup` | slack |
|:--|--:|--:|--:|--:|
| 6 | 2 | 124 | 496 | 19x |
| 30 | 3 | 260 | 2080 | 80x |
| 210 | 4 | 431 | 6896 | 265x |
| 2310 | 5 | 606 | 19392 | 746x |

The slack grows geometrically. With `W_k` the primorial of primes up to `z`, the
loss is `2^{pi(z)}` — super-polynomial in every useful range.

So any useful descent must exploit **cancellation between `T_{pW}(x)` and
`T_{pW}(floor(x/p))`**, not merely bound them separately. That cancellation is
exactly the unproved energy-transfer premise of Issue #171 §11. The closed state
does not supply one drop of it.

### 3.2 The base case is a prime count

Take the wheel large enough for the range. For `p_k < y < p_{k+1}^2`, every
`n <= y` coprime to `W_k` is either `1` or a prime in `(p_k, y]`, so exactly

```text
T_{W_k}(y) = 1 + k - pi(y).
```

Verified exactly for `k = 1..5` over the full admissible range in each case.

A sup bound on the base of the induction is therefore a **prime-counting error
bound**. At RH strength that is RH for `zeta` — the thing being proved. The
induction is exact and closed, and its base case is the conclusion.

## 4. What this changes

The open problem is relocated, not solved, and the relocation is the point.

- **State closure is achieved and is not the bottleneck.** The previous cycle
  listed it as the remaining content of obligation A. That emphasis was wrong:
  a closed state exists and is elementary. Recorded here as a correction to that
  cycle's framing, not to any of its theorems.
- **The bottleneck is, and always was, cancellation.** Every route explored on
  this branch — Walsh high-degree suppression, the two-channel ellipse, the
  positive-form/Gram reformulation, and now the scale-indexed closure — reduces
  to needing signed cancellation that no exact identity supplies.
- **The pattern is now threefold.** Three successive cycles have found the same
  shape: an exact structure that reproduces the target rather than controlling
  it. Full telescoping is tautological (§10.8 of #171); the zero-direct-square
  Gram class exists exactly when the annihilator reconstructs the target; and
  the closed induction has an RH-equivalent base. These are not three
  coincidences — they are the same obstruction seen from three indices.

## 5. Classification

- scale-indexed state closure: **PROVED EXACTLY**, elementary;
- one-step transfer `T_{pW}(x) = T_W(x) + T_{pW}(x/p)`: **LEAN-FORMALIZED**
  (`roughMertens_prime_extension`), pending CI;
- geometric form `T_{pW}(x) = sum_j T_W(x/p^j)`: **PROVED EXACTLY**, not
  formalized;
- exact telescope `M(x) = sum_{d|W} mu(d) T_W(x/d)`: **PROVED EXACTLY**, not
  formalized;
- `2^k` descent loss: **MEASURED EXACTLY** at four wheels; the geometric growth
  is exhibited, not merely asserted;
- base case `T_{W_k}(y) = 1 + k - pi(y)` on `(p_k, p_{k+1}^2)`:
  **PROVED EXACTLY**, verified for `k = 1..5`;
- consequence that the closed induction is not a reduction: **ESTABLISHED**;
- the cancellation premise of #171 §11: **STILL OPEN, UNTOUCHED**;
- protected RH theorem graph: **UNCHANGED**.

## 6. Recommended reframing of obligation A

Obligation A should no longer be stated as "construct an enlarged
extension-compatible state with a positive quadratic form." That formulation has
now been closed from three directions. It should be stated as what it always
reduced to:

> Exhibit signed cancellation between `T_{pW}(x)` and `T_{pW}(floor(x/p))` — or
> equivalently between the `2^k` terms of the exact telescope
> `M(x) = sum_{d|W} mu(d) T_W(floor(x/d))` — strong enough to beat the `2^k`
> triangle-inequality loss.

Any proposal that does not address that sum directly is, on the evidence of the
last three cycles, a reparameterization.

# Required-constant growth test for the diagonal family: `30 -> 210 -> 2310 -> 30030`

## Status

**Predeclared test executed. Outcome: NO GROWTH across three consecutive extensions.**

The previous cycle narrowed PR #176 from *CLOSED BY EXACT RATIONAL SEPARATING
CERTIFICATE* to *OPEN AT A LARGER CONSTANT*, on the ground that a certificate
closes a Gram family only if the required constant `c_k` is **unbounded** along
the extension chain, and predeclared:

> **FEASIBLE / bounded `c_k`:** the diagonal family survives at a larger constant
> and must be re-examined.
> **GROWING `c_k`:** the family is closed for the first time, with the growth
> exhibited.

The measurement has now been run at the first three consecutive primorial
extensions. The required constant does **not** grow: it falls by a factor of
roughly `0.43` from the first to the second, reproduced by four independent test
families, and at the third it remains bounded and far below `c_1`.
**The diagonal family is not closed.**

Verifier: [`scripts/DiagonalConstantGrowth/verify.py`](../scripts/DiagonalConstantGrowth/verify.py)
(exact rational, standard library only).

## 1. What is being measured

For the extension `W -> pW` write the child flip state `s(U)` and the enlarged
parent state `(A_C, B_C)` via the exact operator `s_C = A_C - B_C`,
`s_{C u {p}} = A_C + B_C`. The non-circular mask-specific diagonal family asks
for weights `x_D >= 0` (child, with `x_0 = 0`) and `y_C >= 0` (parent) with

```text
(O)  sum_{D != 0} x_D s_D^2  >=  s_0^2                                (output domination)
(E)  sum_{D != 0} x_D s_D^2  <=  (p-1) sum_C y_C (A_C^2 + B_C^2)      (extension compatibility)
(B)  sum_C y_C (A_C(U)^2 + B_C(U)^2)  <=  b   for every cut U         (seed budget)
```

and the quantity of interest is the smallest admissible `b`, normalized as

```text
c_k = b_k / phi(W_k).
```

`c_k` is the constant that the conjectured seed budget `b(W) = c phi(W)` would
have to carry. The declared budget `2 phi(W)` is the case `c = 2`. Because
`phi(pW) = (p-1) phi(W)` at a primorial extension, the extension law
`b(pW) = (p-1) b(W)` holds for every `c`, and `|R| <~ sqrt(c phi(W_k))` is
square-root-of-block-length — RH-strength — for any fixed `c`. Only an
**unbounded** `c_k` closes the family.

## 2. Method, and why it is the same method PR #176 used

Constraints (O) and (E) are quantified over the whole compatibility space, so the
exact problem is not a linear program. Restricting them to a finite family of
compatible test vectors yields a linear program whose **dual** is exactly the
certificate structure of PR #176:

```text
maximize   sum_v lambda_v v_0^2
s.t.       sum_v (lambda_v - mu_v) v_D^2 <= 0                     for D = 1..2^k-1
           (p-1)/2 sum_v mu_v (v_C^2 + v_{C+h}^2)
                 - sum_U nu_U (A_C(U)^2 + B_C(U)^2) <= 0          for C = 0..h-1
           sum_U nu_U <= 1,      lambda, mu, nu >= 0.
```

PR #176's published certificate is the special case `nu = delta_{U=199}` with 11
`lambda` and 7 `mu` multipliers.

**Validation.** Run on the family of signed sums of at most three realized Walsh
atoms, this LP returns exactly `368/3` at `30 -> 210` — PR #176's value,
reproduced independently and shown to be that family's exact optimum.

## 3. Two-sided exact certificates

A dual-feasible point proves a **lower** bound on `b_k`; a primal-feasible
`(x, y, b)` proves an **upper** bound. Both were extracted in exact rational
arithmetic for the canonical test family — *all realized prefix states of the
block, used both as test vectors and as budget cuts*.

### `30 -> 210` (parent `W = 30`, `phi = 8`, 110 distinct states)

Exact dual certificate, support 10:

| multiplier | value | | multiplier | value |
|:--|--:|--|:--|--:|
| `lambda_92` | `11/8` | | `mu_82` | `13/192` |
| `lambda_93` | `20831/6912` | | `mu_93` | `443/768` |
| `lambda_94` | `10043/2304` | | `mu_94` | `821/768` |
| `lambda_102` | `29/216` | | `mu_103` | `5/48` |
| `nu_0` | `1` | | `mu_106` | `5/24` |

```text
b_1 >= 7819/216 = 36.199074...        c_1 >= 7819/1728 = 4.5248843...
```

A matching exact primal-feasible point attains the same value, so `7819/216` is
the exact LP optimum, not merely a bound.

### `210 -> 2310` (parent `W = 210`, `phi = 48`, 1231 distinct states)

The LP optimum is `94.030038...`, with exact dual and primal certificates
agreeing. The committed verifier embeds a slightly rounded primal-feasible point
(31 child weights, 16 parent weights, all with denominator dividing `10^6`),
which is what makes the upper bound checkable in a few lines of exact arithmetic:

```text
b_2 <= 23511351/250000 = 94.045404...    c_2 <= 7837117/4000000 = 1.9592793...
```

## 4. Result

Combining the level-1 **lower** bound with the level-2 **upper** bound — the two
directions needed for a genuine comparison — gives, exactly:

```text
c_1 >= 7819/1728    = 4.5248843...
c_2 <= 7837117/4e6  = 1.9592793...
c_2 / c_1 <= 0.4330...
```

The required constant **falls**. Under the predeclared criterion this is the
FEASIBLE / bounded branch: **the family survives, and PR #176's certificate does
not close it.**

### Reproduced by four independent test families

| test family | `c_1` | `c_2` | ratio |
|:--|--:|--:|--:|
| realized Walsh atoms only | 0.7708 | 0.4157 | 0.539 |
| all realized prefix states | 4.5249 | 1.9590 | 0.433 |
| states + atoms | 4.5249 | 1.9590 | 0.433 |
| states + signed atom pairs | 6.0833 | 2.6555 | 0.437 |

Every family gives a ratio well below 1, clustered near `0.43`.

## 5. Confounds, stated plainly

These results are **not** a proof that the true minimal constant decreases, and
must not be cited as one.

**(a) The bounds are lower bounds on the truth.** Restricting (O) and (E) to a
finite test family gives a necessary condition only. The true required constant
— with the full quantified constraints — is at least `c_k`, possibly much larger.

**(b) The bounds depend strongly on the test family.** At `30 -> 210`, enriching
the family raises the value sharply:

| family (signed sums of at most `m` atoms) | `b_1` | `c_1` |
|:--|--:|--:|
| `m = 1` | 36.199 | 4.525 |
| `m = 2` | 48.667 | 6.083 |
| `m = 3` | 122.667 | 15.333 |
| `m = 4` | 426.667 | 53.333 |
| `m = 5` | 530.000 | 66.250 |

PR #176's `368/3` is exactly the `m = 3` value. The sequence had not converged at
`m = 5`.

**(c) Coverage is not level-neutral.** A fixed rule such as "signed sums of at
most three atoms" covers a much smaller fraction of the 31-atom cube at
`210 -> 2310` than of the 14-atom cube at `30 -> 210`. Part of the observed fall
may be under-powering at the higher level rather than a genuine decrease.

Confound (c) cuts against the headline, and (b) shows the absolute numbers carry
little meaning. What survives all three is the operational conclusion:

> **The certificate method, applied at comparable strength at two consecutive
> extensions, produces no growth.** Since closure *requires* exhibiting growth,
> and the method's own output moves in the opposite direction, the family remains
> open. The burden is on any future closure claim to exhibit growth, not on this
> note to exclude it.

**(d) A third extension was attempted; the solver fails, not the problem.**

At `2310 -> 30030` the hand-rolled floating-point simplex reports an unbounded
ray and returns no value. That report is **wrong**, and it is worth recording why,
because the earlier note left it as an unexplained "breakdown".

An unbounded dual would mean an infeasible primal. But the primal is provably
feasible: the uniform construction

```text
x_D = lambda  for D != 0,   y_C = 2 lambda / (p-1),   lambda = max_U s_0(U)^2 / sum_{D!=0} s_D(U)^2
```

satisfies all three constraint families at every level by construction, and gives
the exact (very weak) bounds

| extension | `lambda` | `b` | `c` |
|:--|--:|--:|--:|
| `30 -> 210` | `1/15` | `1792/5` | `44.80` |
| `210 -> 2310` | `9/71` | `9819936/355` | `576.29` |
| `2310 -> 30030` | `25/423` | `228198400/423` | `1123.91` |

So the level-3 LP is feasible and bounded. The failure is in the solver: the LP
is massively degenerate — every row has right-hand side `0` except one — and a
Dantzig entering rule with a smallest-ratio tie-break stalls on it. Column
equilibration cut the level-2 solve time from 340 s to 3.4 s and reproduced its
optimum exactly, but did not fix the level-3 stall.

The uniform construction's numbers *rise* across levels. That is **not** evidence
of growth: they are upper bounds, and rising upper bounds are uninformative about
the truth. They are reported only to establish feasibility and to bound the
search.

### A third data point, obtained by sidestepping the stall

The stall is avoided by solving the LP on a **subsample** of the test family and
then repairing the resulting weights exactly against the **full** family. The
repair scales `x` up until output domination holds on every one of the 16300
states, then scales `y` up until extension compatibility holds on every one; the
result is feasible for the full family whatever its origin, so the budget it
attains is a valid upper bound on the full LP optimum. Validated by reproducing
the level-2 optimum exactly (repair factors `1.0000`, `1.0000`).

At `2310 -> 30030` with a 1254-state subsample (repair factors `1.3306` and
`1.5843`):

```text
b_3 <= 17992014840030231/12500000000000 = 1439.3612...
c_3 <= 5997338280010077/2000000000000000 = 2.9986691...
```

and the subsample LP optimum, being a relaxation, gives the indicative lower end
`c_3 >~ 1.8334` (float-derived, **not** exactly certified).

So the three-level picture is

```text
c_1 = 4.5248843    (exact LP optimum, two-sided)
c_2 = 1.9589591    (exact LP optimum, two-sided)
c_3 in [~1.83, 2.9987]   (upper end exactly certified, lower end indicative)
```

The constant is **bounded** across three consecutive extensions and stays far
below `c_1`. The level-3 bracket straddles `c_2`, so this does **not** establish
that the fall continues — only that no growth is exhibited. That distinction is
the whole content of the test, and it is the reason `c_3` is reported as a
bracket rather than a value.

## 6. Effect on the ledger

- PR #176's classification stays **OPEN AT A LARGER CONSTANT**, now supported by
  direct measurement at two consecutive extensions rather than by the logical
  objection alone.
- The predeclared growth test is **discharged**, with the FEASIBLE outcome.
- The exact rational certificate of PR #176 is again confirmed and is not in
  dispute; only the inference from it was ever at issue.

## 7. State closure: the precise obstruction

The second half of the open dependency is the state-closure problem. The
obstruction can now be stated sharply.

At the extension `W -> pW`, the two components of the enlarged state live on
different intervals:

```text
A_C(U) = sum over (W, U]         with W < U <= pW      -- the CHILD block
B_C(U) = sum over (W/p, U/p]                           -- a dilate
```

The dilate is close to, but never equal to, the parent block
`(W_{k-1}, W]`, because `W/p` is not `W_{k-1}`:

| extension | child block | `A` interval length | `B` interval `(W/p, W]` | parent block | equal? |
|:--|:--|--:|:--|:--|:--|
| `30 -> 210` | `(30,210]` | 180 | `(4.29, 30]` | `(6,30]` | no |
| `210 -> 2310` | `(210,2310]` | 2100 | `(19.09, 210]` | `(30,210]` | no |
| `2310 -> 30030` | `(2310,30030]` | 27720 | `(177.69, 2310]` | `(210,2310]` | no |

Two distinct failures follow, and they should not be conflated:

1. **Scale.** `A` is a child-block quantity. Over all 180 cuts of `(30, 210]`,
   `max |A_C| = 92` against `max |B_C| = 11`, under a budget declared as
   `2 phi(30) = 16`. A parent-scale budget is being imposed on an object one
   block-scale too large.
2. **Direction of the recursion.** The extension law is a recursion in **wheel
   depth at fixed interval** — it removes a prime from the roughness wheel. The
   budget is a statement **per block**. These are different recursions, and the
   framework never supplies the bridge between them.

So the induction does not merely lack a positive form; it lacks a state on which
parent and child assertions are about the same object. **No positive form on the
current enlarged state can close the induction, whatever its feasibility at any
single wheel.** This is consistent with, and sharpens, the dichotomy result of
the previous cycle.

## 8. Classification

- LP dual equivalent to the PR #176 certificate structure: **PROVED EXACTLY**;
- independent reproduction of `368/3` as that family's exact optimum:
  **CONFIRMED**;
- two-sided exact certificates at `30 -> 210` and `210 -> 2310`:
  **PROVED EXACTLY** for the declared families;
- `c_2 < c_1`, hence no growth: **PROVED EXACTLY** for the declared families;
  **NOT** proved for the true minimal constants;
- PR #176 remains **OPEN AT A LARGER CONSTANT**;
- `c_3` at `2310 -> 30030`: **UPPER BOUND PROVED EXACTLY**
  (`c_3 <= 5997338280010077/2000000000000000`); lower end indicative only, and
  the bracket does not resolve `c_3` against `c_2`;
- interval mismatch of the enlarged state: **PROVED EXACTLY** (elementary, three
  extensions tabulated);
- state closure: **STILL OPEN**;
- protected RH theorem graph: **UNCHANGED**.

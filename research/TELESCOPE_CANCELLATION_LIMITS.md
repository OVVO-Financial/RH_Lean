# Limits of the telescope-cancellation target

## Status

**The target is not viable. The formulation is withdrawn.**

The previous cycle reframed obligation A as:

> Exhibit signed cancellation between `T_pW(x)` and `T_pW(floor(x/p))` — or
> equivalently among the `2^k` terms of the exact telescope
> `M(x) = sum_{d|W} mu(d) T_W(floor(x/d))` — strong enough to beat the `2^k`
> triangle-inequality loss.

That reframing was mine, and it is wrong. The telescope is an **exactly
invertible re-expression** of `M` that carries no additional exploitable
structure, and every route through it is either equivalent to bounding `M`
directly or strictly worse. This note records the four exact checks that
establish it, so the formulation is not attempted again.

Verifier:
[`scripts/TelescopeCancellationLimits/verify.py`](../scripts/TelescopeCancellationLimits/verify.py)
(exact integer arithmetic, standard library only).

## 0. A correction to the quoted loss

Earlier notes quote the loss as `2^k sup_{y<=x} |T_{W_k}(y)|`. That is correct
but needlessly crude: the honest triangle bound is

```text
sum_{d | W} |T_W(floor(x/d))|,
```

which is substantially smaller — at `W = 30030`, `x = 100000` it is `13882`
against `107840` for `2^k sup`, roughly `8x` better. Every statement below uses
the honest bound. Using the crude one would have overstated the case.

It does not change the conclusion, because the honest bound still grows.

## 1. Marginal information is insufficient

> **Proposition.** Suppose the only information available is a per-term bound
> `|T_W(floor(x/d))| <= Phi_d` for each `d | W`. Then the best bound on `|M(x)|`
> derivable is `sum_d Phi_d`, and it is attained.

*Proof.* The admissible vectors form the box `{(t_d) : |t_d| <= Phi_d}`, and the
linear functional `sum_d mu(d) t_d` attains `sum_d Phi_d` on it at
`t_d = mu(d) Phi_d`. That point respects every hypothesis. `∎`

So **no argument using only per-term bounds can improve on the triangle
inequality.** Any proof must use joint information about the vector
`(T_W(floor(x/d)))_{d|W}` — correlations across `d`, not sizes of individual
entries. Checked exactly at `k = 3, 4, 5`.

## 2. The telescope strictly worsens the problem

Ratio of the honest triangle bound to the target, as primes are added:

| `x` | `\|M(x)\|` | `k=0` | `k=1` | `k=2` | `k=3` | `k=4` | `k=5` | `k=6` |
|:--|--:|--:|--:|--:|--:|--:|--:|--:|
| 20000 | 26 | 1.0x | 2.1x | 12.7x | 43.8x | 95.2x | 147.5x | 200.2x |
| 100000 | 48 | 1.0x | 1.4x | 10.8x | 41.4x | 105.5x | 189.2x | 289.2x |
| 199999 | 1 | 1.0x | 115.0x | 579.0x | 2425.0x | 6657.0x | 12645.0x | 20301.0x |

The ratio is exactly `1` at the **empty** wheel — where the telescope is the
trivial identity `M(x) = M(x)` — and increases monotonically with every prime
added, at every `x` tested.

**The optimal wheel is the empty one.** Each prime adjoined to the roughness
wheel strictly increases the amount of cancellation that must be proved, while
the target stays fixed. The telescope is not a reduction; it is an expansion.

## 3. Regrouping collapses the telescope

For `p | W`, pairing each `d | (W/p)` with `pd` gives

```text
sum_{d | W/p} mu(d) [ T_W(x/d) - T_W(x/(pd)) ]  =  sum_{d | W/p} mu(d) T_{W/p}(x/d),
```

by the one-prime recursion `D_p T_W = T_{W/p}` — the telescope for the *smaller*
wheel. Verified exactly for `(W,p) = (30,5), (210,7), (2310,11), (30030,13)`.

So any pairing of terms along a wheel prime simply undoes one level of the
expansion. The map between levels is exactly invertible in both directions, and
no grouping extracts information that was not already in `M`. This is the precise
form of the observation recorded at Issue #171 §10.8 that full telescoping is
tautological.

## 4. Truncation fails

The classical escape from a Legendre-type expansion is Brun truncation: keep only
`omega(d) <= r`. At `W = 210`, `x = 100000`, where `M(x) = -48`:

| `r` | partial sum | error |
|--:|--:|--:|
| 0 | −773 | 725 |
| 1 | 1142 | 1190 |
| 2 | −573 | 525 |
| 3 | 21 | 69 |
| 4 | −48 | **0** |

The partial sums oscillate with amplitude `10`–`25x` the target, and the error
exceeds `|M(x)|` at every depth short of full. The same pattern holds at
`W = 2310` and `W = 30030`. **The cancellation is entirely last-mile**: it
appears only when the final level is included.

Nor is there a small set of dominant terms to control. At `x = 100000` the
largest single term is only `12`–`15%` of the `L1` mass and the top four are
`34`–`46%`; the mass is spread across all `2^k` terms.

## 5. What this is, classically

The telescope is the **Legendre sieve** for the Möbius function, and the blow-up
above is that sieve's classical failure mode — the reason Brun and Selberg
replaced the exact inclusion–exclusion by truncated or optimized weights `lambda_d`.

Those escapes buy upper and lower bounds for *sifted counts*. They do not apply
here: `M(x) = sum_{n <= x} mu(n)` is a **parity-sensitive** quantity
(`mu(n) = (-1)^{omega(n)}` on squarefree `n`), and Selberg's parity phenomenon —
classical, not established here — is precisely the statement that sieve data
alone cannot distinguish an even from an odd number of prime factors. A route
that reaches `M` through sieve identities plus size information about the sifted
sums is therefore obstructed for structural reasons, independently of the finite
measurements above.

## 6. Consequence for obligation A

The telescope-cancellation formulation is **withdrawn**. It is the fourth
instance of the pattern this branch keeps producing — an exact structure that
reproduces the target rather than controlling it:

1. full telescoping is tautological (#171 §10.8);
2. the zero-direct-square Gram class exists exactly when the compatibility
   annihilator reconstructs the target;
3. the closed prime-extension induction has an RH-equivalent base case;
4. the telescope's cancellation is exactly the cancellation in `M`, and every
   derived route is equivalent or strictly worse.

Each was proposed as the next target and each dissolved on contact for the same
reason. That is now four for four, and the fourth was proposed by this operator
after the pattern had already been named — which is itself evidence that the
pattern is a property of the branch, not of the proposals.

### Recommendation

**Declare the Euler–CRT roughness branch exhausted as an RH route.** Retain what
it produced, which is real and is unaffected:

- the exact identities `D_p T_W = T_{W/p}`, its divisor iterate, the interval
  form, the prime-extension form, the comb–cofactor and mixed-difference
  identities, and the Walsh top-coefficient identity;
- the Lean formalization of the one-prime and interval recursions
  (CI-green via PR #178) and of the prime-extension step (pending CI);
- the exact no-go results, which stop future agents from re-entering closed
  families.

What it does not contain is a mechanism for signed cancellation, and the four
checks above indicate it cannot contain one: the branch's exact structures are
all invertible re-expressions of `M`.

Known routes to Möbius cancellation are bilinear — Vaughan / Heath-Brown Type I
and Type II decompositions. The route registry already records this project's
dyadic attempt in that direction as closed, with a specific instruction not to
repeat it by deriving "more centered Vaughan/Type-I/II bounds while leaving the
coherent mode untouched." Any successor route should be assessed against that
entry before work begins, not after.

## 7. Classification

- honest triangle bound replacing the crude `2^k sup`: **CORRECTION, APPLIED**;
- marginal-information no-go: **PROVED EXACTLY** (elementary);
- monotone worsening of the triangle bound in `k`: **MEASURED EXACTLY**,
  three values of `x`, `k = 0..6`, ratio exactly `1` at `k = 0`;
- regrouping collapse: **PROVED EXACTLY**, four wheel/prime pairs;
- truncation failure: **MEASURED EXACTLY**, three wheels;
- parity obstruction: **CLASSICAL CONTEXT**, cited, not established here;
- telescope-cancellation formulation of obligation A: **WITHDRAWN**;
- recommendation to close the branch: **FOR THE OWNER TO DECIDE** — no registry
  route is marked closed by this note alone;
- protected RH theorem graph: **UNCHANGED**.

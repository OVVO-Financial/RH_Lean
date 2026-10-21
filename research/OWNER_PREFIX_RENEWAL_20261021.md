# Native owner-prefix recurrence and exact renewal Gram

**Date:** 2026-10-21. **Scope:** original Möbius coefficients, original square
endpoints, actual high-prime owners, and the complete smooth companion.
**Status:** finite proof sources and a conditional quantitative consumer;
`OwnerBound` is OPEN. No new Mertens exponent or RH theorem is established.
At drafting, PR #993 at `6bbd016318c3d853df54c9d6a39e5bae270151c7`
awaits the warning-fatal Targeted Lean iteration. Source preparation and
integer verification are distinct from Lean/axiom acceptance at the final head.

## 1. Original source and the open arithmetic premise

For \(R\ge2\), retain \(X_R=R^2-1\), \(A_R\), and \(T_R\) from the native
square-root factorization. Put \(m_p=M(\lfloor X_R/p\rfloor)\), for actual
primes \(R<p\le X_R\). Then
\[
M(X_R)=A_R-T_R,\qquad T_R=\sum_{p>R}m_p,\qquad D_R=\sum_{p>R}m_p^2.
\]
The complete signed off-owner expression is
\[
\Gamma_R=A_R^2-2A_RT_R+T_R^2-D_R,
\qquad M(X_R)^2=D_R+\Gamma_R.
\]
The entire smooth population is included, with both orientations and the unit.
The formulas here retain this full source throughout.

For a fixed \(\kappa\ge0\), the new arithmetic premise is
\[
\tag{OwnerBound: OPEN}
\forall\varepsilon>0\ \exists C_\varepsilon>0\ \forall R\ge2:\quad
\Gamma_R\le C_\varepsilon R^{\kappa+\varepsilon}(X_R+D_R).
\]
This is a one-sided bound on the complete interaction. No hypothesis requires
each covariance to be negative. The finite identities below do not prove it.

## 2. Exact native replacement row and actual owner multiplicities

Use the existing `RecursivePrimeReplacement` definitions:
\[
C_R(n)=\sum_{\substack{d\mid n\\1\le d<R}}\mu(d),\qquad
F_R(y)=\left(\left\lfloor\frac{X_R}{y+1}\right\rfloor,
                 \left\lfloor\frac{X_R}{y}\right\rfloor\right]\cap\mathbb N,
\]
\[
L_R(y)=\sum_{n\in F_R(y)}C_R(n),\qquad
\gamma_R(y)=\mathbf1_{y=R-1}-L_R(y),\qquad 1\le y<R.
\]
Finite divisor reindexing gives the concrete coefficient formula
\[
L_R(y)=\sum_{1\le d<R}\mu(d)
\left(\left\lfloor\frac{X_R}{dy}\right\rfloor-
      \left\lfloor\frac{X_R}{d(y+1)}\right\rfloor\right).
\]
The native renewal theorem proves \(M(X_R)=\sum_{y<R}\gamma_R(y)M(y)\).
Define the actual, clipped prime multiplicity
\[
w_R(y)=\#\{p>R:p\text{ prime},\ \lfloor X_R/p\rfloor=y\}.
\]
Its finite pushforward gives \(T_R=\sum_yw_R(y)M(y)\) and
\(D_R=\sum_yw_R(y)M(y)^2\). Consequently the genuine smooth row is
\[
\boxed{A_R=\sum_{y<R}(\gamma_R(y)+w_R(y))M(y).}
\]
There is no unspecified compensating function. Combining the rows yields
\[
\boxed{\Gamma_R=\sum_{i,j<R}
 (\gamma_R(i)\gamma_R(j)-\mathbf1_{i=j}w_R(i))M(i)M(j).}
\]
The Lean source proves the corresponding complex Gram with conjugation,
using the repository's original complex Mertens function. The real native
specialization identifies its real coordinate with the consumer's coefficients.

`SquareRootPostCrossingRenewal` further identifies \(\gamma_R(y)\) with its
endpoint term, the full canonical rough-prime mass, and all strict descendants.
The rough mass begins at cofactor one. Packet admission changes the same row
coefficientwise: admitted shallow prime faces cancel, the crossing retains
\(j-w_R(K)\), and prime faces inside strict descendants remain.

The last raw floor layer needs an endpoint correction:
\[
w_R(y)=\pi(\lfloor X_R/y\rfloor)-\pi(\lfloor X_R/(y+1)\rfloor)
       -\mathbf1_{y=R-1}\mathbf1_{R\text{ prime}}.
\]
For \(R\ge2\), the raw terminal interval is \((R-1,R+1]\); historical owners
use \((R,R+1]\). The Lean draft proves this finite-window correction; the
displayed full floor formula is a paper derivation checked by the integer audit.

## 3. Cofactor swaps do not remove the interior

Let \(N_R(c)=\pi(\lfloor X_R/c\rfloor)-\pi(R)\), for \(1\le c<R\).
For \(c<d\), the exact distinct-owner kernel splits as
\[
N_R(c)N_R(d)-N_R(d)
=N_R(d)(N_R(d)-1)+N_R(d)(N_R(c)-N_R(d)).
\]
Both terms retain the coefficient \(\mu(c)\mu(d)\). A complete swap satisfies
\(\mu(pc)\mu(qd)=\mu(pd)\mu(qc)\); it preserves the sign.
For \(R=6\), the pairs \((14,33)\) and \((21,22)\) are swapped by
\((p,q,c,d)=(7,11,2,3)\). All four Möbius values are \(+1\).

After summing cofactors, including the diagonal, \(T_R^2-D_R=I_R+W_R\), with
\[
I_R=2\sum_{R<p<q\le X_R}M(\lfloor X_R/q\rfloor)^2\ge0,
\]
\[
W_R=2\sum_{R<p<q\le X_R}
 [M(\lfloor X_R/p\rfloor)-M(\lfloor X_R/q\rfloor)]
 M(\lfloor X_R/q\rfloor).
\]
These globally summed identities are finite paper derivations checked by the
integer audit. The Lean draft certifies the local kernel algebra, actual swap
weights, and full native renewal Gram.
Top-prime cofactor-one faces give \(I_R\gg X_R^2/\log^2X_R\) by the PNT.
The full target is therefore \(A_R^2-2A_RT_R+I_R+W_R\), not the wedge alone.
At \(R=160\), the exact audit gives \(I_R=7581854\), \(W_R=-7515296\),
and \(\Gamma_R=-4098\), after the complete smooth/transport recombination.

## 4. Normalized full-prefix consumer

For a real sequence \(M\), define the finite normalized maximum
\[
E_*(B)=\max\left(1,\max_{1\le n<B}\frac{|M(n)|}{\sqrt n}\right).
\]
For the original Möbius sum, \(M(1)=1\), so this equals the repository's raw
prefix amplitude for every \(B\ge2\). The adjoined 1 is required for the
generic consumer, and absorbs the finite-shell endpoint expense.

All owner arguments satisfy \(1\le\lfloor X_R/p\rfloor<R\). The formal
consumer pays the diagonal using an elementary harmonic sum:
\[
D_R\le X_RE_*(R)^2(1+2\log R)
\ll_\varepsilon X_RR^\varepsilon E_*(R)^2.
\]
This step assumes neither PNT nor a new Mertens exponent. Combining it with
the OPEN `OwnerBound` gives
\[
|M(X_R)|\ll_\varepsilon R^{1+\kappa/2+\varepsilon}E_*(R).
\]
For a sequence with unit increments, \(|M(n+1)-M(n)|\le1\), take
\(R=\lfloor\sqrt n\rfloor+1\). Then \(n\le X_R\),
\(X_R-n\le2R-2\), and \(R\le2\sqrt n\). Every partial square shell is paid,
giving the conditional all-prefix recurrence
\[
\boxed{E_*(B^2)\ll_\varepsilon
 B^{\kappa/2+\varepsilon}E_*(B),\qquad B\ge2.}
\]

## 5. Conditional exponent transfer and its limitation

If the same original sequence also satisfies
\(M(x)=O_\varepsilon(x^{\theta+\varepsilon})\), with \(\theta\ge1/2\), the
consumer yields the conditional map
\[
\boxed{\theta\longmapsto(1+2\theta+\kappa)/4.}
\]
From a supplied \(7/8\) envelope:

| Additional OPEN owner premise | One-step consequence | Iteration fixed point |
|---|---:|---:|
| \(\kappa=3/4\) | \(7/8\) | \(7/8\) |
| \(\kappa=1/4\) | \(3/4\) | \(5/8\) |
| \(\kappa=0\) | \(11/16\) | \(1/2\) |

The value \(3/4\) is only the fixed-point threshold for this transfer map.
A supplied \(7/8\) theorem does NOT prove `OwnerBound(3/4)`: the forward
argument used an upper bound for \(D_R\), which cannot be reversed to lower
bound the right side of the owner premise. Every owner estimate in this table
remains OPEN. Reusing a fixed uniform premise gives the mathematical sequence
\(\theta_j=(1+\kappa)/2+2^{-j}(\theta_0-(1+\kappa)/2)\).
The draft formalizes the one-step consumer; it does not assert the premise or
claim a completed RH closure from the last line.

## 6. Proof-source map and final cautions

- `research/NATIVE_OWNER_SWAP_RENEWAL_20261021.lean`: actual owner pushforward,
  smooth row, rough-row binding, sign-preserving swap, and complete Gram.
- `research/NATIVE_OWNER_PREFIX_RECURRENCE_20261021.lean`: normalized maximum,
  harmonic diagonal, full-prefix recurrence, and conditional exponent transfer.
- `research/NATIVE_OWNER_PREFIX_MERTENS_20261021.lean`: original-source real
  specialization and the repository's Mertens growth predicate.
- Main inputs: `RHLean/Proof/RecursivePrimeReplacement.lean` and
  `RHLean/Analysis/SquareRootPostCrossingRenewal.lean`.

The independent integer audit passed every \(2\le R\le160\). It checks finite
identities and endpoints, not a uniform arithmetic bound. Final Lean acceptance
requires successful CI and terminal axiom audits for the actual PR head.

Without normalization, the generic recurrence is false: the unit-step sequence
\(M(0)=M(1)=0\), \(M(n)=1\) for \(n\ge2\), has raw
\(E(2)=0<E(4)=1/\sqrt2\). Choosing \(A_R=1+T_R\) gives the exact
square-endpoint decomposition and \(\Gamma_R=1-D_R\), which satisfies the
generic \(\kappa=0\) owner premise.
Separately, a low-product cut \(D=P^{1-\delta}\) supports arbitrary fixed-power
Mellin-row saving only with a fixed frequency margin \(|t|\le P^\nu\),
\(\nu<\delta\), under the proved derivative estimate. Cubic one-slot
dualization must retain its explicit \(a_N*a_N*t_N*\tau\) tail; dropping it
already fails on a prime above \(N\). Neither maneuver proves `OwnerBound`.

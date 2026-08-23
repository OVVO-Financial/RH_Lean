# Truncated upper-middle packet: equivalence map

**Status:** exact identities / formalization targets only.  No RH-scale estimate is claimed here.

Let

\[
X_R=R^2-1,
\qquad
N_R(k)=\#\{q\text{ prime}:R<q\le X_R,\ \lfloor X_R/q\rfloor=k\},
\]

and retain the untouched prime seat `c=1`.  The complete post-root prime fibre is

\[
-1+\sum_{2\le c\le k}(-\mu(c))=-M(k).
\]

The incomplete signed packet is therefore

\[
\boxed{U_R(K)=-\sum_{1\le k\le K}N_R(k)M(k)},\qquad K<R.
\]

The upper `k=1` block is part of this object from the start.  It is never to be removed and the middle is never to be tested as a self-cancelling sector.

## 1. Reciprocal depth and prime cutoff

Define

\[
Q_R(K):=\left\lfloor\frac{X_R}{K+1}\right\rfloor.
\]

For every positive `q`, finite division gives

\[
\boxed{
\left\lfloor\frac{X_R}{q}\right\rfloor\le K
\iff
Q_R(K)<q.
}
\]

Thus the first `K` reciprocal layers are literally the primes above one common cutoff.

When `K+1<R`, the square endpoint gives the stronger exact inverse relation

\[
\boxed{
\left\lfloor\frac{X_R}{Q_R(K)+1}\right\rfloor=K.
}
\]

Proof mechanism: `K+1<R` implies `(K+1)^2<=X_R`, hence `K+1<=Q_R(K)`.  If `Q=Q_R(K)`, Euclidean division gives `(K+1)Q<=X_R<(K+1)(Q+1)`, while `Q>=K+1` gives `K(Q+1)<=(K+1)Q`.  Therefore `K(Q+1)<=X_R<(K+1)(Q+1)`.

Consequences:

\[
\operatorname{primeSieveQuotientSupport}(Q_R(K),X_R)=\{1,\ldots,K\}.
\]

And because `Q_R(K)>R` when `K+1<R`, the truncated reciprocal coordinate is genuinely post-root.

## 2. Prime-tail presentation

The existing quotient reindexing gives

\[
\operatorname{primeSieveMertensPrimeTail}(y,x)
=
\sum_d N_{y,x}(d)M(d).
\]

At `y=Q_R(K)` the quotient support is exactly `1..K`, and its reciprocal intervals coincide with the first `K` root-based intervals.  Hence the intended theorem is

\[
\boxed{
U_R(K)=-\operatorname{primeSieveMertensPrimeTail}(Q_R(K),X_R).
}
\]

Equivalently,

\[
U_R(K)
=-\sum_{\substack{Q_R(K)<q\le X_R\\q\text{ prime}}}
M\!\left(\left\lfloor\frac{X_R}{q}\right\rfloor\right).
\]

This is the prime-first version of the same object; no new cancellation hypothesis is introduced.

## 3. Unique large-prime / unresolved-source presentation

Because `Q_R(K)>\sqrt{X_R}` in the strict sub-root range, every still-unresolved source has a unique canonical factorization

\[
n=cq,\qquad q=P^+(n)>Q_R(K),\qquad c<q.
\]

The existing `PrimeSievePostSqrtGap` bridge gives

\[
\sum_{\substack{n\le X_R\\P^+(n)>Q_R(K)}}\mu(n)
=-\operatorname{primeSieveMertensPrimeTail}(Q_R(K),X_R).
\]

Therefore the same packet should be exposed as

\[
\boxed{
U_R(K)
=
\sum_{\substack{n\le X_R\\P^+(n)>Q_R(K)}}\mu(n).
}
\]

This is a particularly important interpretation: `U_R(K)` is the exact Möbius mass of sources whose last/largest prime has not yet acted at cutoff `Q_R(K)`.

## 4. Frozen-prime sequential presentation

Let

\[
F_R(y):=
\operatorname{frozenPrimeUniverseMass}(\operatorname{primesUpTo}y,X_R).
\]

The existing one-prime recurrence and telescope give

\[
F_R(y)=F_R(R)-\sum_{R<q\le y\atop q\text{ prime}}M(\lfloor X_R/q\rfloor),
\]

and the saturated endpoint is

\[
F_R(X_R)=M(X_R).
\]

Subtracting the two finite telescopes yields, for `R<=y<=X_R`,

\[
\boxed{
F_R(y)-M(X_R)
=
\operatorname{primeSieveMertensPrimeTail}(y,X_R).
}
\]

At `y=Q_R(K)`:

\[
\boxed{
U_R(K)=M(X_R)-F_R(Q_R(K)).
}
\]

Thus a packet sign crossing is literally the sequential frozen-prime state crossing its own terminal Möbius value.  It is not an arbitrary analytic sign change.

## 5. All-plus visualization presentation

The already-proved post-square-root gap theorem says

\[
\operatorname{allPlus}(y,X_R)-M(X_R)
=2\operatorname{primeSieveMertensPrimeTail}(y,X_R).
\]

Therefore at the truncated cutoff

\[
\boxed{
\operatorname{allPlus}(Q_R(K),X_R)-M(X_R)=-2U_R(K).
}
\]

Together with the frozen form this gives the affine relation

\[
\boxed{
\operatorname{allPlus}(Q_R(K),X_R)=2F_R(Q_R(K))-M(X_R).
}
\]

This reconnects the original sign-flip visualization to the same truncated packet.

## 6. Abel / shallow-cap presentation

With

\[
P_R(d)=\pi(\max(R,\lfloor X_R/d\rfloor))-\pi(R),
\]

the exact Abel identity is

\[
U_R(K)
=-\sum_{d\le K}\mu(d)P_R(d)+M(K)P_R(K+1).
\]

Subtracting the common lower rectangle gives the incomplete cap

\[
\boxed{
U_R(K)
=-\sum_{d\le K}\mu(d)\,[P_R(d)-P_R(K+1)].
}
\]

Equivalently, because the common boundary is `Q_R(K)`, this is the signed triangular region

\[
\boxed{
U_R(K)
=
\sum_{d\le K}
\sum_{\substack{Q_R(K)<q\le X_R/d\\q\text{ prime}}}\mu(dq).
}
\]

The large prime is fresh, so `mu(dq)=-mu(d)`.

## 7. Fresh-prime finite difference survives because the cap is incomplete

Let

\[
W_{R,K}(d)=P_R(d)-P_R(K+1).
\]

For a fresh prime `p>d`,

\[
-\mu(d)W(d)-\mu(dp)W(dp)
=-\mu(d)[P_R(d)-P_R(dp)].
\]

The common lower boundary cancels exactly, but the upper weight remains nonconstant.  This is the key distinction from the completed `(p,k)` no-go in PR #455: completion does **not** turn the incomplete cap weight into coefficient `1`.

The next factor-resolved candidate is therefore to group `d` by its fresh/largest prime and retain this prime-count finite difference before any completion.

## 8. Crossing and discrete interpolation

Use the integer shadow

\[
U_R^{\mathbb Z}(K)
=-\sum_{k\le K}N_R(k)M_{\mathbb Z}(k).
\]

One layer obeys

\[
U_R^{\mathbb Z}(K)-U_R^{\mathbb Z}(K-1)
=-N_R(K)M_{\mathbb Z}(K).
\]

Therefore a crossing

\[
U_R(K-1)<0\le U_R(K)
\]

forces both

\[
N_R(K)>0,\qquad M(K)<0.
\]

Every prime in that layer changes the partially traversed packet by the same positive integer `-M(K)`.  If `j` is the least number of layer primes needed to reach nonnegative mass, then

\[
\boxed{
0\le V_R(K,j)<-M(K)\le K.
}
\]

Hence any crossing with `K<R` already yields a residual `<R` by pure finite arithmetic.  The overshoot is not the analytic problem; existence/location of a crossing is.

## 9. Monotone sign runs

The one-layer recurrence immediately gives:

- if `M(K)<=0`, then `U_R(K-1)<=U_R(K)`;
- if `M(K)<0` and `N_R(K)>0`, the increase is strict;
- if `M(K)>=0`, the layer moves the packet downward.

Thus the packet trajectory is driven by **lower Mertens sign runs weighted only by positive prime multiplicities**.  No high-prime sign remains.

## 10. Initial negative boundary

At `K=1`,

\[
U_R(1)=-N_R(1),
\]

the top prime block.  Bertrand's postulate is already available in the repository and should be sufficient to prove strict negativity for the stable range by producing a prime in the top interval.

Once `U_R(1)<0` is machine-checked, crossing existence reduces to finding any sub-root depth with nonnegative packet; the least such depth automatically satisfies the crossing predicate.

## 11. Exact coefficient packages behind the observed shallow depth

Define

\[
S_K=\sum_{k\le K}\frac{M(k)}{k(k+1)}.
\]

Finite Abel gives exactly

\[
\boxed{
S_K=\sum_{k\le K}\frac{\mu(k)}k-\frac{M(K)}{K+1}.
}
\]

Likewise the logarithmic finite-difference coefficient is

\[
B_K
=\sum_{k\le K}\frac{\mu(k)\log k}{k}
-\frac{M(K)\log(K+1)}{K+1}.
\]

The finite gate suggests `K*S_K` near `2` and `B_K` near `-1`, which explains the empirical balance `K~2 log X_R~4 log R` after expanding reciprocal prime density.  This is diagnostic only; the repository's current elementary reciprocal-Möbius bounds are not strong enough to prove it.

## 12. `p,k` chronology without the old completion collapse

PR #455 proves predecessor-prime completion identities and primorial deletion.  Those results should now be applied **inside the incomplete cap weight** rather than to a completed `k` fibre.

For a predecessor prime `p`, split the cap cofactors into the old face and fresh `p`-face.  The constant common lower boundary is multiplied by the predecessor mass

\[
A_p(K)=\sum_{d\le K/p,\ P^+(d)<p}\mu(d),
\]

so once the predecessor cube is primorial-complete, that constant term vanishes exactly.  But the varying upper weight `P_R(pd)` remains.  This is precisely what was absent from the completed #455 cell.

The intended surviving object is therefore a weighted predecessor cell of schematic form

\[
\sum_{d\le K/p\atop P^+(d)<p}
\mu(d)\,[P_R(d)-P_R(pd)],
\]

not `A_p(K)` times a constant positive count.

This is the most direct bridge between the old sequential-prime machinery and the new truncated packet.

## Route invariant

Every future manipulation should preserve the following facts simultaneously:

\[
\boxed{
\text{upper }k=1\text{ boundary and shallow middle remain one signed object},
}
\]

\[
\boxed{
\text{high-prime signs are already completed lower-cofactor signs},
}
\]

\[
\boxed{
\text{the reciprocal coordinate remains deliberately incomplete},
}
\]

\[
\boxed{
\text{a successful factor refinement must retain a nonconstant cap weight}.
}
\]

The open theorem is now the existence/location of a sub-root crossing (the finite gate suggests a logarithmic location).  Conditional on such a crossing, the partial-layer interpolation already supplies a strictly sub-root residual without any analytic estimate.

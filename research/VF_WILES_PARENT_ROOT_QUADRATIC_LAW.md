# Universal square-root ancestor contraction versus non-universal signed sector profile

**2026-10-10, PR #925.** This isolates the universal component of the apparent
\(t^2\) law in the fully enumerated \([17,18]\) (and 56, 119, 317, 1027)
within-square clipping datasets, without assuming RH or changing the actual
original physical VF/Sector Six weights.

## A universal multiplicative ancestor-root contraction

Let \(R\ge2\), \(R^2\le x\le(R+1)^2\), and define
\(u=\sqrt{x}-R\in[0,1]\) and
\(t=(x-R^2)/(2R+1)\in[0,1]\). Exactly,

\[
t=u-\frac{u(1-u)}{2R+1},\qquad
0\le u-t\le \frac1{4(2R+1)}.
\tag{SQ1}
\]

For an original integer \(n=cq\), where \(c\ge1\) is an integer
cofactor and \(q\) is the *genuine* earlier integer/prime parent,
\[
\sqrt q=\frac{\sqrt n}{\sqrt c}
       =\frac{R+u}{\sqrt c}.
\tag{SQ2}
\]
The entire current square block thus maps into an ancestral
square-root interval of **exact width \(1/\sqrt c\)**.
Compositions of two ancestry steps contract by
\(1/\sqrt{c_1c_2}\), without independence, mean-square arguments,
or any new representation of pi.

Let
\[
b_c(R)=\lfloor(R+1)/\sqrt c\rfloor-\lfloor R/\sqrt c\rfloor.
\]
For \(c>1\), \(b_c(R)\in\{0,1\}\). Across *any* consecutive current
square blocks \(R=A,\ldots,B-1\), the actual historical root-boundary
transitions obey the **exact all-scale telescope**
\[
\sum_{R=A}^{B-1}b_c(R)
=\lfloor B/\sqrt c\rfloor-\lfloor A/\sqrt c\rfloor,
\quad
\left|\sum b_c(R)-\frac{B-A}{\sqrt c}\right|<1.
\tag{SQ3}
\]
For nonsquare c these count interior parent-root crossings;
for square c the changes are endpoint hits, not interior crossings.

Independent exact integer check for A=8, B=201 (193 roots):
c=3: 112 observed, 193/sqrt(3)=111.43;
c=5: 86 observed, 193/sqrt(5)=86.31;
c=7: 72 observed, 193/sqrt(7)=72.95;
c=11: 58 observed, 193/sqrt(11)=58.19;
c=15: 49 observed, 193/sqrt(15)=49.83;
c=27: 37 observed, 193/sqrt(27)=37.14.
c=9 has no *interior* root crossings; its floor-step transitions
are right-endpoint hits at multiples of 3.

Concrete physical R=17,c=3: the contracted parent-root interval is
(9.815,10.392), crossing historical root 10. It contains actual
prime parents q=97,101,103,107, whose literal descendants n=3q
are 291,303,309,321 in the current original square band.

## An exact two-coordinate quadratic geometric backbone

There are exactly R odd candidate sites in the strict-open band.
Let m(x) be the count encountered by cutoff x; a parity count
gives \(|m(x)/R-t|\le1/R\). Every original unordered candidate pair
has two coordinates, so the cumulative total of candidate pairs is
\({m(x)\choose2}\). Let q=m(x)/R. The finite identity is

\[
\boxed{
\frac{\binom{m(x)}2}{\binom R2}
=q^2-\frac{q(1-q)}{R-1}
=t^2+O(1/R)
}
\tag{SQ4}
\]
uniformly for all cutoffs and all R>=2, *independent* of prime
distribution. The first equality was added as Mathlib-only kernel
lemma \`vfWilesUnfilteredPairQuadratic_ratio\`.

There is also an exact cofactor-window interpretation:
\[
\#\{q\in\mathbb Z:R^2/c<q\le x/c\}
=\lfloor x/c\rfloor-\lfloor R^2/c\rfloor
=t(2R+1)/c+\epsilon_c,\quad|\epsilon_c|<1.
\tag{SQ5}
\]
Unrestricted two-parent rectangle areas therefore have leading
\(t^2(2R+1)^2/(cd)\), with an elementary floor error.

**CAUTION:** Filtering these windows to genuine *prime parents*,
to selected squarefree/squareful native owners, and to a precise
first/next/returned clip orientation changes their occupancy.
The geometric square-law (SQ4) does not automatically pass
through this nonuniform arithmetic selection.

## The exact signed next-right correction to t^2

Let P(t) = genuine current prime physical sites, C(t) = genuine
squarefree current composite physical sites, N(t) = genuine
composite/composite native next-right pair count. Let P,C,N
denote their full-block totals. Keep the ORIGINAL fixed
\(w=(2R+1)/(R\log(R^2+R+1/2))\) and write

\[
Z_{\rm NR}(t)=w^2N(t)-w(1-w)P(t)C(t).
\tag{SQ6}
\]
Introduce ***measured arithmetic*** discrepancies
\(\delta_P=P(t)-tP,\ \delta_C=C(t)-tC,\
\delta_N=N(t)-t^2N\).
Then ordinary algebra gives the precise identity

\[
\boxed{
Z_{\rm NR}(t)-t^2 Z_{\rm NR}(1)
=w^2\delta_N-
w(1-w)\left[
t(P\delta_C+C\delta_P)+\delta_P\delta_C
\right].
}
\tag{SQ7}
\]

**This is the criterion, not an assumption:** a pure quadratic
signed profile follows only if the actual arithmetic
correction on the right is sufficiently small.
The identity was added as kernel theorem
\`vfWilesSignedNextRight_quadraticDeviation\`.
No bound on the correction follows from the identity.

At R=1027 and x=1,055,757, the cutoff is at t≈0.50024:
\[
(P(t),C(t),N(t))=(64,351,26101),\quad
(P,C,N)=(144,686,102733).
\]
For the reference t=1/2, these produce
\(\delta_P=-8,\delta_C=+8,\delta_N=+417.75\).
The two right-hand terms in (SQ7) are respectively
**+8.6948 and +275.5521**, for an actual signed deviation
of **+284.2470**. The normalized signed progress is
\(Z_{\rm NR}(t)/Z_{\rm NR}(1)\approx0.2217\), not 0.25.

The *entire squarefree active pair population* in this same
sample has 415 of 830 active sites, hence its exact cumulative
pair ratio is \(\binom{415}{2}/\binom{830}{2}\approx0.2497\).
Thus the universal pair-square geometry is almost perfect,
while the signed arithmetic sector has an additional 11%
relative deviation at the midpoint.

At R=25, x=629, the true next-right signed sector is +0.099177
before the first prime enters; its completed value is negative.
That is an actual integer counterexample to a universal
pointwise signed \(Z_{\rm NR}(t)=t^2 Z_{\rm NR}(1)\).

## Proof frontier

We have a **true unconditional self-similar ancestral contraction**
(SQ2), a **uniform floor-phase telescope** (SQ3), and a
**universal unfiltered pair-square law** (SQ4).
The conjectured *signed* arithmetic scale invariance is
precisely the independent prime/composite/owner-phase correction
(SQ7), which is not forced by those geometrical identities.

The useful research question is whether the actual multiplicative
ancestor-root phases and historical once-charged owner structure
control SQ7 at the original RH-strength first-bad boundary.
That requires an independently proved bound on the *signed*
prime-filtered correction (or the full original six-sector Gram);
the finite census does not prove it.

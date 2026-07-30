# Complete collision cells and the vanishing frontier

## Statement

Fix distinct lower primes

\[
\mathcal P_y=\{p:p\le y\},\qquad P_y=\prod_{p\le y}p.
\]

For an integer `m`, let

\[
\kappa_y(m)=\#\{p\le y:p\mid m\}
\]

be its lower-prime collision multiplicity, and define the collision sign

\[
\sigma_y(m)=(-1)^{\kappa_y(m)}.
\]

The pattern is periodic modulo `P_y`. In every complete `P_y`-cell, the number
of even-collision entries equals the number of odd-collision entries. Hence

\[
\sum_{r=0}^{P_y-1}\sigma_y(r)=0.
\]

For the square block

\[
B_n=[n^2,(n+1)^2),\qquad |B_n|=2n+1,
\]

all complete `P_y`-cells cancel. Only the two incomplete boundary fragments and
positions whose full factorization is not yet resolved by the lower-prime base
can contribute to the final Möbius discrepancy.

## Exact collision counts

Let `C_{y,j}` be the number of residues modulo `P_y` hit by exactly `j` lower
prime combs. The collision polynomial is

\[
F_y(z)=\prod_{p\le y}(p-1+z).
\]

Indeed, for each prime `p`, there are `p-1` residue choices avoiding the
`p`-comb and one residue choice lying on it. Therefore

\[
C_{y,j}=[z^j]F_y(z).
\]

The signed collision mass of a complete cell is

\[
\sum_j(-1)^jC_{y,j}=F_y(-1)=\prod_{p\le y}(p-2).
\]

Because `2` belongs to the prime base,

\[
F_y(-1)=0.
\]

Thus every complete collision cell has exact even/odd balance.

## Successive-prime recursion

Suppose the current prime base has collision counts `C_j`, and a new prime `q`
is added. The old cell is copied `q` times inside the new cell of length `qP`.
Of those copies, `q-1` avoid the new comb and retain collision depth `j`; one
copy lies on the new comb and moves from depth `j-1` to depth `j`. Hence

\[
C'_j=(q-1)C_j+C_{j-1}.
\]

Equivalently,

\[
F_{\mathrm{new}}(z)=(q-1+z)F_{\mathrm{old}}(z).
\]

This is the exact arithmetic meaning of adding one prime coordinate to the
collision cube.

## Boundary decomposition

Write the square block as

\[
B_n=E^-_{n,y}\;\sqcup\;
\left(\bigsqcup_{t=1}^{N_{n,y}}(a_t+[0,P_y))\right)
\;\sqcup\;E^+_{n,y},
\]

where the middle pieces are complete aligned `P_y`-cells. The two boundary
fragments satisfy

\[
|E^-_{n,y}|+|E^+_{n,y}|<2P_y.
\]

Since every complete cell has signed collision mass zero,

\[
\left|\sum_{m\in B_n}\sigma_y(m)\right|<2P_y.
\]

For fixed `y`, division by the block length gives

\[
\frac1{2n+1}\left|\sum_{m\in B_n}\sigma_y(m)\right|
\le \frac{2P_y}{2n+1}\longrightarrow0.
\]

## From collision sign to Möbius sign

For a squarefree integer whose prime factors are all represented in the active
collision state,

\[
\mu(m)=(-1)^{\omega(m)}=(-1)^{\kappa_y(m)}=\sigma_y(m).
\]

Let `U_{n,y}` be the unresolved frontier: positions in `B_n` where the active
lower-prime collision state does not yet determine the complete squarefree
factorization state. Off this frontier, the collision sign equals the actual
Möbius sign. Since `|\mu(m)|\le1`,

\[
|\Delta_n|
\le 2P_y+|U_{n,y}|,
\qquad
\Delta_n=\sum_{m\in B_n}\mu(m).
\]

This is the required two-error estimate:

\[
\boxed{|\Delta_n|\le 2P_y+|U_{n,y}|.}
\]

The first term is the incomplete-cell boundary. The second is the unresolved
prime frontier.

## Ordered-limit closure

Assume the growing prefix-prime sieve gives

\[
\lim_{y\to\infty}\limsup_{n\to\infty}
\frac{|U_{n,y}|}{2n+1}=0.
\]

Given `epsilon > 0`, choose `y` so that eventually

\[
\frac{|U_{n,y}|}{2n+1}<\frac{\epsilon}{2}.
\]

With this fixed `y`, choose `n` so large that

\[
\frac{2P_y}{2n+1}<\frac{\epsilon}{2}.
\]

Then

\[
\frac{|\Delta_n|}{2n+1}<\epsilon.
\]

Therefore

\[
\boxed{\Delta_n=o(n).}
\]

The cancellation and density arguments have distinct roles:

1. collision parity gives exact cancellation on every completed cell;
2. the growing lower-prime base makes the unresolved frontier negligible.

The finite block never needs to be perfectly balanced. It only needs to consist
of an increasing number of exactly balanced complete cells plus a frontier of
vanishing relative size.

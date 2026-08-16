# Square-root legal-ancestry Gram attack

## Status

The square-root endpoint experiment suggests the fixed-amplification statement

\[
(M(R^2-1)-1)^2 \le A R^2 K_R,
\]

where `A` is an absolute constant and `K_R` controls all lower Mertens values:

\[
(M(y)-1)^2 \le K_R (y+1),\qquad y<R.
\]

The exhaustive exact scan through `R = 100000` found

\[
\max_{56\le R\le 100000}
\frac{(M(R^2-1)-1)^2}{R^2K(R)}
=0.1291432502985845
\]

at `R = 88130`.  The formal theorem deliberately does not assert a subunit
constant.  Any finite absolute `A` is enough for the RH-scale exponent after
square-root descent.

## Formal reduction now in Lean

`RHLean/Proof/SquareRootLegalAncestryGramReduction.lean` defines the lower
critical envelope and the complete legal root-successor Gram defect

\[
G_R=(U_R-S_R)^2.
\]

It proves the exact identities

\[
U_R-S_R=M(R^2-1)-1,
\]

\[
U_R=\text{squareRootAncestryRootPrimeMass}(R),
\]

and

\[
S_R=-\text{squareRootAncestrySmoothMassInt}(R).
\]

Therefore

\[
G_R=(U_R+V_R)^2,
\qquad
V_R=\text{squareRootAncestrySmoothMassInt}(R).
\]

The fixed-amplification Gram statement is proved equivalent to the direct
anti-alignment statement

\[
U_R^2+V_R^2-A R^2K_R\le -2U_RV_R.
\]

`RHLean/Proof/SquareRootMertensEndpointAmplification.lean` then proves that the
same Gram statement is exactly the scalar endpoint statement measured in the
experiment.  Thus the analytic open theorem is not a proxy for the empirical
quantity: they are definitionally connected by proved identities.

## Why any fixed amplification constant is enough

Fix `epsilon > 0` and suppose the endpoint theorem holds with some finite
`A >= 0`.  Choose `R0` so large that

\[
4A\le R_0^{\epsilon}.
\]

Choose `C >= 36` large enough to cover the finite base range below `R0^2`.
Assume inductively that

\[
(M(y)-1)^2\le C(y+1)^{1+\epsilon}
\]

for every `y < R^2`, with `R >= R0`.

For every `y<R`,

\[
(M(y)-1)^2
\le C(y+1)^{1+\epsilon}
\le C R^{\epsilon}(y+1),
\]

so the legal lower-envelope parameter may be taken as

\[
K_R=C R^{\epsilon}.
\]

The endpoint theorem gives

\[
(M(R^2-1)-1)^2
\le A C R^{2+\epsilon}.
\]

Since `4A <= R^epsilon`, this is at most

\[
\frac{C}{4}R^{2+2\epsilon}.
\]

Now let

\[
R^2\le x<(R+1)^2.
\]

The unfinished part of the square block has length at most `2R+1 <= 3R`, hence

\[
|M(x)-M(R^2-1)|\le3R.
\]

Using `(a+b)^2 <= 2a^2+2b^2`,

\[
(M(x)-1)^2
\le
2ACR^{2+\epsilon}+18R^2.
\]

The first term is at most

\[
\frac{C}{2}R^{2+2\epsilon},
\]

and, because `C >= 36`, the second is also at most

\[
\frac{C}{2}R^{2+2\epsilon}.
\]

Therefore

\[
(M(x)-1)^2\le C R^{2+2\epsilon}
\le C(x+1)^{1+\epsilon}.
\]

This closes strong induction by entire square blocks.  Consequently any fixed
absolute amplification constant gives

\[
M(x)=O_\epsilon(x^{1/2+\epsilon/2}),
\]

and renaming the exponent gives the repository's Mertens energy criterion.
The fixed amplification is absorbed by the extra `R^epsilon` available at each
square-root jump.  No claim of `O(sqrt x)` is needed or intended.

The remaining Lean work in this reduction is generic real-power bookkeeping and
finite-base packaging; the number-theoretic obstruction is the fixed-`A`
anti-alignment theorem above.

## Direct attack: parent fibres

`RHLean/Proof/SquareRootAncestryParentFibres.lean` expands the complete successor
without truncating the ancestry.

For every bounded canonical parent `p`, define the active legal-child
multiplicity

\[
\nu_{B,x}(p)
=
\#\{s:\operatorname{clock}(s)\le x,\ \operatorname{parent}(s)=p\}.
\]

The Lean module proves exactly

\[
S_{B,x}
=
\sum_p \nu_{B,x}(p)\,w(p).
\]

At the complete square endpoint, the root-successor cross term is therefore

\[
U_RS_R
=
\left(\sum_{u\in\mathcal R_R}w(u)\right)
\left(\sum_p \nu_R(p)w(p)\right),
\]

and the module expands it as a source-level finite ledger indexed by root,
parent, and child.  No norm is taken before this expansion.

This is the next arithmetic target.  The canonical parent map strips the largest
prime of the core, so each inverse parent fibre is an actual legal prime-extension
family.  The desired estimate is therefore a signed correlation theorem between
transport roots and the genuine prime-extension multiplicities `nu_R(p)`.

## Prime-wheel seam

The repository already reindexes square-wheel endpoint and survivor prime fibres
onto the same `CanonicalSourceData q c` atoms.  Hence the next useful theorem is
not an ambient operator estimate.  It should identify the parent-fibre
multiplicity ledger with a centered prime-wheel fibre ledger on the same
`(q,c)` coordinates and then retain the complete signed sum over `q`.

A useful target shape is

\[
-2U_RV_R
\ge U_R^2+V_R^2-A R^2K_R,
\]

proved after prime-fibre centering.  Separate estimates for `U_R`, `V_R`, or
individual prime fibres are specifically avoided.

## Next exact lemma to pursue

Reindex each inverse parent fibre by the stripped extension prime.  For a parent
with canonical coordinates `(q,a)`, characterize all children as cores `a p`
with

- `p` prime,
- `p` strictly larger than every prime factor of `a`,
- `p < q`,
- `p` coprime to `q a`,
- the child remains under the complete-square cutoff.

This turns `nu_R(q,a)` into an explicit legal-prime count.  That count can then
be compared on the same distinguished-prime coordinate `q` with the existing
square-wheel centered prime fibres.

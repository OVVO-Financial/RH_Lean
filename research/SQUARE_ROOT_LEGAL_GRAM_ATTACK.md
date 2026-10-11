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

at `R = 88130`. The formal theorem deliberately does not assert a subunit
constant. Any finite absolute `A` is enough for the RH-scale exponent after
square-root descent.

## Formal reduction in Lean

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

Thus the fixed-amplification Gram statement is exactly the direct
prime-root/smooth-mass anti-alignment statement

\[
U_R^2+V_R^2-A R^2K_R\le -2U_RV_R.
\]

`RHLean/Proof/SquareRootMertensEndpointAmplification.lean` proves that this is
exactly the scalar endpoint statement measured by the `A_R` experiment.

`RHLean/Proof/SquareRootAmplificationClosure.lean` closes the deterministic
part: any fixed endpoint amplification constant implies the repository's
`MertensEnergyBoundedStatement`. The proof is strong induction on physical
`x`, with `R = floor(sqrt x)`. The fixed amplification is absorbed by one extra
`R^epsilon`, while the unfinished square block contributes only `O(R^2)` after
squaring. No subunit contraction is required.

## Direct attack: complete successor parent fibres

`RHLean/Proof/SquareRootAncestryParentFibres.lean` expands the complete successor
without truncating ancestry. If `nu_{B,x}(p)` is the number of active legal
children selecting parent `p`, then exactly

\[
S_{B,x}=\sum_p \nu_{B,x}(p)w(p).
\]

The root-successor cross term is also expanded as a finite root/parent/child
ledger before any norm is taken.

`RHLean/Proof/SquareRootAncestryExtensionWindows.lean` supplies the generic
inverse-parent geometry at every ancestry depth. A child is obtained from a
canonical parent `(q,a)` by adjoining a new largest core prime `p`; stripping
that prime recovers the parent exactly. Every legal extension under `R^2-1`
satisfies

\[
p<q<R.
\]

Thus both the parent data and the newly adjoined prime lie strictly below the
square-root induction scale.

## Fixed-prime cancellation is not the mechanism

A direct fibre diagnostic rules out estimating each distinguished-prime fibre
separately.

At `R = 5561`, the exact scalar pieces are

\[
M(R^2-1)=-2544,
\quad U=125204,
\quad V=-127749,
\]

so `U+V = M-1 = -2545`. But the same-`q` root/smooth cross term accounts for
only about `0.54%` of the diagonal energy, whereas the global scalar cross term
accounts for about `99.98%`.

The prime-region split is

\[
U_{q\le R}=831,
\qquad U_{q>R}=124373,
\qquad V=-127749.
\]

The same pattern strengthens with scale: at `R = 2000`, same-`q` cancellation is
about `1.45%` of the diagonal while the global cross-`q` cancellation is about
`99.996%`.

Therefore a theorem that takes norms of fixed-prime fibres separately attacks
the wrong interaction. The dominant cancellation is lower-prime smooth mass
against upper-prime transport mass across different distinguished primes.

## Cross-region sufficient targets

`RHLean/Proof/SquareRootCrossRegionAmplification.lean` packages the observed
interaction in two already-signed channels:

\[
P_R=\text{positiveSmooth}(R),
\qquad
J_R=\text{matched}(R)-1.
\]

The exact shifted endpoint identity is

\[
M(R^2-1)-1=P_R+J_R.
\]

Fixed critical-envelope bounds for `P_R` and `J_R` imply the full endpoint
amplification with a fixed constant, hence imply Mertens energy through the
square-root closure theorem.

The exact scan through `R = 100000` gives

\[
\max_{R\ge56}\frac{|P_R|^2}{R^2K(R)}
=0.12126291751707746,
\]

and

\[
\max_{R\ge56}\frac{|J_R|^2}{R^2K(R)}
=0.24759970370225298.
\]

These are stronger sufficient targets than the full scalar estimate, but they
retain the essential signed interaction within each channel rather than
splitting raw root and successor diagonals.

## Matched channel localizes to the far-survivor core

For `R >= 56`, the existing exact bridge gives

\[
\text{matched}(R)-1
=
\bigl(\text{bornSmooth}(R)+\text{farSurvivor}(R-1)-1\bigr)
-
\text{nearTransport}(R).
\]

The near strip has norm at most `7R`. Since every lower critical envelope is at
least one, `SquareRootCrossRegionAmplification.lean` proves that a fixed
amplification bound for the signed core

\[
C_R=\text{bornSmooth}(R)+\text{farSurvivor}(R-1)-1
\]

implies one for the full matched channel with only an explicit constant penalty.

Numerically,

\[
\max_{56\le R\le100000}\frac{|C_R|^2}{R^2K(R)}
=0.24820652956264863
\]

at `R = 62340`. Removing the seven-coordinate strip therefore does not expose a
hidden growing term.

The exact increment is

\[
C_{R+1}-C_R
=
\text{bornSmoothBlock}_R
+
\bigl(\text{farSurvivor}_R-\text{farSurvivor}_{R-1}\bigr).
\]

Through `R = 100000`, the increment never exceeds about `0.353 R` in absolute
value, and its dyadic quadratic variation is consistently of order
`(band length) * (scale)`. This is evidence for a signed block-Gram mechanism,
not for absolute summation: Cauchy on the increments would still lose a factor
of the root scale.

## Sign-blind lower-cofactor collapse fails

Fully unwinding ancestry gives an exact lower-cofactor transform

\[
M(R^2-1)-1=\sum_{c<R} a_R(c)\mu(c).
\]

But absolute coefficient variation is far too large. The weighted variation
normalized by `R` grows from about `130` at `R=100` to about `8423` at
`R=2000`, and the coefficient at `c=1` already contains the prime main mode
`-pi(R^2-1)`.

So Abel summation after sign-blind cofactor collapse is not a viable proof. The
prime coherent mode must be centered and canceled before any norm, in line with
the square-wheel architecture.

## Prime-wheel seam and current analytic target

The repository already rewrites the upper transport channel as lower-cofactor
explicit prime windows and exposes Li bulk plus prime-count discrepancy. The new
parent-fibre layer is the smooth-side mirror. But the fixed-prime diagnostic
shows that these windows must be recombined globally before taking a norm.

The current hard target is therefore the complete signed cross-region object,
preferably the far-survivor core

\[
\boxed{
\text{bornSmooth}(R)+\text{farSurvivor}(R-1)-1
}
\]

under the lower critical envelope. `FarSurvivorRenewal_is_LowerMertens.lean`
identifies the far fixed-prime finite difference with lower Mertens values, but
that identity should be used only inside the global signed recombination. A
fixed-`q` norm would discard essentially all of the observed cancellation.

The next proof-level advance should be a global signed Gram or centered
prime-window theorem for this cross-region core. No raw diagonal estimate,
fixed-prime absolute bound, or sign-blind renewal telescope is an acceptable
replacement.


## Euler-product square-root cutoff and finite C / A (2026-10-11)

See [Euler product and finite C/A: exact square-root bridge](EULER_PRODUCT_SQUARE_ROOT_FINITE_C_A.md)
and the runnable audit at [euler_finite_ca_cutoff_audit.py](../scripts/euler_finite_ca_cutoff_audit.py).

The **same original** Möbius bilinear floor operator, with X=R^2-1, is

\[
Q_R=\sum_{a,b<R}\mu(a)\mu(b)\lfloor X/(ab)\rfloor
    =2M(R-1)-M(X).
\]

The second equality is a formal Euler-product coefficient identity: write
F=1/\zeta, Z_R=\sum_{n<R}\mu(n)n^{-s}, T_R=F-Z_R. Then
\(\zeta Z_R^2=F-2T_R+\zeta T_R^2\), and the last term has
**no coefficient below R^2**. This is why the historical cutoff is the square root.

Writing \(K_R=\max_{y<R}(M(y)-1)^2/(y+1)\), the fixed-C estimate

\[
|Q_R|\le C R\sqrt{K_R}
\]

would imply the already-established conditional amplification premise with

\[
A\le(C+\sqrt2+1/2)^2.
\]

The opposite implication also holds with C<=sqrt(A)+sqrt(2)+1/2.
The finite high-prime Euler factor has a uniformly bounded critical-line
*mean-square* (<=11/6), and high-prime descendants have an exact
reciprocal-weighted energy contraction (<=5/6). Neither estimate is an
unweighted sharp-endpoint bound for Q_R. The needed **signed** low-smooth /
high-prime compensation remains open; neither the product factor nor the
finite numerical audit establishes a finite universal C.

Historical tables earlier in this document include older provisional
maximum-ratio figures; use the independently corrected finite-A census
and the linked Euler audit for the current C/A numerical normalization.

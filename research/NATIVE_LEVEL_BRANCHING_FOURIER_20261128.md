# Degree-sensitive branching and finite Fourier transport

Continues #1214 at 3ae62df, preserving the exact source, rank and window
acceptance contract. The independent upstream level saving is earned by
restrictToY in Columns/ColumnDefs.lean, with the real bound
weylNormSq_restrictToY_le and finite gauge identity
GaugeLe.restrictToY_of_diag in Seesaw/LiftCharacters.lean, pinned
lsernau/grh-lean 72fead102f663d5c7a407964a13dc0cf9d977207.
Columns/TwistedHeckeType.lean connects that finite gauge to
chain2_pairTranslates_eq_smul_chain and the Fourier preimage index.

## Actual native polynomial restriction

NativeLevelBranching.lean works in the existing NativeThetaFock metric,
not a newly defined norm. For a distinguished variable t and degree h,
reweight the coefficients by the multiplier 1_(alpha(t)=h) v^(-h).
Here v is the conjugate of the existing integral level-prime norm
element, so |sigma(v)|^2=N in every embedding. Its squared Fock
operator bound is N^(-h). On the dilated polynomial P(z,Nt), the
same operator gives the selected degree times u^h, since uv=N.
Thus the finite coefficient integrality and the real contraction
refer to exactly the same map. No independent artificial norm.

The cyclic Fourier transform is Mathlib's actual ZMod.dft, now acting
on the same MvPolynomial carrier. A coefficient reweighting is a linear
map and commutes with that transform. Its exact pair identity is
F^2 f(j)=N f(-j), not N^h f(j). All signed complex phases are kept.
The degree mean identity shows the average coordinate exponent on a
coordinate-symmetric family; its application requires an actual
permutation symmetry of the retained sections.

## Paired preimage on the cyclic polynomial sections

Let $F$ be the existing counting-measure DFT and $D_z$ substitute $zt$
for the distinguished source variable $t$. Use $T=D_{N^{-1}}F$ on
these sections. For each monomial of distinguished degree $e$,
$q$ Fourier pairs act by $N^{q-2qe}J^q$, with $J$ the actual residue
reflection. To land in $D_N$ of the integral coefficient lattice, clear
that monomial by $N^{c_e}$, where
\[
c_e=((2q+1)e-q)_+ .
\]
The remaining output relative to $D_N$ is $N^{(q-(2q+1)e)_+}$ times
the reflected coefficient. In particular the proof produces an integral
seed for the dilated output at every residue. The same cleared rows
have integral output under the degree-$h$ restriction, by the already
proved compensation identity for the two norm factors.

At one residue level, cyclic ramification is the image of one minus
substitution by a scalar unit $u$. The DFT sends that image to the
image for $u^{-1}$. Reflection commutes with the unit action, so the
cleared paired preimage transports an integral seed for the same
ramification. For any finite list of coefficient basis labels the
diagonal clearing determinant is $N^{\sum_i c_{e_i}}$. The labels
can include repetitions from the residue basis, with those
multiplicities counted in the sum. On a degree-$A$ coefficient list
with equal column-degree sums in $k$ variables this exponent is at
most $(2q+1)A/k$ per column. The Lean bound takes the integer form
$k\sum_i c_{e_i}\le(2q+1)A\lvert I\rvert$.
[Cyclic preimage, restriction and determinant](NativeLevelBranching.lean).

## Attachment to the retained lift

The compact proof uses a different finite operator. It applies
$\operatorname{diag}(1,\ldots,1,N^{-1})$ to a character sum over
matrix actions indexed by residue vectors with unit final entry.
To transfer the preimage to the signed short-form estimate, the actual
paired native lift on the retained sections must intertwine with the
source action at that level. The retained basis must also satisfy the
source degree and rank count on the same lift. The calculation above
proves the preimage, its index certificate and its ramification on
the cyclic polynomial sections. The comparison with the original
wheel lift, its full signed volume and the window estimate remains open.
[Upstream finite operator and paired-chain identity](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Seesaw/NamesAtSplitLevel.lean#L104-L117)
([paired-chain proof](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Seesaw/NamesAtSplitLevel.lean#L229-L255)).

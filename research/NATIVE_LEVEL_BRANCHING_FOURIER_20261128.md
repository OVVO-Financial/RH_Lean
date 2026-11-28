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

## What still needs proving

The above identities are enabling suppliers. They do not establish
that the actual ramified native composite chain maps the Fourier
preimage of the small-degree lattice into the high-degree dilation.
In particular, ordinary Fourier on a residue label and homogeneous
coefficient dilation on a polynomial variable act on different axes.
They commute, but that is not the upstream paired-chain transport.

The next mathematical step is the intertwining equality of the actual
native chain (not just formal Fock inputs) with a source Fourier
operation and the dilated target lattice. Prove the low mean
elementary-divisor bound on that preimage, including retained rank and
all place gauges. Do not simply pre-dilate the final polynomial by
N^h; the global determinant price would repay the entire saving.
Do not count the full symmetric monomial space as the native
retained rank without a proved span/attachment.

No signed asymptotic estimate is asserted. No terminal theorem is
imported and no closure premise is added. The Lean declarations are
submitted to the existing hosted research audit; verification is pending.

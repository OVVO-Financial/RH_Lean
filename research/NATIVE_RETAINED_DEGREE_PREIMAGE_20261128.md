# The exact retained physical star preimage

Continues #1214 after 169a2ba and the literal reflection attachment.
The source is the existing physical star columns, not the ambient
space of all coefficient functions. This is an exact finite calculation
and proof text for the existing strict audit, not a terminal RH proof.

## Exact retained lattice and determinant

At a level N coprime to the admitted depths D_i, retain the actual
nonempty layers A_i, and all original star columns
X_j = D_(j+1) 1_(A_(j+1)) - D_0 1_(A_0).
Let g(i,k) be the demanded clearing exponent at physical slot k.
For the paired Fourier preimage it is ((2q+1)e(i,k)-q)_+,
computed from the grading actually used on that slot.

Write E_i=max_(k in A_i) g(i,k). On the original coefficients u_j
of the stars, simultaneous divisibility of every slot reading
is EXACTLY
    N^E_(j+1) divides u_j  (all leaves),
    N^E_0 divides sum_j u_j.
This follows because each depth factor is a unit at N and the
physical amplitude is constant in each layer. It is an equivalence,
not a sufficient overestimate obtained from the ambient dimension.

Choose a leaf p of minimum E_(p+1), possible on every nonempty
star. Replace its coefficient by the total sum, keeping every
other leaf coordinate. This is an integral unimodular change;
its inverse subtracts the other leaves from the total. Since
every leaf is a multiple of N^E_(p+1), the transformed constraint
on the total is precisely divisibility by N^max(E_0,E_(p+1)).
No other constraint changes. This constructs the entire preimage,
not only a sublattice of convenient vectors.

An explicit integral basis consists of the columns
    N^E_(j+1) (e_j-e_p), j != p,
    N^max(E_0,E_(p+1)) e_p.
Its exact determinant and index (for positive N) are
    N^[sum_(j>0) E_j + (E_0-min_(j>0) E_j)_+].
Thus the retained rank is unchanged. The same basis works for
both actual profiles D and E whenever both are units at the level.
The relative Gram determinant is unchanged because the common
basis determinant multiplies both squared covolumes by its square.
For a zero-star block (no leaves) there is no preimage cost; the
literal anchor can be handled separately.

## Consequence for the proposed degree attachment

The average degree of the full cyclic polynomial carrier is not
the price of a retained wheel column. In the literal layer-constant
attachment it is the maximum demanded degree across its physical
slots that matters. If every leaf contains a high target degree h,
then every E_j is at least ((2q+1)h-q)_+.
In this model the supposed mean-degree benefit is lost. Selecting
a low-degree source representative per layer can preserve rank,
but replicating its reading into the high-degree target does not
transport the finite lattice unless a separate local equivariance
law is proved. The exact preimage above excludes treating this
replication as a free change of grading.

This gives a sharp retained-lattice test for any proposed paired
lift. It uses the existing original physical columns and pays the
root (not a diagonal surrogate). It does not rule out Alpoge's
different source and target representations: the upstream
LiftLaw.integral_equivariant and LiftLaw.diagNInv_law change the
actual local evaluation kernel, not just the clearing weights of
a fixed physical amplitude.

Pinned upstream NamesAtSplitLevel.lean: the last-row/last-column
indicator exchange under rectangular level conjugation and
compUpTo_pairs_eq_smul are the required additional laws.
The present computation determines the exact cost if the physical
rows are left layer-constant. A genuine alternative must construct
a non-layer-constant lifted family, prove its common tested readout
and rank, and pay its finite and real index on the same rows.
Do not reuse this finite basis determinant as a signed height gain.

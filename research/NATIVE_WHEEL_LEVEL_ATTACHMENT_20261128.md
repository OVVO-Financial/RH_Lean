# Exact signed wheel attachment to the cyclic level carrier

Continues #1214 from the hosted-verified research head 169a2ba.
The source here is the actual original physical quotient interval and
the signed sector of NativeSignSchurHandoff. No new rank or signed
bound is assumed. Lean text is submitted, pending hosted verification.

## 1. Literal residue attachment

Use the existing original_addresses equivalence, not a new set of
monomial labels. Write k for each original quotient integer, and let
N be the existing level prime in the collar N > 2 floor(h_0). Then
k -> k mod N is injective, all k are positive, and the image is
disjoint from its negative (since 0 < k+l < N). Use this collar only
where it is proved for the original level parameters.

For the original physical column matrix X, let s_X be its zero
extension on these positive cyclic addresses. Define

    K_X(z)=s_X(z)-s_X(-z).

This is exactly ramifiedResidue(-1) on the original scalar entries,
or on the monomial-valued seed s_X(z) times a fixed monomial.
It is the image of 1-J, not a replacement of the wheel by an
unrelated cyclic representation. At the original address k the
readout is X(k); at -k it is -X(k), and outside the two images it
is zero. Thus rank is preserved. It is the primitive signed
sector of the integral four-channel observation map: on (c,-c),
the original map [A B; B A] sends to (Xc,-Xc).
The original common unsigned sector sends (c,c) to (Mc,Mc).
Do not count either of these as an extra independent arithmetic rank.

For every pair of columns i,j the exact mixed Gram entry is

    sum_z K_X(z,i) K_X(z,j) = 2 sum_k X(k,i) X(k,j).

Hence det(CoDiv K_X)=2^r det(CoDiv X), for r actual columns.
The factor 2^r cancels exactly between the original D,E profiles;
the signed logarithmic ratio and the #1205 normalization are
unchanged. This also holds for anchored columns and their original
common unsigned sector, using the already proved sign-Schur ratio.

## 2. What the economical preimage actually does here

At positive distinguished degree h, the submitted verified
pairedFourier_preimage multiplies the cleared coefficient by N^h
relative to the reflected original, because q-(2q+1)h <= 0.
Restriction then gives u^h times that coefficient. Thus for a
homogeneous monomial lift of the literal physical column, the
exact squared Fock norm of the final cleared reading is N^h
times the original squared Fock norm, not N^(-h). The equality
uses |sigma(u)|^2=N. In the Gram the same factor is common only
if the degrees are the same in both profiles. It cannot supply
an independent signed forward upper estimate.

At degree zero the reflected factor is N^q and no degree saving
is present. The exact attachment therefore resolves the cyclic
ramification and signed-rank bookkeeping but not the degree
change with a paid index. It must not be promoted to the
upstream paired-chain intertwining theorem.

There is an additional stringent test on the actual original
unanchored physical stars: NativeMeasuredSlotProjector.left_inverse
constructs an integral Y with Y X=1 using the pairwise coprime
depth powers and nonempty bands. Consequently if X C=d Z
for integral matrices, then C=d (Y Z). The bare physical
carrier cannot hide any common level divisibility via cancellation
between columns; a genuinely different target lattice and its
integral evaluation map must be constructed.

## 3. The precise next mathematical requirement

Build the actual degree-changing paired-chain lift on the
retained signed sections with the same physical readout and
common table, and prove the norm comparison on that lift.
The finite preimage must be computed from its own source
grading, not from an arbitrary homogeneous labelling of
the physical rows. Preserve the rank and both D/E signed
determinants through that operation. The inexpensive source
Fourier preimage alone does not transport a source degree
e to target degree h.

Do not introduce a conditional terminal interface. The original
full signed G_z estimate, complementary unserved term, and
complete cofinal real windows are all still open. No acceptance
criterion has been changed.

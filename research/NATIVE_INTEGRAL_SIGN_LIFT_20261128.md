# Primitive integral NNS sign lifts

Continue the true-zero Schur fit. Upstream tether: ComparisonForms,
HeckeValueHeight, LiftVolumeHeight and LongForms, pinned compact
Alpoge source 72fead102f663d5c7a407964a13dc0cf9d977207. No external
terminal theorem. NativeSignLift.lean submits the integral algebra.

For two endomorphisms A,B of the SAME free integral module, retain
the four channels on its doubled carrier:
    L(A,B)=[A B; B A].
Composition is exact even without commutativity:
    L(A,B)L(C,D)=L(AC+BD,AD+BC).
The sum and difference of those channels are the respective products
(A+B)(C+D) and (A-B)(C-D). Nonnegative A,B on the physical counting
coordinates give the parity-resolved nonnegative path weights.

Do NOT use the symmetric/antisymmetric eigenbasis over Z: its
determinant has absolute value 2^d on a d-dimensional carrier.
Instead the integral coordinates (s,v)=(x+y,x) have inverse
(x,y)=(v,s-v). In this basis
    L(A,B)=[A+B 0; B A-B].
This is integral at EVERY place, including 2. The kernel of the
sum map is primitive and carries A-B; the quotient carries A+B.
No repeated 2^d index is incurred to separate their actions and
determinants. The lower-left block must be retained for local
Smith analysis and metrics: e.g. A=3,B=1 has Smith factors 1,8
rather than the factors 2,4 of the split diagonal comparison.
The coordinate change is unimodular, NOT an isometry.

For m steps the two diagonal blocks of the triangular product are
(A_m+B_m)...(A_1+B_1) and (A_m-B_m)...(A_1-B_1).
The determinant factors exactly into their determinants. In the
actual cyclic Euler model, take A=(c+1)I, B=c U_n. On the original
regular cyclic slot space both are nonnegative, and they preserve
the actual integral primitive section. Thus the restriction
carries the native signed cyclotomic determinant and a positive-path
comparison on exactly the same primitive rank. The positive-path
comparison cannot simply be identified with Alpoge's flat reference.

Write r=c/(c+1), F_n(r)=det(I-r U_n) on the primitive section.
The unsigned normalized factor is F_n(-r), not 1. Multiplication
by -1 permutes primitive roots by the following exact involution:
    n odd -> 2n,
    n == 2 mod 4 -> n/2,
    4 divides n -> n.
Consequently F_n(-r)=F_{iota(n)}(r). The case n=2 involves n=1
and must remain explicit. With w_n=E(n/x) on 2<=n<=floor x and
zero elsewhere, the relative signed/unsigned log-volume is exactly
    sum_{odd n>=3} (w_n-w_{2n}) log(F_n(r)/F_{2n}(r))
       + w_2 log((1+r)/(1-r)).
The identity works also with rounded integral multiplicities, not
just real weights. It removes all n divisible by 4 from this
relative comparison and reuses the native dyadic history for the
remaining labels. It does NOT remove the unsigned normalization
from the original complete discrepancy. In particular, the exact
odd trace identity is
    log F_n(r)-log F_n(-r)
       = -2 sum_{j odd>=1} r^j c_n(j)/j.
For fixed j, the Dirichlet generating function of c_n(j) is
sigma_{1-s}(j)/zeta(s). At j=1 this is 1/zeta(s), which retains
the critical-zero signal. No estimate on the complete odd series
or cancellation of its Mellin poles follows from parity alone.

This is the primitive composition mechanism to investigate before
introducing new lift geometry. Use the true-zero augmented Gram on
the actual carrier and reconcile the retained anchor via Schur.
Apply both reciprocal heights to the SAME volume, and supply the
independent coefficient-height comparison; neither the determinant
factorization nor the nonnegative path reference constitutes it.

Exact integer regression in this session: 600 pairs of samples in
dimensions 1 through 6, 3,012 checks of inverse coordinates, channel
composition, signed/unsigned multiplication, triangular conjugation
and determinant factorization. Finite checks are not Lean verification.
The parity formula and its native application here are paper deductions.
The submitted Lean module has 9 roots registered in both audits.
The terminal acceptance gate is unchanged.

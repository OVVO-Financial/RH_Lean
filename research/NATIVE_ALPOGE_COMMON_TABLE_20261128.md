# Follow Alpöge's comparison-map arrow: common native tables and the normalization obstruction

Paper result, not a terminal RH proof. This continues the primitive fit
and Parseval work without requiring the stronger, invented negative-fiber
condition.

## 1. The exact upstream suppliers

Alpöge's remark pp. 3–4 (https://alpo.ge/remark.pdf, footnote 3 and timeline
items 8–18) distinguishes the finite-field path argument from the integer
proof. In the latter, multiplicity m ~ sqrt(x) comes from iterated theta
lifts, their norms, divisibility, and common comparison forms. Do not
identify a pointwise signed fiber inequality with the upstream result.
Zhang, https://arxiv.org/html/2611.30749v1, Lemmas 2.1–2.2 and Theorem 2.4,
uses a cohomological injection/concentration across extension degrees.

The compact Lean source at lsernau/grh-lean commit
72fead102f663d5c7a407964a13dc0cf9d977207 supplies the following
specific dependencies:
- New/Rows/ComparisonForms.lean:200–228, exists_comparison_forms:
  u_theta^* gl_theta = gamma_theta A, A surjective and independent of
  theta. The scalar norm ratio is the Hecke-value product ratio.
  The maps have integrality, testedness and untwisted real norm bounds.
- New/Rows/HeckeValueHeight.lean:154–238, heightLe_inv_ratio and
  heightLe_inv_heckeValueProd_div: the separate signed coefficient
  height bound is 6 B0 - dirCost per rank-one pair, aggregated over
  k directions with explicit ramified costs.
- New/Rows/LiftVolumeHeight.lean:24–38,103–127: the common table identity
  and the independent coefficient height are combined by the
  compressed Gram determinant identity. These are TWO suppliers,
  not a deduction of the coefficient inequality from the table map.
- New/Endgame/LongForms.lean:22–74: multiplication across m lifts,
  a forward certificate on the actual short rows, and the product
  formula yield d(mainHeight-3L)<=V+2 delta.
- New/Main.lean:121–167: the short-form bound and rank/index budget
  on those same rows give m remainder <= logB^2 budget.

The native analogue must keep the common table and its independently
bounded scalar on the same objects. This is more specific than looking
for an arbitrary sign condition on the quadratic path.

## 2. Common tables constructed on the actual fitted primitive module

Use the CRT difference basis from NATIVE_PRIMITIVE_EULER_FIT_20261128.md.
Write C_0 for the full rectangular integral matrix embedding its basis
in the fixed repeated physical coordinates. C_l is the place-dependent
cropped matrix from that note. In the nonanchor CRT coordinates of
each fibre there is exactly one basis column with entry 1 and all
other columns have entry 0. Pick one such physical copy for each
column, giving a fixed coordinate restriction J with
    J C_0 = I,   J J^T = I.
This is an integral isometric dual, not a Gram inverse.

Let B_0 represent (c+1)I-cU_n in the CRT basis on each block, and
B_l the one-column-repaired operator transported from the integral
cyclic basis to the CRT basis. Use block direct sums, with the original
site/translate accounting; the full primitive table is still an
enlarged space, not the original star rank. Put
    u_0=C_0 B_0, u_l=C_l B_l, G_i=u_i^T u_i.
The previous fitting proof makes G_l invertible over Z_l.

Define the fixed table map A=B_0^T, the untwisted comparison map
gl_0=J^T, and at each chosen finite place
    gl_l=u_l G_l^{-1} A.
These are actual rational matrices. Then exactly
    u_0^T gl_0=A=u_l^T gl_l.
A is surjective over Q since B_0 is nonsingular; do NOT assume it
is surjective over Z. gl_0 is integral and has real operator norm 1.
gl_l is integral over Z_l because u_l, A are integral there and
G_l is a unit matrix over Z_l. Moreover gl_l maps into range(u_l),
so its columns are orthogonal to the complementary space. This
does not assert any additional automorphic testedness of the source.
The same construction works blockwise on any actual fitted cycle.
The test maps have a common table and an independent size bound.

For any full-column-rank u and square table A=u^T gl, the compressed
Gram on range(u) of gl gl^T has determinant
    Delta = det(A)^2 / det(u^T u).
Proof: write its matrix in basis u as G^{-1} A A^T. This is the
native instance of det_compressedGramOp (with hook scalar 1).
Consequently, writing g_C=det(C_0^T C_0), for this construction
    Delta_0=1/g_C,
    v_l(Delta_l)=2 v_l(det B_0).
The latter is nonnegative, so the local projected determinant has
p-adic norm at most one. The exact arithmetic allowance is
    log Delta_0 + sum_l log|Delta_l|_l
       = -log g_C - 2 log|det B_0|
       = -log det G_0.
This uses the *actual* local contents of A, not an asserted unit
determinant. It works per block before applying signed multiplicities.
It recovers the volume by an independently bounded comparison map,
but it is an identity in the same determinant, not the independent
upper and lower arithmetic comparisons of star_inequality.

## 3. Where the missing scalar is forced

Set a=c+1. The normalized primitive rational is det(B_0)/a^t,
t=phi(n). A natural flat block a C_0 has precisely this common
normalizing scale. However it cannot be used in the preceding
unscaled common-table map with locally integral tests at primes l|a.

Indeed B_0 is invertible modulo l for l|a, since B_0=-c U_n mod l
and c and U_n are units. Thus A=B_0^T is invertible over Z_l.
For any integral local embedding C and integral local test g,
the identity
    (a C)^T g = gamma A
forces v_l(gamma)>=v_l(a): multiply by A^{-1} over Z_l.
If C has an integral left inverse J, equality is attainable with
gamma=a and g=J^T A. In particular no choice of the cropped metric
makes this scalar a unit while retaining both integral test maps
and the same table.

This is a precise restriction on the proposed scalar flat lift,
not on all conceivable flat lifts. It explains why the normalized
factor a^t cannot be dropped merely because the nonflat local
projectors are integral. In general, for a primitive integral
table A (at least one entry a local unit), integral u_l,gl_l with
u_l^T gl_l=gamma_l A force gamma_l integral. If gamma_0=1, then
the inverse scalars have nonnegative local log norms. A rational
common witness H cannot turn them into a negative signed height:
sum over a sufficiently large cutoff containing every prime
dividing H, and use log|H|+sum log|H|_l=0. This elementary argument
is for the rational model, not a claim about all algebraic height
witnesses in Alpöge.

Alpöge gets the missing scalar through the comparison of flat and
nonflat algebraic lift norms and the separate recovered coefficient
height (Separation.lean:83–98 and HeckeValueHeight.lean:154–216).
Do not assume our scalar=1 construction supplies that negative
directional cost. A different flat section or compatible
nonintegral scale with fully paid local costs is needed if using
this route.

## 4. The normalization itself carries the critical-zero signal

There is also an analytic reason not to discard this common scale.
Let E be the fixed calibrated residual. Consider the unrounded
dimension-weighted mass
    A_E(x)=sum_{2<=n<=x} phi(n) E(n/x).
For Re s>2, substitution y=n/x and the elementary totient divisor
identity phi(n)=sum_{d|n} mu(d) n/d give
    integral_1^infinity A_E(x) x^(-s-1) dx
        = Ehat(s) (zeta(s-1)/zeta(s)-1).
The equality is by absolute convergence there. The existing
residual note gives E(y)=O(y), so Ehat is analytic for Re s>-1,
and Ehat(rho)=1/(rho(1-rho)) at every nontrivial zero.
Also zeta(rho-1) is nonzero by the functional equation and the
Euler product in Re(2-rho)>1 (rho-1 is not a trivial zero).
The normalization mass has a pole of the same multiplicity at
every nontrivial zeta zero.

The possible main pole at s=2 has residue Ehat(2)/zeta(2).
Thus an eventual two-sided estimate
    A_E(x)-[Ehat(2)/zeta(2)] x^2 = O_epsilon(x^(1/2+epsilon))
for every epsilon>0 would itself imply RH: subtract the main
pole and use holomorphy of the Mellin integral in Re s>1/2,
then functional-equation symmetry. No such estimate is established
here. In particular PNT-level asymptotics do not justify stripping
the normalization at the desired error scale. This statement
concerns the unrounded mass; do not bound the two parts of the
rounded rational separately without controlling their cancellation.

Keep the exact normalized rational in
NativePrimitiveDeterminantCertificate.lean (certificate and
certificate_rounding). The rounded multiplicities must occur in
both the numerator and the denominator. The complete real-clock
trace/reference handoff from the intervening work is preserved.

## 5. Remaining operation dictated by the actual upstream arrow

Use the common-table construction as the algebraic base. The new
target is a different flat/nonflat pair with a scalar relation
whose independent norm and coefficient estimates earn the signed
directional cost, as in heightLe_inv_ratio. Produce both reciprocal
certificates on the SAME physical section, at the original
normalization, with the independently evaluated reference. Do not
manufacture a scalar from the target error or treat the present
common-table identity as that estimate. A direct arithmetic
alternative remains acceptable if it proves the original bound.
The full primitive space still requires a justified connection
to the original star family if using the star/covolume route.

The explicit common table, the scalar divisibility restriction and
the normalization Mellin identity are paper deductions. No new
Lean theorem or terminal bound is claimed. Acceptance is unchanged.

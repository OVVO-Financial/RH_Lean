# Positive real quadratic fit on the original depth lines

Continuation of NATIVE_DAG_CONGRUENCE_PHASE_ATTACK_20261128.md.
Direct attack on the actual two compact nodes, not another RH closure
interface. Upstream pinned lsernau/grh-lean 72fead102f663d5c7a407964a13dc0cf9d977207:
New/Rows/HeckeValueHeight.lean 87--216, New/Selmer/FitTwists.lean
(AuxPair.IsTestForm and DenominatorLe), New/Selmer/RankOneDenominator.lean,
New/Rows/ComparisonForms.lean 200--228, New/Endgame/LongForms.lean.

## 1. The actual all-embedding condition

IsTestForm requires membership in integralForms at EVERY embedding
above the selected finite prime, plus testedness. A Gaussian scalar
of local valuation +v at one embedding and -v at its conjugate cannot
be used as an integral test multiplier on a primitive test. The
upstream rank-one argument explicitly uses both ordinary and conjugate
pairings. A unit phase is not a positive real lift norm.

## 2. Positive integral twist with no complex-conjugate repayment

For integer depth N>=1 take the real roots

    t_+ = (2N+1+sqrt(4N+1))/2,
    t_- = (2N+1-sqrt(4N+1))/2.

Both are positive algebraic integers, t_++t_-=2N+1, t_+t_-=N^2.
Every complex field conjugate is one of these two positive real
roots, so ordinary complex conjugation fixes either root.
At every embedding into an algebraic closure of Q_l both roots
have norm <=1 by their monic equation or the ultrametric sum and
product constraints. If l divides N, their sum is a unit, and
exactly one root is a unit; the companion has valuation 2 v_l(N).
Otherwise both are units. This includes l=2. For N=1 one may use
the literal scalar 1. Choose the unit t_iota after the embedding.
Both choices are integral at ALL embeddings.

With z=1/(2 sqrt N), t_+/N=(sqrt(1+z^2)+z)^2 and
t_-/N=(t_+/N)^(-1). Hence |log(t_±/N)|=2 arsinh z<=2z=1/sqrt N,
since the derivative of arsinh is at most 1 on the nonnegative
axis. This independent real norm estimate holds at all conjugates.

## 3. Actual native rank-one test and common scalar

On an original retained layer of size m take w=(1,...,1).
In sparse Schur coordinates the star columns are diag(N_i) B,
B unimodular. These are actual independent physical directions.

Use u_0=N w, u_iota=t_iota w on the SAME original layer with
NO cropping. Their ranges coincide and Pi=ww^T/m is their
orthogonal projector. For integral test vectors X,Y,
    m <X,Pi Y> = (sum conj X_i)(sum Y_i).
At every embedding with both conjugate-side tests integral
the norm is <=1 by the ultrametric inequality. The class
multiplier is actual m, not a discarded normalization.

Take Xi=w, integral at ALL embeddings, in the range and
orthogonal to its entire complement. Then
    <Xi,u_iota>=m t_iota,
    <Xi,u_0>=m N,
    |<Xi,u_iota>|_l=|m|_l.
This is a non-overdivisible coefficient with the same global
multiplier and test. The measured real squared norm of Xi is m.
The normalized indicator w/m has energy 1/m but cannot be
assumed integral when m is a nonunit. The class multiplier m
handles that denominator without changing physical rows.

The common rank-one table A=m N and gamma_iota=t_iota/N
satisfy the comparison relation exactly. Both lift norms
are actually measured:
    ||u_iota||^2=m t_iota^2, ||u_0||^2=m N^2,
    rho_iota=||u_iota||^2/||u_0||^2=|gamma_iota|^2.
These are native analogues of the rank-one test, coefficient
read, class pairing and positive common-table scalar on the
diagonal carrier. This is NOT an identification with Alpoge's
rank-12 theta kernel or original general IsTestForm domain.
The orthogonality is for the specified physical layer model.

For several retained layers the determinant of the sparse
frame is product N_i times the unimodular incidence determinant.
The actual t_iota frame gives the product of the rank-one
scalars on the true exterior line. No rank multiplication.
The full rank-r table may have different scalars by direction;
do not claim a single full-rank scalar without pricing the
adjugate factors. The exterior scalar is exactly the determinant.
Retain the omitted root layer and all unserved prime factors.

## 4. Exact reciprocal height computation

For the positive real rank-one family rho, use the upstream
HeightLe definition with H=1, alpha=0. At each selected embedding,
    |rho_iota^(-1)|_l=|N|_l^2,
    |rho_iota|_l=|N|_l^(-2).
The finite allowances are their logarithms, with finite support.
Therefore
    HeightLe(-2 log N, rho^(-1)),
    HeightLe( 2 log N, rho).
Both are optimal by the product formula on their product 1.
The negative height now belongs to a genuine positive real
squared norm ratio with all-embedding integral class tests.
Its magnitude alone proves no signed prime cancellation.

Apply the construction separately to the actual depth profiles
D_i,E_i, counting each retained incidence exactly once. On the
exterior line write
    Q_iota=product_i ((t_iota(D_i)/D_i)/(t_iota(E_i)/E_i))^2,
    R=product_i D_i/E_i.
Then
    |Q_iota|_l=|R|_l^(-2), |Q_iota^(-1)|_l=|R|_l^2.
The exact optimal bounds are
    HeightLe(-2 log R, Q^(-1)),
    HeightLe( 2 log R, Q).
The complex-conjugate cancellation is bypassed, but the signed
height bill is not improved. Bounded real values of Q_iota
are NOT bounds on the common witness H in HeightLe. The
perturbation per profile is <= sum_{p<=x} p^(-1/2)<=2 sqrt x
for the complete prime set; depth zero uses 1. With original
incidences and 6/c normalization this is O(1). The exact
finite height conclusion does not need this estimate.

## 5. The independent short-form obstruction on this carrier

For a fixed sparse pivot use the same integral layer coordinates B.
Let L_D=diag(D_i) Z^r, L_E=diag(E_i) Z^r. Their intersection is
diag(lcm(D_i,E_i)) Z^r. The two exact indices are
    [L_D:L_D intersect L_E]=product_i max(1,E_i/D_i),
    [L_E:L_D intersect L_E]=product_i max(1,D_i/E_i).
Here D_i,E_i are powers of the same prime at each layer.
Their log sum is sum_i |beta_i-alpha_i| log p_i. These indices
are invariant under integral basis mixing. A full-rank family
in L_E integral in L_D pays at least the second index in L_E.
For an integral sublattice of L_D the actual covolume is the
covolume of L_D times its index. These volume/index identities
cannot establish an independent signed gain.

For near-full rank, at p with m_p copies of a uniform pole a,
dropping s dimensions can save at most s of those copies:
the image of the saturated retained lattice in
(Z/p^a)^m_p loses at most s generators in the quotient. Its
required length is >=a(m_p-s)_+. This is the paired-index
argument already in the project applied to one intersection,
not a statement about every upstream short-form realization.
One must count actual multiplicities before using rank loss;
one direction per distinct prime is insufficient to rule out
a rank-one omission.

On the complete calibrated population the two positive-part
log sums are each (c/6)(kappa x+o(x)), kappa>0, by the earlier
calibration and ordinary PNT. Paying the full-rank intersection
as an error is therefore linear after the original normalization.
This particular diagonal carrier cannot give the required
square-root bill by that route. This does not exclude another
common lattice with independently cancellable main heights.

The compact proof proves the forward bound through actual
projected Poincare rows, short_forms, enough_forms,
heightPerRow_le, and heightLe_volume_rows. None follows from
a rank-one identity even when the negative inverse height
and positive scalar are exact. The actual remaining obstacle
is an independent forward size-versus-divisibility estimate
on compatible rows, using the original split-factorial J.
The complete signed lower bound on R_full remains open.
Do not count the reciprocal height identity as a proof of
that bound or add a new closure interface.

## Verification

NativePositiveTwist.lean submits the quadratic roots, integral
equation, nonarchimedean unit selection, exact signed norm ratio,
indicator and class-averaged paired tests, and scalar/norm relation.
The full height calculation, sharp real perturbation, exterior
and intersection transfer are paper deductions.
scripts/research/check_native_positive_twist.js passed 10,549
exact checks, including the dyadic place: 154 algebraic identities,
231 local Hensel/valuation checks, 9,548 class tests, 77 individual
and 539 signed valuation checks. Finite checks are not a proof
of asymptotics or Lean elaboration. Hosted verification is needed.
No imported terminal theorem, changed normalization or weakened
acceptance gate. native_riemannHypothesis remains open.

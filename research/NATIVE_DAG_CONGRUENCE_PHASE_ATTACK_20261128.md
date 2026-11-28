# Direct DAG attack: actual paired depth graph, Selmer separator and Gaussian fit

2026-11-28. Continues #1214 on the original two split-factorial depth
profiles and sparse Schur anchor. No new conditional closure interface.
The terminal gate stays unchanged.

## 1. Trace the actual upstream dependency, not the size of the proof map

Dashboard: https://riemann.verifytask.cn/?lang=en . The public text
exposes the proof-map and upper-triangular import-matrix sections but
the interactive node data are dynamically loaded. The declaration
DAG below is traced directly from the pinned compact Lean sources,
lsernau/grh-lean at 72fead102f663d5c7a407964a13dc0cf9d977207:

* New/Rows/GluedFormTheta.lean: Data.depth_indicator_jet. One common
  nonzero auxiliary t, small at every complex conjugate, before the
  finite place is selected; at every place some coefficient has
  valuation no greater than forcedPart after the prescribed scaling.
* New/Rows/HeckeValueHeight.lean: exists_test_form_inner_kernelForm.
  It constructs an actual integral test, with three flat auxiliary
  factors and orthogonality to the unwanted forms, not just a reading.
* New/Selmer/FitTwistsExist.lean: exists_isFitFamily, consuming
  New/Selmer/DenominatorBound.lean: denominatorLe_rowBudget.
  The latter separates selected lift spaces using Galois/Hecke
  operators and a bound on congruence (Selmer) lengths.
* New/Selmer/RankOneDenominator.lean: DenominatorLe.rank_one_bound.
  The class multiplier times the pairing of two integral tested
  forms through the rank-one orthogonal projector is bounded.
  The proof actually averages over the integral class representatives.
* New/Rows/Separation.lean: heightLe_norm_trivialLift_sq. An independent
  size comparison with the flat integral algebraic part.
* New/Rows/HeckeValueHeight.lean: heightLe_inv_ratio. Combines the
  above in the orientation 6 B0 - dirCost. Both the ordinary and
  conjugate finite-place pairings are used.
* New/Rows/ComparisonForms.lean: exists_comparison_forms, with scalar
  common-table relation and a norm relation to Hecke values.
* New/Rows/LiftVolumeHeight.lean: heightLe_liftVolume_ratio.
* New/Endgame/LongForms.lean: heightLe_volume_ratio_sq AND
  heightLe_volume_rows on the same family; integral_forms_long.
* New/Endgame/ShortAndEnough.lean: independent short and enough
  forms and heightPerRow_le. New/Main.lean: star_inequality.

The critical node for the present NNS construction is not another
Gram identity. It is the genuine tested-space congruence bound and
its nontrivial norm comparison. The following attacks that node on
one concrete same-family replacement.

## 2. Use the actual paired profiles, not unrelated trial data

At a site let D_i=p_i^beta_i and E_i=p_i^alpha_i, with the same
nonempty original layer counts n_i. Use the common sparse anchor
j from NativeSparseAnchorHeight. Both projected star matrices on
the nonpivot layers have the SAME integral unimodular column
coordinate matrix B, preceded by diag(D_i), diag(E_i), respectively.
This follows by deleting row j of the incidence star (determinant
+/-1). The coupled observation graph is

    u -> (diag(D_i) B u, diag(E_i) B u).

Its rational range, and its saturated integral lattice on the
layer-constant coordinates, split into the actual two-copy layer
lines. Remove gcd(D_i,E_i) and swap the two coordinates when
necessary. The primitive vectors on retained layers are

    v_i=(1,u_i),  w_i=(-u_i,1),
    u_i=p_i^|beta_i-alpha_i|.

The count metric is n_i I_2, so these two lines are orthogonal for
the original counting metric too. No new arbitrary metric or
primitive multiplicity has been supplied. The following obstruction
is for this coupled graph, not all possible NNS representations.

## 3. Exact non-overdivisible coefficient witness (native jet analogue)

Before dividing by the gcd, form the primitive exterior coefficient
table indexed by binary choices, one coordinate from each retained
layer. Its nonzero minors, up to signs, are

    a_e = prod_i (D_i if e_i=0, E_i if e_i=1).

This is the actual Pluecker vector of the coupled layer-coordinate
map. Multiplication by the unimodular incidence B changes it only
by a sign. Define C=prod min(D_i,E_i), M=prod max(D_i,E_i).
Every coefficient is divisible by C and at least one is exactly C.
Consequently the maximum p-adic coefficient norm at each place is
EXACTLY |C|_p, with the same coefficient working at all places.
No local jet selection or common auxiliary denominator is needed.
This is a genuine elementary version of the no-overdivisibility
operation on the actual common-minimum depth profile. It is NOT
an identification of these degrees with all upstream nominal jets
or with Data.forcedPart.

In the counting-coordinate exterior metric, before the common
factor prod n_i, its squared real norm is

    sum_e a_e^2 = prod_i(D_i^2+E_i^2),
    M^2 <= sum_e a_e^2 <= 2^r M^2.

All quantities measured directly. Hence the upper norm relative
to the maximum profile is within r log(2)/2, and the coefficient
valuation is fixed by the minimum profile. This is a joint
coefficient/size computation on the SAME object, rather than an
upper bound on a norm defined from the desired deficit.

The mismatch between min and max must now be paid. It is exactly
the absolute, not signed, depth difference.

## 4. Direct Selmer-congruence computation

On one retained two-copy layer,
    det [v_i,w_i] = 1+u_i^2 = q_i.
The quotient of Z^2 by the lattice generated by these two vectors
is cyclic of order q_i: the first generator has a coordinate 1
and the matrix reduces by integer row and column operations to
diag(1,q_i). If T is any integral endomorphism with
    T v_i = a v_i, T w_i = b w_i
for integral eigenvalues a,b, its first row (A,B) satisfies
    A+u_i B=a, -u_i A+B=-u_i b.
Eliminating B gives
    a-b=(1+u_i^2)(A-b).
Thus every integral separator has eigenvalue difference divisible
by q_i. Conversely T=bI+k v_i v_i^T realizes a-b=k q_i. This is
the exact congruence ideal of the two lines, not an estimate of
the chosen separator's inefficiency.

The orthogonal line projector has a unit-numerator diagonal entry
1/q_i. For the full exterior line, write v_e=prod u_i^{e_i}.
Its primitive pivot v_0=1, and
    S=sum_e v_e^2=prod_i q_i.
The orthogonal projector entries v_e v_f/S have exact common
denominator S. In particular a common integral class multiplier h
and clearing M0 pay the exterior projector exactly when
    S | h M0.
This is the SAME-family determinant test. The lcm for separately
tested individual lines does not pay this exterior test unless it
also contains the missing multiplicities. This is a direct
calculation of a native congruence module, analogous to the issue
priced in denominatorLe_rowBudget and rank_one_bound; it is not
a claim that the upstream Selmer module is isomorphic to it.

The normalizing factors n_i cancel from the projection matrices
in the layer-constant basis. Counting all original physical rows
can only impose extra constraints; it cannot remove the necessary
restriction on these layer-constant test directions.

## 5. NNS signed deconstruction and arbitrary oblique reconciliation

The swap of v=(1,u) to v'=(u,1) gives exactly
    P_v-P_v'=(1-u^2)/(1+u^2) diag(1,-1).
Thus the mixed off-diagonal terms cancel, leaving a signed
probability reading. For odd u (all admitted primes odd),
gcd(u^2-1,u^2+1)=2 and q_i == 2 mod 8. The reduced denominator
of the signed reading is q_i/2. All its odd factors remain;
the primitive signed deconstruction does not turn them into units.

Allow ANY rational retraction of the exterior line, P=v w^T,
w^T v=1, including arbitrary mixed coordinates, not just a
diagonal retraction. Take h positive integral clearing all
coefficients. Since v_0=1, hP integral iff hw integral. The
cleared test z=hw satisfies z^T v=h, so z is a nonzero integer
vector and ||z||_2>=1. Therefore
    h^2 ||P||_op^2 = ||v||_2^2 ||z||_2^2 >= S.
The physical layer-constant exterior metric is a common scalar
on these coordinates, so the operator norm is unchanged.
The bound is sharp: choose w=e_0, h=1. This provides a fully
integral oblique retraction, but its archimedean norm is sqrt(S).
The orthogonal retraction instead has norm one and h=S.
Even arbitrary mixed rational retractions pay
    log h + log ||P||_op >= (1/2) log S.
Taking the exterior power of any retraction onto the original
coupled graph gives this line retraction; the inequality does
not assume that the original retraction preserves the layer split.
This is the quantitative test of a proposed oblique NNS shortcut.

Moreover
    0 <= (1/2) log S - sum_i |beta_i-alpha_i| log p_i
      <= (r/2) log 2.
Thus the exact combined cost is unsigned total variation. On the
complete admitted prime population, the actual calibrated residual
has both positive and negative linear mass kappa x+o(x), kappa>0,
as shown by ordinary PNT and the split-factorial calibration.
The uniform depth rounding error gives
    (6/c) sum_p |beta_p-alpha_p| log p
       = 2 kappa x + o(x).
This uses the already established paper calibration, not RH.
For the physical served sum the incidence is k |tops| per prime;
one omitted layer per site costs at most O(c log x) in a row,
hence O(x^(eps/8) log x) after original normalization. Unserved
mass remains explicit. The complete paired-graph clearing+norm
price, if treated as an error on the signed G_x normalization,
is therefore linear, not square-root. This does not exclude a
different representation or a large main amount independently
cancelled by the other half of Alpoge's comparison.

## 6. A genuine place-dependent Gaussian phase fit and the conjugate test

This is a direct constructive twist attack on the computed
congruence modulus. For each u, let s=u+i, t=u-i in Q(i).
For each odd prime ell dividing q=1+u^2, q factors as s*t;
s-t=2i is a unit. Exactly one factor is divisible, with valuation
v_ell(q), at each chosen embedding into Qbar_ell. The other is a
unit. Such odd primes are 1 mod 4. At ell=2 both valuations are
equal (for odd u), so the ratio is a unit. At other primes both
factors are units. For each embedding choose

    theta_iota = s/t or t/s,

in the orientation with norm <=1. Every complex conjugate of
every theta has modulus one, while

    log |theta_iota|_ell = -v_ell(q) log ell (odd ell),
    log |theta_iota|_2 = 0.

For products over retained layers the construction is simultaneous
and retains multiplicity. In the precise upstream HeightLe
definition, take H=1, alpha=0, finite allowance equal to these
actual logarithms. The resulting varying Gaussian phase family
has an independently proved NEGATIVE height bound

    HeightLe(-log(prod_i(q_i/2)), theta).

This is not a fixed rational ratio and not a circular height
assignment. At the chosen embedding the phase times the
orthogonal exterior projector clears its odd denominator and has
real operator norm one. The common 2^r pays the dyadic factor.

But this is only a ONE-SIDED scalar twist. Multiplying a projector
by a phase is not an idempotent projection onto the same line.
Moreover conjugation inverts theta. In the same embedding the
conjugate phase has exactly the opposite valuation. The two
scalar-cleared tests cannot both be credited as integral on
the same original projected pairing: the unchosen phase can
increase the original odd pole from k to 2k. In Hermitian
products theta*conj(theta)=1. In particular a phase alone
does not change the positive real volume ratio. One must not
claim heightLe_inv_ratio for the actual lift norm from this
negative height of a unit phase.

This locates the precise missing transfer: retain the four
phase-sensitive mixed sectors until the common-table scalar
and the actual positive volume have been linked. Find a
tested-space separation and a forward height bound for the
same coupled phase-sensitive family, as in the two reciprocal
heights of LongForms. Use the genuine upstream construction
of the competing form spaces (Selmer/Hecke separation), not
the full orthogonal complement of the paired depth graph as
an arbitrary substitute. The elementary Gaussian fit is worth
testing on those actual mixed spaces, but it does not supply
their construction or the forward signed gain.

## 7. Status and reproducibility

NativeDepthCongruence.lean submits eleven proof roots for the
exact congruence gap, primitive coefficients, joint denominator,
mixed retraction price and signed swap. Two audits register them.
The native graph construction, asymptotic price, Gaussian phase
height and conjugate obstruction above are paper deductions.

scripts/research/check_native_depth_congruence.js: 27,840 exact
checks (14,400 eigenvalue-gap equations, 5,760 swap checks,
3,840 coefficient identities, 1,280 projector tests, 2,560
retraction checks). scripts/research/check_native_gaussian_phase.js:
789 odd-prime phase cases, 5,536 exact checks. These finite tests
are not an asymptotic proof or kernel verification. The earlier
hosted Schur errors were addressed by a targeted source repair;
subsequent hosted verification is required.

The complete arithmetic supplier and native_riemannHypothesis
remain open. No external terminal theorem, new closure premise,
altered original normalization or weakened review gate.

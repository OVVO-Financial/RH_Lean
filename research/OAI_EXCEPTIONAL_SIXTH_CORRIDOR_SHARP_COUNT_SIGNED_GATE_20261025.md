# Original low-Gaussian bottleneck: signed exceptional sixth-power Gram
2026-10-25. Pinned source: openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a.
STATUS: Sharpness of the absolute count is proved here. The signed bound and global improvement are NOT proved.

## Exact bottleneck and existing Lean locations

The original chain is:
Detector/GramClassification.lean -> GramFrequencySummation.lean ->
GramFrequencyMass.lean -> GramIdealMass.lean ->
GramSourceEstimate.lean -> GramInfiniteEstimate.lean ->
GramBound.lean -> LowGramApplied.lean -> LowCentralTuple.lean.

With P=Y^2/Q and original fixed calibration norm g,
the actual original Gram bound is
  E_low <= C(Q/Y)*(1 + P^(1/6) + P^2/Y)*Y^epsilon.

Physical X=Z^(17/48), Y=Z^(23/48), Q=g*X*Y:
sqrt energy exponents are zero/diagonal=17/96,
exceptional=3/16, other nonexceptional=1/16.
The active excess is 3/16-17/96=1/96.

The exceptional term is formed by the absolute weighted count of ideal
frequencies k whose valuations outside G=jointFixedModulus(S)*C
are all 0 mod 6, followed by the triangle inequality in k.
GramIdealMass.lean::normalized_double_sum_bound then takes another
triangle inequality over C,D and drops sourceMobiusWeight=mu(D).

## Proof the absolute count exponent 1/6 is SHARP

Use O=Z[omega], omega^2+omega+1=0, N(a+b*omega)=a^2-a*b+b^2.
For integer M>=1 put
  V_M={a+b*omega:1<=b<=M, 2b<=a<=3b}.
Then |V_M|=M(M+3)/2 and N(v)<=7*M^2.

v->v^6 is injective on V_M: if v^6=w^6, w/v is a sixth
root of unity, a rotation through a multiple of 60 degrees.
The wedge 2b<=a<=3b lies strictly within an angular sector of
width less than 30 degrees, so no nontrivial such rotation maps
one point of the wedge to another.

Every k=v^6 is nonzero and exceptional for EVERY fixed G because
valuation((v^6),p)=6*valuation((v),p).
Choose H=(7*M^2)^6. All the resulting frequencies have N(k)<=H,
so the exact NONNEGATIVE frequency counting weight satisfies

  sum_{k exceptional} (1+N(k)/H)^(-2)
      >= |V_M|/4
      >= H^(1/6)/56.

H is unbounded with M, so no O_G(H^(1/6-xi)) with any xi>0
is possible for the ABSOLUTE exceptional weighted frequency count.
This does NOT lower-bound the signed Gram source: the original
amplitudes and Moebius coefficients may cancel.
Numerical validation: scripts/oai_exceptional_sixth_corridor_sharpness.py.

Original Detector/SixthFrequency.lean already proves bare physical
Fourier invariance under v^6. Detector/CalibrationFourier.lean proves
the calibrated character is sixth-order. A new Lean adapter checks
that the ACTUAL calibrated coefficient is also invariant under
coprime sixth-frequency multiplication, and simultaneously that
every sixth power is in the original ExceptionalFrequency set:
research/oai_434/VF919OriginalExceptionalSixthCorridor.lean.
This rules out pretending there is independent sextic phase
cancellation on the coherent sixth-power family.

## Exact signed exceptional source theorem needed

Use the actual Lean definition from Detector/GramTruncation.lean:

 X_exc := sourceCanonicalSum S hS sigma F
    (exceptionalFrequencies S hS E) W hW Y Q hY U v.

Expanding definitions gives, with P=Y^2/Q:

 X_exc = (Q/Y^3)* sum_C sum_D mu(D) sum_{k exceptional for C}
   canonicalLatticeBlock(S,sigma,C,k,primaryGenerator(D),W,U,v,
     N(k)/(P/N(C)), Y/(N(C)*N(D))).

All masks and D in sourceDivisorUnion are the original ones.
The hard, as-yet-UNPROVED analytic theorem is to improve its
CURRENT absolute majorant (Q/Y)*P^(1/6+o(1))
to an actual signed estimate

  |X_exc| <= C * (Q/Y) * (fixedModulus)^epsilon *
             P^(1/6-xi),

uniform in actual admissible coefficients, Schwartz seminorms,
Mellin v, ray sigma, Gaussian dyadics and selected-slot compensation,
for SOME xi>0.

The existing full-source Mobius divisor sum is a coprimality sieve:
sum_{D|gcd(m,n)} mu(D)=1_{gcd(m,n)=1}, NOT identically zero.
Thus the signed power saving does not follow from formal Mobius
regrouping or the calibrated zero-frequency theorem.

## Why the L compensation does NOT reintroduce the P loss

For selected-slot product norm L:
 X_L=Z^(17/48)/L, Y_L=Z^(23/48)/L,
 Q_L=g*X_L*Y_L.
The exact identity is
 P_L=Y_L^2/Q_L=Z^(1/8)/g (INDEPENDENT of L)
and Q_L/Y_L=g*Z^(17/48)/L.

Assuming a signed improvement P^(1/6-xi) with 0<xi<1/6,
the improved conditional low Gram factor is
  sqrt(E_low) << sqrt(g/L)*Z^(3/16-xi/16+o(1)),
with existing diagonal 17/96 and other term 1/16 smaller,
uniformly for the original L<=Z^(1/6+o(1)).
It has precisely the L^(-1/2) structure consumed by
LowCentralTuple.lean::low_central_compensated_tuple.

The maximum amplitude improvement possible by KILLING the entire
exceptional term while retaining the existing diagonal bound is
3/16-17/96=1/96. The corresponding squared-energy reserve
is 1/48, not the earlier claimed 71/384.

Getting the signed xi>0 first is the missing NEW arithmetic.
Only after replacing the actual full compensated low operator
theorem, not merely the abstract scalar source, can the
global high, sextic moment and multiplicity terms be rebalanced.
No beta<7/8, no full Global Theorem A and no RH are proved here.

## Higher-leverage route: move the CRT argument BEFORE low Cauchy

This is a key logical distinction in the actual pinned proof.
Detector/LowSeparated.lean defines
  lowSeparatedIntegrand =
    mellin(W0) *
      sum_m lowNumeratorWeight(m) *
        sum_sigma lowRayAmplitude(sigma,m) * B(sigma,m).

The true B(sigma,m) is the MARKED COMPLETED DETECTOR ROW, built from
correctedCompletedT(...,physicalRayRowMonoid(...),gaussianCompletedProfile Z)
as shown in Detector/LowSeparated.lean and PhysicalReopen.lean.
The good column character chi_I(m)*chi_J(m)^3 from #1022
appears **ONLY WHEN B IS REOPENED**. It does NOT appear in
the isolated lowRayAmplitude or the squared low-only Gram.

Detector/LowCauchy.lean::lowSeparatedIntegrand_cauchy replaces the
signed bilinear product with sqrt(lowGaussEnergy)*sqrt(sum|B|^2).
This removes chi_I(m)chi_J(m)^3 from the low factor. As a result,
the fixed (s,I,J) primitive-column CRT saving DOES NOT IMPLY the
proposed low-only energy gain. Elementary orthogonality makes the
logical distinction exact: <A,B>=0 need not make ||A||^2 small.

Hence two distinct possible routes:
(A) Prove a genuinely NEW signed exceptional frequency/Gram saving
after Cauchy, necessarily across C,D or residual character seeds;
OR
(B) Bypass LowCauchy for the ACTUAL detector B, reopen
PhysicalReopen BEFORE the Cauchy inequality, and bound the fully
weighted four-channel sum over s,I,J,m, preserving its
chi_s^-1 * chi_I * chi_J^3 * rho_C character, as well as Gaussian
profiles, selected slots and compensation terms.

Route (B) is the only direct avenue for harvesting #1022's local
Z^(-71/768) primitive-column gain without an independent positive
Gram theorem. Its acceptance test is to improve the very SAME
complete LHS of original
Detector/LowCentralTuple.lean::low_central_compensated_tuple
from Z^(3/16+254 epsilon) to Z^(3/16-delta+C epsilon)
with all real sources/cutoffs and uniform analytic constants.
This is NOT proved by the existing source-local bound, since
summing all original s,I,J coefficients and compensations may
consume more than the available CRT gain.

No general claim "primitive-column CRT implies global low Gram gain"
is valid; the complete low Gram has no I,J primitive-column
oscillation to exploit.

## Candidate signed mechanism: nonprincipal periodic fixed-ray low-column coefficients

Pinned Detector/LowGramArithmetic.lean::lowArithmeticCoefficient_periodic
and Detector/LowGramFixedCoefficient.lean::gramCoefficientExtension_periodic
express the admissible column coefficient, up to one fixed scalar, as

  alpha(n) = rho_g(n)^(-1) * idealRowHom(g,(n)),

a multiplicative PERIODIC function of the primary element n. The
physical ray modulo 4 is projected separately.

For MINIMAL S=fixedBadPrimes={(lambda),(2)}, the conductor ideal
(g)=(2*lambda), lambda=1-omega, and any generator is a unit associate
of g0=2*(1-omega). Take primary split-prime elements
  n7=-2-3*omega,   N(n7)=7,
  n139=10-3*omega, N(n139)=139.
Both are 1 modulo lambda^2 and have SAME ray (2,1) mod4.
Their difference 12=g0*(4+2*omega), so EVERY calibration character
modulo (g) takes the SAME value on these two elements.

Exact sixth-root residue calculations in F7 and F139 give, for
the six associates of g0, exponents modulo 6:
  g0                   (0,1)
  -g0                  (3,4)
  omega*g0             (2,5)
  -omega*g0            (5,2)
  (1+omega)*g0         (1,0)
  -(1+omega)*g0        (4,3)
where pairs mean (chi_n7(g),chi_n139(g)). They are ALWAYS distinct.
The low-column periodic multiplicative function is thus
nonconstant on this primary ray subgroup for minimal calibration,
irrespective of the generator's unit normalization or the chosen
local calibration characters.

Exact modular-arithmetic test:
  scripts/oai_low_fixed_ray_nonprincipal_witness.py.
No assertion of warning-fatal Lean certification of these specific
F7/F139 residue evaluations is made here.

WHY IT MATTERS: A nonprincipal multiplicative finite-group character
has zero average on a coset of any subgroup where it is nontrivial.
With fixed conductor, smooth Poisson supplies arbitrary power
decay of the corresponding SEPARABLE weighted lattice sum.

BUT the ACTUAL exceptional Gram is NOT automatically separable:
it includes both columns, IsCoprime(I,J), variable sixth-free seeds,
physical radial kernel and original jointFixed/actualCommon factors.
Finite Fourier expansion of the two-column source may create
principal sectors even when alpha by itself is nonprincipal.

The exact remaining finite test is the two-coordinate mean of
the ORIGINAL jointExtension for EVERY sixth-free seed R|G^5.
If it vanishes in the low-C sector, Poisson can save power there;
the large-C tail is already absolutely damped by C^(-7/6).
This is a candidate new xi>0, not a proven global bound.

## An explicit principal-seed collision: fifth power of the CALIBRATION generator

The original primary numerator factorization theorem
ChineseRemainder/FrequencyLifts.lean::idealRowHom_factor_numerator
identifies the bad-prime numerator twist for the supported seed
z=g^5 with idealRowHom(g^5,(n)) on primary n. For any supported n
coprime to g, the exact sixth-mask identity yields
  idealRowHom(g,(n))*idealRowHom(g^5,(n))
    = idealRowHom(g^6,(n)) = 1.
As original LowGramArithmetic.lean::gramPeriodicMonoid_primary shows,
the low-column coefficient is (rho_g(n))^(-1)*idealRowHom(g,(n)).
Therefore the fifth-power exceptional seed has
  [low column coefficient]*[numerator bad twist]
    = rho_g(n)^(-1).

The new Lean theorem
research/oai_434/VF919OriginalExceptionalSixthCorridor.lean::
original_low_column_fifth_seed_restores_calibration
proves this final identity as a conditional exact algebraic statement.
The separate source factorization and equivalence to the actual k=g^5
frequency should be imported from the original numerator factorization
theorem, with the true unit/ramified/inert decomposition of g.
Until that adapter is kernel checked this note does not claim the
entire jointExtension at that seed is a constant scalar.

For MINIMAL calibration g=2*lambda, primary n have n≡1 mod lambda^2,
and a fixed physical ray n mod4 fixes n mod2. Consequently rho_g(n)
is constant on that particular primary-ray class. This means the
finite nonprincipality of the low column cannot kill ALL bad-prime
exceptional seeds. At some seeds the numerator twist restores the
principal calibration-ray sector.

This moves the real arithmetic gate from 'prove alpha nonprincipal'
to 'subtract/classify the restoring bad-prime seed and prove its
SIGNED contribution is controlled by the original common divisor
and sourceMobiusWeight cancellation, without taking absolute values.'
One cannot assign an unconditional P^(-xi) gain to the entire
exceptional class before that restoring contribution has been paid.

The arithmetic cancellation and frequency phase-invariance results
do NOT imply that the fully weighted exceptional source is
nonzero; other source labels and original compensation may cancel.
No global theorem A or beta<7/8 follows.

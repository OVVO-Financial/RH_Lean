# Can NNS LPM/UPM sharpen OpenAI's asymmetric 7/8 moment bounds?

**October 9, 2026. Classification:** source-grounded, concrete
research target; new finite NNS partial-moment lemmas are
independent Mathlib/RH_Lean algebra, NOT a proved improvement
of OpenAI's zero-free region.

## 1. The THREE asymmetries are distinct

1. **Geometric asymmetric scale**:
   the OAI second stage fixes X=Z^(17/48), Y=Z^(23/48),
   b=1/8, h=13/16, total selected-prime length ell=1/6.
   Its bound theta=1-h/6+b/12=7/8 follows from
   optimizing *both* direct/reflected energy and
   nonprincipal spectral row power. b is not a
   random variable to which LPM/UPM can be applied.
2. **Actual prime-amplitude asymmetry**:
   OAI's formal
   HeckePrimeAmplitudeBins.amplitude and
   DetectorAmplitudeFirst.rowMean define a REAL
   clipped logarithmic prime-slot amplitude g,
   with 0<=g<=delta/2, and weighted mean q.
   The normalized ratio x=q/delta lies in [0,1/2].
   The selected large spikes and row count R(q)
   are jointly optimized by a balanced cutoff t.
   This is a valid population for directional
   LPM/UPM around a *fixed* threshold.
3. **Signed complex row and VF historical asymmetry**:
   the OAI marked-minus-rescaled local correction
   cancels a SCALAR Euler contribution in
   Eq 5.13b, leaving an oscillatory sextic
   character term. On the VF side the four
   original physical NNS sectors (CUPM, CLPM,
   DUPM, DLPM) track real signed covariance
   and prime-owner returns. A genuine coupling
   requires exact physical row labels and
   zero extensions, and preservation of EVERY
   historical once-paid prime owner.

## 2. The exact near-saturation worst case

OAI's proof obtains, at row height h=13/16,
the signed high exponent

  E(h)= -1/48 +(2/3)*delta +q/6 - h*(1-R).

For 0<=delta<=5/6 and
y=1/2-q/delta in [0,1/2], its balanced
row-count choice R=R_*(delta,y) gives
from the paper's own endpoint-certificate
calculation

  D(y)=(37+34*y)/18
  P(y)=(7+18*y+8*y^2)/9
  J(y,delta)=(5/6-delta)*D(y)+delta*P(y)

  -E_*(delta,y)
    = [1+(3+8*y)*delta]/48
      - (13/32)*(5/6-delta)*delta*P(y)/J(y,delta).

Paper theorem: -E_* >= 49/440640 (~0.0001112)
throughout that entire rectangle. The bound
is RIGOROUS in OAI, and is a conservative
certificate rather than the exact minimum.

An independent numerical minimization of THIS
EXPLICIT SAME FUNCTION shows its tight corner
is near **SATURATION**, y~0
(q/delta~1/2), delta~0.386638,
with margin ~0.0002281473.
Numerical table from minimizing over delta
for several fixed y (NOT Lean-certified):

  x=q/delta   y=1/2-x   min_delta   min(-E_*)
  0.500       0.000     0.386638    0.000228147
  0.490       0.010     0.382666    0.000315650
  0.475       0.025     0.376835    0.000448321
  0.450       0.050     0.367440    0.000672537
  0.400       0.100     0.349767    0.001128638
  0.300       0.200     0.318288    0.002048444

This is a VERY SPECIFIC LPM/UPM target. It
would help if actual arithmetic could PROVE
that rows with nearly saturated q/delta
are more sparse than OAI's present worst-bin
count. Their limiting paper moment bounds
already account for prime spikes, so this
extra sparsity cannot simply be assumed.

## 3. The exact NNS concentration interface

Fix an actual finite row family S in one
OAI detector zero bin; let m(u)>=0 be its
physical multiplicity and x(u)=q(u)/delta.

For any fixed eta>0 define the
nonnegative saturation deficit

  y(u)=1/2-x(u)

and the LOWER degree-2 partial moment

  LPM_2(y;eta)=sum_(u in S) m(u)*(eta-y(u))_+^2.

Every row in the extreme saturation
strip y(u)<=eta/2 contributes at least
(eta/2)^2*m(u). Thus the exact inequality

  (eta/2)^2 * sum_{u:y(u)<=eta/2}m(u)
    <= LPM_2(y;eta).

The equivalent upper-partial-moment
statement for the ORIGINAL amplitude q is

  gamma^2 * sum_{u:q(u)>=t+gamma}m(u)
    <= UPM_2(q;t).

This is the correct one-sided inequality
to seek. The native RHLean.Mathlib-only
theorems are

  vf919RowUPM2_controls_upperTail
  vf919RowLPM2_controls_lowerTail
  vf919OAI_saturationTail_le_deficitLPM2

in VF_MID_919_OAI_PARTIAL_MOMENT_TAILS.lean.
They have NO analytic gain hypothesis.
They simply isolate exactly what estimate
would be needed.

If one independently proved, in the
ACTUAL Hecke row family with its existing
moment hypotheses and fixed eta,

  LPM_2(y;eta) << U^(R_old - nu + epsilon)
  
where U is the row-size parameter and
nu>0 is UNIFORM in the moving family,
then the saturated-row population
would inherit the same exponent saving
(up to fixed eta powers). In the high
energy ledger a genuine improvement of
the worst row-count exponent by nu
reduces E(h) by h*nu=(13/16)*nu.

This is a strictly stronger input
than an algebraic UPM/LPM decomposition:
it is a NEW sharp signed large-sieve/
owner-occurrence-moment estimate.

## 4. Also possible: directional improvements on the LOW side

A separate goal would be an improvement
in the normalized DIRECT physical probe:

  |J_II(Z)| << Z^(3/16 - lambda + epsilon)

for a fixed lambda>0, rather than the
published 3/16+epsilon.

At a proposed stronger boundary
theta'=7/8-xi and C(s)=s-11/16,
the low target becomes

  C(theta') = 3/16 - xi.

Hence an actual saving lambda>xi
would allow the NEW low-side bound
(with a small slack), PROVIDED all
corresponding high-side bounds,
contour continuations and moment
hypotheses are also established.

A possible source is positive correlation
between the physically MARKED and
RESCALED terms before Cauchy:
  |M-R|^2 = |M|^2+|R|^2 -2 Re(M*conj(R)).
Split Re(M*conj(R)) into NNS CLPM,
CUPM, DLPM, DUPM on both fixed real
and imaginary coordinates. If
same-sign quadrant products dominate
opposite-sign products in the actual
row distribution, their cross term
would strictly lower the square norm
compared with discarding it.

BUT OAI already has an EXACT local
scalar cancellation. NNS will add
nothing unless a **further** uniformly
quantified phase/cross-correlative
saving survives all normalizations,
character sum identities, zero masks,
and principal-row nonvanishing.

## 5. Two guardrails

**A. A diagonal norm cannot cancel itself.**
For any real amplitude g and target t,
  UPM_2(g;t)+LPM_2(g;t)=(g-t)^2
pointwise. Native theorem:
vf919RowUPM2_add_LPM2_eq_deviationSquare.
Thus renaming a Cauchy positive
second moment as two partial moments
DOES NOT improve the OAI proof.

**B. Target choice cannot erase the degree-one
historical energy.**
Native already-proved
finiteTargetScaledSchur_target_invariant
shows that the scaled Schur covariance
is independent of the arbitrary NNS
target; the rank-one first moment shifts
to compensate. A favorable NNS target
can IDENTIFY asymmetry but cannot
reduce genuine variance or safely
discard degree-one signed owner
mass. In particular, pointwise
same-sign bias of 293/316 owner
columns in #919 is not an
independently spendable negative
"credit" in a Hecke row count.

Further, the OAI character phases are
COMPLEX, so a signed partial-moment
argument must use both fixed Re and Im
coordinates or an exact Hermitian
quadratic form. Choosing a different
phase separately for each row would
change its fixed-coefficient class,
potentially violating the OAI
large-sieve hypotheses.

## 6. Research priority

Best FIRST experiment:
apply a fixed-threshold LPM_2 to the
near-saturated OAI prime-amplitude
rows in the actual retained
character family, THEN show how
the *genuine signed VF historical*
owner/Co-Div cross terms create a
uniform exponent saving in that
one-sided mass. Without an explicit
Hecke-row/physical-owner map, one
can state this as a precise
conditional theorem but cannot
declare it proved.

Other useful experiment: apply the
full NNS four-quadrant covariance
to the MARKED minus RESCALED
complex-row residual *before* the
final row-wise absolute-value/
Cauchy–Schwarz estimate. Measure
whether any directional saving
persists at the worst bin after
the source-to-boundary occurrence
map. This could improve the
LOW-side bound, which is just as
necessary as a HIGH-side improvement.


## 7. Actual original-weight NNS partial moments on the 316 native owners

A new CI regression now computes NNS zero-target
LPM/UPM of the signed analytic owner-column
residuals already obtained from genuine p<q
prime products at A=2634,B=5267. This is an
actual physical arithmetic census, NOT
fictional independent sample rows:

\[
e_p=\sum_{\substack{q>p,\ q\mathrm{\ prime}\\pq<B^2}}
w_{\lfloor\sqrt{pq}\rfloor}
-\sum_{q=p+1}^{\lfloor(B^2-1)/p\rfloor}
w_{\lfloor\sqrt{pq}\rfloor}
  \big(\operatorname{Li}_2(q)-\operatorname{Li}_2(q-1)\big).
\]

All 316 error columns use their ORIGINAL
root-of-product VF weights. The zero-target
partial moments are:

| Moment | Upper partial | Lower partial | LPM/UPM |
|---|---:|---:|---:|
| Degree 1 | 2.245021603 | 138.538713855 | 61.709x |
| Degree 2 | 0.356130001 | 86.937765732 | 244.118x |

They satisfy exactly

\[
\sum_p e_p=\mathrm{UPM}_1-\mathrm{LPM}_1
=-136.293692253
\]

and

\[
\sum_p e_p^2=\mathrm{UPM}_2+\mathrm{LPM}_2
\approx87.293895733.
\]

Thus the four-sector/directional construction
is NOT merely aesthetically asymmetric:
there is a real 61.7x first-order and
244x second-order lower-tail dominance in
this original native numerical packet.

This is STILL NOT evidence that the hard
OPENAI Hecke rows have the same partial
moments, or that the lower tail is always
restoring. For a LOWER-wall first-bad escape,
negative owner errors could in fact be
OUTWARD and DANGEROUS. Which partial tail
is favorable must be fixed relative to the
first-bad wall's sign and the genuine OAI
marked-minus-rescaled phase.

The only legitimate way to spend this
asymmetry is to establish a sign-correct,
uniform-in-scale, occurrence-preserving
transfer into the OAI retained row count
or normalized probe norm, including the
mixed original Sector Six Gram and its
unique historical owner charges.

This is a better *diagnostic* than simply
comparing an uncentered positive
semiprime mass to Li, but it is not yet
the missing arithmetic power saving.

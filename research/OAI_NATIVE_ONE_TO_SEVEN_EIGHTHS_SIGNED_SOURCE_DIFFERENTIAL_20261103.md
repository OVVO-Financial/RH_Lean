# The original OAI 1 -> 7/8 mechanism in RH_Lean/NNS coordinates

Status: **source-path audit and exact finite signed source equality**, not a
new analytic gain, new zeta-zero theorem, or an RH proof.
Original pinned source: openai/math @
1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Native repository: OVVO-Financial/RH_Lean.

## 1. The actual original exponent difference (no hypothetical owner)

The principal Hecke signal has power Z^(beta-11/16). The complete
compensated original LOW estimate has power Z^(3/16+epsilon).

  (beta-11/16) - 3/16 = beta - 7/8.

At beta=1 the separation is exactly 1/8. At beta=7/8 the separation
is zero. This is the *original* boundary crossing and why the proof
goes from exponent one to seven eighths.

The OAI HIGH estimate has a separate positive sigma reserve. Consequently
a strengthening of the marked-HIGH supplier alone cannot move the final
bound: LOW remains binding at the boundary.

With #1079 actual slots, LOW becomes 3/16-9*tilt, the principal shift
becomes -11/16-8*tilt, so the actual gap is beta-7/8+tilt. This
explains the proved *one-off* positive source-geometric gap. The sum
of physical slot lengths is exactly 1/6; the same slot gate yields
tilt <= (1/6)/24 = 1/144. Reusing this geometric certificate is not
a proof of a renewable contraction to 1/2.

## 2. Exact SOURCE chain leading to LOW 3/16

Read these original declarations in dependency order:

1. Detector/LowSelectedBound.lean,
   low_selected_physical_energy:
   * The actual selected Hecke inverse row, with the exact admitted prime
     lists, row masks, character, Fourier phase, actual reflected ideal,
     is bounded in squared energy by
       C (1+|t|)^J Z^(5/6-2*d+507*epsilon).
   * The scalar 5/6-2*d is the physical row-mass exponent, not a
     free signed covariance theorem.

2. Detector/LowNominalEnergy.lean,
   low_selected_nominal_energy:
   * Specializes that SAME actual row to the low physical source, not an
     arbitrary replacement row.

3. Detector/LowPhysicalInverseBound.lean,
   low_physical_inverse_normalized:
   * Divides the square root of the original row energy by sqrt(Q),
     where Q is the true physical scale.
   * The 5/6-2*d baseline is exhausted by the normalization; the result
     is C (1+|t|)^J Z^(507*epsilon/2).
   * Therefore the established inverse-row estimate contributes
     **zero fixed additional power** to LOW.

4. Detector/LowSlotPolynomial.lean,
   compensation_tuple_low_polynomial:
   * Exact original signed Fubini to the physical unselected tuples.
     The atom indexed by a is
       U_a = lowUnselectedWeight(a)
             * (sqrt(Q_a))^(-1)/(2*pi)
             * integral(lowSeparatedIntegrand(original inverse row)).
   * It retains the actual Hecke sign, selected prime-pool masks,
     selected Fourier phase, original W0/W1 compensation, and the
     original Mellin normalizer.

5. Detector/LowTupleGram.lean,
   compensation_tuple_actual_gram, lines 71-75:
   * Rewrites by compensation_tuple_low_polynomial, then applies
     norm_sum_le to the unselected tuple sum.
   * This is the **first explicit irreversible loss of the
     cross-unselected-tuple Hermitian interaction** in this chain.
   * Before this step the original source satisfies
       |sum_a U_a|^2
        = sum_a |U_a|^2
          + sum_a sum_(b != a) Re(U_a conjugate(U_b)).
     The original upper bound discards the second term.

6. Detector/LowCentralTuple.lean,
   low_central_compensated_tuple:
   * Combines lowGramFactor, the normalized inverse bound, and absolute
     unselected-tuple mass. Writes the deterministic Gram contribution
       G=Z^(3/16+(23/96)*epsilon)
     and the inverse mass
       V=C(1+|t|)^J Z^(507*epsilon/2).
   * In particular the 3/16 LOW power is not secretly an owner covariance
     bound; it is the scalar completed-Gaussian cost after the selected
     square-root energy has been normalized.
   * The bound is Z^(3/16+254*epsilon).

7. Detector/LowGaussianDyad.lean, LowGaussianCentral.lean,
   LowGaussianSum.lean, LowCommonBound.lean, LowNormalized.lean:
   * Sum the actual central and remote dyads; fixed subset and Gaussian
     moments add only epsilon losses. Normalize the genuine physical
     probe. Terminal power is 3/16+loss.

8. RH_Lean research/oai_434/VF919NativeSevenEighthsReplay.lean:
   * Replays original OAI 7/8 through these actual suppliers and the
     genuine Mertens/Hecke transfer.

## 3. What native NNS changes and what it cannot change by itself

research/oai_434/VF919NativeEnergyInduction.lean is a coordinate-exact
NNS UPM/LPM realification of the SAME original complex squared norm.
An isometric coordinate change is not a strict norm saving.

research/oai_434/VF919OriginalMarkedSharpenedSignedNNS.lean retains the
true selected marked-moment exponent 1+t/2, where
VF919NativeSourceMoments.lean currently widens it to 1+t in its final
shared Moments certificate. This is an identified actual HIGH loss.
But the OAI detector count uses a shared moment epsilon_m across
inverse, plain-unmarked, plain-marked branches. The marked-only gain
survives their maximum only when marked is the binding branch.
In all cases improving HIGH *alone* leaves LOW=3/16 binding.

## 4. Do NOT borrow the canonical cstar gain from a different branch

Original Reflection/CanonicalFrozenEnergy.lean and
CompletedCanonicalEnergy.lean contain valid local powers such as
-cstar/16 and the source constraint eta<=cstar/100000.
OriginalRetained.lean / RetainedBudget.lean spend cstar to pay
retained-dyad count, pool and branch costs; CanonicalChoiceEnergy
also spends a further cstar/32.

However, the actual LOW terminal chain above uses
LowSlotPolynomial -> LowTupleGram -> LowCentralTuple, and its inverse
supplier uses LowSelectedBound -> LowOriginalEnergy ->
LowCompletedFiber -> LowFrozenEnergy -> LowInactiveEnergy ->
LowChoiceEnergy -> LowDyads -> LowFixedMember -> LowMemberGeometry ->
LowMemberBudget -> LowGlobalBudget -> LowFullBudget ->
LowFull -> LowRetainedBudget -> LowRetained -> LowSector.

A -cstar/16 local theorem on an alternate canonical-completion family
cannot be substituted for a signed saving in the terminal LOW family
without a source-faithful equivalence for the SAME labels, masks,
prime-pool exclusions, original normalizer and complete compensated
return. In particular, a matching exponent written on paper is not
that equivalence.

## 5. The new source-faithful signed-LOW target

In RH_Lean PR #1083,
research/oai_434/VF919OriginalLowTupleSignedGram.lean specializes the
already proved generic NNS Hermitian polarization to the literal
original U_a from compensation_tuple_low_polynomial.

Define, on that actual admitted LOW tuple population, without taking
absolute values prematurely,

  D_low = sum_a |U_a|^2,
  C_low = sum_a sum_(b != a) Re(U_a conjugate(U_b)).

Then the actual OAI source is exactly D_low + C_low.

The needed new analytic result is **not** a formal hypothesis
Gamma_R=M(R^2-1)^2-D_R. It is a genuine estimate of the complete
compensated LOW source (including the unselected cross terms) below
the current 3/16 amplitude threshold. One concrete sufficient target,
with ALL same-source quantifiers and all dyadic/normalization losses,
is

  ||complete normalized compensated LOW probe|| 
       <= C_epsilon Z^(3/16-g+epsilon),  g>0.

Equivalently, before the square root, a new source-backed gamma/covariance
estimate must save 2*g in the squared LOW exponent. A proposed saving
from the inner original inverse energy 5/6-2*d-nu would yield g=nu/2
*if* it survives all weights, the unselected full return, and the
complete compensated source. The bare uniform inner energy estimate
is NOT assumed or proved; arbitrary row and mask configurations may
obstruct such a statement without centering.

The exact exchange rate is

  (beta-11/16) - (3/16-g) = beta-7/8+g,

therefore a source-faithful g>0 plus the already-positive HIGH reserve
would give beta <= 7/8-g. This *source-first* path must come before
deducing consequences in native square-block or Mertens owner coordinates.

## 6. Instructions for the next arithmetic proof, not a conditional loop

A. Compare, at the same source SHA, the true lowUnselectedWeight,
   lowSelectedInverseRow and lowSeparatedIntegrand cross terms with
   the native RH_Lean NNS Co/Div signed terms (on actual Hecke labels).
B. Establish finite exact cancellations of equal-prime/diagonal/common-
   offset parts BEFORE any Cauchy or norm_sum_le, and retain all
   complementary terms in a single ledger.
C. Test proposed strict gain against J=empty, all-present/partial
   selected slots, nonprincipal/trivial local characters, excluded bad
   prime pools, and moving dyadic boundaries.
D. Determine whether the canonical -cstar/16 family can be mapped to
   these exact original LOW rows and whether its fixed part survives
   the true pool, dyadic, terminal and normalization bills.
E. Only then prove a uniform arithmetic 2*g power gain in the COMPLETE
   original LOW source and propagate through existing original
   LowGaussianSum/LowNormalized and principal/HIGH suppliers.
F. Only AFTER that invoke native Mertens / Co-Div / square-block
   consequences. Do not assume ownerBound, Gamma_R+, or an abstract
   negative covariance that restates the desired endpoint.

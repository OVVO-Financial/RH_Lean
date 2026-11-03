# Binding exceptional sixth-power source: exact signed attack

Date: 2026-11-03. Upstream pinned OpenAI/math 1581d4cbdd69a0faf34b2089614fe2a814316a6a.

## Do not attack another slot parameter

The old proof's fixed physical scales X=Z^(17/48), Y=Z^(23/48) and Q=q X Y, q=N(g)>0
give P=Y^2/Q=Z^(1/8)/q. The worst original additive Gaussian Gram term is

  (Q/Y) * P^(1/6) = q^(5/6) * Z^(3/8).

The square root of this term costs Z^(3/16). The principal pole has size
Z^(-11/16), so the endpoint crossing equals 7/8.

The positive exceptional frequency estimate comes from:
- Detector/LowGramExceptional.lean, actual sixth-power-remainder count R^(1/6);
- Detector/GramFrequencySummation.lean, exceptional_frequency_weighted_sum;
- Detector/GramFrequencyMass.lean, canonical_exceptional_frequency_sum;
- Detector/GramIdealMass.lean, canonical_exceptional_ideal_sum;
- Detector/GramSourceEstimate.lean, original_source_truncation_bound;
- Detector/GramInfiniteEstimate.lean, original_energy_nonzero_bound;
- Detector/GramBound.lean, actual_additive_gram_bound;
- Detector/LowGramIntegrated.lean, lowSeparatedIntegral_actual_gram;
- Detector/LowTupleGram.lean, compensation_tuple_actual_gram;
- Detector/LowCentralTuple.lean, low_central_compensated_tuple.

The exponent 1/6 is sharp as a bound on the SIZE of the exceptional universe:
outside a fixed conductor, frequency ideals may have all valuations divisible
by six, and sixth powers already produce about R^(1/6) lattice frequencies.
A frequency-counting improvement is impossible without exploiting coefficients.

## The exact coefficient that the original proof erases

Detector/GramSourceDivisors.lean:
  sourceMobiusWeight W hW Y hY C D =
    if D in sourceDivisors W hW Y hY C
    then ((moebius D.val : Z) : C) else 0.

Detector/GramTruncation.lean:
  sourceCanonicalSum = (Q/Y^3) *
    sum_{C in F} sum_{D in sourceDivisorUnion F} mu_C(D) *
       sum_{k in E(C)} canonicalLatticeBlock(C,k,primaryGenerator D, ...).

Detector/GramIdealMass.lean:
  normalized_double_sum_bound uses only |mu_C(D)| <= 1 and takes triangle
  separately in C,D. Detector/GramFrequencyMass.lean also takes triangle
  in the exceptional k-frequency sum. No uniform source-specific phase
  saving is proved at either point.

The new file research/oai_434/VF919OriginalExceptionalSignedGram.lean
retains exact full coefficients and identifies the signed source with its
Hermitian Gram and with the true normalized two-real NNS Co-Div expression,
including a theorem specific to the exceptional sixth-power branch.
Neither a stand-in Gaussian family nor a fake unweighted NNS source is used.

## Quantitative arithmetic target

Seek a fixed theta>0 so that for the ACTUAL original source, uniformly in
all admissible high-scale physical rows, selected slots, fixed masks, all
characters, and all source cutoffs, the exceptional part improves from

  |sourceExceptional| <= C_(epsilon) (Q/Y) P^(1/6+epsilon)

to

  |sourceExceptional| <= C_(epsilon) (Q/Y) P^(1/6-theta+epsilon).

The original high/low 3/16 proof would then gain, at its Gaussian Gram
square-root stage, an amplitude exponent theta/16 because P=Z^(1/8)/q.
The target crossing is 7/8-theta/16, subject to preserving the original
nonexceptional, zero-frequency, low inverse, normalizer, HIGH and
principal comparisons. theta=1/12 would correspond to an amplitude gain
1/192. This is a CONDITIONAL exchange rate, NOT a proved saving.

Correct signed proof must preserve:
- every C common divisor and its entire D Möbius support;
- every exceptional nonzero k with the true sixth-power local restriction;
- all canonicalJoint Hecke phases, CRT calibration and source Fourier weights;
- the original Mobius/generator scale Y/(norm C norm D);
- the source's selected-slot and Gaussian compensation factors on
  return through LowTupleGram.

The step that is STILL OPEN is a genuinely independent arithmetic
upper bound on this exact original signed exceptional source. The signed
identity is NOT that bound, and no theorem here claims a new exponent.

## Why the immediately preceding triangle step is not by itself enough

LowSlotPolynomial.lean fixes J and defines
  lowUnselectedWeight = (-1)^|J| * norm(L)^(-3/2) * product W_i.
The parity is constant over unselected tuples at a fixed J. Replacing
the triangle inequality at LowTupleGram by an unsupported assumption
of alternating signs across these tuples is not a valid improvement.
Phases may reside in the selected inverse rows and in the inner
Möbius / exceptional-frequency cancellation. This PR attacks the latter
without incorrectly assigning a new sign to each unselected tuple.

## Verification

Compile the exact module with original pinned OAI modules under warning-fatal
Lean 4.34.1 and inspect actual theorem axioms. The existing LOW/HIGH
endpoint and original arithmetic supplier are not changed.

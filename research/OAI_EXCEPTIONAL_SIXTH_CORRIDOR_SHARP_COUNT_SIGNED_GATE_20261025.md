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

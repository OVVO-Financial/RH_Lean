# Alpöge's ACTUAL map -> RH_Lean NNS, with no new surrogate source

Date: 2026-11-21. Independent focused PR; supersedes the generic "NNS Gz tail" as the proposed translation target.

## 1. The published map — already reconstructed in RH_Lean's arithmetic

Original Alpöge tree:
- src/Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean
  defines ArithData, HostFacts, cosetMean, primVal, GPsi,
  ASK, MAIN, De and the proposition AskMainBalance.
- src/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean
  proves characterSum_expansion and colour_balance:
    ASK(D,N,a,t,w) - MAIN(ell,a,w) = De(D,ell,a,t,w).
- src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean
  defines topExcess as the average over u0 in H, t in TT,
  j in Fin m of these exact ASK-MAIN gaps. All height/geometry
  returns are charged against this topExcess.
- src/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean
  proves extension_data_field, the actual Frobenius/inertia host realization.

Existing, unconditional, native RH_Lean results (NOT imported
from Alpöge's completed theorem):
- RHLean/Analysis/AlpogeNativeSharpASKBalance.lean:
  alpogeNativeFullASK_sub_MAIN_eq_De;
  alpogeNativeConcreteHostASK_sub_MAIN_eq_De;
  alpogeNativeHostData e q d;
  alpogeNativeRecMap e q d;
  alpogeNativeFullKernelASK and alpogeNativeMAIN.
- RHLean/Analysis/AlpogePrimitiveDirichletFull.lean:
  alpogeNativeCosetMean_eq_primitive;
  alpogeNativePrimVal_eq_primitive.
- RHLean/Analysis/AlpogeCompletePrimitiveASK.lean:
  alpogeNativeCftGPsi_eq_primitiveGPsi;
  alpogeNativeCanonicalHostASK_sub_MAIN_eq_primitiveDe.

These already supply the exact physical map, including ALL prime
powers, ramified conductor zeros, original a/w shifts and the
principal Gz. No new mapping needs to be hypothesized.

## 2. ONE literal change of coordinates

Let N=2^(e+2) q d, with q,d odd primes, and
r=alpogeNativeRecMap e q d. The host group is the original
(E0 x H_e), where E0=(Z/2)^2 and H_e is the dyadic local
unit quotient. Let Phi be the exact original positive-color
set; let g run over all original non-Phi color fibers.

For every color g define the REAL, signed source atom

  B(g) = Re[
      (1 / |Phi|) *
        sum_(psi in additive characters of E0 x H_e)
          conj(psi(g)) * w(partner(t,g)) *
          GPsi^primitive_{r,ell,psi}
            (a / w(partner(t,g)))
     ].

The character sum is performed BEFORE taking its positive/negative
parts. Its principal term is the *actual* original Gz. Its
nonprincipal terms are the ACTUAL primitive Dirichlet characters
induced by the same modular-unit reciprocity homomorphism, with
genuine inertia mean and conductor zeros.

Let
   U = sum_(g notin Phi) max(B(g), 0);
   L = sum_(g notin Phi) max(-B(g), 0).

Our new theorem proves EXACTLY:

  Re[ASK(D,N,a,t,w)-MAIN(ell,a,w)] = U-L.               (1)

This is a same-source, identical-index, identical-normalization
rewrite. It is NOT merely that "both admit a Fourier expansion";
the equality uses existing *proved* exact native arithmetic maps.

The new module additionally instantiates r, D and N to the
literal Alpine modular unit host, rather than leaving them generic.

## 3. Translate the COMPLETE averaged cost, not a local toy

Keep original u0:H, t in TT, j:Fin m, a(t), widths w(u0,j),
with the original cutoff and positive-width hypotheses. Define

  Ex_Alpoge := (1/|H|) sum_u0 sum_(t in TT) sum_(j in Fin m)
      Re[ASK(D,M,a(t),t,w(u0,j))
         -MAIN(ell,a(t),w(u0,j))],

  Ex_NNS := (1/|H|) sum_u0 sum_(t in TT) sum_(j in Fin m)
      [U(u0,t,j)-L(u0,t,j)].

The new Lean theorem proves

     Ex_Alpoge = Ex_NNS,                               (2)

and for EVERY error allowance Err,

     Ex_Alpoge <= Err IFF Ex_NNS <= Err.                (3)

No signed term, Euler correction, primitive-conductor zero,
width, prime-power fiber, or thick/thin source is removed.

The theorem declarations are:

  alpogeCompletePrimitiveDe_re_eq_originalNNS
  alpogeActualCftASK_sub_MAIN_re_eq_originalNNS
  alpogeActualCanonicalASK_MAIN_re_eq_originalNNS
  alpogeActualCanonicalTopExcess_eq_NNS
  alpogeActualCanonicalTopExcess_le_iff_NNS
  alpogeLiteralHostModulus_ne_zero
  alpogeLiteralHostASK_MAIN_re_eq_originalNNS
  alpogeLiteralHostASK_MAIN_le_iff_originalNNS

## 4. Why this is the correct one-point bridge

Alpöge's growth-inequality proof consumes a bound on the COMPLETE
topExcess, not an unrelated Gram norm or the individual Gz history.
Equation (3) transports this exact premise, unchanged, to native
NNS (UPM1 - LPM1) on his original actual color and character
fibers. The character sum is evaluated first so the source's
internal complex phase cancellation is preserved.

This answers the representation question. The exact same bound
can now be stated and tested in either coordinate. Importantly,
a representation equivalence DOES NOT prove the quantitative
cost itself. To infer the critical Gz inequality unconditionally,
one must supply the specific fully parameterized geometric/height
cost bound used in the Alpöge growth proof, or translate its
already-proved upstream certificate with all original hypotheses.
This PR does not import the upstream final RH theorem, assume
that an ASK bound exists, or assert that general NNS positivity
forces the RH-strength estimate.

## 5. Verification and acceptance

This is a fully implemented Lean source-file proof attempt on a
fresh branch and included in the root import manifest.
Only exact-head hosted Lean CI establishes compilation.
Do not merge or claim a new RH bound while that check is failing
or pending. No assertion about terminal RH or newly proved
source saving is warranted by a coordinate conversion alone.

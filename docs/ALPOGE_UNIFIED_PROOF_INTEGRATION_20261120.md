# One unified RH proof assembly: original Alpöge plus RH_Lean

**Date:** 2026-11-20.  **Status:** source integration implemented;
native and upstream CI receipts must be checked before certification.

## Full theorem chain, without replacing geometric lemmas

Original Levent Alpöge proof (CocoSgt mirror; source pinned to
7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
Lean 4.33.1, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474):

    UpperTheory.FinalTheorems.everyCharacter
       : UpperTheory.EveryCharacter
       -> allChi
       -> Formalism.VW.rh_of_every allChi
       -> rhOfAll : RiemannHypothesis
       -> src/Main.lean: riemannHypothesis : RiemannHypothesis

The FULL ORIGINAL imported proof is used. No speculative substitute
for its integral Hecke / geometric / covolume construction is needed.

The new external adapter integrations/alpoge/AlpogeProofAdapter.lean
imports ORIGINAL Main, original Formalism.StatementOC and an IDENTICAL
COPY of the common RHLean/AlpogeInterface.lean. Inside the SAME upstream
Lean 4.33.1 compiler environment it proves, without assumptions:

    originalAlpoge_proves_RHLean_RH
       : RHLean.AlpogeInterface.rhStatement
    originalAlpoge_proves_RHLean_DirichletHalf
       : RHLean.AlpogeInterface.dirichletRightHalfStatement
    gz_eq_upstream_Alpoge_Gz
       : forall x, RHLean.AlpogeInterface.gz x = Formalism.Gz x
    originalAlpoge_RH_and_nativeGz
       : rhStatement AND equality of the original Gz with the native sum

The RHLean-native v4.34.1 module
RHLean/Analysis/AlpogeUnifiedNativeBridge.lean uses the SAME
RHLean/AlpogeInterface.lean bytes and proves by definitional equality:

    interface.rhStatement = RHLean.Analysis.RiemannHypothesisStatement
    interface.psi N = nativePsi N
    interface.lambdaRecip N = nativeLambdaRecip N
    interface.error N = nativePNTError N
    interface.gz x = the existing exact RHLean Gz arithmetic signal

It further proves the complete signed second-Selberg expression, with
all reciprocal-Lambda, floor, prime-square and prime-power returns.

## Reproducible verification

The script

    bash integrations/alpoge/check_joint_proof.sh

downloads EXACT pinned original Alpöge source, checks both upstream
toolchain and Mathlib commit, builds unmodified ORIGINAL Main, copies
RHLean/AlpogeInterface.lean VERBATIM, and compiles the adapter in the
same upstream kernel. It prints and parses kernel axiom lists for the
RH, Dirichlet and Gz theorem terms. Nonstandard axioms and missing
audit output cause a failure.

The manual GitHub workflow
.github/workflows/alpoge-joint-original-proof.yml runs the FULL
175,187-module upstream proof assembly on a runner the user selects.
It is deliberately manual: automatic builds of 17M lines on every
RHLean PR would be unnecessarily expensive.

The RHLean-native v4.34.1 bridge is compiled by ordinary CI through
the sorted RHLean.lean root manifest.

## Proof boundary

The original proof and the native adapter use different Lean/Mathlib
versions. The shared SOURCE is compiled in both, and the entire RH
theorem is imported and checked in the ORIGINAL upstream environment.
There is no 4.33 .olean import into the 4.34 RHLean kernel. A
NATIVE-4.34 unconditional theorem still requires porting the upstream
full proof dependency graph or aligning the entire RHLean version.

This is an actual same-kernel proof composition in the upstream
environment, not a new conjectural Selberg estimate. Do not claim
the new co-compiled declaration was kernel-checked until its manual
upstream build and axiom audit have succeeded. In particular, the
separate original RHLean arithmetic and the independent full original
Alpöge proof are joined through source-level identities, not via a
fabricated theorem that imports across incompatible Lean versions.

## Completion checklist

1. Native RHLean new modules compile, no sorry or custom axioms.
2. The original huge pinned upstream proof and our adapter compile
   together under its own 4.33.1 kernel.
3. The exact theorem axiom report admits only propext,
   Classical.choice (or choice) and Quot.sound.
4. Only then record co-compiled theorem success; a native RHLean 4.34
   theorem certificate requires a separately checked compatible port.

**Do not spend further effort trying to simulate the already-verified
geometric input with arbitrary RHLean K2 matrices unless the user
explicitly requests an independent elementary proof.**

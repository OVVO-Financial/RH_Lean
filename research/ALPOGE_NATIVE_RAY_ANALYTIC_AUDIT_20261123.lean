import RHLean.Analysis.AlpogeThin.NativeRayAnalyticFamily
import RHLean.Analysis.AlpogeThin.NativeRayNormPrimeCount
import RHLean.Analysis.AlpogeThin.NativeRaySelectedHostLevelPrime

/-!
# Native ray analytic and actual level-prime terminal-axiom audit

The guarded endpoints include continuation, complete prime-power logarithmic
differentiation, the real exception, Perron and its floor correction, actual
identity-ray mass, norm-prime counting, and a prime plus integral norm element
in the same constructed native host. Constants and thresholds precede the
actual fields, ray data and windows as the theorem statements specify.
Only propext, Classical.choice and Quot.sound are accepted.
-/

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.RayCont.continuation_growth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.RayCont.continuation_growth

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.LogDeriv.logDeriv_F' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.LogDeriv.logDeriv_F

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.LFamPos.positivity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.LFamPos.positivity

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.LFam.exp_sum_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.LFam.exp_sum_bounds

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.RealChar.norm_F_one_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.RealChar.norm_F_one_ge

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.LFam.real_zero_far_from_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.LFam.real_zero_far_from_one

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.LogDerivZeros.main' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.LogDerivZeros.main

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.HkLocal.logDeriv_local' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.HkLocal.logDeriv_local

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.ZeroFree.zero_free_region' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.ZeroFree.zero_free_region

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.RealZero.main' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.RealZero.main

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.LFam.ofRayData_continuation_growth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.LFam.ofRayData_continuation_growth

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.LFam.ofRayData_logDeriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.LFam.ofRayData_logDeriv

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.LFam.ofRayData_real_nonvanishing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.LFam.ofRayData_real_nonvanishing

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.ChebyshevBounds.sum_vonMangoldt_le_two_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.ChebyshevBounds.sum_vonMangoldt_le_two_mul

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.ResRect.residue_rectangle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.ResRect.residue_rectangle

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.ExplicitRect.expand_simple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.ExplicitRect.expand_simple

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.PerronCoeff.truncated_perron_of_le_two_vonMangoldt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.PerronCoeff.truncated_perron_of_le_two_vonMangoldt

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.LogDerivHalf.logDeriv_sub_exceptional_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.LogDerivHalf.logDeriv_sub_exceptional_le

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.PsiExc.psi_exceptional' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.PsiExc.psi_exceptional

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.ShortInt.trivialClass_shortInterval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.ShortInt.trivialClass_shortInterval

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.normPrimes_short_interval_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.normPrimes_short_interval_lower

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.NormPrimeCount.normPrimesN' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.NormPrimeCount.normPrimesN

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.LevelPrime.levelPrimeN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.LevelPrime.levelPrimeN

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_levelPrime_rayNormElement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_levelPrime_rayNormElement

/--
info: 'RHLean.Analysis.AlpogeThin.nativePageN_modAt_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativePageN_modAt_eventually

/--
info: 'RHLean.Analysis.AlpogeThin.nativeSelectedDyadicHost_levelPrime_rayNormElement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeSelectedDyadicHost_levelPrime_rayNormElement

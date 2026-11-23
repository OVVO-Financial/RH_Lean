import RHLean.Analysis.AlpogeThin.NativeRayAnalyticFamily

/-!
# Native ray analytic construction: exact terminal-axiom guards

The actual LFam arithmetic constructor is used by the final three guarded
declarations. The preceding guards cover the original continuation, full
prime-power logarithmic derivative, signed positivity, real-character lower
bound, local zeros, zero-free region and retained exceptional zero.
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

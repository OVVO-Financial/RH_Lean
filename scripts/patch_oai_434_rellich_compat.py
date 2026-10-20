#!/usr/bin/env python3
"""Local auditable Lean 4.34.1 compatibility rewrites to pinned Rellich library.

Existing RellichKondrachov proofs are mathematically unchanged. They use
simp across pointwise-function eta expansions which Lean 4.34.1 no longer
identifies automatically. This script changes these proofs to explicit
Pi.smul_apply, Pi.mul_apply, and Function.comp_def normalizations.

Changes only affect the workflow's temporary .lake/packages checkout.
Failure to match any expected source snippet is fatal.
No sorry, axiom or proof bypass is inserted.
"""
from pathlib import Path

ROOT = Path("oai-upstream/lean/.lake/packages/rellich-kondrachov/RellichKondrachov")


def patch(rel, changes):
    path = ROOT / rel
    text = path.read_text()
    for change in changes:
        old, new = change[:2]
        expected_count = change[2] if len(change) == 3 else 1
        count = text.count(old)
        if count != expected_count:
            raise RuntimeError(
                f"{path}: expected {expected_count} occurrence(s), found {count}: {old!r}")
        text = text.replace(old, new)
    path.write_text(text)
    print(f"Lean 4.34 pointwise compatibility: {path} ({len(changes)} rewrites)")


patch("Analysis/FunctionalSpaces/Sobolev/Euclidean/H1.lean", [
    (
        "simpa using (HasCompactSupport.smul_left (f := fun _ : E => c) hf.2)",
        "have heq : c • f = (fun _ : E => c) * f := by\n"
        "      funext x\n"
        "      simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]\n"
        "    rw [heq]\n"
        "    exact HasCompactSupport.smul_left (f := fun _ : E => c) hf.2"
    ),
    (
        "simpa [grad] using this",
        "change Continuous (fun x =>\n"
        "    (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))\n"
        "  exact this"
    ),
    (
        "simpa [grad] using\n"
        "    (HasCompactSupport.comp_left (f := fderiv ℝ f) (g := (InnerProductSpace.toDual ℝ E).symm)\n"
        "      hf' (by simp))",
        "change HasCompactSupport\n"
        "    ((InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ f)\n"
        "  exact (HasCompactSupport.comp_left (f := fderiv ℝ f)\n"
        "    (g := (InnerProductSpace.toDual ℝ E).symm) hf' (by simp))"
    ),
    (
        "simpa [grad, Function.comp] using\n"
        "      (tsupport_comp_subset\n"
        "        (g := (InnerProductSpace.toDual ℝ E).symm) (hg := by simp)\n"
        "        (f := fderiv ℝ f))",
        "change tsupport ((InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ f) ⊆\n"
        "    tsupport (fderiv ℝ f)\n"
        "    exact (tsupport_comp_subset\n"
        "      (g := (InnerProductSpace.toDual ℝ E).symm) (hg := by simp)\n"
        "      (f := fderiv ℝ f))"
    )
])

patch("MeasureTheory/Function/LpSpace/Restrict.lean", [
    (
        "simpa using (Lp.coeFn_add (μ := μ.restrict s) f g)",
        "have h := Lp.coeFn_add (μ := μ.restrict s) f g\n"
        "      filter_upwards [h] with x hx\n"
        "      simpa only [Pi.add_apply] using hx"
    ),
    (
        "simpa using (Lp.coeFn_smul (μ := μ.restrict s) c f)",
        "have h := Lp.coeFn_smul (μ := μ.restrict s) c f\n"
        "      filter_upwards [h] with x hx\n"
        "      simpa only [Pi.smul_apply] using hx"
    )
])

patch("Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/Kernels.lean", [
    (
        "simpa [ψ] using (continuous_const.mul hf_cont)",
        "have heq : ψ = (fun _x : E => I⁻¹) * f := by\n"
        "      funext x\n"
        "      simp only [ψ, Pi.mul_apply]\n"
        "    rw [heq]\n"
        "    exact continuous_const.mul hf_cont"
    ),
    (
        "simpa [ψ, smul_eq_mul] using\n"
        "      (HasCompactSupport.smul_left (f := fun _x : E => I⁻¹) (f' := f) hf_cs)",
        "have heq : ψ = (fun _x : E => I⁻¹) * f := by\n"
        "      funext x\n"
        "      simp only [ψ, Pi.mul_apply]\n"
        "    rw [heq]\n"
        "    exact HasCompactSupport.smul_left (f := fun _x : E => I⁻¹) (f' := f) hf_cs"
    )
])


# The downstream translation and compactness files use exactly the same
# pointwise eta convention. Make the actual term at each x explicit rather
# than relying on Lean 4.34's simplifier to normalize function wrappers.
patch("Analysis/FunctionalSpaces/Sobolev/Euclidean/Translation.lean", [
    (
        "simpa [translate] using hf.comp (contDiff_id.add contDiff_const)",
        "change ContDiff ℝ 1 (fun x : E => f (x + a))\n"
        "  exact hf.comp (contDiff_id.add contDiff_const)"
    ),
    (
        "simpa [translate] using hf.comp_homeomorph (Homeomorph.addRight a)",
        "change HasCompactSupport (f ∘ fun x : E => x + a)\n"
        "  exact hf.comp_homeomorph (Homeomorph.addRight a)"
    ),
    (
        "simp [grad]\n"
        "  -- Reduce to the standard `fderiv` translation lemma.\n"
        "  simpa [translate] using (fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := x) a)",
        "change (InnerProductSpace.toDual ℝ E).symm\n"
        "    (fderiv ℝ (fun y : E => f (y + a)) x) =\n"
        "      (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f (x + a))\n"
        "  exact congrArg\n"
        "    (fun v : E →L[ℝ] ℝ => (InnerProductSpace.toDual ℝ E).symm v)\n"
        "    (fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := x) a)"
    ),
    (
        "simpa [translateL2] using\n"
        "    (MeasureTheory.Lp.coeFn_compMeasurePreserving (g := (g : MeasureTheory.Lp F (2 : ENNReal) μ))\n"
        "      (hf := MeasureTheory.measurePreserving_add_right μ a))",
        "have h :=\n"
        "    (MeasureTheory.Lp.coeFn_compMeasurePreserving\n"
        "      (g := (g : MeasureTheory.Lp F (2 : ENNReal) μ))\n"
        "      (hf := MeasureTheory.measurePreserving_add_right μ a))\n"
        "  filter_upwards [h] with x hx\n"
        "  exact hx"
    ),
    (
        "simpa [Function.comp, Pi.add_apply] using\n"
        "        (Measure.QuasiMeasurePreserving.ae_eq_comp\n"
        "          (MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving hf)",
        "have h :=\n"
        "        (Measure.QuasiMeasurePreserving.ae_eq_comp\n"
        "          (MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving hf)\n"
        "      filter_upwards [h] with x hx\n"
        "      exact hx",
        2
    ),
    (
        "simpa [translateC1c, translate] using\n"
        "      (memLp_of_mem_C1c (μ := μ) (E := E) (translateC1c (E := E) a f).2).coeFn_toLp",
        "have h :=\n"
        "      (memLp_of_mem_C1c (μ := μ) (E := E)\n"
        "        (translateC1c (E := E) a f).2).coeFn_toLp\n"
        "    filter_upwards [h] with x hx\n"
        "    exact hx"
    ),
    (
        "simpa [translate] using grad_translate (E := E) a f.1 x",
        "exact grad_translate (E := E) a f.1 x"
    )
])

patch("Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/Compactness.lean", [
    (
        "simpa using this.comp continuous_subtype_val",
        "change Continuous ((smoothFun (E := E) (K := K) ψ u) ∘ Subtype.val)\n"
        "    exact this.comp continuous_subtype_val"
    )
])


# Proof-preserving upgrades for the remaining pinned Rellich 4.34.1 DAG.
# Each rewrite is checked against the exact original dependency text.
# Keep all real functional-analytic proof obligations intact.
patch("Analysis/FunctionalSpaces/Sobolev/Euclidean/TranslationEstimateL2.lean", [
    ("        simpa [Function.comp, Pi.add_apply] using\n          (Measure.QuasiMeasurePreserving.ae_eq_comp\n            (MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving hf)", "        have h :=\n          (Measure.QuasiMeasurePreserving.ae_eq_comp\n            (MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving hf)\n        filter_upwards [h] with x hx\n        exact hx"),
    ("    simp_rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal\n      h2_ne0 h2_netop, ENNReal.toReal_ofNat] at *", "    simp only [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal\n      h2_ne0 h2_netop, ENNReal.toReal_ofNat]"),
])

patch("Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/Approximation.lean", [
    ("local instance instIsProbabilityMeasure_kernelMeasure", "private lemma instIsProbabilityMeasure_kernelMeasure"),
    ("    simpa [Function.comp] using (hmp.quasiMeasurePreserving.ae_eq_comp hF_ae)", "    have h := hmp.quasiMeasurePreserving.ae_eq_comp hF_ae\n    filter_upwards [h] with x hx\n    exact hx"),
    ("      simpa using hdiff.pow_const 2", "      filter_upwards [hdiff] with x hx\n      exact congrArg (fun z : ℝ => z ^ 2) hx"),
    ("    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hadd.comp hneg", "    have hfun : (fun t : E => x - t) =\n        ((fun y : E => y + x) ∘ (Neg.neg : E → E)) := by\n      funext t\n      simp [Function.comp_def, sub_eq_add_neg, add_comm]\n    rw [hfun]\n    exact hadd.comp hneg"),
    ("      simpa using hSF_ae.pow_const 2", "      filter_upwards [hSF_ae] with x hx\n      exact congrArg (fun z : ℝ => z ^ 2) hx"),
    ("    simpa [Function.comp] using this", "    exact this", 2),
    ("      simpa [Measure.map_fst_prod] using hf_mem.1", "      simpa [Measure.map_fst_prod] using hf_mem.aestronglyMeasurable"),
    ("    simpa [h] using (hsub'.pow 2)", "    have heq : h = (fun z : E × E => f (z.1 - z.2) - f z.1) ^ (2 : ℕ) := by\n      funext z\n      simp only [h, Pi.pow_apply]\n    rw [heq]\n    exact hsub'.pow 2"),
])

patch("Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/ArzelaAscoli.lean", [
    ("            simpa [sub_eq_add_neg, add_assoc] using hxy", "            simpa only [dist_sub_right, Subtype.dist_eq] using hxy"),
])


# Explicit AEMeasurable witnesses for the pinned L2 exponent rewrite;
# function-valued subtraction and transparent Kpsi support transport.
patch("Analysis/FunctionalSpaces/Sobolev/Euclidean/TranslationEstimateL2.lean", [
    ("    simp only [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal\n      h2_ne0 h2_netop, ENNReal.toReal_ofNat]", "    have hfn : AEStronglyMeasurable\n        (fun x : E => f.1 (x + a) - f.1 x) μ := by\n      have hfcont : Continuous (f.1) := f.2.1.continuous\n      have hshift : Continuous (fun x : E => x + a) :=\n        continuous_id.add continuous_const\n      exact ((hfcont.comp hshift).sub hfcont).aestronglyMeasurable\n    have hgrad : AEStronglyMeasurable\n        (fun x : E => grad (E := E) f.1 x) μ :=\n      (continuous_grad (E := E) (f := f.1) f.2.1).aestronglyMeasurable\n    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal\n        h2_ne0 h2_netop hfn,\n      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal\n        h2_ne0 h2_netop hgrad]\n    simp only [ENNReal.toReal_ofNat]"),
])

patch("Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/Transfer.lean", [
    ("          simpa [Pi.sub_apply] using hsub.trans (hu.sub hv)", "          filter_upwards [hsub.trans (hu.sub hv)] with x hx\n          simpa only [Pi.sub_apply] using hx"),
    ("        simpa [Pi.sub_apply] using hsub.trans (hu.sub hv)", "        filter_upwards [hsub.trans (hu.sub hv)] with x hx\n        simpa only [Pi.sub_apply] using hx"),
    ("        simpa [s] using", "        simpa [s, Kψ] using", 2),
])

# Lean 4.34.1: preserve the actual MemLp source measurability rather than
# demanding separability of the arbitrary inner-product target E.
# Also unfold function composition in the product-measure Tonelli witness.
patch("Analysis/FunctionalSpaces/Sobolev/Euclidean/TranslationEstimateL2.lean", [
    (
        "    have hgrad : AEStronglyMeasurable\n"
        "        (fun x : E => grad (E := E) f.1 x) μ :=\n"
        "      (continuous_grad (E := E) (f := f.1) f.2.1).aestronglyMeasurable",
        "    have hgrad : AEStronglyMeasurable\n"
        "        (fun x : E => grad (E := E) f.1 x) μ :=\n"
        "      (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).aestronglyMeasurable",
    ),
    (
        "        simpa [F] using (hpow.comp hbase).aemeasurable",
        "        simpa only [F, Function.comp_def] using (hpow.comp hbase).aemeasurable",
    ),
])


# Original OAI CompensationActual depends on H1 translation closedness.
# Lean 4.34.1 needs the pointwise Pi and composition evaluation made explicit.
patch("Analysis/FunctionalSpaces/Sobolev/Euclidean/TranslationEstimateH1.lean", [
    (
        "        simpa [sub_eq_add_neg] using htr.sub hfst",
        "        have hpoint :\n"
        "            ((fun v : V => translateL2 (μ := μ) (F := ℝ) a v.1) -\n"
        "              (fun v : V => v.1)) =\n"
        "              (fun v : V => translateL2 (μ := μ) (F := ℝ) a v.1 - v.1) := by\n"
        "          funext v\n"
        "          simp only [Pi.sub_apply]\n"
        "        rw [← hpoint]\n"
        "        exact htr.sub hfst",
    ),
    (
        "      simpa using (continuous_norm.comp hsub)",
        "      simpa only [Function.comp_def] using (continuous_norm.comp hsub)",
    ),
    (
        "      simpa [mul_assoc] using (continuous_const.mul hnorm)",
        "      have hpoint :\n"
        "          ((fun _ : V => ‖a‖) * (fun v : V => ‖v.2‖)) =\n"
        "            (fun v : V => ‖a‖ * ‖v.2‖) := by\n"
        "        funext v\n"
        "        simp only [Pi.mul_apply]\n"
        "      rw [← hpoint]\n"
        "      exact continuous_const.mul hnorm",
    ),
])


# Lean 4.34.1: Rellich compactness closes via the SAME local normed inclusion.
# The old implicit mem_closedBall_zero_iff application has an unconstrained
# metavariable; rewrite the actual hypothesis instead. The CLM norm is the
# operator norm by the pinned Mathlib NormedSpace instance, so express the
# local bookkeeping constant with its kernel-definitional norm.
patch("Analysis/FunctionalSpaces/Sobolev/Euclidean/Rellich.lean", [
    (
        "  let C : ℝ :=\n"
        "    (h1ToL2 (μ := (volume : Measure E)) (E := E)).opNorm",
        "  let C : ℝ :=\n"
        "    ‖h1ToL2 (μ := (volume : Measure E)) (E := E)‖",
    ),
    (
        "  have hCnonneg : 0 ≤ C := by\n"
        "    dsimp [C]\n"
        "    exact (h1ToL2 (μ := (volume : Measure E)) (E := E)).opNorm_nonneg",
        "  have hCnonneg : 0 ≤ C := by\n"
        "    dsimp [C]\n"
        "    exact norm_nonneg (h1ToL2 (μ := (volume : Measure E)) (E := E))",
    ),
    (
        "      exact (mem_closedBall_zero_iff.mp hx)",
        "      simp only [Metric.mem_closedBall, dist_zero_right] at hx\n"\n        "      exact hx",
        2,
    ),
])

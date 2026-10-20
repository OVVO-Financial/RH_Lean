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
    for old, new in changes:
        count = text.count(old)
        if count != 1:
            raise RuntimeError(f"{path}: expected once, found {count}: {old!r}")
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
        "  -- Reduce to the standard \`fderiv\` translation lemma.\n"
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
        "      exact hx"
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

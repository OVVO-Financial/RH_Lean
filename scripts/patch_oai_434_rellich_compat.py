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

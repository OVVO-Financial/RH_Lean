#!/usr/bin/env python3
"""Exact guarded StrongPNT/PNT1_ComplexAnalysis proof port for Lean 4.34.1.

The candidate port is not validated until its Lean build and axiom audit pass.
No theorem statement or assumptions are weakened. The removed PNT1-local
power-series and tangent-cone proof bodies are replaced by the equivalent
direct Mathlib lemmas at the pinned revision.
"""
from __future__ import annotations
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
TARGET = ROOT / ".lake/packages/StrongPNT/StrongPNT/PNT1_ComplexAnalysis.lean"
PINS = {"StrongPNT": "2f5835c322314f55f1026ec2f139d704b7c45c69",
        "mathlib": "d13f23b723b8a846827a245b89c10fc7d3f11612"}
REPLACEMENTS = [
  [
    "Eventually-to-set for hEZ",
    "have hU : {z : ℂ | f z = 0} ∈ nhds (0 : ℂ) := by simpa using hEZ",
    "have hU : {z : ℂ | f z = 0} ∈ nhds (0 : ℂ) := hEZ",
    1
  ],
  [
    "Eventually-to-set for hfac_ev",
    "have hV : {z : ℂ | f z = z * h0 z} ∈ nhds (0 : ℂ) := by simpa using hfac_ev",
    "have hV : {z : ℂ | f z = z * h0 z} ∈ nhds (0 : ℂ) := hfac_ev",
    1
  ],
  [
    "IsMaxOn predicate updated in Mathlib",
    "    simp only [Function.comp_apply]\n    -- Since norm is deprecated in favor of norm, they should be definitionally equal\n    convert hw_max z hz",
    "    simpa only [Function.comp_apply, Set.mem_setOf_eq, iff_self]",
    1
  ],
  [
    "Field simp closes ring step",
    "    field_simp\n    ring\n\n  -- Apply the rearrangement",
    "    field_simp\n\n  -- Apply the rearrangement",
    1
  ],
  [
    "Convert closedBall dist to norm",
    "have h1 : ‖z - 0‖ ≤ r_z := Metric.mem_closedBall.mp hz",
    "have h1 : ‖z - 0‖ ≤ r_z := by simpa only [dist_eq_norm] using (Metric.mem_closedBall.mp hz)",
    1
  ],
  [
    "Complex coefficient numerator simplified by field_simp",
    "  field_simp [Complex.I_ne_zero, Real.pi_pos.ne']\n  -- After field_simp, we have: I * (2 * ↑Real.pi) / (2 * ↑Real.pi * I) = 1\n  exact mul_comm_div_cancel I (2 * ↑Real.pi) Complex.I_ne_zero (by norm_num; exact Real.pi_pos.ne')",
    "  field_simp [Complex.I_ne_zero, Real.pi_pos.ne']\n  exact div_self Complex.I_ne_zero",
    1
  ],
  [
    "Remove finished ring integrand bound",
    "    field_simp [ne_of_gt h_R_sub_r_pos, ne_of_gt (pow_pos h_r_sub_r_pos 2)]\n    ring\n\n  -- Apply transitivity",
    "    field_simp [ne_of_gt h_R_sub_r_pos, ne_of_gt (pow_pos h_r_sub_r_pos 2)]\n\n  -- Apply transitivity",
    1
  ],
  [
    "ContinuousOn univ modern API",
    "rwa [← continuous_iff_continuousOn_univ] at hcomp_on",
    "exact continuousOn_univ.mp hcomp_on",
    1
  ],
  [
    "Functions require explicit extensionality",
    "simpa using hconst.add hmul",
    "convert hconst.add hmul using 1 <;> (ext τ; rfl)",
    1
  ],
  [
    "Addition monotonicity direction changed",
    "have : a.re ^ 2 + τ ^ 2 ≤ a.re ^ 2 + a.im ^ 2 := add_le_add_left hτ_sq _",
    "have : a.re ^ 2 + τ ^ 2 ≤ a.re ^ 2 + a.im ^ 2 := by\n      calc\n        a.re ^ 2 + τ ^ 2 = τ ^ 2 + a.re ^ 2 := add_comm _ _\n        _ ≤ a.im ^ 2 + a.re ^ 2 := add_le_add_left hτ_sq _\n        _ = a.re ^ 2 + a.im ^ 2 := add_comm _ _",
    1
  ],
  [
    "Retired algebra scalar multiplication normalization",
    "[Algebra.id.smul_eq_mul, smul_eq_mul, mul_comm]",
    "[smul_eq_mul, mul_comm]",
    1
  ],
  [
    "Old algebra id smul rewrite",
    "[Algebra.id.smul_eq_mul]",
    "[smul_eq_mul]",
    1
  ],
  [
    "Bound sum linear arithmetic",
    "exact add_le_add_left τ_bound _",
    "linarith only [τ_bound]",
    1
  ],
  [
    "Strictly bounded summed norms",
    "have htemp : ‖z‖ + ‖h‖ < ‖z‖ + (R' - ‖z‖) := add_lt_add_left hnorm_lt _",
    "have htemp : ‖z‖ + ‖h‖ < ‖z‖ + (R' - ‖z‖) := by linarith only [hnorm_lt]",
    1
  ],
  [
    "Simple triangle inequality summation",
    "exact le_trans tri (add_le_add_right hwz_le _)",
    "linarith only [tri, hwz_le]",
    1
  ],
  [
    "Radius inequalities Lean 4.34",
    "have : r1 + δ < r1 + (R - r1) := add_lt_add_left hδlt r1",
    "have : r1 + δ < r1 + (R - r1) := by linarith only [hδlt]",
    2
  ],
  [
    "Radius R' inequality Lean 4.34",
    "have : r1 + δ < r1 + (R' - r1) := add_lt_add_left hδlt r1",
    "have : r1 + δ < r1 + (R' - r1) := by linarith only [hδlt]",
    1
  ],
  [
    "Self membership in punctured neighborhoods",
    "simpa [Set.mem_setOf_eq] using\n      (self_mem_nhdsWithin : {h : ℂ | h ≠ 0} ∈ 𝓝[{h : ℂ | h ≠ 0}] (0:ℂ))",
    "exact (self_mem_nhdsWithin : {h : ℂ | h ≠ 0} ∈ 𝓝[{h : ℂ | h ≠ 0}] (0:ℂ))",
    1
  ]
]
REGIONS = [
  [
    "Replace obsolete power-series auxiliary proof with Mathlib bridge",
    "theorem analyticWithinAt_to_analyticAt_aux ",
    "-- First, the easy auxiliary lemmas:",
    "theorem analyticWithinAt_to_analyticAt {f : ℂ → ℂ} {S : Set ℂ} {z : ℂ}\n    (hS : S ∈ nhds z) (h : AnalyticWithinAt ℂ f S z) : AnalyticAt ℂ f z := by\n  rcases h with ⟨p, hp⟩\n  exact ⟨p, (hasFPowerSeriesWithinAt_iff_of_nhds f p hS).mp hp⟩\n\n\n"
  ],
  [
    "Use Mathlib complex unique differentiability theorem",
    "lemma uniqueDiffWithinAt_convex_complex ",
    "lemma interior_closedBall_nonempty_of_pos",
    "lemma uniqueDiffWithinAt_convex_complex {s : Set ℂ} (hconv : Convex ℝ s)\n    (hs : (interior s).Nonempty) {x : ℂ} (hx : x ∈ closure s) :\n    UniqueDiffWithinAt ℂ s x := by\n  exact uniqueDiffWithinAt_convex_of_isRCLikeNormedField hconv hs hx\n\n"
  ],
  [
    "Use modern scalar derivWithin/Frechet derivative equivalence",
    "lemma fderivWithin_eq_zero_of_derivWithin_eq_zero ",
    "lemma hasDerivWithinAt_of_hasDerivAt ",
    "lemma fderivWithin_eq_zero_of_derivWithin_eq_zero {s : Set ℂ} {f : ℂ → ℂ} {x : ℂ}\n    (_hdiff : DifferentiableWithinAt ℂ f s x)\n    (hderiv : derivWithin f s x = 0) :\n    fderivWithin ℂ f s x = 0 := by\n  calc\n    fderivWithin ℂ f s x = toSpanSingleton ℂ (derivWithin f s x) :=\n      (toSpanSingleton_derivWithin).symm\n    _ = 0 := by simp [hderiv]\n\n"
  ]
]

def main():
    pkgs = {p["name"]: p["rev"] for p in
            json.loads((ROOT / "lake-manifest.json").read_text())["packages"]}
    for name, expected in PINS.items():
        if pkgs.get(name) != expected:
            raise RuntimeError(f"Unexpected dependency {name}: {pkgs.get(name)}")
    text = TARGET.read_text(encoding="utf-8")
    for name, old, new, count in REPLACEMENTS:
        actual = text.count(old)
        if actual != count:
            if actual == 0 and text.count(new) == count:
                print(f"Already applied: {name}")
                continue
            raise RuntimeError(f"Source mismatch for {name}: {actual} != {count}")
        text = text.replace(old,new)
        print(f"Applied: {name}")
    for name, start, end, new in REGIONS:
        if text.count(start) != 1:
            if text.count(new) == 1:
                print(f"Already applied region: {name}")
                continue
            raise RuntimeError(f"Source mismatch for region: {name}")
        i=text.index(start)
        j=text.index(end,i+len(start))
        text=text[:i]+new+text[j:]
        print(f"Applied region: {name}")
    TARGET.write_text(text,encoding="utf-8")
    print("Port staged; run kernel compilation and forbidden-axiom audit.")

if __name__ == "__main__":
    main()

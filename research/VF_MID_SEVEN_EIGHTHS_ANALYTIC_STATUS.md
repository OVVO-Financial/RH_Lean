# New analytic-input experiment: OpenAI quasi-RH 7/8 → VF midpoint

**Status: conditional Lean bridge, not an unconditional 7/8 prime-counting theorem and NOT RH.**
**Independent branch:** `vf-seven-eighths-analytic-zero-free-bridge` based on `main`, not the open owner-decomposition #918.
**Lean file:** `research/VF_MID_SEVEN_EIGHTHS_ANALYTIC_BRIDGE.lean`.
**CI:** `.github/workflows/vf-mid-seven-eighths-analytic.yml`.

## Hypothesis separation (nothing implicit)

OpenAI's public [zeta nonvanishing result](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean) states in Lean:

```lean
OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re
  {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) : riemannZeta s ≠ 0
```

Their paper, [*The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s)>7/8*](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf), states a uniform zero-free half-plane. The stronger result for Dirichlet and Hecke L-functions is not needed for this endpoint experiment.

**Major compatibility constraint:** OpenAI's `lean/lean-toolchain` uses **Lean 4.34.1**; RH_Lean is pinned to **Lean 4.24.0**, with StrongPNT and Mathlib version constraints. Therefore an `import OAI...` in the RH_Lean native kernel is *not* a viable direct integration without a substantial dependency/toolchain port. The fast workflow verifies the upstream theorem name/source and both pins but deliberately does not compile external OAI inside RH_Lean.

**Mathematical missing step:** The public zeta nonvanishing theorem is NOT, by itself, a Lean theorem providing the classical power-saving prime-counting estimate. The explicit-formula/Perron/zero-sum quantitative transfer is separately required:

[
left[orall s, Re(s)>7/8 Longrightarrow zeta(s)
e0ight]
 Longrightarrowexists Cge0, orall Rge2,quad
left|pi(R^2)-operatorname{Li}_{2}(R^2)ight|
le C R^{7/4}log R.
	ag{ANALYTIC-TRANSFER}
]

The conventional derivation uses the zero-free half-plane with explicit formula and appropriate truncation/zero-counting and partial summation. This implication is not in the checked OpenAI zeta solution, as evidenced by its theorem statement alone. **The current PR does not pretend to prove this transfer.** It is named in Lean as `VFMidSevenEighthsExplicitFormulaBridge`.

The `Li_2` convention here is RH_Lean's `vfMidLogarithmicIntegralFromTwo` rather than a default shifted Li; additive normalization is absorbed into the constant.

## The portion now proved in RH_Lean

The fully existing uniform midpoint quadrature theorem establishes

[
orall Rge2,quad
|operatorname{VF}_{mid}(R^2)-operatorname{Li}_2(R^2)|
le Q,
]

where `Q = vfMidLiSquareEndpointUniformConstant` is an explicit positive fixed real number.

The new Mathlib-only proof consumes exactly the named external quantitative prime-Li estimate and derives

[
oxed{quad
orall Rge2,quad
|pi(R^2)-operatorname{VF}_{mid}(R^2)|
le left(C+rac{Q}{log2}ight)R^{7/4}log R.
quad}
]

The `Q/log 2` term is justified by the exact inequality
(log2le R^{7/4}log R) for (Rge2); no hidden finite-exception convention or unproved bound is needed.

The conclusion is the original genuine `Nat.primeCounting` / VF_mid endpoint, **not** a floor-Li fantasy staircase, owner payment, or a new NNS denominator. The proof is kernel-checkable at `-DwarningAsError=true` with `#print axioms` acceptance checks.

The named endpoint result is `vfMidSevenEighthsVFEndpointBounded_of_primeLi`, and the two-premise entry point is `vfMidSevenEighthsVFEndpointBounded_of_zeroFree`. Their signatures openly display the external hypothesis.

## What it does NOT establish

- **NOT** an unconditional (O(R^{7/4}log R)) estimate in RH_Lean, until the explicit-formula transfer is actually formalized and the external zeta theorem integrated on a compatible toolchain.
- **NOT** an RH-strength (,O(Rlog R),) bound. Merely replacing `2` by any larger constant in (CRlog R) would remain RH-equivalent.
- **NOT** a solution to the original first-bad Sector Six signed inequality. A weaker wall does not automatically imply an NNS (1/2) contraction.
- **NOT** evidence that the rank-two p*q owner graph has the required bilinear cancellation. Inserting the one-variable (7/8) error independently into (asymp A/log A) columns only gives an absolute error on the order of (A^{15/8}), not (Alog A).
- **NOT** a port of all 2,924 or more OpenAI modules to Lean 4.24.

## Actual new analytic research seams

1. **Classical explicit-formula bridge:** Prove `VFMidSevenEighthsExplicitFormulaBridge` with the published zeta zero-free theorem (on a compatible Lean 4.34 OAI environment) and transfer the resulting `π-Li` statement into the RH_Lean normalization.
2. **Optionally strengthen from `ψ` to `π`:** first establish ( |psi(x)-x| ll x^{7/8}log^2 x ), then derive the prime-Li estimate via actual prime powers and Abel summation. Do not label this as established without a kernel proof.
3. **True owner bilinear route:** seek a signed *joint* bound on (sum_{A<p<B} [pi((B^2-1)/p)-pi(p)]) with the ORIGINAL physical (w_{lfloorsqrt{pq}floor}) tags and all historical Gram cross terms. Pointwise substitution of a (7/8) theorem cannot close RH-scale payment.

## Reproduce

```sh
lake env lean -DwarningAsError=true -o .lake/build/lib/lean/research.VF_MID_VON_KOCH_BRIDGE.olean research/VF_MID_VON_KOCH_BRIDGE.lean
lake env lean -DwarningAsError=true -o .lake/build/lib/lean/research.VF_MID_LI_UNIFORM_QUADRATURE.olean research/VF_MID_LI_UNIFORM_QUADRATURE.lean
lake env lean -DwarningAsError=true -o .lake/build/lib/lean/research.VF_MID_SEVEN_EIGHTHS_ANALYTIC_BRIDGE.olean research/VF_MID_SEVEN_EIGHTHS_ANALYTIC_BRIDGE.lean
```

The pull-request workflow runs these commands on Lean 4.24 with no StrongPNT/PNT5 dependency compilation and separately checks the external public source's toolchain and theorem name.

**Merge policy:** merge the provable, honest interface/proof after green CI; do NOT replace the unresolved analytic transfer by an unproved local axiom or treat the conditional result as unconditional.

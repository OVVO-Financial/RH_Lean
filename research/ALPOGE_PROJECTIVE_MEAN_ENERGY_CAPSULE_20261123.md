# Attaching mean energy to the actual projective trace family

Status: source-reviewed mathematical proof and implementation capsule; the new projective transport declarations below are **not yet Lean-verified**. No local Lean was run. This file does not claim a universal `Gz` bound.

Source checkpoint: PR #1197, integrating main `ff00d98d0a54c4c47017b036dda2c4e8afc6150d` and the actual #1194 geometric source at `2eee27648b7bc24e20bdae068a28bcdc2b9f8b66`. The two finite mean-energy/translation modules already submitted in #1197 are unchanged by this capsule.

## 1. Exact theorem to add

The useful replacement for `AlpogeAllPlace.GlobalTheory.DescentFamily.descent` has its existing hypotheses, except that its collective norm hypothesis is replaced by the **individual** bound

\[
  N_B(\sigma,\phi_h f)\le e^P N_A(\sigma,f).
\]

Keep the actual projective `𝓞 K`-submodules `A`, `B`, their finite generation, `A ≠ ⊥`, integral inclusion `φ_h(A) ⊆ B`, joint injectivity, the actual short spanning set of `B`, and

\[
q\,\mathrm{rk}_K B\le(1+\delta)\mathrm{rk}_K A.
\]

Its improved conclusion is

\[
t\le\operatorname{slope}_{sq}(A)-2P-\log(1+\delta)
\quad\Longrightarrow\quad
\operatorname{slope}_{sq}(B)\ge t-\delta(|t|+2\Lambda).
\]

This declaration has **no mean-energy premise**, no `𝓞 K`-freeness premise, and no new height normalization. Its energy estimate must be derived from the displayed individual map bounds and rank saturation.

For `NativeRegularCharacterSlopeDescent.nativeAllPlaceDescent_of_regular_groupDet`, use the already constructed `φH`, its proved `hφIntegral`, its proved `hφInj`, and its proved `hRankB`. Its individual norm is

\[
N_B(\sigma,\phi_hf)\le q e^{Cz^9}N_A(\sigma,f),
\]

directly from its equality `hφ`, `nativeCharacterTrace_norm_le`, and the supplied multiplication bound `hM`. Thus the squared-slope price becomes

\[
2\log q+2Cz^9+\log(1+\delta).
\]

The previous sufficient joint-operator price was `3 log q + 2 C z^9`. The saving is `log(q/(1+δ))` when positive. Under `log q ≤ 45 z²`, the corresponding displayed ledger changes from `135 z² + 2 C z⁹` to `90 z² + 2 C z⁹ + log(1+δ)`. This removes a map-count logarithm; it does not remove the section cost or prove a stronger global exponent.

## 2. No freeness gap: use the actual real lattices

Choose the existing `GramFr` witnesses `b,X` and `b',X'` of `NA,NB`. Set

\[
\rho_A=\operatorname{realize}(b,X),\quad
\rho_B=\operatorname{realize}(b',X'),\quad
L_A=\operatorname{zl}(\rho_A,A),\quad L_B=\operatorname{zl}(\rho_B,B),
\]

and let `U = span ℝ (L_A : Set _)`, `W = span ℝ (L_B : Set _)` with their inherited inner products. These are the **original** all-place realizations. `place_lattice_structure` proves discreteness and

\[
\operatorname{rk}_{\mathbb Z}L_A=d_K\operatorname{rk}_K A,
\qquad
\operatorname{rk}_{\mathbb Z}L_B=d_K\operatorname{rk}_K B,
\quad d_K=[K:\mathbb Q].
\]

The public theorem `F.rank_eq_finrank_span` in `LatticeSlopesProofs/SaturationProperties.lean` identifies these ranks with the real dimensions of `U,W`. The private rank lemma in `SlopeInequality.lean` need not be exposed or duplicated.

For each actual `φ_h`, define the ambient real map by

```lean
HN.htImageMap (HN.htImageMat b X b' X' (φ h))
```

`HN.htImage_map_realize` proves its value on `ρ_A f` is exactly `ρ_B (φ_h f)`. `HN.htImage_mem_zl` and the original integral inclusion prove it maps `L_A` into `L_B`; taking real spans restricts it to `T_h : U →ₗ[ℝ] W`.

The actual pointwise estimate and `AllWt.norm_realize_sq` give

\[
\|T_h(\rho_A f)\|^2
=\sum_v N_B(v,\phi_hf)^2
\le e^{2P}\sum_vN_A(v,f)^2
=e^{2P}\|\rho_Af\|^2.
\]

Use a genuine `ℤ`-basis of `L_A`, and `F.norm_sum_smul_le_of_int` in `LatticeSlopesProofs/SlopeInequality.lean`, to extend this inequality from lattice points to all of `U`. Its hypotheses are exactly bounds for all integer combinations of the basis, which hold by the same original pointwise bound. This introduces no field-density or freeness assumption.

## 3. The finite real Hilbert lemma needed

For finite-dimensional real Hilbert spaces `U,W`, a finite family `T_h : U →ₗ[ℝ] W`, an orthonormal basis `e` of `U`, and `∀ h x, ‖T_h x‖ ≤ exp P * ‖x‖`, prove

\[
\sum_{h,i}\|T_he_i\|^2
\le q\dim(W)e^{2P}.
\]

There is an elementary proof with the adjoint: for any unit target vector `v`, Cauchy–Schwarz and the original bound applied to `T_h^*v` give `‖T_h^*v‖ ≤ exp P`; Parseval then swaps the source/target basis sums. Alternatively use the conjugate-row argument already formalized over `ℂ` in `NativeMeanEnergyDescent.row_energy_le_of_operator_energy`; its real version omits conjugation.

For the actual joint map `F : U →ₗ[ℝ] W^q`, with the Hilbert product metric, rank saturation now gives

\[
\sum_i\|Fe_i\|^2\le(1+\delta)\dim(U)e^{2P}.
\]

The factor `d_K` cancels from `q dim(W) ≤ (1+δ) dim(U)`. Hadamard plus AM–GM gives

\[
F.\operatorname{normDet}^2
\le((1+\delta)e^{2P})^{\dim U},
\quad
F.\operatorname{normDet}
\le e^{(P+\frac12\log(1+\delta))\dim U}.
\]

The field-specific complex version is already in `NativeMeanEnergyDescent`; a small real counterpart and exact Gram-to-`normDet` conversion are still required. No operator inequality with `(1+δ)e^{2P}` as the joint squared operator bound is asserted: it is false in general.

## 4. Exact covolume bridge, with every integral index retained

The required reusable real-lattice lemma is the equality

```text
covol (L.map (φ.restrictScalars ℤ))
  = (φ.domRestrict (span ℝ (L : Set E))).normDet * covol L
```

for a discrete `ℤ`-lattice `L`, a real linear map `φ` injective on `L`, and discrete actual image lattice. The conclusion is about `L.map φ`, not the saturation of that image.

It is enough to adapt approximately 50–100 lines of existing proof:

1. Define the actual map `L →ₗ[ℤ] L.map φ` by `LinearMap.codRestrict`. It is bijective onto its image by the stated injectivity. Use `LinearEquiv.ofBijective`.
2. Take `u = Module.finBasis ℤ L`. Its image under that equivalence is a `ℤ`-basis of the actual image. Apply `F.covolEqGram` (or its lowercase proved version `F.covol_eq_gram`) to both bases.
3. `F.det_gram_eq_normDet_sq` in `LatticeSlopesProofs/GramDetLe.lean` expresses both Gram determinants as squared `normDet`s of `F.linearCombinationMap`.
4. Prove `linearCombinationMap (φ ∘ u) = φ ∘ₗ linearCombinationMap u` by linearity. Apply **`LinearMap.normDet_comp`**, already used in `F.gram_det_le`.
5. The range of `linearCombinationMap u` is the real span of `L`; use `F.span_range_coe_basis'` and `Submodule.span_span_of_tower`, or identify the range directly. The restriction in `normDet_comp` is therefore the required actual-span restriction.
6. Take square roots using nonnegativity of `normDet` and covolumes. There is no discarded determinant or finite-index factor: it is absorbed exactly in `covol (L.map φ)`.

For the native joint trace, discreteness of the image follows from its inclusion in the realized `B^q`; injectivity follows from `hφInj` and `HN.htImage_realize_eq_zero`. The actual product realization has the same norm as the Hilbert direct sum by `norm_realize_sq` and `DescentFamily.normAt_pi_sq`.

This route is shorter than editing the general quotient proof in `HtImage.lean`. In that file the coarse step is exactly its `have hG := (h3 ...).1` after `hcovQ` and `hcovI`. Replacing only that line is insufficient because the current `GramBlock` interface knows only the operator norm of each whole place block, not the target ranks of the individual trace summands. The injective joint-map route avoids that quotient and place-block machinery entirely.

## 5. Finish the original projective slope proof

The preceding two lemmas imply, on the actual source and image `I`,

\[
\operatorname{covol}(I)
\le e^{(P+\frac12\log(1+\delta))d_Kr}\operatorname{covol}(A),
\]

so

\[
2\operatorname{slope}(I)
\ge2\operatorname{slope}(A)-2P-\log(1+\delta).
\]

The `muDef` field/discriminant constant cancels between source and image of the same rank. It is not deleted from either definition. Copy the remainder of `ExtensionFiltration.descent_slope` after its call to `slope_image_injective`, retaining its saturation/target-min-slope argument. This gives

\[
r(\mu_A-2P-\log(1+\delta))+(qs-r)\mu_{\min}(B)
\le qs\mu_B.
\]

Then copy `DescentFamily.descent`'s unchanged construction of `B^q`, `power_slope_mu`, and the actual short spanning set proof of `muMinDef ≥ -2Λ`. Apply the existing `DescentFamily.numeric` with

\[
P_{\mathrm{eff}}=P+\tfrac12\log(1+\delta).
\]

This closes the stated improved projective descent from existing individual map bounds; no new energy estimate is assumed.

## 6. Alternative per-place supplier already present

If a complex-first implementation is preferred, `TheoremFSharp.thmF_place` already provides a source-checked template for all the actual projective span constructions:

- `Nτ` and `T`: the Euclidean complex spans of the original coordinate images, obtained by mapping through `(WithLp.linearEquiv 2 ℂ _).symm`.
- `hNτ`, `hT`: their dimensions equal `rkK` by `PlaceDecomposition.finrank_span_complex`.
- `hST`: actual integral inclusion implies inclusion of these spans; use `PlaceOperatorNorms.fcoord_map`.

`L2.Geo.ExtensionFiltration.opNormAt_le_of_points` in `OperatorNormFibers/PDescentCutA.lean` already converts the individual `qB` bound on field vectors into the full actual complex Gram-frame operator bound. Thus no new norm-density lemma is missing. Restrict to the actual spans and use orthonormal coordinates with `NativeMeanEnergyDescent.jointMapMatrix_gram_det_le_of_rank_saturation`.

The real-lattice route in Sections 2–5 is preferable for the first complete projective descent proof because it preserves the actual all-place covolume directly and avoids an additional complex-block-to-real determinant product lemma.

## 7. Exact remaining boundary

The mathematical projective attachment is valid and uses the same section/maps/ranks; its new formal declarations are still open. The already submitted finite integral descent proves a genuine volume improvement and sharp finite model, but does not yet instantiate the projective theorem above. Neither this volume saving nor its future projective instantiation supplies the complete signed native ASK/MAIN/thin payment or universal `Gz` estimate. The next arithmetic step must still connect the same growing geometric family to the complete original signed source and its derived normalizer.

import Mathlib

/-!
# Quadratic unit norms over genuine Henselian local rings

This reconstructs the `Quad` section of
`Formalism/HermitianLattices/HermitianLatticesProofs/UnimodUnramUnique.lean`
by Levent Alpöge (with Claude), from `CocoSgt/riemann-hypothesis-lean`
at source commit `7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
Its unused `StatementJac` dependency is omitted: finite-field quadratic
representation and Hensel lifting use only Mathlib.

The main theorem constructs `s,t` with `s² + T*s*t + N*t² = d` from a unit
`d` and unit discriminant. In particular it supplies the exact local
norm-minus-one equation consumed by the original `Adelic.adicInt_exists_norm`.
It assumes no represented-value witness, Hermitian isometry or geometric datum.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false

noncomputable section

namespace RHLean.Geometry.NativeLocalQuadraticNorm

open Polynomial IsLocalRing

section Quad

variable {S : Type*} [CommRing S] [HenselianLocalRing S]

theorem lift_quadratic (T N d s₀ t₀ : S)
    (h0 : s₀ ^ 2 + T * s₀ * t₀ + N * t₀ ^ 2 - d ∈ maximalIdeal S)
    (h1 : IsUnit (2 * s₀ + T * t₀)) :
    ∃ s t : S, s ^ 2 + T * s * t + N * t ^ 2 = d := by
  set f : S[X] := X ^ 2 + C (T * t₀) * X + C (N * t₀ ^ 2 - d) with hfdef
  have hf : f.Monic := by rw [hfdef]; monicity!
  have he : f.eval s₀ = s₀ ^ 2 + T * s₀ * t₀ + N * t₀ ^ 2 - d := by
    rw [hfdef]; simp; ring
  have hd : f.derivative.eval s₀ = 2 * s₀ + T * t₀ := by
    rw [hfdef]; simp only [derivative_add, derivative_C, derivative_X_pow, derivative_C_mul_X, add_zero]
    simp
  obtain ⟨s, hs, -⟩ := HenselianLocalRing.is_henselian f hf s₀ (he ▸ h0) (hd ▸ h1)
  refine ⟨s, t₀, ?_⟩
  have h2 : f.eval s = 0 := hs
  rw [hfdef] at h2
  simp at h2
  linear_combination h2

omit [HenselianLocalRing S] in
theorem split_quadratic (T N d r : S) (hr : r ^ 2 + T * r + N = 0)
    (hu : IsUnit (T + 2 * r)) : ∃ s t : S, s ^ 2 + T * s * t + N * t ^ 2 = d := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  refine ⟨1 + r * ((d - 1) * v), (d - 1) * v, ?_⟩
  linear_combination ((d - 1) * v) ^ 2 * hr + (d - 1) * hv

theorem finiteField_quadratic {k : Type*} [Field k] [Finite k] (T N d : k)
    (hD : T ^ 2 - 4 * N ≠ 0) : ∃ a b : k, a ^ 2 + T * a * b + N * b ^ 2 = d := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  rcases Nat.mod_two_eq_zero_or_one (Fintype.card k) with h | h
  · obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (FiniteField.even_card_iff_char_two.2 h) d
    exact ⟨c, 0, by rw [hc]; ring⟩
  · have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero (fun hc => by
      rw [FiniteField.even_card_iff_char_two.1 hc] at h; exact absurd h (by decide))
    have hf : (X ^ 2 : k[X]).degree = 2 := by compute_degree!
    have hg : (C (-(T ^ 2 - 4 * N)) * X ^ 2 + C (-(4 * d)) : k[X]).degree = 2 := by
      compute_degree!
      intro h; exact hD (by linear_combination -h)
    obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg h
    simp at hxy
    refine ⟨(x - T * y) / 2, y, ?_⟩
    field_simp
    linear_combination hxy

theorem henselian_quadratic_unit [Finite (ResidueField S)] (T N d : S)
    (hD : IsUnit (T ^ 2 - 4 * N)) (hd : IsUnit d) :
    ∃ s t : S, s ^ 2 + T * s * t + N * t ^ 2 = d := by
  have hD' : residue S (T ^ 2 - 4 * N) ≠ 0 := (residue_ne_zero_iff_isUnit _).2 hD
  have h2 : residue S 2 = 2 := map_ofNat _ 2
  have h4 : residue S 4 = 4 := map_ofNat _ 4
  by_cases hroot : ∃ ρ : ResidueField S, ρ ^ 2 + residue S T * ρ + residue S N = 0
  · obtain ⟨ρ, hρ⟩ := hroot
    obtain ⟨r₀, rfl⟩ := residue_surjective ρ
    set g : S[X] := X ^ 2 + C T * X + C N with hgdef
    have hg : g.Monic := by rw [hgdef]; monicity!
    have he : g.eval r₀ = r₀ ^ 2 + T * r₀ + N := by rw [hgdef]; simp
    have hd1 : g.derivative.eval r₀ = 2 * r₀ + T := by
      rw [hgdef]
      simp only [derivative_add, derivative_C, derivative_X_pow, derivative_C_mul_X, add_zero]
      simp
    have hsq : (2 * r₀ + T) ^ 2 = (T ^ 2 - 4 * N) + 4 * (r₀ ^ 2 + T * r₀ + N) := by ring
    have h0 : g.eval r₀ ∈ maximalIdeal S := by
      rw [he, ← residue_eq_zero_iff]; simpa using hρ
    have h1 : IsUnit (g.derivative.eval r₀) := by
      rw [hd1, ← residue_ne_zero_iff_isUnit]
      intro hz
      apply hD'
      have key : residue S (T ^ 2 - 4 * N) = (residue S (2 * r₀ + T)) ^ 2
          - 4 * residue S (r₀ ^ 2 + T * r₀ + N) := by
        rw [← map_pow, ← map_ofNat (residue S) 4, ← map_mul, ← map_sub]
        congr 1; linear_combination -hsq
      have hz2 : residue S (r₀ ^ 2 + T * r₀ + N) = 0 := (residue_eq_zero_iff _).2 (he ▸ h0)
      rw [key, hz, hz2]; ring
    obtain ⟨r, hr, -⟩ := HenselianLocalRing.is_henselian g hg r₀ h0 h1
    have hr' : r ^ 2 + T * r + N = 0 := by
      have h2 : g.eval r = 0 := hr
      rw [hgdef] at h2; simpa using h2
    apply split_quadratic T N d r hr'
    have : (T + 2 * r) ^ 2 = T ^ 2 - 4 * N := by linear_combination 4 * hr'
    rw [← isUnit_pow_iff (two_ne_zero), this]; exact hD
  · push Not at hroot
    have hN : IsUnit N := by
      rw [← residue_ne_zero_iff_isUnit]
      intro h; exact hroot 0 (by simp [h])
    obtain ⟨a, b, hab⟩ := finiteField_quadratic (residue S T) (residue S N) (residue S d)
      (by simpa [h4] using hD')
    obtain ⟨s₀, rfl⟩ := residue_surjective a
    obtain ⟨t₀, rfl⟩ := residue_surjective b
    have h0 : s₀ ^ 2 + T * s₀ * t₀ + N * t₀ ^ 2 - d ∈ maximalIdeal S := by
      rw [← residue_eq_zero_iff]; simp only [map_sub, map_add, map_mul, map_pow]
      rw [hab]; ring
    by_cases hs : IsUnit (2 * s₀ + T * t₀)
    · exact lift_quadratic T N d s₀ t₀ h0 hs
    ·
      have ht : IsUnit (T * s₀ + 2 * N * t₀) := by
        rw [← residue_ne_zero_iff_isUnit]
        rw [← residue_ne_zero_iff_isUnit, not_not] at hs
        intro ht
        have hs' := hs
        simp only [map_add, map_mul, h2] at hs' ht
        have hdz : residue S d ≠ 0 := (residue_ne_zero_iff_isUnit _).2 hd
        apply hdz
        rw [← hab]
        have hDk : residue S T ^ 2 - 4 * residue S N ≠ 0 := by simpa [h4] using hD'
        have htz : residue S t₀ = 0 := by
          have : (residue S T ^ 2 - 4 * residue S N) * residue S t₀ = 0 := by
            linear_combination residue S T * hs' - 2 * ht
          rcases mul_eq_zero.1 this with h | h
          · exact absurd h hDk
          · exact h
        have hsz : residue S s₀ = 0 := by
          have : (residue S T ^ 2 - 4 * residue S N) * residue S s₀ = 0 := by
            linear_combination residue S T * ht - 2 * residue S N * hs'
          rcases mul_eq_zero.1 this with h | h
          · exact absurd h hDk
          · exact h
        simp [htz, hsz]
      obtain ⟨v, hv⟩ := hN.exists_right_inv
      obtain ⟨t, s, hts⟩ := lift_quadratic (T * v) v (d * v) t₀ s₀
        (by
          have : t₀ ^ 2 + T * v * t₀ * s₀ + v * s₀ ^ 2 - d * v
              = v * (s₀ ^ 2 + T * s₀ * t₀ + N * t₀ ^ 2 - d) + (1 - N * v) * t₀ ^ 2 := by ring
          rw [this, hv, sub_self, zero_mul, add_zero]
          exact Ideal.mul_mem_left _ _ h0)
        (by
          have : 2 * t₀ + T * v * s₀ = v * (T * s₀ + 2 * N * t₀) + (1 - N * v) * (2 * t₀) := by ring
          rw [this, hv, sub_self, zero_mul, add_zero]
          exact (isUnit_iff_exists_inv.2 ⟨N, by rw [mul_comm]; exact hv⟩).mul ht)
      exact ⟨s, t, by linear_combination N * hts - (T * s * t + s ^ 2 - d) * hv⟩

end Quad

/-- The local unit-norm equation needed in the finite-adelic construction. -/
theorem henselian_quadratic_neg_one
    {S : Type*} [CommRing S] [HenselianLocalRing S] [Finite (ResidueField S)]
    (T N : S) (hD : IsUnit (T ^ 2 - 4 * N)) :
    ∃ s t : S, s ^ 2 + T * s * t + N * t ^ 2 = -1 :=
  henselian_quadratic_unit T N (-1) hD isUnit_one.neg

end RHLean.Geometry.NativeLocalQuadraticNorm

end

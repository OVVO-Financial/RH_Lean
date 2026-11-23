import RHLean.Analysis.AlpogeThin.NativeHostThin

/-!
# Selected principal pairs pay every native dyadic primitive thin channel

This specialization removes the number-field HostRaw interface from the thin
application. The original selected q,d and their real-character boxes give a
uniform exceptional-zero exclusion for all primitive conductors dividing
2^k*q*d, for every k. A real primitive character has a base conductor dividing
eight and the actual q,d twist decomposition. The bounded base family is paid
by the proved small-zero theorem; the other three twist types are paid by the
boxes of the same selected pair.

The final theorem constructs the pair and applies the proved thin estimate to
the existing native arithmetic response, retaining the actual ell constant.
Neither NoExc, PairGood, nor a number-field host is an assumed supplier.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open scoped Classical

namespace RHLean.Analysis.AlpogeThin

private theorem principalThin_isReal_of_sq {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (h2 : χ ^ 2 = 1) (a : ZMod N) :
    (χ a).im = 0 := by
  by_cases ha : IsUnit a
  · have h := congrArg (fun f : DirichletCharacter ℂ N => f a) h2
    simp only [pow_two, MulChar.one_apply ha] at h
    rw [MulChar.mul_apply] at h
    have hz : χ a = 1 ∨ χ a = -1 := by
      have he : (χ a - 1) * (χ a + 1) = 0 := by
        ring_nf
        rw [← pow_two] at h
        rw [h]
        ring
      rcases mul_eq_zero.1 he with h1 | h1
      · left
        linear_combination h1
      · right
        linear_combination h1
    rcases hz with hz | hz <;> simp [hz]
  · simp [MulChar.map_nonunit χ ha]

private theorem principalThin_coprime_of_dyadic_dvd
    {a N k q d : ℕ} (hN : N ∣ 2 ^ k * q * d)
    (ha : a.Coprime (2 * 1 * q * d)) : a.Coprime N := by
  have ha' : a.Coprime (2 * q * d) := by simpa using ha
  have h2 : a.Coprime 2 :=
    Nat.Coprime.coprime_dvd_right ⟨q * d, by ring⟩ ha'
  have hq : a.Coprime q :=
    Nat.Coprime.coprime_dvd_right ⟨2 * d, by ring⟩ ha'
  have hd : a.Coprime d :=
    Nat.Coprime.coprime_dvd_right ⟨2 * q, by ring⟩ ha'
  exact Nat.Coprime.coprime_dvd_right hN
    (((h2.pow_right k).mul_right hq).mul_right hd)

/-- The same selected-pair boxes give one actual exclusion width, uniform over
all dyadic exponents and all primitive real characters in the native modulus.
The finite base-character width is constructed by QH.small_zeros 8. -/
theorem principalPair_uniform_noExc :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (eps Y X : ℝ) (q d : ℕ),
        UpperTheory.Top.PairGood 1 eps Y X q d →
        ∀ (k N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
          χ.IsPrimitive → N ∣ 2 ^ k * q * d →
          χ ^ 2 = 1 → χ ≠ 1 → QH.NoExc c₀ χ := by
  obtain ⟨c, hc, hsmall⟩ := QH.small_zeros 8
  refine ⟨min c (1 / 400), lt_min hc (by norm_num), ?_⟩
  intro eps Y X q d hG k N _ χ hp hN h2 hne
  have hq := hG.pair.q_prime
  have hd := hG.pair.d_prime
  have hq2 : q ≠ 2 := by
    intro h
    have hm := hG.pair.q_mod
    rw [h] at hm
    norm_num at hm
  have hd2 : d ≠ 2 := by
    intro h
    have hm := hG.pair.d_mod
    rw [h] at hm
    norm_num at hm
  have hqd : q ≠ d := by
    intro h
    have hm := hG.pair.q_mod
    have hm' := hG.pair.d_mod
    rw [h] at hm
    omega
  have hcop : Nat.Coprime (2 ^ k) (q * d) :=
    (((Nat.coprime_primes Nat.prime_two hq).2 hq2.symm).mul_right
      ((Nat.coprime_primes Nat.prime_two hd).2 hd2.symm)).pow_left k
  have hreal : (Formalism.HC.PChar.mk N χ hp).IsReal :=
    principalThin_isReal_of_sq χ h2
  obtain ⟨ρ, i, j, hρr, hρN, hrepr, hval⟩ :=
    UpperTheory.Top.realSplit (Formalism.HC.PChar.mk N χ hp)
      (2 ^ k) q d hreal (by positivity) hq hd hq2 hd2 hqd hcop hN
  have hρ8 : ρ.N ∣ 8 := by
    simpa only [Nat.ordCompl_self_pow Nat.prime_two, mul_one] using hρN
  change N = ρ.N * q ^ (i : ℕ) * d ^ (j : ℕ) at hrepr
  by_cases hz : i = 0 ∧ j = 0
  · obtain ⟨hi, hj⟩ := hz
    have hN8 : N ≤ 8 := by
      have hNr : N = ρ.N := by simpa [hi, hj] using hrepr
      rw [hNr]
      exact Nat.le_of_dvd (by norm_num) hρ8
    intro β hβ hβ1
    exact hsmall N χ hN8 hne β
      (by have := min_le_left c (1 / 400); linarith) hβ1
  · have hij : i ≠ 0 ∨ j ≠ 0 := by
      by_cases hi : i = 0
      · exact Or.inr (fun hj => hz ⟨hi, hj⟩)
      · exact Or.inl hi
    have hind : Formalism.HC.An.Induces χ
        (UpperTheory.Top.tw ρ.val q d i j) (2 * 1 * q * d) := by
      refine ⟨hp, fun a ha => ?_⟩
      exact hval a (principalThin_coprime_of_dyadic_dvd hN ha)
    have hbox := hG.boxes ρ hρr (by simpa using hρ8) i j hij N χ hind
    intro β hβ _hβ1
    refine hbox (β : ℂ) ?_ ?_
    · have hmin := min_le_right c (1 / 400)
      simp only [Complex.ofReal_re]
      linarith
    · simp only [Complex.ofReal_im, abs_zero]
      unfold UpperTheory.Top.height
      positivity

/-- Constructed q,d simultaneously pay every primitive thin character whose
conductor divides the native modulus 2^k*q*d. The host size and dyadic exponent
remain arbitrary; no finite host or arithmetic channel is replaced by one.

This is the original complete thin estimate, now on the exact native response
and with the exceptional-zero premise discharged by the constructed pair. -/
theorem nativePrincipalSelectedPairThin
    (eps A : ℝ) (he : 0 < eps) (he52 : eps < 1 / 52) (hA : 1 ≤ A) :
    ∃ Y₀ x₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∃ q d : ℕ, UpperTheory.Top.PairGood 1 eps Y (Y ^ A) q d ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ (k N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
            χ.IsPrimitive → N ∣ 2 ^ k * q * d →
            Real.log N ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 →
            ∀ y : ℝ, Real.exp (x ^ (eps / 3)) / 3 ≤ y →
              ‖nativeResponse χ y‖ ≤ y * Real.exp (-(x ^ (eps / 8))) := by
  obtain ⟨c₀, hc₀, hnoExc⟩ := principalPair_uniform_noExc
  obtain ⟨x₀, hthin⟩ := QH.thin eps 2 1 c₀ he two_pos one_pos hc₀
  obtain ⟨Y₀, hpair⟩ := QH.pairEx 1 (by norm_num) eps A he he52 hA
  refine ⟨Y₀, x₀, fun Y hY => ?_⟩
  obtain ⟨q, d, hG⟩ := hpair Y hY
  refine ⟨q, d, hG, ?_⟩
  intro x hx k N _ χ hp hN hlog y hy
  have hb := hthin x hx N χ hp hlog
    (hnoExc eps Y (Y ^ A) q d hG k N χ hp hN) y hy
  rw [G0_eq_nativeResponse] at hb
  simpa only [one_mul] using hb

end RHLean.Analysis.AlpogeThin

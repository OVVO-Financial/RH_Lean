import RHLean.Analysis.AlpogeThin.Development.AutomorphicArithmetic.MeanSquareBounds.GaussSumFunctionEq
import RHLean.Analysis.AlpogeThin.Development.AutomorphicArithmetic.CharacterBoxes.RealBox
import RHLean.Analysis.AlpogeThin.Development.AutomorphicArithmetic.MeanSquareBounds.pairEx
import RHLean.Analysis.AlpogeNativeFourCharacterArithmetic

/-!
# Constructed pairs and the complete native thin response on the same host

The selected primes are supplied by the reconstructed proof of QH.pairEx.
Its real-character boxes, for those same primes, imply RealBox for every
compatible host. QH.thinH supplies the uniform thin estimate, using these
boxes and the bounded-conductor small-zero theorem to discharge NoExc.

The response below uses the existing native Gz/Gchi arithmetic. Its exact
logarithmic derivative is retained. No exceptional-zero-free hypothesis,
prime-pair existence assumption, or terminal RH theorem is introduced.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open scoped BigOperators Classical

namespace RHLean.Analysis.AlpogeThin

/-- Existing native arithmetic, with the actual primitive log derivative.
The principal branch includes the native Euler-constant normalization. -/
def nativeResponse {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ :=
  if χ = 1 then (RHLean.Analysis.alpogeNativeGzArithmetic y : ℂ)
  else RHLean.Analysis.alpogeNativeGchiArithmetic χ
    (deriv (DirichletCharacter.LFunction χ) 1 /
      DirichletCharacter.LFunction χ 1) y

theorem G1_eq_nativeGz (y : ℝ) :
    Formalism.HermitianLattices.ZeroFreeRegionGL2.G1 y =
      RHLean.Analysis.alpogeNativeGzArithmetic y := by
  rw [RHLean.Analysis.alpogeNativeGzArithmetic_eq_principal]
  unfold Formalism.HermitianLattices.ZeroFreeRegionGL2.G1
    RHLean.Analysis.alpogeNativePrincipalPrimeSum
    RHLean.Analysis.alpogeNativePrimePowerWeight
  ring

theorem Gchi_eq_nativeGchi {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (y : ℝ) :
    Formalism.HermitianLattices.ZeroFreeRegionGL2.Gchi χ y =
      RHLean.Analysis.alpogeNativeGchiArithmetic χ
        (deriv (DirichletCharacter.LFunction χ) 1 /
          DirichletCharacter.LFunction χ 1) y := by
  unfold Formalism.HermitianLattices.ZeroFreeRegionGL2.Gchi
    Formalism.HermitianLattices.ZeroFreeRegionGL2.logDerivLAtOne
    RHLean.Analysis.alpogeNativeGchiArithmetic
    RHLean.Analysis.alpogeNativeTwistedPrimeSum
  congr 1
  apply Finset.sum_congr rfl
  intro n _hn
  unfold RHLean.Analysis.alpogeNativePrimePowerWeight
  push_cast
  ring

theorem G0_eq_nativeResponse {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (y : ℝ) :
    QH.G0 χ y = nativeResponse χ y := by
  unfold QH.G0 nativeResponse
  split_ifs
  · rw [G1_eq_nativeGz]
  · exact Gchi_eq_nativeGchi χ y

/-- The original host response is exactly the native response, including all
prime powers at its original cutoff. No positivity assumption on y is needed. -/
theorem hostResponse_eq_nativeResponse {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (y : ℝ) :
    Formalism.HC.An.gChi χ y = nativeResponse χ y := by
  have hcut : ∀ n ∈ Finset.Icc 1 ⌊y⌋₊,
      max (y / (n : ℝ) - 1) 0 = y / n - 1 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hy1 : 1 ≤ y := Nat.floor_pos.1 (by omega)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hny : (n : ℝ) ≤ y :=
      (Nat.cast_le.2 hn.2).trans (Nat.floor_le (by linarith))
    have hquot : 1 ≤ y / n := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    exact max_eq_left (by linarith)
  rw [← G0_eq_nativeResponse]
  unfold Formalism.HC.An.gChi QH.G0
  by_cases h : χ = 1
  · simp only [h, ite_true]
    congr 1
    unfold Formalism.HC.An.G
      Formalism.HermitianLattices.ZeroFreeRegionGL2.G1
    congr 1
    exact Finset.sum_congr rfl fun n hn => by rw [hcut n hn]
  · simp only [h, ite_false]
    unfold Formalism.HC.An.sumLamChi
      Formalism.HermitianLattices.ZeroFreeRegionGL2.Gchi
    congr 1
    exact Finset.sum_congr rfl fun n hn => by rw [hcut n hn]

/-- Actual selected prime pairs supply the real-character exclusions for every
compatible host with those same q,d. The resulting thin bound is simultaneous
over every primitive character of that host and every thin argument.

The existential c is fixed before all scale, modulus, and host choices.
Neither NoExc nor PairGood is an input hypothesis. -/
theorem nativeSelectedPairThin :
    ∃ c : ℝ, 0 < c ∧
      ∀ (M : ℕ), 0 < M → ∀ eps A B : ℝ,
        0 < eps → eps < 1 / 52 → 1 ≤ A →
        ∃ Y₀ x₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
          ∃ q d : ℕ,
            UpperTheory.Top.PairGood M eps Y (Y ^ A) q d ∧
            ∀ x : ℝ, x₀ ≤ x →
              ∀ (φ : Formalism.HC.Frame) (H : Formalism.HC.HostRaw φ),
                H.q = q → H.d = d →
                ((ordCompl[2] H.QS : ℕ) : ℝ) ≤ B →
                Real.log (H.condN : ℝ) ≤
                  2 * x ^ (eps / 5) * Real.log x ^ 2 →
                (∀ l : ℕ, l.Prime → l ∣ H.QS → l ∣ 2 * M) →
                ordCompl[2] H.QS ∣ M →
                ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
                  H.IsCharE χ → ∀ y : ℝ,
                    Real.exp (x ^ (eps / 3)) / 3 ≤ y →
                    ‖nativeResponse χ y‖ ≤
                      y * Real.exp (-(c * x ^ (eps / 8))) := by
  obtain ⟨c, hc, hthin⟩ := QH.thinH
  refine ⟨c, hc, ?_⟩
  intro M hM eps A B he he52 hA
  obtain ⟨Y₀, hpair⟩ := QH.pairEx M hM eps A he he52 hA
  obtain ⟨x₀, hthin⟩ := hthin B eps he he52
  refine ⟨Y₀, x₀, fun Y hY => ?_⟩
  obtain ⟨q, d, hG⟩ := hpair Y hY
  refine ⟨q, d, hG, ?_⟩
  intro x hx φ H hq hd hB hlog hpr hodd N _ χ hχ y hy
  have hG' : UpperTheory.Top.PairGood M eps Y (Y ^ A) H.q H.d := by
    simpa only [hq, hd] using hG
  have hbox :=
    (UpperTheory.Top.realBox M φ H eps Y (Y ^ A) hM hpr hodd hG').2
  have hbound := hthin x hx φ H hB hlog hbox N χ hχ y hy
  rw [hostResponse_eq_nativeResponse] at hbound
  exact hbound

end RHLean.Analysis.AlpogeThin

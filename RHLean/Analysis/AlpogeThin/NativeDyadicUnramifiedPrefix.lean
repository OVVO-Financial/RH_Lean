import RHLean.Analysis.AlpogeThin.NativeDyadicPrimePowerIncidence
import RHLean.Analysis.AlpogeThin.NativeDyadicHostPrimePowerWeights
import RHLean.Analysis.AlpogeThin.Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN
import Mathlib.Data.Nat.Prime.Int

/-!
# Unramified prime-power colour rows on a PageN prefix

At the native square anchor take `N = R ^ 2 - 1`. The PageN lower
bound places the entire prefix below half the dyadic modulus. Its
unramified prime powers have distinct physical colours simultaneously.
The resulting minor concerns the unrestricted integer colour sites.
-/

set_option autoImplicit false

noncomputable section

namespace RHLean.Analysis.AlpogeThin

/-- Every pair of natural numbers in the prefix has sum below the dyadic modulus. -/
theorem nativeDyadicPageN_prefix_lt_half (N e : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hN : 1 ≤ N) (hPage : UpperTheory.Top.PageN ε (N : ℝ) e) :
    2 * N < 2 ^ (e + 2) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : (N : ℝ) ≤ (2 : ℝ) ^ e := calc
    (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (N : ℝ) ^ (2 + 8 * ε) := Real.rpow_le_rpow_of_exponent_le hN' (by linarith)
    _ ≤ _ := hPage.1
  have hn : N ≤ 2 ^ e := by exact_mod_cast hpow
  have he : 0 < (2 : ℕ) ^ e := pow_pos (by decide) e
  rw [pow_add]
  change 2 * N < 2 ^ e * 4
  omega

/-- Every unramified power in this prefix precedes its first dyadic return. -/
theorem nativeDyadicPageN_prefix_before_return (N e q d p i : ℕ)
    [Fact q.Prime] [Fact d.Prime] {ε : ℝ} (hε : 0 ≤ ε) (hN : 1 ≤ N)
    (hPage : UpperTheory.Top.PageN ε (N : ℝ) e) (hp : p.Prime)
    (hpN : ¬ p ∣ alpogeNativeHostN e q d) (hpi : p ^ i ≤ N) :
    i < addOrderOf ((alpogeNativeHostData e q d).frob p).2 := by
  apply nativeDyadicFrobenius_exp_lt_order_of_short_power e q d p i hp hpN
  have h := nativeDyadicPageN_prefix_lt_half N e hε hN hPage
  omega

/-- All unramified positive prime powers up to `N`, with their base and exponent. -/
def nativeDyadicUnramifiedPrefix (e q d N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (N + 1)).product (Finset.range (N + 1))).filter fun s =>
    s.1.Prime ∧ 0 < s.2 ∧ ¬ s.1 ∣ alpogeNativeHostN e q d ∧ s.1 ^ s.2 ≤ N

theorem mem_nativeDyadicUnramifiedPrefix {e q d N p i : ℕ} :
    (p, i) ∈ nativeDyadicUnramifiedPrefix e q d N ↔
      p.Prime ∧ 0 < i ∧ ¬ p ∣ alpogeNativeHostN e q d ∧ p ^ i ≤ N := by
  simp only [nativeDyadicUnramifiedPrefix, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨⟨?_, ?_⟩, h⟩⟩
  · exact Nat.lt_succ_of_le ((Nat.le_self_pow h.2.1.ne' p).trans h.2.2.2)
  · have hi : i < p ^ i := Nat.lt_pow_self h.1.one_lt
    exact Nat.lt_succ_of_le (hi.le.trans h.2.2.2)

/-- Evaluate each unramified colour row at the representative of another
prefix power. The two prime bases may be different. -/
theorem nativeDyadicPageN_prefix_incidence (N e q d p l i j : ℕ)
    [Fact q.Prime] [Fact d.Prime] {ε : ℝ} (hε : 0 ≤ ε) (hN : 1 ≤ N)
    (hPage : UpperTheory.Top.PageN ε (N : ℝ) e)
    (hs : (p, i) ∈ nativeDyadicUnramifiedPrefix e q d N)
    (ht : (l, j) ∈ nativeDyadicUnramifiedPrefix e q d N) :
    nativeDyadicPrimePowerIncidence e q d p i (j • (alpogeNativeHostData e q d).frob l) =
      if (p, i) = (l, j) then (1 : ℤ) else 0 := by
  classical
  obtain ⟨hp, hi, hpN, hpi⟩ := mem_nativeDyadicUnramifiedPrefix.mp hs
  obtain ⟨hl, hj, hlN, hlj⟩ := mem_nativeDyadicUnramifiedPrefix.mp ht
  let H := alpogeNativeHostData e q d
  have hI : H.inertia p = ⊥ := nativeDyadicHostData_inertia_unramified e q d p hp hpN
  have hmod := nativeDyadicPageN_prefix_lt_half N e hε hN hPage
  have heq : j • H.frob l - i • H.frob p ∈ H.inertia p ↔ (p, i) = (l, j) := by
    rw [hI, AddSubgroup.mem_bot, sub_eq_zero]
    constructor
    · intro hg
      have hproj : i • (H.frob p).2 = j • (H.frob l).2 := congrArg Prod.snd hg.symm
      have hpowers := nativeDyadicPrimePower_eq_of_displacement_eq e q d p l i j hp hl hpN hlN
        (by omega) hproj
      obtain ⟨hpl, hij⟩ := hp.pow_inj' hl hi.ne' hj.ne' hpowers
      exact Prod.ext hpl hij
    · intro hg
      obtain ⟨hpl, hij⟩ := Prod.mk.inj hg
      subst l
      subst j
      rfl
  change (if j • H.frob l - i • H.frob p ∈ H.inertia p then (1 : ℤ) else 0) = _
  rw [heq]

/-- The complete finite unramified prefix has an integer identity minor on
its actual Frobenius representatives, before any geometric section lift. -/
theorem nativeDyadicPageN_unramifiedPrefix_minor (N e q d : ℕ)
    [Fact q.Prime] [Fact d.Prime] {ε : ℝ} (hε : 0 ≤ ε) (hN : 1 ≤ N)
    (hPage : UpperTheory.Top.PageN ε (N : ℝ) e) :
    let S := nativeDyadicUnramifiedPrefix e q d N
    (Matrix.of fun s t : ↥S => nativeDyadicPrimePowerIncidence e q d s.1.1 s.1.2
      (t.1.2 • (alpogeNativeHostData e q d).frob t.1.1)) = (1 : Matrix S S ℤ) := by
  classical
  let S := nativeDyadicUnramifiedPrefix e q d N
  change (Matrix.of fun s t : ↥S => nativeDyadicPrimePowerIncidence e q d s.1.1 s.1.2
    (t.1.2 • (alpogeNativeHostData e q d).frob t.1.1)) = (1 : Matrix S S ℤ)
  ext s t
  change nativeDyadicPrimePowerIncidence e q d s.1.1 s.1.2
    (t.1.2 • (alpogeNativeHostData e q d).frob t.1.1) = (1 : Matrix S S ℤ) s t
  rw [nativeDyadicPageN_prefix_incidence N e q d s.1.1 t.1.1 s.1.2 t.1.2 hε hN hPage s.2 t.2,
    Matrix.one_apply]
  by_cases h : s = t
  · subst t
    simp only [ite_eq_left rfl]
  · have hpair : (s.1.1, s.1.2) ≠ (t.1.1, t.1.2) := fun hst => h (Subtype.ext hst)
    rw [ite_eq_right hpair, ite_eq_right h]

end RHLean.Analysis.AlpogeThin

end

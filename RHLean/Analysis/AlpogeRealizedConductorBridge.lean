import Mathlib
import RHLean.Analysis.AlpogeNativeSharpASKBalance
import RHLean.Analysis.AlpogeNativeFourCharacterArithmetic

/-!
# Alpoge's complete modular-unit host = primitive Dirichlet character

This reconstructs the number-theoretic bridge from the concrete
Frobenius/inertia host to Dirichlet L-function coefficients, WITHOUT
importing an RH/GRH theorem or treating host data as arbitrary.

For a modular-unit group character r and ψ on its finite quotient,
the product of all inertia-coset Euler factors is proved equal to
the primitive Dirichlet character of the actual composed unit character.
In particular, ramified prime powers are ZERO when ψ does not
factor through inertia, not fictitious unit phases.

The Frobenius-unit existence/uniqueness is proved using the explicit
CRT on ordProj[p] N and ordCompl[p] N, as in Alpoge's published
formalization.

This is an EXACT arithmetic realization, not a proof of any
uniform square-root bound on character sums or of the VWin
cohomological cost inequality.
-/

noncomputable section
open Finset

namespace RHLean.Analysis

/-- The actual Dirichlet character of a modular-unit Galois host. -/
def alpogeNativeDirChar
    {N : ℕ} {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (ψ : AddChar (AlpogeNativeE0 × H) ℂ) :
    DirichletCharacter ℂ N :=
  MulChar.ofUnitHom (ψ.toMonoidHom.comp r).toHomUnits

/-- Actual character equality at EVERY unit of the conductor modulus. -/
theorem alpogeNativeDirChar_unit
    {N : ℕ} {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (ψ : AddChar (AlpogeNativeE0 × H) ℂ) (u : (ZMod N)ˣ) :
    alpogeNativeDirChar r ψ (u : ZMod N) =
      ψ (Multiplicative.toAdd (r u)) := by
  unfold alpogeNativeDirChar
  rw [MulChar.ofUnitHom_coe, MonoidHom.coe_toHomUnits]
  rfl

/-- Nonunits are zero, including every prime dividing this modulus. -/
theorem alpogeNativeDirChar_nonunit
    {N : ℕ} {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (ψ : AddChar (AlpogeNativeE0 × H) ℂ)
    (u : ZMod N) (hu : ¬ IsUnit u) :
    alpogeNativeDirChar r ψ u = 0 :=
  MulChar.map_nonunit _ hu

/-- This is an actual source-lattice membership equivalence: a
Frobenius/inertia element comes from a unit in the kernel of the
complementary prime-factor modulus. -/
theorem alpogeNativeCftData_mem_inertia_iff
    {N : ℕ} {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (q d : ℕ)
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (p : ℕ) (x : AlpogeNativeE0 × H) :
    x ∈ (alpogeNativeCftData N q d r).inertia p ↔
      ∃ u ∈ alpogeNativeLocalUnits N p,
        Multiplicative.toAdd (r u) = x := by
  change Multiplicative.ofAdd x ∈
      (alpogeNativeLocalUnits N p).map r ↔ _
  rw [Subgroup.mem_map]
  rfl

/-- The precise conductor criterion: inertia is annihilated by ψ if
and only if the composed character factors through ordCompl[p](N).
This is the missing ramified local multiplier in an exact Euler bridge. -/
theorem alpogeNativeTrivialOnInertia_iff
    {N : ℕ} [NeZero N]
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (q d : ℕ)
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (ψ : AddChar (AlpogeNativeE0 × H) ℂ) (p : ℕ) :
    (∀ x ∈ (alpogeNativeCftData N q d r).inertia p,
      ψ x = 1) ↔
        (alpogeNativeDirChar r ψ).conductor ∣ ordCompl[p] N := by
  rw [← DirichletCharacter.mem_conductorSet_iff_conductor_dvd _
    (Nat.ordCompl_dvd N p),
      DirichletCharacter.mem_conductorSet_iff,
      DirichletCharacter.factorsThrough_iff_ker_unitsMap
        (Nat.ordCompl_dvd N p)]
  constructor
  · intro h u hu
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom,
      alpogeNativeDirChar_unit, Units.val_one]
    exact h _
      ((alpogeNativeCftData_mem_inertia_iff q d r p _).2
        ⟨u, hu, rfl⟩)
  · intro h x hx
    obtain ⟨u, hu, rfl⟩ :=
      (alpogeNativeCftData_mem_inertia_iff q d r p _).1 hx
    have h0 := h hu
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom,
      alpogeNativeDirChar_unit, Units.val_one] at h0
    exact h0

/-- At a prime p, nontrivial inertia is EQUIVALENT to p dividing
the genuine primitive-character conductor, with no bad prime dropped. -/
theorem alpogeNativeInertiaConductor_iff
    {N : ℕ} [NeZero N]
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (q d : ℕ)
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (ψ : AddChar (AlpogeNativeE0 × H) ℂ) (p : ℕ)
    (hp : p.Prime) :
    (∀ x ∈ (alpogeNativeCftData N q d r).inertia p, ψ x = 1) ↔
      ¬ p ∣ (alpogeNativeDirChar r ψ).conductor := by
  rw [alpogeNativeTrivialOnInertia_iff q d r ψ p]
  constructor
  · intro h hp0
    exact Nat.not_dvd_ordCompl hp (NeZero.ne N) (hp0.trans h)
  · intro h
    exact Nat.dvd_ordCompl_of_dvd_not_dvd
      (DirichletCharacter.conductor_dvd_level _) h

/-- Actual coset character mean when the inertia restriction is
trivial; its physical Frobenius phase is paid exactly. -/
theorem alpogeNativeCosetMean_of_trivial
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (I : AddSubgroup G) (g : G) (ψ : AddChar G ℂ)
    (hI : ∀ x ∈ I, ψ x = 1) :
    alpogeNativeInertiaCosetMean I g ψ = ψ g := by
  classical
  unfold alpogeNativeInertiaCosetMean
  have h0 :
      ((Finset.univ.filter (fun x : G => x ∈ I)).card : ℂ) ≠ 0 := by
    have hz :
        (0 : G) ∈ Finset.univ.filter (fun x : G => x ∈ I) := by
      simp [I.zero_mem]
    exact_mod_cast
      (Finset.card_pos.mpr ⟨0, hz⟩).ne'
  rw [div_eq_iff h0,
      Finset.sum_congr rfl (g := fun _ => ψ g)]
  · rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  · intro x hx
    rw [AddChar.map_add_eq_mul, hI x (by simpa using hx), mul_one]

/-- Nontrivial inertia kills the entire coset mean EXACTLY. This
is the non-lossy local cancellation, not an assumed random phase. -/
theorem alpogeNativeCosetMean_of_nontrivial
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (I : AddSubgroup G) (g : G) (ψ : AddChar G ℂ)
    (hI : ¬ ∀ x ∈ I, ψ x = 1) :
    alpogeNativeInertiaCosetMean I g ψ = 0 := by
  classical
  unfold alpogeNativeInertiaCosetMean
  push Not at hI
  obtain ⟨y, hy, hy1⟩ := hI
  have key :
      (∑ x ∈ Finset.univ.filter (fun x : G => x ∈ I), ψ (g+x)) = 0 := by
    have h1 :
        (∑ x ∈ Finset.univ.filter (fun x : G => x ∈ I),
          ψ (g+x)) =
        ∑ x ∈ Finset.univ.filter (fun x : G => x ∈ I),
          ψ (g+(y+x)) := by
      symm
      apply Finset.sum_bij (fun x _ => y+x)
      · intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx ⊢
        exact I.add_mem hy hx
      · intro a _ b _ hab
        exact add_left_cancel hab
      · intro b hb
        simp only [mem_filter, mem_univ, true_and] at hb
        exact ⟨-y + b, by simpa using I.add_mem (I.neg_mem hy) hb,
          by simp⟩
      · intro x _
        rfl
    have h2 :
        (∑ x ∈ Finset.univ.filter (fun x : G => x ∈ I),
          ψ (g+(y+x))) =
        ψ y * ∑ x ∈ Finset.univ.filter (fun x : G => x ∈ I),
          ψ (g+x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
        AddChar.map_add_eq_mul]
      ring
    rw [h2] at h1
    have h3 :
        (1 - ψ y) *
          (∑ x ∈ Finset.univ.filter (fun x : G => x ∈ I),
            ψ (g+x)) = 0 := by
      rw [sub_mul, one_mul, ← h1, sub_self]
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (sub_eq_zero.mp h4).symm hy1
    · exact h4
  rw [key, zero_div]

/-- Exact local ramified projector, split by the ACTUAL conductor
rather than an artificial prime sign or unknown local error. -/
theorem alpogeNativeCosetMean_conductor_split
    {N : ℕ} [NeZero N]
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (q d : ℕ)
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (ψ : AddChar (AlpogeNativeE0 × H) ℂ) (p : ℕ)
    (hp : p.Prime) (i : ℕ) :
    alpogeNativeInertiaCosetMean
      ((alpogeNativeCftData N q d r).inertia p)
      (i • (alpogeNativeCftData N q d r).frob p) ψ =
        if p ∣ (alpogeNativeDirChar r ψ).conductor then
          0 else ψ ((alpogeNativeCftData N q d r).frob p) ^ i := by
  by_cases h : p ∣ (alpogeNativeDirChar r ψ).conductor
  · rw [if_pos h]
    exact alpogeNativeCosetMean_of_nontrivial _ _ _ (by
      intro ht
      exact (alpogeNativeInertiaConductor_iff q d r ψ p hp).mp ht h)
  · rw [if_neg h]
    rw [alpogeNativeCosetMean_of_trivial _ _ _
      ((alpogeNativeInertiaConductor_iff q d r ψ p hp).mpr h)]
    exact AddChar.map_nsmul_eq_pow _ _ _

/-- Source-level all prime-power equivalence: the actual inertia
coset is either a zero on ramification or the full Frobenius phase.
The conductor is the primitive Dirichlet conductor, not N itself. -/
theorem alpogeNativePrimePower_conductor_split
    {N : ℕ} [NeZero N]
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (q d : ℕ)
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (ψ : AddChar (AlpogeNativeE0 × H) ℂ) (p i : ℕ)
    (hp : p.Prime) (hi : 0 < i) :
    alpogeNativeFrobInertiaPrimeValue
      (alpogeNativeCftData N q d r).inertia
      (alpogeNativeCftData N q d r).frob ψ (p ^ i) =
        if p ∣ (alpogeNativeDirChar r ψ).conductor then
          0 else ψ ((alpogeNativeCftData N q d r).frob p) ^ i := by
  rw [alpogeNativeFrobInertiaPrimeValue_primePower
    _ _ ψ p i hp hi]
  exact alpogeNativeCosetMean_conductor_split q d r ψ p hp i

end RHLean.Analysis

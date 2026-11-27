import «research.NativeMeasuredSlotProjector»
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Matrix.Trace

/-! The local index and translated frame of the measured high first-prime sections.
All translates at a partner site use its original integer slot numbers. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace RHLean.Analysis.AlpogeThin.SlotProjector

/-- Reduction of all measured star pairings on one finite lattice of slot
functions. The different depth requirements are imposed at the same prime. -/
def residueRead {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ)
    (p : ℕ) (depth : Fin r → ℕ) :
    (Address S → ℤ) →+ ((i : Fin r) → ZMod (p^depth i)) where
  toFun z i := ((Matrix.vecMul z (columns S D) i : ℤ) : ZMod (p^depth i))
  map_zero' := by funext i; simp
  map_add' z w := by funext i; simp [Matrix.add_vecMul]

/-- The index of joint divisibility is exact, including unequal depths.
Enforcing it solely by restriction pays the full gross prime power. -/
theorem residueRead_index {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ)
    (hS : ∀ i, (S i).Nonempty) (hD : ∀ i, 0 < D i)
    (cop : Pairwise (fun i j => (D i).Coprime (D j))) (p : ℕ) (hp : p.Prime)
    (depth : Fin r → ℕ) :
    (residueRead S D p depth).ker.index = p^(∑ i, depth i) := by
  classical
  let F := residueRead S D p depth
  let (i : Fin r) : NeZero (p^depth i) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨Y, hY⟩ := left_inverse S D hS hD cop
  have onto : Function.Surjective F := by
    intro y
    choose v hv using fun i => ZMod.intCast_surjective (y i)
    refine ⟨Matrix.vecMul v Y, funext fun i => ?_⟩
    change ((Matrix.vecMul (Matrix.vecMul v Y) (columns S D) i : ℤ) : ZMod (p^depth i)) = _
    rw [Matrix.vecMul_vecMul, hY, Matrix.vecMul_one]
    exact hv i
  change F.ker.index = _
  rw [AddSubgroup.index_ker, F.range_eq_top_of_surjective onto, AddSubgroup.card_top]
  simp only [Nat.card_eq_fintype_card, Fintype.card_pi, ZMod.card, Finset.prod_pow_eq_pow_sum]

/-- At a positive first-prime partner with host coordinate s, Frobenius
determines the top uniquely. Thus the fibre is a set of actual primes. -/
def partnerPrimes {H : Type*} [AddCommGroup H] [DecidableEq H]
    (tops : Finset H) (primes : Finset ℕ) (frob : ℕ → H) (s : H) : Finset ℕ :=
  primes.filter (fun p => s - frob p ∈ tops)

/-- One star with k cuts has k-1 independent columns. Across physical sites
the exact missing count is one per occupied site, for any pattern of collisions. -/
theorem partnerPrimes_rank {H : Type*} [AddCommGroup H] [DecidableEq H] [Fintype H]
    (tops : Finset H) (primes : Finset ℕ) (frob : ℕ → H) :
    (∑ s : H, ((partnerPrimes tops primes frob s).card - 1)) +
      (Finset.univ.filter (fun s : H => (partnerPrimes tops primes frob s).Nonempty)).card =
      tops.card * primes.card := by
  classical
  let N := fun s => (partnerPrimes tops primes frob s).card
  have card (p : ℕ) : (Finset.univ.filter (fun s : H => s - frob p ∈ tops)).card = tops.card := by
    have hs : Finset.univ.filter (fun s : H => s - frob p ∈ tops) =
        tops.map (Equiv.addRight (frob p)).toEmbedding := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro h
        exact ⟨s - frob p, h, sub_add_cancel _ _⟩
      · rintro ⟨t, ht, rfl⟩
        simpa using ht
    rw [hs, Finset.card_map]
  have total : ∑ s : H, N s = tops.card * primes.card := by
    simp only [N, partnerPrimes, Finset.card_filter]
    rw [Finset.sum_comm]
    calc
      _ = ∑ _p ∈ primes, tops.card := Finset.sum_congr rfl fun p _ =>
        (by simpa only [Finset.card_filter] using card p)
      _ = _ := by simp [Nat.mul_comm]
  rw [← total, Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : (partnerPrimes tops primes frob s).Nonempty
  · have := hs.card_pos
    simp only [hs, if_true, N]
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs, N]

end RHLean.Analysis.AlpogeThin.SlotProjector

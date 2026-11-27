import «research.NativeTranslatedSlotFrame»

/-! Integral recovery on the layer amplitudes of a measured quotient-slot block.
The zeroth amplitude and the successive jumps determine every original slot value. -/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace RHLean.Analysis.AlpogeThin.SlotProjector

def layerJump {r : ℕ} (A : Fin (r+1) → ℤ) (j : Fin r) : ℤ :=
  A j.succ - A j.castSucc

private theorem layerJump_add {r : ℕ} (A B : Fin (r+1) → ℤ) (j : Fin r) :
    layerJump (A+B) j = layerJump A j + layerJump B j := by
  simp only [layerJump, Pi.add_apply]
  abel

private theorem layerJump_smul {r : ℕ} (k : ℤ) (A : Fin (r+1) → ℤ) (j : Fin r) :
    layerJump (k • A) j = k * layerJump A j := by
  simp only [layerJump, Pi.smul_apply, smul_eq_mul, mul_sub]

/-- Integrate the boundary increments starting at the physical pivot. -/
def fromJumps {r : ℕ} (a : ℤ) (y : Fin r → ℤ) (i : Fin (r+1)) : ℤ :=
  a + ∑ j ∈ Finset.range i.val, if h : j < r then y ⟨j,h⟩ else 0

@[simp] theorem fromJumps_zero {r : ℕ} (a : ℤ) (y : Fin r → ℤ) :
    fromJumps a y 0 = a := by simp [fromJumps]

@[simp] theorem layerJump_fromJumps {r : ℕ} (a : ℤ) (y : Fin r → ℤ) (j : Fin r) :
    layerJump (fromJumps a y) j = y j := by
  simp [layerJump, fromJumps, Finset.sum_range_succ, j.isLt]

theorem eq_of_anchor_jumps {r : ℕ} {A B : Fin (r+1) → ℤ}
    (h0 : A 0 = B 0) (h : ∀ j, layerJump A j = layerJump B j) : A = B := by
  funext i
  refine Fin.inductionOn i h0 fun j ih => ?_
  have hj := h j
  unfold layerJump at hj
  omega

/-- Each multiplier acts on the indicated boundary of the original ordered cuts. -/
def anchoredRecovery {r : ℕ} (d : Fin r → ℤ) : (Fin (r+1) → ℤ) →ₗ[ℤ] (Fin (r+1) → ℤ) where
  toFun A := fromJumps (A 0) fun j => d j * layerJump A j
  map_add' A B := by
    apply eq_of_anchor_jumps
    · simp only [Pi.add_apply, fromJumps_zero]
    · intro j
      simp only [layerJump_add, layerJump_fromJumps, mul_add]
  map_smul' k A := by
    apply eq_of_anchor_jumps
    · simp only [Pi.smul_apply, RingHom.id_apply, fromJumps_zero]
    · intro j
      simp only [layerJump_smul, layerJump_fromJumps, RingHom.id_apply]
      ring

@[simp] theorem anchoredRecovery_zero {r : ℕ} (d : Fin r → ℤ) (A : Fin (r+1) → ℤ) :
    anchoredRecovery d A 0 = A 0 :=
  fromJumps_zero (A 0) (fun i => d i * layerJump A i)

@[simp] theorem anchoredRecovery_jump {r : ℕ} (d : Fin r → ℤ) (A : Fin (r+1) → ℤ) (j : Fin r) :
    layerJump (anchoredRecovery d A) j = d j * layerJump A j :=
  layerJump_fromJumps (A 0) (fun i => d i * layerJump A i) j

theorem anchoredRecovery_mul {r : ℕ} (d e : Fin r → ℤ) (A : Fin (r+1) → ℤ) :
    anchoredRecovery d (anchoredRecovery e A) = anchoredRecovery (d*e) A := by
  apply eq_of_anchor_jumps
  · simp
  · intro j
    simp only [anchoredRecovery_jump, Pi.mul_apply, mul_assoc]

theorem anchoredRecovery_comm {r : ℕ} (d e : Fin r → ℤ) (A : Fin (r+1) → ℤ) :
    anchoredRecovery d (anchoredRecovery e A) = anchoredRecovery e (anchoredRecovery d A) := by
  rw [anchoredRecovery_mul, anchoredRecovery_mul, mul_comm d e]

/-- The whole image, with arbitrary pivot and simultaneous unequal divisibilities. -/
theorem anchoredRecovery_image {r : ℕ} (d : Fin r → ℤ) (B : Fin (r+1) → ℤ) :
    (∃ A, anchoredRecovery d A = B) ↔ ∀ j, d j ∣ layerJump B j := by
  constructor
  · rintro ⟨A,rfl⟩ j
    exact ⟨layerJump A j, anchoredRecovery_jump d A j⟩
  · intro h
    choose z hz using h
    refine ⟨fromJumps (B 0) z, eq_of_anchor_jumps (by simp) fun j => ?_⟩
    simpa only [anchoredRecovery_jump, layerJump_fromJumps] using (hz j).symm

/-- Reading the constant amplitude at each original integer address. -/
def onSlots {r : ℕ} (S : Fin (r+1) → Finset ℕ) :
    (Fin (r+1) → ℤ) →ₗ[ℤ] (Address S → ℤ) where
  toFun A s := A s.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The retained rank includes the physical pivot, even for a singleton block. -/
theorem anchoredRecovery_slot_rank {r : ℕ} (S : Fin (r+1) → Finset ℕ)
    (hS : ∀ i, (S i).Nonempty) (d : Fin r → ℤ) (hd : ∀ i, d i ≠ 0) :
    Module.finrank ℤ (LinearMap.range ((onSlots S).comp (anchoredRecovery d))) = r+1 := by
  have hslot : Function.Injective (onSlots S) := by
    intro A B h
    funext i
    obtain ⟨k,hk⟩ := hS i
    exact congrFun h (⟨i,⟨k,hk⟩⟩ : Address S)
  have hinj : Function.Injective (anchoredRecovery d) := by
    intro A B h
    apply eq_of_anchor_jumps
    · simpa only [anchoredRecovery_zero] using congrFun h 0
    · intro j
      have h' := congrArg (fun C => layerJump C j) h
      simpa only [anchoredRecovery_jump, mul_right_inj' (hd j)] using h'
  have hc : Function.Injective ((onSlots S).comp (anchoredRecovery d)) := fun _ _ h => hinj (hslot h)
  rw [LinearMap.finrank_range_of_inj hc, Module.finrank_pi, Fintype.card_fin]

def boundaryResidues {r : ℕ} (d : Fin r → ℕ) :
    (Fin (r+1) → ℤ) →+ ((j : Fin r) → ZMod (d j)) where
  toFun A j := (layerJump A j : ZMod (d j))
  map_zero' := by funext j; simp [layerJump]
  map_add' A B := by funext j; simp only [layerJump, Pi.add_apply, Int.cast_add, Int.cast_sub]; abel

/-- The additional physical coordinate adds no finite index. Every factor in the
image index is paid by an actual boundary divisibility requirement. -/
theorem anchoredRecovery_index {r : ℕ} (d : Fin r → ℕ) (hd : ∀ j, 0 < d j) :
    (anchoredRecovery (fun j => (d j : ℤ))).toAddMonoidHom.range = (boundaryResidues d).ker ∧
    (anchoredRecovery (fun j => (d j : ℤ))).toAddMonoidHom.range.index = ∏ j, d j := by
  classical
  let F := boundaryResidues d
  let (j : Fin r) : NeZero (d j) := ⟨(hd j).ne'⟩
  have hr : (anchoredRecovery (fun j => (d j : ℤ))).toAddMonoidHom.range = F.ker := by
    ext B
    change (∃ A, anchoredRecovery (fun j => (d j : ℤ)) A = B) ↔ F B = 0
    rw [anchoredRecovery_image, funext_iff]
    exact forall_congr' fun j => (ZMod.intCast_zmod_eq_zero_iff_dvd (layerJump B j) (d j)).symm
  refine ⟨hr, ?_⟩
  have onto : Function.Surjective F := by
    intro y
    choose z hz using fun j => ZMod.intCast_surjective (y j)
    refine ⟨fromJumps 0 z, funext fun j => ?_⟩
    change (layerJump (fromJumps 0 z) j : ZMod (d j)) = y j
    rw [layerJump_fromJumps, hz]
  rw [hr, AddSubgroup.index_ker, F.range_eq_top_of_surjective onto, AddSubgroup.card_top]
  simp only [Nat.card_eq_fintype_card, Fintype.card_pi, ZMod.card]

end RHLean.Analysis.AlpogeThin.SlotProjector

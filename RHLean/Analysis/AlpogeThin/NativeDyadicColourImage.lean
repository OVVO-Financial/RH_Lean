import RHLean.Analysis.AlpogeThin.NativeDyadicPrimePowerIncidence

/-!
# Integral image of one prime's Frobenius coset sums

The coordinates of the domain are actual native colours in a prescribed
mask. A lift places each desired coset sum at one representative inside
that mask. This computes the integral site-coefficient image for the
specified prime, including inertia, repeated powers, and missed cosets.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace RHLean.Analysis.NativeColourImage

variable {O G Q A : Type*} [CommRing O] [Fintype G]

/-- Sum of the integral coordinates in a single fibre. -/
def fibreSum (q : G → Q) (v : G → O) (y : Q) : O := by
  classical
  exact ∑ g, if q g = y then v g else 0

private theorem fibreSum_zero_of_missed (q : G → Q) (v : G → O) (y : Q)
    (hy : y ∉ Set.range q) : fibreSum q v y = 0 := by
  classical
  unfold fibreSum
  exact Finset.sum_eq_zero fun g _ => ite_eq_right (fun h => hy ⟨g, h⟩)

private theorem fibreSum_surjective (q : G → Q) (hq : Function.Surjective q) :
    Function.Surjective (fibreSum (O := O) q) := by
  classical
  intro b
  choose rep hrep using hq
  let v (g : G) := if g = rep (q g) then b (q g) else 0
  refine ⟨v, funext fun y => ?_⟩
  unfold fibreSum
  rw [Finset.sum_eq_single (rep y)]
  · simp [v, hrep]
  · intro g _ hg
    by_cases h : q g = y
    · simp [v, h, hg]
    · exact ite_eq_right h
  · simp

/-- Prescribing a value at each served fibre gives one lift; unserved
fibres are exactly the coordinates forced to zero. -/
theorem fibreSum_image (q : G → Q) (b : Q → O) :
    (∃ v, fibreSum q v = b) ↔ ∀ y, y ∉ Set.range q → b y = 0 := by
  classical
  constructor
  · rintro ⟨v, rfl⟩ y hy
    exact fibreSum_zero_of_missed q v y hy
  · intro hb
    let q' (g : G) : Set.range q := ⟨q g, ⟨g, rfl⟩⟩
    have hs : Function.Surjective q' := by
      rintro ⟨y, g, rfl⟩
      exact ⟨g, rfl⟩
    obtain ⟨v, hv⟩ := fibreSum_surjective (O := O) q' hs (fun y => b y.val)
    refine ⟨v, funext fun y => ?_⟩
    by_cases hy : y ∈ Set.range q
    · have hk (g : G) : q' g = ⟨y, hy⟩ ↔ q g = y := Subtype.ext_iff
      simpa only [fibreSum, hk] using congrFun hv ⟨y, hy⟩
    · exact (fibreSum_zero_of_missed q v y hy).trans (hb y hy).symm

/-- Repeated selected labels, competing collisions, and missed classes
give the exact image for one simultaneous integral lift. -/
theorem labelled_image (q : G → Q) (k : A → Q) (S T : Set A) (d : O) (b : A → O) :
    (∃ v : G → O, (∀ i ∈ S, fibreSum q v (k i) = b i) ∧
      (∀ j ∈ T, d ∣ fibreSum q v (k j))) ↔
    (∀ i ∈ S, ∀ j ∈ S, k i = k j → b i = b j) ∧
    (∀ i ∈ S, ∀ j ∈ T, k i = k j → d ∣ b i) ∧
    (∀ i ∈ S, k i ∉ Set.range q → b i = 0) := by
  classical
  constructor
  · rintro ⟨v, hS, hT⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i hi j hj h
      rw [← hS i hi, ← hS j hj, h]
    · intro i hi j hj h
      rw [← hS i hi, h]
      exact hT j hj
    · intro i hi hm
      rw [← hS i hi]
      exact fibreSum_zero_of_missed q v (k i) hm
  · rintro ⟨hsame, hcomp, hmiss⟩
    let needed (y : Q) := ∃ i ∈ S, k i = y
    let a (y : Q) := if h : needed y then b h.choose else 0
    have ha (i : A) (hi : i ∈ S) : a (k i) = b i := by
      have h : needed (k i) := ⟨i, hi, rfl⟩
      have hc : h.choose ∈ S ∧ k h.choose = k i := h.choose_spec
      exact (dite_eq_left h).trans (hsame h.choose hc.1 i hi hc.2)
    have hzero (y : Q) (hy : y ∉ Set.range q) : a y = 0 := by
      by_cases h : needed y
      · have hc : h.choose ∈ S ∧ k h.choose = y := h.choose_spec
        exact (dite_eq_left h).trans (hmiss h.choose hc.1 (hc.2.symm ▸ hy))
      · exact dite_eq_right h
    obtain ⟨v, hv⟩ := (fibreSum_image q a).mpr hzero
    refine ⟨v, fun i hi => (congrFun hv (k i)).trans (ha i hi), ?_⟩
    intro j hj
    rw [congrFun hv (k j)]
    by_cases h : needed (k j)
    · have hc : h.choose ∈ S ∧ k h.choose = k j := h.choose_spec
      change d ∣ (if h : needed (k j) then b h.choose else 0)
      rw [dite_eq_left h]
      exact hcomp h.choose hc.1 j hj hc.2
    · change d ∣ (if h : needed (k j) then b h.choose else 0)
      rw [dite_eq_right h]
      exact dvd_zero _

/-- Coordinate factors of the diagonal image after equal fibre labels
have been identified. -/
def diagonalFactor (q : G → Q) (T : Set Q) (d : O) (y : Q) : O := by
  classical
  exact if y ∈ Set.range q then (if y ∈ T then d else 1) else 0

theorem distinct_image (q : G → Q) (S T : Set Q) (d : O) (b : Q → O) :
    (∃ v : G → O, (∀ y ∈ S, fibreSum q v y = b y) ∧
      (∀ t ∈ T, d ∣ fibreSum q v t)) ↔
    ∀ y ∈ S, diagonalFactor q T d y ∣ b y := by
  classical
  rw [show (∃ v : G → O, (∀ y ∈ S, fibreSum q v y = b y) ∧ (∀ t ∈ T, d ∣ fibreSum q v t)) ↔
      _ from labelled_image q id S T d b]
  constructor
  · rintro ⟨_, hcomp, hmiss⟩ y hy
    by_cases hq : y ∈ Set.range q
    · by_cases ht : y ∈ T
      · simpa [diagonalFactor, hq, ht] using hcomp y hy y ht rfl
      · simp [diagonalFactor, hq, ht]
    · simp [diagonalFactor, hq, hmiss y hy hq]
  · intro h
    refine ⟨fun _ _ _ _ he => congrArg b he, ?_, ?_⟩
    · rintro y hy t ht he
      change y = t at he
      subst t
      by_cases hq : y ∈ Set.range q
      · simpa [diagonalFactor, hq, ht] using h y hy
      · have hb : b y = 0 := by simpa [diagonalFactor, hq] using h y hy
        rw [hb]
        exact dvd_zero _
    · intro y hy hq
      exact (by simpa [diagonalFactor, hq] using h y hy : b y = 0)

open Classical in
/-- When every fibre is served, the diagonal factors are the imposed
modulus exactly on the selected and competing overlap, and one elsewhere. -/
theorem surjective_diagonal_image (q : G → Q) (hq : Function.Surjective q)
    (S T : Set Q) (d : O) (b : Q → O) :
    (∃ v : G → O, (∀ y ∈ S, fibreSum q v y = b y) ∧
      (∀ t ∈ T, d ∣ fibreSum q v t)) ↔
    ∀ y ∈ S, (if y ∈ T then d else 1) ∣ b y := by
  rw [distinct_image]
  simp only [diagonalFactor, Set.range_eq_univ.mpr hq, Set.mem_univ, ite_true]

open Classical in
/-- Product of the invariant factors on distinct selected classes; over a
DVR with modulus a uniformizer power its valuation is the exact length. -/
theorem det_overlap_diagonal (S T : Finset Q) (d : O) :
    (Matrix.diagonal (fun y : S => if y.val ∈ T then d else 1)).det =
      d ^ (Finset.univ.filter (fun y : S => y.val ∈ T)).card := by
  rw [Matrix.det_diagonal, ← Finset.prod_filter, Finset.prod_const]

end RHLean.Analysis.NativeColourImage

namespace RHLean.Analysis

open NativeColourImage

/-- The genuine coset of inertia containing this group element. -/
def nativeInertiaClass {G : Type*} [AddCommGroup G] (I : AddSubgroup G) (g : G) : G ⧸ I :=
  (QuotientAddGroup.mk' I) g

theorem nativeInertiaClass_surjective {G : Type*} [AddCommGroup G] (I : AddSubgroup G) :
    Function.Surjective (nativeInertiaClass I) := QuotientAddGroup.mk'_surjective I

private theorem nativeInertiaClass_eq_iff {G : Type*} [AddCommGroup G] (I : AddSubgroup G) (a b : G) :
    nativeInertiaClass I a = nativeInertiaClass I b ↔ a - b ∈ I :=
  QuotientAddGroup.eq_iff_sub_mem

variable {O : Type*} [CommRing O]

/-- The actual integer Frobenius indicator acts on the coefficients of the
colours in the supplied mask, with their original multiplicity. -/
def nativeDyadicRestrictedColourSum (e q d p i : ℕ) [Fact q.Prime] [Fact d.Prime]
    (U : Finset (AlpogeNativeE0 × AlpogeNativeDyadicH e)) (v : U → O) : O :=
  ∑ g : U, (nativeDyadicPrimePowerIncidence e q d p i g.val : O) * v g

theorem nativeDyadicRestrictedColourSum_eq_fibreSum (e q d p i : ℕ) [Fact q.Prime] [Fact d.Prime]
    (U : Finset (AlpogeNativeE0 × AlpogeNativeDyadicH e)) (v : U → O) :
    let H := alpogeNativeHostData e q d
    nativeDyadicRestrictedColourSum e q d p i U v =
      fibreSum (fun g : U => nativeInertiaClass (H.inertia p) g.val) v
        (nativeInertiaClass (H.inertia p) (i • H.frob p)) := by
  classical
  let H := alpogeNativeHostData e q d
  unfold nativeDyadicRestrictedColourSum fibreSum
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases h : g.val - i • H.frob p ∈ H.inertia p
  · have hrow : nativeDyadicPrimePowerIncidence e q d p i g.val = 1 := ite_eq_left h
    have hc := (nativeInertiaClass_eq_iff (G := AlpogeNativeE0 × AlpogeNativeDyadicH e)
      (H.inertia p) g.val (i • H.frob p)).mpr h
    simp only [hrow, Int.cast_one, one_mul, ite_eq_left hc]
  · have hrow : nativeDyadicPrimePowerIncidence e q d p i g.val = 0 := ite_eq_right h
    have hc := mt (nativeInertiaClass_eq_iff (G := AlpogeNativeE0 × AlpogeNativeDyadicH e)
      (H.inertia p) g.val (i • H.frob p)).mp h
    simp only [hrow, Int.cast_zero, zero_mul, ite_eq_right hc]

/-- Exact simultaneous integral image on one actual prime's masked colour
coefficients. S and T still contain the original exponent labels. -/
theorem nativeDyadic_restrictedColourImage (e q d p : ℕ) [Fact q.Prime] [Fact d.Prime]
    (U : Finset (AlpogeNativeE0 × AlpogeNativeDyadicH e)) (S T : Set ℕ)
    (modulus : O) (b : ℕ → O) :
    let H := alpogeNativeHostData e q d
    let site := fun g : U => nativeInertiaClass (H.inertia p) g.val
    let orbit := fun i : ℕ => nativeInertiaClass (H.inertia p) (i • H.frob p)
    (∃ v : U → O, (∀ i ∈ S, nativeDyadicRestrictedColourSum e q d p i U v = b i) ∧
      (∀ j ∈ T, modulus ∣ nativeDyadicRestrictedColourSum e q d p j U v)) ↔
    (∀ i ∈ S, ∀ j ∈ S, orbit i = orbit j → b i = b j) ∧
    (∀ i ∈ S, ∀ j ∈ T, orbit i = orbit j → modulus ∣ b i) ∧
    (∀ i ∈ S, orbit i ∉ Set.range site → b i = 0) := by
  let H := alpogeNativeHostData e q d
  let site := fun g : U => nativeInertiaClass (H.inertia p) g.val
  let orbit := fun i : ℕ => nativeInertiaClass (H.inertia p) (i • H.frob p)
  simpa only [nativeDyadicRestrictedColourSum_eq_fibreSum] using
    (labelled_image site orbit S T modulus b)

private theorem translated_class_eq_iff {G : Type*} [AddCommGroup G] (I : AddSubgroup G)
    (x a v b : G) : nativeInertiaClass I x = nativeInertiaClass I (a + v + b) ↔
      x - a - b - v ∈ I := by
  rw [nativeInertiaClass_eq_iff, show x - (a + v + b) = x - a - b - v by abel]

/-- Read the original prime-power indicator in partner coordinates. The
argument of the integer row is the inverse of the native partner
translation at this top. The mask U is in the partner coordinate. -/
def nativeDyadicPartnerColourSum (e q d p i : ℕ) [Fact q.Prime] [Fact d.Prime]
    (t : AlpogeNativeDyadicH e) (U : Finset (AlpogeNativeE0 × AlpogeNativeDyadicH e))
    (v : U → O) : O :=
  ∑ g : U, (nativeDyadicPrimePowerIncidence e q d p i
      (g.val - alpogeNativeCconj (AlpogeNativeDyadicH e) - alpogeNativeTopPl t) : O) * v g

theorem nativeDyadicPartnerColourSum_eq_fibreSum (e q d p i : ℕ) [Fact q.Prime] [Fact d.Prime]
    (t : AlpogeNativeDyadicH e) (U : Finset (AlpogeNativeE0 × AlpogeNativeDyadicH e))
    (v : U → O) :
    let H := alpogeNativeHostData e q d
    nativeDyadicPartnerColourSum e q d p i t U v =
      fibreSum (fun g : U => nativeInertiaClass (H.inertia p) g.val) v
        (nativeInertiaClass (H.inertia p) (alpogeNativePartner t (i • H.frob p))) := by
  classical
  let H := alpogeNativeHostData e q d
  let a := alpogeNativeCconj (AlpogeNativeDyadicH e)
  let b := alpogeNativeTopPl t
  unfold nativeDyadicPartnerColourSum fibreSum
  refine Finset.sum_congr rfl fun g _ => ?_
  have hc : nativeInertiaClass (H.inertia p) g.val =
      nativeInertiaClass (H.inertia p) (alpogeNativePartner t (i • H.frob p)) ↔
      g.val - a - b - i • H.frob p ∈ H.inertia p :=
    translated_class_eq_iff (G := AlpogeNativeE0 × AlpogeNativeDyadicH e)
      (H.inertia p) g.val a (i • H.frob p) b
  by_cases h : g.val - a - b - i • H.frob p ∈ H.inertia p
  · have hrow : nativeDyadicPrimePowerIncidence e q d p i (g.val - a - b) = 1 := ite_eq_left h
    simp only [hrow, Int.cast_one, one_mul, ite_eq_left (hc.mpr h)]
  · have hrow : nativeDyadicPrimePowerIncidence e q d p i (g.val - a - b) = 0 := ite_eq_right h
    simp only [hrow, Int.cast_zero, zero_mul, ite_eq_right (mt hc.mp h)]

/-- On one prime the original partner coordinate groups all top/exponent
labels that represent the same inertia coset. This includes collisions
between different tops as well as returns at one top. -/
theorem nativeDyadic_partnerColourImage {A : Type*} (e q d p : ℕ) [Fact q.Prime] [Fact d.Prime]
    (top : A → AlpogeNativeDyadicH e) (exponent : A → ℕ)
    (U : Finset (AlpogeNativeE0 × AlpogeNativeDyadicH e)) (S T : Set A)
    (modulus : O) (b : A → O) :
    let H := alpogeNativeHostData e q d
    let site := fun g : U => nativeInertiaClass (H.inertia p) g.val
    let orbit := fun i : A => nativeInertiaClass (H.inertia p)
      (alpogeNativePartner (top i) (exponent i • H.frob p))
    (∃ v : U → O, (∀ i ∈ S, nativeDyadicPartnerColourSum e q d p (exponent i) (top i) U v = b i) ∧
      (∀ j ∈ T, modulus ∣ nativeDyadicPartnerColourSum e q d p (exponent j) (top j) U v)) ↔
    (∀ i ∈ S, ∀ j ∈ S, orbit i = orbit j → b i = b j) ∧
    (∀ i ∈ S, ∀ j ∈ T, orbit i = orbit j → modulus ∣ b i) ∧
    (∀ i ∈ S, orbit i ∉ Set.range site → b i = 0) := by
  let H := alpogeNativeHostData e q d
  let site := fun g : U => nativeInertiaClass (H.inertia p) g.val
  let orbit := fun i : A => nativeInertiaClass (H.inertia p)
    (alpogeNativePartner (top i) (exponent i • H.frob p))
  simpa only [nativeDyadicPartnerColourSum_eq_fibreSum] using
    (labelled_image site orbit S T modulus b)

end RHLean.Analysis

end

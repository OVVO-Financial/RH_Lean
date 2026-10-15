import «research.MERTENS_HEATH_BROWN_SIGNED»

/-!
# Exact signed hyperbola decomposition

The overlap is subtracted before any estimate. The result is a finite identity,
not an assertion that scalar prefix bounds pay all growing bilinear sums.
-/

noncomputable section
namespace RHLean.Analysis.MertensFiniteExtension
open Finset

/-- The complete physical positive-integer product region. -/
def hyperbolaRegion (X : Nat) : Finset (Prod Nat Nat) :=
  ((Icc 1 X).product (Icc 1 X)).filter (fun p => p.1 * p.2 <= X)

def signedHyperbola (f g : Nat -> Int) (X : Nat) : Int :=
  Finset.sum (hyperbolaRegion X) (fun p => f p.1 * g p.2)

def leftHyperbola (f g : Nat -> Int) (X U : Nat) : Int :=
  Finset.sum ((hyperbolaRegion X).filter (fun p => p.1 <= U))
    (fun p => f p.1 * g p.2)

def rightHyperbola (f g : Nat -> Int) (X V : Nat) : Int :=
  Finset.sum ((hyperbolaRegion X).filter (fun p => p.2 <= V))
    (fun p => f p.1 * g p.2)

/-- Exact inclusion-exclusion on the hyperbola, with signed overlap retained. -/
theorem signedHyperbola_split_filtered (f g : Nat -> Int) {X U V : Nat}
    (hcover : X < (U + 1) * (V + 1)) :
    signedHyperbola f g X = leftHyperbola f g X U + rightHyperbola f g X V -
      Finset.sum ((hyperbolaRegion X).filter (fun p => p.1 <= U ∧ p.2 <= V))
        (fun p => f p.1 * g p.2) := by
  unfold signedHyperbola leftHyperbola rightHyperbola
  simp only [Finset.sum_filter]
  rw [<- Finset.sum_add_distrib, <- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hprod := (Finset.mem_filter.mp hp).2
  have hor : p.1 <= U ∨ p.2 <= V := by
    by_contra h
    have hU : U + 1 <= p.1 := by omega
    have hV : V + 1 <= p.2 := by omega
    have hm := Nat.mul_le_mul hU hV
    omega
  rcases hor with hi | hj
  · by_cases hj : p.2 <= V <;> simp [hi, hj]
  · by_cases hi : p.1 <= U <;> simp [hi, hj]

/-- The overlap is a whole signed rectangle. -/
theorem hyperbola_overlap_sum (f g : Nat -> Int) {X U V : Nat}
    (hU : U <= X) (hV : V <= X) (hUV : U * V <= X) :
    Finset.sum ((hyperbolaRegion X).filter (fun p => p.1 <= U ∧ p.2 <= V))
      (fun p => f p.1 * g p.2) =
    (Finset.sum (Icc 1 U) f) * (Finset.sum (Icc 1 V) g) := by
  have hset : (hyperbolaRegion X).filter (fun p => p.1 <= U ∧ p.2 <= V) =
      (Icc 1 U).product (Icc 1 V) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hh, hiU, hjV⟩ := Finset.mem_filter.mp hp
      obtain ⟨hm, _⟩ := Finset.mem_filter.mp hh
      obtain ⟨hi, hj⟩ := Finset.mem_product.mp hm
      exact Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, hiU⟩,
          Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1, hjV⟩⟩
    · intro hp
      obtain ⟨hi, hj⟩ := Finset.mem_product.mp hp
      obtain ⟨hi1, hiU⟩ := Finset.mem_Icc.mp hi
      obtain ⟨hj1, hjV⟩ := Finset.mem_Icc.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨hi1, hiU.trans hU⟩,
            Finset.mem_Icc.mpr ⟨hj1, hjV.trans hV⟩⟩,
          (Nat.mul_le_mul hiU hjV).trans hUV⟩, hiU, hjV⟩
  rw [hset]
  change (∑ p ∈ (Icc 1 U) ×ˢ (Icc 1 V), f p.1 * g p.2) = _
  rw [Finset.sum_product]
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

/-- Dirichlet's split, including the exact signed rectangle correction. -/
theorem signedHyperbola_split (f g : Nat -> Int) {X U V : Nat}
    (hU : U <= X) (hV : V <= X) (hUV : U * V <= X)
    (hcover : X < (U + 1) * (V + 1)) :
    signedHyperbola f g X = leftHyperbola f g X U + rightHyperbola f g X V -
      (Finset.sum (Icc 1 U) f) * (Finset.sum (Icc 1 V) g) := by
  rw [signedHyperbola_split_filtered f g hcover, hyperbola_overlap_sum f g hU hV hUV]

/-- Actual convolution coefficients reindex onto every physical product pair. -/
theorem convolution_sum_eq_signedHyperbola (f g : ArithmeticFunction Int) (X : Nat) :
    Finset.sum (Finset.range (X + 1)) (fun n => (f * g) n) =
      signedHyperbola f g X := by
  simp only [ArithmeticFunction.mul_apply]
  calc
    Finset.sum (Finset.range (X + 1))
        (fun n => Finset.sum n.divisorsAntidiagonal (fun p => f p.1 * g p.2)) =
      Finset.sum ((Finset.range (X + 1)).sigma (fun n => n.divisorsAntidiagonal))
        (fun p => f p.2.1 * g p.2.2) := by rw [Finset.sum_sigma]
    _ = signedHyperbola f g X := by
      unfold signedHyperbola
      apply Finset.sum_bij (fun p _ => p.2)
      · intro p hp
        obtain ⟨hn, hd⟩ := Finset.mem_sigma.mp hp
        have hx : p.1 <= X := by have h := Finset.mem_range.mp hn; omega
        have hprod := (Nat.mem_divisorsAntidiagonal.mp hd).1
        have hnon := Nat.ne_zero_of_mem_divisorsAntidiagonal hd
        have hi : 1 <= p.2.1 := Nat.one_le_iff_ne_zero.mpr hnon.1
        have hj : 1 <= p.2.2 := Nat.one_le_iff_ne_zero.mpr hnon.2
        have hix : p.2.1 <= X := by nlinarith
        have hjx : p.2.2 <= X := by nlinarith
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨hi, hix⟩, Finset.mem_Icc.mpr ⟨hj, hjx⟩⟩,
          hprod.trans_le hx⟩
      · intro a ha b hb hab
        have hpa := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp ha).2).1
        have hpb := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hb).2).1
        have hfirst : a.1 = b.1 := by rw [<- hpa, <- hpb, hab]
        exact Sigma.ext hfirst (heq_of_eq hab)
      · intro p hp
        obtain ⟨hmem, hprod⟩ := Finset.mem_filter.mp hp
        obtain ⟨hi, hj⟩ := Finset.mem_product.mp hmem
        have hipos : 0 < p.1 := by have h := (Finset.mem_Icc.mp hi).1; omega
        have hjpos : 0 < p.2 := by have h := (Finset.mem_Icc.mp hj).1; omega
        refine ⟨⟨p.1 * p.2, p⟩, ?_, rfl⟩
        apply Finset.mem_sigma.mpr
        exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hprod),
          Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, Nat.ne_of_gt (Nat.mul_pos hipos hjpos)⟩⟩
      · intro p _hp
        rfl

/-- The left strip is a signed sum of genuine cumulative inner sums. -/
theorem leftHyperbola_eq_prefixSums (f g : Nat -> Int) {X U : Nat} (hU : U <= X) :
    leftHyperbola f g X U =
      Finset.sum (Icc 1 U) (fun i => f i * Finset.sum (Icc 1 (X / i)) g) := by
  symm
  simp_rw [Finset.mul_sum]
  calc
    (∑ i ∈ Icc 1 U, ∑ j ∈ Icc 1 (X / i), f i * g j) =
        Finset.sum ((Icc 1 U).sigma (fun i => Icc 1 (X / i)))
          (fun p => f p.1 * g p.2) := by rw [Finset.sum_sigma]
    _ = leftHyperbola f g X U := by
      unfold leftHyperbola
      apply Finset.sum_bij (fun p _ => (p.1, p.2))
      · intro p hp
        obtain ⟨hi, hj⟩ := Finset.mem_sigma.mp hp
        obtain ⟨hi1, hiU⟩ := Finset.mem_Icc.mp hi
        obtain ⟨hj1, hjdiv⟩ := Finset.mem_Icc.mp hj
        have hipos : 0 < p.1 := by omega
        have hprod : p.1 * p.2 <= X :=
          (Nat.mul_comm p.1 p.2).trans_le ((Nat.le_div_iff_mul_le hipos).mp hjdiv)
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr
            ⟨Finset.mem_Icc.mpr ⟨hi1, hiU.trans hU⟩,
              Finset.mem_Icc.mpr ⟨hj1, hjdiv.trans (Nat.div_le_self X p.1)⟩⟩,
            hprod⟩, hiU⟩
      · intro a _ha b _hb hab
        exact Sigma.ext (congrArg Prod.fst hab) (heq_of_eq (congrArg Prod.snd hab))
      · intro p hp
        obtain ⟨hh, hiU⟩ := Finset.mem_filter.mp hp
        obtain ⟨hm, hprod⟩ := Finset.mem_filter.mp hh
        obtain ⟨hi, hj⟩ := Finset.mem_product.mp hm
        have hi1 := (Finset.mem_Icc.mp hi).1
        have hj1 := (Finset.mem_Icc.mp hj).1
        have hipos : 0 < p.1 := by omega
        have hjdiv : p.2 <= X / p.1 :=
          (Nat.le_div_iff_mul_le hipos).mpr ((Nat.mul_comm p.2 p.1).trans_le hprod)
        exact ⟨⟨p.1, p.2⟩, Finset.mem_sigma.mpr
          ⟨Finset.mem_Icc.mpr ⟨hi1, hiU⟩, Finset.mem_Icc.mpr ⟨hj1, hjdiv⟩⟩, rfl⟩
      · intro p _hp
        rfl

private theorem swap_mem_hyperbola {X : Nat} {p : Prod Nat Nat}
    (hp : p ∈ hyperbolaRegion X) : p.swap ∈ hyperbolaRegion X := by
  obtain ⟨hm, hprod⟩ := Finset.mem_filter.mp hp
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp hm
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hj, hi⟩, (Nat.mul_comm p.2 p.1).trans_le hprod⟩

/-- Swapping the factors preserves their signed product and every occurrence. -/
theorem rightHyperbola_eq_leftSwap (f g : Nat -> Int) (X V : Nat) :
    rightHyperbola f g X V = leftHyperbola g f X V := by
  unfold rightHyperbola leftHyperbola
  apply Finset.sum_bij (fun p _ => p.swap)
  · intro p hp
    exact Finset.mem_filter.mpr
      ⟨swap_mem_hyperbola (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
  · intro a _ha b _hb hab
    exact Prod.swap_injective hab
  · intro p hp
    refine ⟨p.swap, Finset.mem_filter.mpr
      ⟨swap_mem_hyperbola (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩, ?_⟩
    rfl
  · intro p _hp
    exact mul_comm _ _

/-- Full cumulative-sum hyperbola interface, with the overlap still signed. -/
theorem signedHyperbola_split_prefixSums (f g : Nat -> Int) {X U V : Nat}
    (hU : U <= X) (hV : V <= X) (hUV : U * V <= X)
    (hcover : X < (U + 1) * (V + 1)) :
    signedHyperbola f g X =
      Finset.sum (Icc 1 U) (fun i => f i * Finset.sum (Icc 1 (X / i)) g) +
      Finset.sum (Icc 1 V) (fun j => g j * Finset.sum (Icc 1 (X / j)) f) -
      (Finset.sum (Icc 1 U) f) * (Finset.sum (Icc 1 V) g) := by
  rw [signedHyperbola_split f g hU hV hUV hcover,
    rightHyperbola_eq_leftSwap, leftHyperbola_eq_prefixSums f g hU,
    leftHyperbola_eq_prefixSums g f hV]

/-- Native Dirichlet convolution to signed cumulative sums, end to end. -/
theorem convolution_sum_hyperbola (f g : ArithmeticFunction Int) {X U V : Nat}
    (hU : U <= X) (hV : V <= X) (hUV : U * V <= X)
    (hcover : X < (U + 1) * (V + 1)) :
    Finset.sum (Finset.range (X + 1)) (fun n => (f * g) n) =
      Finset.sum (Icc 1 U) (fun i => f i * Finset.sum (Icc 1 (X / i)) g) +
      Finset.sum (Icc 1 V) (fun j => g j * Finset.sum (Icc 1 (X / j)) f) -
      (Finset.sum (Icc 1 U) f) * (Finset.sum (Icc 1 V) g) := by
  rw [convolution_sum_eq_signedHyperbola]
  exact signedHyperbola_split_prefixSums f g hU hV hUV hcover

end RHLean.Analysis.MertensFiniteExtension

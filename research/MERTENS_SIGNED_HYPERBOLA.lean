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

/-- When the overlap rectangle lies under the hyperbola, its signed sum is
exactly the product of two prefix sums, not a sum of coefficient magnitudes. -/
theorem hyperbola_overlap_sum (f g : Nat -> Int) {X U V : Nat}
    (hU : U <= X) (hV : V <= X) (hUV : U * V <= X) :
    Finset.sum ((hyperbolaRegion X).filter (fun p => p.1 <= U ∧ p.2 <= V))
      (fun p => f p.1 * g p.2) =
    (Finset.sum (Icc 1 U) f) * (Finset.sum (Icc 1 V) g) := by
  have hset : (hyperbolaRegion X).filter (fun p => p.1 <= U ∧ p.2 <= V) =
      (Icc 1 U).product (Icc 1 V) := by
    ext p
    simp only [hyperbolaRegion, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨⟨hi, _⟩, ⟨hj, _⟩⟩, _⟩, hiU, hjV⟩
      exact ⟨⟨hi, hiU⟩, ⟨hj, hjV⟩⟩
    · rintro ⟨⟨hi, hiU⟩, ⟨hj, hjV⟩⟩
      exact ⟨⟨⟨⟨hi, hiU.trans hU⟩, ⟨hj, hjV.trans hV⟩⟩,
        (Nat.mul_le_mul hiU hjV).trans hUV⟩, hiU, hjV⟩
  rw [hset, Finset.sum_product]
  simp only [Finset.mul_sum, Finset.sum_mul]

/-- Dirichlet's hyperbola split, including the exact signed rectangle correction. -/
theorem signedHyperbola_split (f g : Nat -> Int) {X U V : Nat}
    (hU : U <= X) (hV : V <= X) (hUV : U * V <= X)
    (hcover : X < (U + 1) * (V + 1)) :
    signedHyperbola f g X = leftHyperbola f g X U + rightHyperbola f g X V -
      (Finset.sum (Icc 1 U) f) * (Finset.sum (Icc 1 V) g) := by
  rw [signedHyperbola_split_filtered f g hcover, hyperbola_overlap_sum f g hU hV hUV]

/-- Reindexing bridge from the actual Dirichlet convolution to the full finite
hyperbola. No pair, multiplicity, or signed coefficient is dropped. -/
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
        exact ⟨Finset.mem_range.mpr (by omega),
          Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, Nat.ne_of_gt (Nat.mul_pos hipos hjpos)⟩⟩
      · intro p _hp
        rfl

end RHLean.Analysis.MertensFiniteExtension

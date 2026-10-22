import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationRows
import OAI.NumberTheory.DirichletL.CenteredExceptionalCount
import OAI.NumberTheory.DirichletL.GaussSum.CubicNormalization
import OAI.NumberTheory.DirichletL.GaussSum.LocalProductAssembly

/-!
Original OAI true Eisenstein ideal base-3 adapter and canonical sextic
square-to-cubic and sixth-power zero-mask lemmas. Actual FreeRow
is an ELEMENT with a sixth-free PRINCIPAL IDEAL; no element-level
unit-normalized row bijection is claimed here.
-/

namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CubeFreeRowAdapter

open CenteredExceptionalCount
open HeckeInverseAmplification
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def squarefreeCubeRoot (I : Id) : Id := factorPart I (fun n => n / 3)
def cubeFreeRemainder (I : Id) : Id := factorPart I (fun n => n % 3)

theorem squarefreeCubeRoot_ne_zero (I : Id) :
    squarefreeCubeRoot I ≠ 0 := factorPart_ne_zero I _

theorem cubeFreeRemainder_ne_zero (I : Id) :
    cubeFreeRemainder I ≠ 0 := factorPart_ne_zero I _

@[simp] theorem squarefreeCubeRoot_valuation (I P : Id) :
    valuation (squarefreeCubeRoot I) P = valuation I P / 3 := by
  exact factorPart_valuation I P _ (by norm_num)

@[simp] theorem cubeFreeRemainder_valuation (I P : Id) :
    valuation (cubeFreeRemainder I) P = valuation I P % 3 := by
  exact factorPart_valuation I P _ (by norm_num)

/-- Original Eisenstein ideals, not abstract valuation vectors. -/
theorem actual_ideal_base3_factorization
    (I : Id) (hI : I ≠ 0) :
    squarefreeCubeRoot I ^ 3 * cubeFreeRemainder I = I := by
  have hC := squarefreeCubeRoot_ne_zero I
  have hR := cubeFreeRemainder_ne_zero I
  apply ideal_eq_of_valuation_eq
    (mul_ne_zero (pow_ne_zero 3 hC) hR) hI
  intro P
  rw [valuation_mul _ _ _ (pow_ne_zero 3 hC) hR, valuation_pow,
    squarefreeCubeRoot_valuation, cubeFreeRemainder_valuation]
  omega

/-- Both true squarefreeness and true cubefreeness; the factors
    are allowed to have overlapping prime support. -/
theorem sixthFree_ideal_sqFree_mul_cube_cubeFree
    (I : Id) (hI : I ≠ 0) (hSix : SixthFree I) :
    squarefreeCubeRoot I ^ 3 * cubeFreeRemainder I = I ∧
      Squarefree (squarefreeCubeRoot I) ∧
      (∀ P : Id, valuation (cubeFreeRemainder I) P < 3) := by
  have hSq : Squarefree (squarefreeCubeRoot I) := by
    apply (squarefree_iff_nodup_normalizedFactors
      (squarefreeCubeRoot_ne_zero I)).mpr
    apply Multiset.nodup_iff_count_le_one.mpr
    intro P
    change valuation (squarefreeCubeRoot I) P ≤ 1
    rw [squarefreeCubeRoot_valuation]
    have hv : valuation I P < 6 := hSix P
    omega
  refine ⟨actual_ideal_base3_factorization I hI, hSq, ?_⟩
  intro P
  rw [cubeFreeRemainder_valuation]
  omega

/-- Actual FreeRow gives the ORIGINAL sixth-free principal ideal. -/
theorem original_FreeRow_principal_ideal_base3
    (u : FreeRow) :
    squarefreeCubeRoot (Ideal.span {u.val}) ^ 3 *
        cubeFreeRemainder (Ideal.span {u.val}) =
      Ideal.span {u.val} ∧
      Squarefree (squarefreeCubeRoot (Ideal.span {u.val})) ∧
      (∀ P : Id,
        valuation (cubeFreeRemainder (Ideal.span {u.val})) P < 3) := by
  apply sixthFree_ideal_sqFree_mul_cube_cubeFree
  · exact Ideal.span_singleton_eq_bot.not.mpr u.property.1
  · exact u.property.2

/-- Uniqueness among actual ideal factors, not only symbolic profiles. -/
theorem actual_ideal_base3_unique
    (I C R : Id) (hC : C ≠ 0) (hR : R ≠ 0)
    (_hCsq : ∀ P : Id, valuation C P < 2)
    (hRfree : ∀ P : Id, valuation R P < 3)
    (hFactor : C ^ 3 * R = I) :
    C = squarefreeCubeRoot I ∧ R = cubeFreeRemainder I := by
  have heq (P : Id) : 3 * valuation C P + valuation R P =
      valuation I P := by
    have h := congrArg (fun J : Id => valuation J P) hFactor
    rwa [valuation_mul _ _ _ (pow_ne_zero 3 hC) hR,
      valuation_pow] at h
  have hCv (P : Id) :
      valuation C P = valuation (squarefreeCubeRoot I) P := by
    rw [squarefreeCubeRoot_valuation]
    have h := heq P
    have hr := hRfree P
    omega
  have hRv (P : Id) :
      valuation R P = valuation (cubeFreeRemainder I) P := by
    rw [cubeFreeRemainder_valuation]
    have h := heq P
    have hr := hRfree P
    omega
  exact ⟨ideal_eq_of_valuation_eq hC (squarefreeCubeRoot_ne_zero I) hCv,
    ideal_eq_of_valuation_eq hR (cubeFreeRemainder_ne_zero I) hRv⟩

/-- In the literal pinned source canonicalSextic squared is cubicChar
    on all residues, retaining zero values. -/
theorem original_canonicalSextic_sq_eq_cubic
    (P : Id) [P.IsMaximal] (hg : lambda ∉ P) (u : O) :
    (canonicalSextic P hg (Ideal.Quotient.mk P u)) ^ 2 =
      ((cubicChar P hg).ringHomComp ConcreteTraceCRT.eisEmbedding)
        (Ideal.Quotient.mk P u) := by
  have h := congrArg
    (fun chi : MulChar (O ⧸ P) ℂ => chi (Ideal.Quotient.mk P u))
    (canonicalSextic_pow_two P hg)
  simpa only [MulChar.pow_apply'] using h

/-- True original mask including the zero value when c belongs to P:
    squaring the sextic character kills the c-cube factor. -/
theorem original_canonical_cubic_cube_mask
    (P : Id) [P.IsMaximal] (hg : lambda ∉ P) (c u : O) :
    (canonicalSextic P hg (Ideal.Quotient.mk P (c ^ 3 * u))) ^ 2 =
      (if c ∈ P then (0 : ℂ) else 1) *
        (canonicalSextic P hg (Ideal.Quotient.mk P u)) ^ 2 := by
  let chi := canonicalSextic P hg
  have h6 : (chi (Ideal.Quotient.mk P c)) ^ 6 =
      if c ∈ P then (0 : ℂ) else 1 := by
    simpa only [chi, map_pow] using
      canonicalSextic_sixth_power_mask P hg c
  calc
    _ = (chi (Ideal.Quotient.mk P c)) ^ 6 *
        (chi (Ideal.Quotient.mk P u)) ^ 2 := by
      change (chi (Ideal.Quotient.mk P (c ^ 3 * u))) ^ 2 = _
      simp only [map_mul, map_pow]
      ring
    _ = _ := by rw [h6]

/-- The original D-head is the CONJUGATED cubic character. -/
theorem original_conjugated_cubic_cube_mask
    (P : Id) [P.IsMaximal] (hg : lambda ∉ P) (c u : O) :
    star ((canonicalSextic P hg
        (Ideal.Quotient.mk P (c ^ 3 * u))) ^ 2) =
      (if c ∈ P then (0 : ℂ) else 1) *
        star ((canonicalSextic P hg (Ideal.Quotient.mk P u)) ^ 2) := by
  have h := congrArg star
    (original_canonical_cubic_cube_mask P hg c u)
  simpa only [star_mul, map_ite, star_zero, star_one] using h

end SevenEighths.CubeFreeRowAdapter
end

#print axioms SevenEighths.CubeFreeRowAdapter.actual_ideal_base3_factorization
#print axioms SevenEighths.CubeFreeRowAdapter.sixthFree_ideal_sqFree_mul_cube_cubeFree
#print axioms SevenEighths.CubeFreeRowAdapter.original_FreeRow_principal_ideal_base3
#print axioms SevenEighths.CubeFreeRowAdapter.actual_ideal_base3_unique
#print axioms SevenEighths.CubeFreeRowAdapter.original_canonicalSextic_sq_eq_cubic
#print axioms SevenEighths.CubeFreeRowAdapter.original_canonical_cubic_cube_mask
#print axioms SevenEighths.CubeFreeRowAdapter.original_conjugated_cubic_cube_mask

end OAI

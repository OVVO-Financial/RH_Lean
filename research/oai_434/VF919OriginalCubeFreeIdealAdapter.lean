import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationRows
import OAI.NumberTheory.DirichletL.CenteredExceptionalCount
import OAI.NumberTheory.DirichletL.GaussSum.CubicNormalization
import OAI.NumberTheory.DirichletL.GaussSum.LocalProductAssembly
import OAI.NumberTheory.DirichletL.Detector.EulerCoordinates

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
    apply (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
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

/-- The actual original FreeRow principal ideal norm splits into
    its cube-root and cube-free remainder norms, without replacing a
    labelled row by an arbitrary chosen generator. -/
theorem original_FreeRow_cube_ideal_norm_identity
    (u : FreeRow) :
    ((Ideal.absNorm (Ideal.span {u.val}) : ℕ) : ℝ) =
      ((Ideal.absNorm (squarefreeCubeRoot (Ideal.span {u.val})) : ℕ) : ℝ) ^ 3 *
      ((Ideal.absNorm (cubeFreeRemainder (Ideal.span {u.val})) : ℕ) : ℝ) := by
  have h := congrArg (fun J : Id => ((Ideal.absNorm J : ℕ) : ℝ))
    (original_FreeRow_principal_ideal_base3 u).1
  simpa only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] using h.symm

/-- EXACT weighted Fubini of ORIGINAL labelled FreeRow ELEMENTS by
    their genuine squarefree cube-root IDEAL. Every original row and
    its weight occurs once, even when several element associates
    determine the same principal ideal. No density or weight-spread
    hypothesis is used. -/
theorem original_FreeRow_cube_fiber_weighted_reindex
    (rows : Finset FreeRow) (rho : FreeRow → ℝ)
    (amplitude : FreeRow → ℂ) :
    (∑ u ∈ rows, rho u * ‖amplitude u‖ ^ 2) =
      ∑ C ∈ rows.image (fun u =>
        squarefreeCubeRoot (Ideal.span {u.val})),
        ∑ u ∈ rows with
          squarefreeCubeRoot (Ideal.span {u.val}) = C,
          rho u * ‖amplitude u‖ ^ 2 := by
  let g : FreeRow → Id := fun u =>
    squarefreeCubeRoot (Ideal.span {u.val})
  have hmaps : ∀ u ∈ rows, g u ∈ rows.image g := by
    intro u hu
    exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
  simpa only [g] using
    (Finset.sum_fiberwise_of_maps_to
      (s := rows) (t := rows.image g) (g := g) hmaps
      (fun u => rho u * ‖amplitude u‖ ^ 2)).symm

/-- Concrete OAI ideal counting already gives an explicit constant
    128 for the number of distinct squarefree cube-root ideals
    arising from original sixth-free ELEMENT rows of norm <= U.
    No average multiplicity or abstract ideal-density premise.
    Unit associates may share the same root and only reduce count. -/
theorem original_FreeRow_cube_root_ideal_count_le
    (rows : Finset FreeRow) (U : ℝ) (hU : 1 ≤ U)
    (hRows : ∀ u ∈ rows,
      ((Ideal.absNorm (Ideal.span {u.val}) : ℕ) : ℝ) ≤ U) :
    ((rows.image (fun u =>
      squarefreeCubeRoot (Ideal.span {u.val}))).card : ℝ) ≤
        128 * U ^ (1 / 3 : ℝ) := by
  have hU0 : 0 ≤ U := by linarith
  have hRoot : 1 ≤ U ^ (1 / 3 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
      hU (by norm_num : (0 : ℝ) ≤ (1 / 3 : ℝ))
    simpa using h
  have hBound (u : FreeRow) (hu : u ∈ rows) :
      ((Ideal.absNorm (squarefreeCubeRoot
        (Ideal.span {u.val})) : ℕ) : ℝ) ≤
        U ^ (1 / 3 : ℝ) := by
    let I : Id := Ideal.span {u.val}
    let C : Id := squarefreeCubeRoot I
    let R : Id := cubeFreeRemainder I
    have hR1 : 1 ≤ ((Ideal.absNorm R : ℕ) : ℝ) :=
      norm_one_le (cubeFreeRemainder_ne_zero I)
    have hCpos : 0 ≤ ((Ideal.absNorm C : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    have hCubed :
        (((Ideal.absNorm C : ℕ) : ℝ) ^ 3) ≤ U := by
      calc
        _ = ((Ideal.absNorm C : ℕ) : ℝ) ^ 3 * 1 := by ring
        _ ≤ ((Ideal.absNorm C : ℕ) : ℝ) ^ 3 *
            ((Ideal.absNorm R : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hR1 (by positivity)
        _ = ((Ideal.absNorm I : ℕ) : ℝ) := by
          simpa only [C, R, I] using
            (original_FreeRow_cube_ideal_norm_identity u).symm
        _ ≤ U := hRows u hu
    have hPower :
        ((Ideal.absNorm C : ℕ) : ℝ) ^ (3 : ℝ) ≤ U := by
      simpa only [Real.rpow_ofNat] using hCubed
    have hCubeRoot :=
      (Real.le_rpow_inv_iff_of_pos hCpos hU0
        (by norm_num : (0 : ℝ) < 3)).mpr hPower
    simpa only [C, I, one_div] using hCubeRoot
  apply DescentFiberCost.finite_ideal_count_real
    (rows.image (fun u => squarefreeCubeRoot (Ideal.span {u.val})))
    (U ^ (1 / 3 : ℝ)) hRoot
  · intro C hC
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hC
    exact squarefreeCubeRoot_ne_zero _
  · intro C hC
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hC
    exact hBound u hu

/-- This is the ORIGINAL OAI 128X ideal count instantiated on
    one genuine Eisenstein norm-dyadic shell. It supplies the
    exact 256*2^k cap used in our elementary zeta(2), zeta(3)
    finite dyadic argument. The ideal support can be any finite
    subset of nonzero ideals (including squarefree cube roots). -/
theorem original_ideal_dyadic_shell_count_le
    (carrier : Finset Id) (hnz : ∀ I ∈ carrier, I ≠ 0)
    (k : ℕ) :
    (((carrier.filter (fun I =>
      (2 : ℝ) ^ k ≤ (Ideal.absNorm I : ℝ) ∧
      (Ideal.absNorm I : ℝ) < (2 : ℝ) ^ (k + 1))).card : ℕ) : ℝ) ≤
        256 * (2 : ℝ) ^ k := by
  let shell : Finset Id := carrier.filter (fun I =>
      (2 : ℝ) ^ k ≤ (Ideal.absNorm I : ℝ) ∧
      (Ideal.absNorm I : ℝ) < (2 : ℝ) ^ (k + 1))
  have hOne : 1 ≤ (2 : ℝ) ^ (k + 1) :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hNZ : ∀ I ∈ shell, I ≠ 0 := by
    intro I hI
    exact hnz I (Finset.mem_filter.mp hI).1
  have hBound : ∀ I ∈ shell,
      (Ideal.absNorm I : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
    intro I hI
    exact (Finset.mem_filter.mp hI).2.2.le
  have hc := DescentFiberCost.finite_ideal_count_real
    shell ((2 : ℝ) ^ (k + 1)) hOne hNZ hBound
  change (shell.card : ℝ) ≤ 256 * (2 : ℝ) ^ k
  calc
    _ ≤ 128 * (2 : ℝ) ^ (k + 1) := hc
    _ = 256 * (2 : ℝ) ^ k := by
      rw [pow_succ]
      ring

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
  rw [MulChar.pow_apply' (canonicalSextic P hg)
    (by norm_num : (2 : ℕ) ≠ 0) (Ideal.Quotient.mk P u)] at h
  exact h

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
  by_cases hc : c ∈ P
  · simpa [hc] using h
  · simpa [hc] using h


/-! ## Source-exact three harmonic D bill, without false scalar W -/

/-- In the literal original source, W=v*Q^(-w), not Q^(-w).
    The row-independent object is q=Q^(-w), with star(v)*W=q
    whenever v has norm one. -/
theorem original_Physical_W_is_row_sextic
    (Q : ℝ) (v w : ℂ) :
    ProbeEuler.coordW Q v w = v * (Q : ℂ) ^ (-w) := rfl

/-- The source phase equation is a CONSEQUENCE of unit-modulus
    sextic character, not an independence assumption. -/
theorem original_Physical_vinv_W_eq_q
    (Q : ℝ) (v w : ℂ) (hv : star v * v = 1) :
    star v * ProbeEuler.coordW Q v w = (Q : ℂ) ^ (-w) := by
  unfold ProbeEuler.coordW
  calc
    _ = (star v * v) * (Q : ℂ) ^ (-w) := by ring
    _ = (Q : ℂ) ^ (-w) := by rw [hv]; ring

/-- Literal compensated normalized D-bill in original OAI
    ProbeLocal coordinates. The three leading terms remain
    uncombined, preserving cubic, sextic and principal windings. -/
theorem original_Physical_D_three_harmonics
    (Q : ℝ) (eta v x w z : ℂ)
    (hUnit : star v * v = 1)
    (hV : 1 - ProbeEuler.coordV Q z ≠ 0)
    (hD : 1 - ProbeEuler.coordD Q eta v x ≠ 0) :
    let V := ProbeEuler.coordV Q z
    let W := ProbeEuler.coordW Q v w
    let D := ProbeEuler.coordD Q eta v x
    let q := (Q : ℂ) ^ (-w)
    (1 - V) * (1 - W) / (1 - D) * (star v - q) *
       (V / (1 - V) - D) =
      -star v * D + 2 * q * D - star v * D * W ^ 2 +
        star v * (V * (1 + D) - D ^ 2) *
          (1 - W) ^ 2 / (1 - D) := by
  dsimp
  rw [← original_Physical_vinv_W_eq_q Q v w hUnit]
  field_simp [hV, hD]
  simp only [starRingEnd_apply]
  ring

/-- In the ORIGINAL physical coordinates, the W² cross term is a
    TRUE PRINCIPAL ROW HARMONIC (eta itself may depend on the prime).
    It is NOT another cubic column and cannot be paid by a cubic
    large sieve without an independent cancellation. -/
theorem original_Physical_DW2_is_row_principal
    (Q : ℝ) (eta v x w : ℂ) (hUnit : star v * v = 1) :
    star v * ProbeEuler.coordD Q eta v x *
       (ProbeEuler.coordW Q v w) ^ 2 =
      eta * (Q : ℂ) ^ (-x) * ((Q : ℂ) ^ (-w)) ^ 2 := by
  unfold ProbeEuler.coordD ProbeEuler.coordW
  calc
    _ = eta * (star v * v) ^ 2 *
        (Q : ℂ) ^ (-x) * ((Q : ℂ) ^ (-w)) ^ 2 := by ring
    _ = eta * (Q : ℂ) ^ (-x) * ((Q : ℂ) ^ (-w)) ^ 2 := by
      rw [hUnit]
      ring

/-- The other formerly-absolute size Q^(-Re(x)-Re(w))
    term is the TRUE sextic harmonic q*eta*star(v)*Q^(-x).
    n=6 fixed-order large sieve matching is still an
    explicit separate analytic hypothesis. -/
theorem original_Physical_qD_is_row_sextic
    (Q : ℝ) (eta v x w : ℂ) :
    (Q : ℂ) ^ (-w) * ProbeEuler.coordD Q eta v x =
      eta * star v * (Q : ℂ) ^ (-x) * (Q : ℂ) ^ (-w) := by
  unfold ProbeEuler.coordD
  ring

end SevenEighths.CubeFreeRowAdapter
end

#print axioms SevenEighths.CubeFreeRowAdapter.actual_ideal_base3_factorization
#print axioms SevenEighths.CubeFreeRowAdapter.sixthFree_ideal_sqFree_mul_cube_cubeFree
#print axioms SevenEighths.CubeFreeRowAdapter.original_FreeRow_principal_ideal_base3
#print axioms SevenEighths.CubeFreeRowAdapter.original_FreeRow_cube_ideal_norm_identity
#print axioms SevenEighths.CubeFreeRowAdapter.original_FreeRow_cube_fiber_weighted_reindex
#print axioms SevenEighths.CubeFreeRowAdapter.original_FreeRow_cube_root_ideal_count_le
#print axioms SevenEighths.CubeFreeRowAdapter.original_ideal_dyadic_shell_count_le
#print axioms SevenEighths.CubeFreeRowAdapter.actual_ideal_base3_unique
#print axioms SevenEighths.CubeFreeRowAdapter.original_canonicalSextic_sq_eq_cubic
#print axioms SevenEighths.CubeFreeRowAdapter.original_canonical_cubic_cube_mask
#print axioms SevenEighths.CubeFreeRowAdapter.original_conjugated_cubic_cube_mask
#print axioms SevenEighths.CubeFreeRowAdapter.original_Physical_D_three_harmonics
#print axioms SevenEighths.CubeFreeRowAdapter.original_Physical_DW2_is_row_principal
#print axioms SevenEighths.CubeFreeRowAdapter.original_Physical_qD_is_row_sextic

end OAI

import RHLean.Geometry.NativeThetaCuspFiniteOverlap
import RHLean.Geometry.NativeThetaCuspShiftedPhase

/-!
# Shared-coordinate vacua for the actual conjugate-level shift

The original and shifted projective lattices are placed in the same actual
rational symplectic coordinates. Their self-duality and canonical half-root
phase supply every field needed by the finite vacuum construction. The
resulting overlap uses their actual subgroup relative index and the same
normalized rational Haar inner product.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/
TensorLatticeVacuaExistUnique.lean (`Good.vac`, `Good.overlap`) and
LevelStructureProperties.lean (`selfD_idq`). This specializes the finite
construction to the native projective coefficient lattice and fixed-five
conjugate level. General auxiliary tensor lattices, Weil covariance and
the global cusp-form span remain subsequent inputs. The source mirror
states no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField Module Matrix
open scoped Pointwise nonZeroDivisors BigOperators TensorProduct Classical ComplexConjugate

namespace RHLean.Geometry.NativeTheta.Cusp.ShiftedVacua

open RHLean.Analysis.AlpogeThin
open Formalism.HC Formalism.FrobeniusOrbits NativeRawHostPolarization
open NativePrescribedHermitian NativeIntegralSymplectic

variable {φ : Frame} (H : HostRaw φ)

section Coordinates

variable (B : Ideal (𝓞 H.E))
  (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
  {N : ℕ} {κ ι : Type} [Fintype κ] [Fintype ι]

/-- The same symplectic coordinates for every lattice in the original field
ambient, using the proved inverse of its rationalization equivalence. -/
def coordinates (b : Basis (ι ⊕ ι) ℤ (twistedLattice H B N)) :
    (κ → Fin N → H.E) ≃ₗ[ℚ] (Matrix κ ι ℚ × Matrix κ ι ℚ) :=
  (LinearEquiv.piCongrRight fun _ : κ => (Ambient.equiv H B hB N).symm).trans
    (RationalCoordinates.coord b)

end Coordinates

section Rows

variable {N : ℕ} {κ : Type}

/-- The literal row inclusion of the same integral module. -/
def rowInclusion (L : Submodule (𝓞 H.E) (Fin N → H.E)) :
    (κ → L) →+ (κ → Fin N → H.E) where
  toFun x a := x a
  map_zero' := rfl
  map_add' _ _ := rfl

end Rows

section Prescribed

variable [IsCMField H.E]
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (G : NativeGeometricHost H.E)
    (hΨ : ∀ τ : H.E →+* ℂ, G.InPsi τ ↔ τ ∈ H.cmType)
    (hconj : ∀ (τ : H.E →+* ℂ) (x : H.E), τ (H.conj x) = conj (τ x))
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m)
    {κ ι : Type} [Fintype κ] [Fintype ι]
    (b : Basis (ι ⊕ ι) ℤ (prescribedLattice H B k m))
    (hb : IsSymplecticBasis
      (prescribedGeometricDatum H B hB G hΨ hconj hbar k m j hk hj).EF b)

include G hΨ hconj hbar hk hj hb in
/-- Rational symplectic coordinates preserve the exact native ambient
trace pairing, with every original diagonal sign. -/
theorem coordinates_pairing (x y : κ → Fin (k + m - 1) → H.E) :
    FiniteOverlap.omega (coordinates H B hB b x) (coordinates H B hB b y) =
      ∑ a, Ambient.pair H (negTail (k + m - 1) (m - j)) (x a) (y a) := by
  let D := prescribedGeometricDatum H B hB G hΨ hconj hbar k m j hk hj
  calc
    _ = ∑ a, RationalCoordinates.form D
        ((Ambient.equiv H B hB (k + m - 1)).symm (x a))
        ((Ambient.equiv H B hB (k + m - 1)).symm (y a)) :=
      RationalCoordinates.coord_pairing D b hb _ _
    _ = _ := by
      refine Finset.sum_congr rfl fun a _ => ?_
      unfold RationalCoordinates.form
      rw [show D.EF = prescribedTraceForm H B hB k m j from
        prescribedGeometricDatum_form H B hB G hΨ hconj hbar k m j hk hj]
      change (twistedTraceForm H B hB (negTail (k + m - 1) (m - j))).baseChange ℚ
        ((Ambient.equiv H B hB (k + m - 1)).symm (x a))
        ((Ambient.equiv H B hB (k + m - 1)).symm (y a)) = _
      rw [Ambient.equiv_pairing, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- Row coordinates of the literal integral lattice. -/
def rowCoordinates (L : Submodule (𝓞 H.E) (Fin (k + m - 1) → H.E)) :
    (κ → L) →+ (Matrix κ ι ℚ × Matrix κ ι ℚ) :=
  (coordinates H B hB b).toLinearMap.toAddMonoidHom.comp (rowInclusion H L)

/-- The actual coordinate subgroup, with no chosen finite quotient. -/
def lattice (L : Submodule (𝓞 H.E) (Fin (k + m - 1) → H.E)) :
    AddSubgroup (Matrix κ ι ℚ × Matrix κ ι ℚ) := (rowCoordinates H B hB k m b L).range

/-- One phase on the entire coordinate ambient; its field expression is
identified with the actual prescribed datum's rational phase. -/
def phase (p : Matrix κ ι ℚ × Matrix κ ι ℚ) : ℂ :=
  ShiftedPhase.phase H (negTail (k + m - 1) (m - j)) G.w0
    ((coordinates H B hB b).symm p)

theorem phase_zero : phase H B hB G k m j b (0 : Matrix κ ι ℚ × Matrix κ ι ℚ) = 1 := by
  rw [phase, map_zero, ShiftedPhase.phase_zero]

theorem phase_mul_conj (p : Matrix κ ι ℚ × Matrix κ ι ℚ) :
    phase H B hB G k m j b p * conj (phase H B hB G k m j b p) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hn := ShiftedPhase.norm_phase H (negTail (k + m - 1) (m - j)) G.w0
    ((coordinates H B hB b).symm p)
  change ((‖phase H B hB G k m j b p‖ ^ 2 : ℝ) : ℂ) = 1
  change ‖phase H B hB G k m j b p‖ = 1 at hn
  rw [hn, one_pow, Complex.ofReal_one]

include hΨ hconj hbar hk hj hb in
/-- Every finite-vacuum hypothesis is proved from the actual self-dual
lattice, the original integral CM action and the common half-root phase. -/
theorem good_lattice
    {L : Submodule (𝓞 H.E) (Fin (k + m - 1) → H.E)}
    (hL : ShiftedLattice.SelfDual H (negTail (k + m - 1) (m - j)) L) :
    FiniteOverlap.Good (phase H B hB G k m j b)
      (lattice H B hB k m b (κ := κ) L) := by
  have : Module.Finite (𝓞 H.E) L := Module.Finite.iff_fg.mpr hL.1
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 H.E) L
  have : AddGroup.FG (κ → L) := Module.Finite.iff_addGroup_fg.1 inferInstance
  have hfg : (lattice H B hB k m b (κ := κ) L).FG :=
    (AddGroup.fg_iff_addSubgroup_fg _).1 (AddGroup.fg_range (rowCoordinates H B hB k m b L))
  have hrow (x : κ → L) : rowCoordinates H B hB k m b L x =
      coordinates H B hB b (rowInclusion H L x) := rfl
  have hself : ∀ p, p ∈ lattice H B hB k m b (κ := κ) L ↔
      ∀ p' ∈ lattice H B hB k m b L, ∃ z : ℤ, FiniteOverlap.omega p p' = z := by
    intro p
    constructor
    · rintro ⟨x, rfl⟩ p' ⟨y, rfl⟩
      choose z hz using fun a => (hL.2 (x a)).1 (x a).2 (y a) (y a).2
      refine ⟨∑ a, z a, ?_⟩
      rw [hrow, hrow, coordinates_pairing H B hB G hΨ hconj hbar k m j hk hj b hb]
      simpa only [rowInclusion, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Int.cast_sum] using
        Finset.sum_congr rfl fun a _ => hz a
    · intro h
      let x := (coordinates H B hB b).symm p
      have hx : ∀ a, x a ∈ L := by
        intro a
        apply (hL.2 (x a)).2
        intro y hy
        obtain ⟨z, hz⟩ := h (rowCoordinates H B hB k m b L (Pi.single a ⟨y, hy⟩))
          ⟨Pi.single a ⟨y, hy⟩, rfl⟩
        refine ⟨z, ?_⟩
        rw [← (coordinates H B hB b).apply_symm_apply p, hrow,
          coordinates_pairing H B hB G hΨ hconj hbar k m j hk hj b hb] at hz
        have he : rowInclusion H L (Pi.single a ⟨y, hy⟩) = Pi.single a y := by
          funext a'
          by_cases ha : a' = a
          · subst a'
            simp only [rowInclusion, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.single_eq_same]
          · simp only [rowInclusion, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.single_eq_of_ne ha,
              Submodule.coe_zero]
        rw [he] at hz
        have hs : (∑ a', Ambient.pair H (negTail (k + m - 1) (m - j))
            (x a') ((Pi.single a y : κ → Fin (k + m - 1) → H.E) a')) =
              Ambient.pair H (negTail (k + m - 1) (m - j)) (x a) y := by
          rw [Finset.sum_eq_single a]
          · rw [Pi.single_eq_same]
          · intro a' _ ha
            rw [Pi.single_eq_of_ne ha]
            simp [Ambient.pair]
          · intro ha
            exact (ha (Finset.mem_univ a)).elim
        exact hs ▸ hz
      refine ⟨fun a => ⟨x a, hx a⟩, ?_⟩
      change coordinates H B hB b x = p
      exact (coordinates H B hB b).apply_symm_apply p
  refine ⟨hfg, hself, ?_⟩
  rintro p ⟨x, rfl⟩
  constructor
  · change ShiftedPhase.phase H (negTail (k + m - 1) (m - j)) G.w0
      ((coordinates H B hB b).symm (coordinates H B hB b (rowInclusion H L x))) ^ 2 = 1
    rw [LinearEquiv.symm_apply_apply]
    exact ShiftedPhase.phase_sq H G.w0 hL _ fun a => (x a).2
  · rintro p' ⟨y, rfl⟩
    change ShiftedPhase.phase H _ G.w0
        ((coordinates H B hB b).symm
          (coordinates H B hB b (rowInclusion H L x) +
            coordinates H B hB b (rowInclusion H L y))) = _
    simp only [phase, hrow, map_add, LinearEquiv.symm_apply_apply]
    rw [ShiftedPhase.phase_add H G.w0
      (ShiftedPhase.prescribed_halfRoot H G hbar) hL (rowInclusion H L x) (rowInclusion H L y)
      (fun a => (x a).2) (fun a => (y a).2),
      coordinates_pairing H B hB G hΨ hconj hbar k m j hk hj b hb]

include hΨ hconj hbar hk hj hb in
/-- The normalized vacua and their exact overlap are constructed for the
original lattice and its literal conjugate-level shift in common coordinates. -/
theorem shifted_vacua
    {P : Ideal (𝓞 H.E)} (hP0 : P ≠ ⊥) (hP1 : P ≠ ⊤)
    (hPc : IsCoprime P (H.conj • P)) :
    let L := prescribedLattice H B k m
    let L' := ShiftedLattice.idq P (H.conj • P) L
    ∃ v v' : Matrix κ ι ℚ → ℂ,
      FiniteOverlap.IsVac (phase H B hB G k m j b) (lattice H B hB k m b L) v ∧
      FiniteOverlap.IsVac (phase H B hB G k m j b) (lattice H B hB k m b L') v' ∧
      ((lattice (κ := κ) H B hB k m b L').relIndex (lattice (κ := κ) H B hB k m b L) : ℝ) *
        ‖ip v v'‖ ^ 2 = 1 := by
  let L := prescribedLattice H B k m
  have hL := ShiftedLattice.twisted_selfDual H B hB (negTail (k + m - 1) (m - j))
  have hL' := ShiftedLattice.selfDual_idq H (negTail (k + m - 1) (m - j)) hP0 hP1 hPc hL
  have hgood := good_lattice H B hB G hΨ hconj hbar k m j hk hj b hb (κ := κ) hL
  have hgood' := good_lattice H B hB G hΨ hconj hbar k m j hk hj b hb (κ := κ) hL'
  obtain ⟨v, hv, _⟩ := FiniteOverlap.Good.vac hgood
  obtain ⟨v', hv', _⟩ := FiniteOverlap.Good.vac hgood'
  exact ⟨v, v', hv, hv', FiniteOverlap.Good.overlap
    (phase_zero H B hB G k m j b) (phase_mul_conj H B hB G k m j b) hgood hgood' hv hv'⟩

end Prescribed

/-- Construct the shared-coordinate pair of normalized vacua at the actual
fixed-five conjugate level on the same prescribed native datum. -/
theorem exists_native_shifted_vacua
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (B : Ideal (𝓞 (nativeDyadicHostRaw e q d he hH).E))
    (hB : let H := nativeDyadicHostRaw e q d he hH
      differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) (n : ℕ) :
    let H := nativeDyadicHostRaw e q d he hH
    let _ : IsCMField H.E := (nativeDyadicHostAx e q d he hH).der.cm
    let _ : IsCMField (nativeDyadicHostAx e q d he hH).E :=
      (nativeDyadicHostAx e q d he hH).der.cm
    let G := nativeDyadicGeometricHostOfDerived e q d he hH
    let D := nativeDyadicPrescribedGeometricDatum e q d he hH B hB k m j hk hj
    let g := finrank ℚ H.E / 2 * (D.p + D.q)
    ∃ b : Basis (Fin g ⊕ Fin g) ℤ D.La, IsSymplecticBasis D.EF b ∧
      ∃ P : Ideal (𝓞 H.E), P ≠ ⊤ ∧ P ≠ ⊥ ∧ IsCoprime P (H.conj • P) ∧
        IsCoprime P (Ideal.span {(2 : 𝓞 H.E)}) ∧
        P * (H.conj • P) = Ideal.span {(5 : 𝓞 H.E)} ∧
        let L := prescribedLattice H B k m
        let L' := ShiftedLattice.idq P (H.conj • P) L
        ∃ v v' : Matrix (Fin n) (Fin g) ℚ → ℂ,
          FiniteOverlap.IsVac (phase H B hB G k m j b) (lattice H B hB k m b L) v ∧
          FiniteOverlap.IsVac (phase H B hB G k m j b) (lattice H B hB k m b L') v' ∧
          ((lattice (κ := Fin n) H B hB k m b L').relIndex
              (lattice (κ := Fin n) H B hB k m b L) : ℝ) *
            ‖ip v v'‖ ^ 2 = 1 := by
  let H := nativeDyadicHostRaw e q d he hH
  let _ : IsCMField H.E := (nativeDyadicHostAx e q d he hH).der.cm
  let _ : IsCMField (nativeDyadicHostAx e q d he hH).E :=
    (nativeDyadicHostAx e q d he hH).der.cm
  let G := nativeDyadicGeometricHostOfDerived e q d he hH
  let D := nativeDyadicPrescribedGeometricDatum e q d he hH B hB k m j hk hj
  have := D.fin
  have := D.proj
  have : Module.Finite ℤ D.La :=
    Module.Finite.trans (𝓞 (nativeDyadicHostAx e q d he hH).E) D.La
  have : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 (nativeDyadicHostAx e q d he hH).E) D.La
  have : Module.Free ℤ D.La := inferInstance
  obtain ⟨b, hb⟩ := exists_isSymplecticBasis_of_finrank D.alt D.unimod
    (NativeGeometricSymplectic.finrank_int_lattice D)
  obtain ⟨P, hP1, hP0, hPc, hPo, hP5⟩ := SplitLevel.exists_five_split_level e q d he hH
  refine ⟨b, hb, P, hP1, hP0, hPc, hPo, hP5, ?_⟩
  exact shifted_vacua H B hB G
    (nativeDyadicGeometricHostOfDerived_inPsi e q d he hH)
    (nativeDyadicHostRaw_prescribed_embedding_conj e q d he hH)
    (nativeDyadicGeometricHost_bar_eq e q d he hH)
    k m j hk hj b hb (κ := Fin n) hP0 hP1 hPc

end RHLean.Geometry.NativeTheta.Cusp.ShiftedVacua

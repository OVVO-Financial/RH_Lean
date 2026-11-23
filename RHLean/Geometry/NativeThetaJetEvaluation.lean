import RHLean.Geometry.NativeThetaHarmonicPolynomials

/-!
# The explicit formal-jet formula for native theta evaluation

This file constructs the polynomial evaluation operator appearing in
ShortValAt. It keeps the reciprocal beta, lattice index, cardinality of the
level-function set and power of the level separately. The total-degree
normalizer agrees with one linear operator on each homogeneous degree,
including the zero polynomial.

The column jets can be computed from the source's actual formal group law,
gauge and germs: Dof, the ordered iterated derivatives DmonOf, and the
constant coefficient of the gauge-corrected germ. No theta evaluation map or
linearity conclusion is supplied as a hypothesis. The existence of charts
and section germs, independence of charts, and descent to geometric sections
are separate geometric obligations.

The coefficient field K is independent of the CM host field and of the
algebra S in which an evaluation is made. In the application K is the
original cover field Y.d.c₂.F. The lattice index argument must be specialized
to the original mIdx; this file does not manufacture that geometric datum.

Mathematical source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/
ToroidalCompactification/CocycleRightZeroThd.lean, Dof, DmonOf, DpolyOf,
FB.hL and FB.nabVal; Formalism/LocalToGlobal/ProjectiveLattices/IsThRule.lean,
colOf; ThShort.lean, ShortValAt; and Development/AbelianVarietyTheory/Proofs/
CuspFormEvaluations/ShortThetaValueLinearInPolynomial.lean,
ShortValueLinear.sum_support_eq_constr and formula_linear.
The source archive/mirror states no license; this notice preserves
attribution without assigning a new license.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace RHLean.Geometry.NativeTheta.JetEvaluation

section Coefficients

variable {ι K S : Type} [CommRing K] [CommRing S] [Algebra K S]

/-- The linear coefficient contraction, constructed from its monomial values. -/
def coefficientContraction (G : (ι →₀ ℕ) → S) : MvPolynomial ι K →ₗ[K] S :=
  (MvPolynomial.basisMonomials ι K).constr K G

theorem coefficientContraction_apply (G : (ι →₀ ℕ) → S)
    (P : MvPolynomial ι K) :
    coefficientContraction G P =
      ∑ m ∈ P.support, algebraMap K S (P.coeff m) * G m := by
  classical
  rw [coefficientContraction, Module.Basis.constr_apply]
  change (∑ m ∈ P.support, P.coeff m • G m) = _
  simp only [Algebra.smul_def]

theorem coefficientContraction_monomial (G : (ι →₀ ℕ) → S)
    (m : ι →₀ ℕ) (c : K) :
    coefficientContraction G (monomial m c) = algebraMap K S c * G m := by
  classical
  rw [coefficientContraction_apply]
  by_cases hc : c = 0
  · simp [hc]
  · simp [MvPolynomial.support_monomial, hc, MvPolynomial.coeff_monomial]

end Coefficients

section FormalGerms

variable {S : Type} [CommRing S] {d : ℕ}

/-- The source's formal series in n copies of d coordinates. -/
abbrev Series (S : Type) [CommRing S] (n d : ℕ) :=
  MvPowerSeries (Fin n × Fin d) S

def coordinatePoint (n : ℕ) (j : Fin n) : Fin d → Series S n d :=
  fun i => MvPowerSeries.X (j, i)

def substituteCopies {m n : ℕ} (a : Fin m → Fin d → Series S n d)
    (f : Series S m d) : Series S n d :=
  MvPowerSeries.subst (fun p : Fin m × Fin d => a p.1 p.2) f

/-- The invariant directional derivative defined by the given formal group
law coefficients. No additive-group replacement is made. -/
def directionalDerivative (F : Fin d → Series S 2 d) (u : Fin d → S)
    (f : Series S 1 d) : Series S 1 d :=
  ∑ j : Fin d,
    (∑ i : Fin d, MvPowerSeries.C (u i) *
      substituteCopies ![coordinatePoint 1 0, 0]
        (MvPowerSeries.pderiv ((1 : Fin 2), i) (F j))) *
      MvPowerSeries.pderiv ((0 : Fin 1), j) f

/-- This retains the source's ordered iteration of all row directions. -/
def monomialDerivative {ι : Type} [Fintype ι]
    (F : Fin d → Series S 2 d) (u : ι → Fin d → S) (m : ι →₀ ℕ)
    (f : Series S 1 d) : Series S 1 d :=
  (Finset.univ : Finset ι).toList.foldr
    (fun l g => (directionalDerivative F (u l))^[m l] g) f

def polynomialDerivative {ι : Type} [Fintype ι]
    (F : Fin d → Series S 2 d) (u : ι → Fin d → S)
    (P : MvPolynomial ι S) (f : Series S 1 d) : Series S 1 d :=
  ∑ m ∈ P.support, MvPowerSeries.C (P.coeff m) * monomialDerivative F u m f

/-- Pull the actual two-variable gauge back along x ↦ (x,[w0]x). -/
def lineGauge (actW0 : Fin d → Series S 1 d) (h : Series S 2 d) :
    Series S 1 d :=
  substituteCopies ![coordinatePoint 1 0,
    fun i => substituteCopies ![coordinatePoint 1 0] (actW0 i)] h

variable [Algebra ℚ S]

def exponentialSeries {n : ℕ} (f : Series S n d) : Series S n d :=
  PowerSeries.subst f (PowerSeries.exp S)

def gaugedGerm (actW0 : Fin d → Series S 1 d) (h : Series S 2 d)
    (m : ℕ) (f : Series S 1 d) : Series S 1 d :=
  f * exponentialSeries ((m : S) • lineGauge actW0 h)

/-- The source's nabVal formula, with the formal group coefficients,
the action of w0, the gauge and the germ given explicitly. -/
def formalNablaValue {ι : Type} [Fintype ι]
    (F : Fin d → Series S 2 d) (actW0 : Fin d → Series S 1 d)
    (h : Series S 2 d) (m : ℕ) (f : Series S 1 d)
    (u : ι → Fin d → S) (P : MvPolynomial ι S) : S :=
  MvPowerSeries.constantCoeff
    (polynomialDerivative F u P (gaugedGerm actW0 h m f))

/-- A column jet is computed by iterating the given formal derivatives on
the same gauge-corrected germ, then taking its constant coefficient. -/
def formalColumnJet {ι : Type} [Fintype ι]
    (F : Fin d → Series S 2 d) (actW0 : Fin d → Series S 1 d)
    (h : Series S 2 d) (m : ℕ) (f : Series S 1 d)
    (u : ι → Fin d → S) (α : ι →₀ ℕ) : S :=
  MvPowerSeries.constantCoeff
    (monomialDerivative F u α (gaugedGerm actW0 h m f))

theorem formalNablaValue_eq_contraction {ι : Type} [Fintype ι]
    (F : Fin d → Series S 2 d) (actW0 : Fin d → Series S 1 d)
    (h : Series S 2 d) (m : ℕ) (f : Series S 1 d)
    (u : ι → Fin d → S) (P : MvPolynomial ι S) :
    formalNablaValue F actW0 h m f u P =
      coefficientContraction (formalColumnJet F actW0 h m f u) P := by
  classical
  simp only [formalNablaValue, polynomialDerivative, map_sum, map_mul,
    MvPowerSeries.constantCoeff_C, coefficientContraction_apply,
    Algebra.algebraMap_self, RingHom.id_apply, formalColumnJet]

theorem formalNablaValue_monomial {ι : Type} [Fintype ι]
    (F : Fin d → Series S 2 d) (actW0 : Fin d → Series S 1 d)
    (h : Series S 2 d) (m : ℕ) (f : Series S 1 d)
    (u : ι → Fin d → S) (α : ι →₀ ℕ) :
    formalNablaValue F actW0 h m f u (monomial α 1) =
      formalColumnJet F actW0 h m f u α := by
  rw [formalNablaValue_eq_contraction, coefficientContraction_monomial,
    map_one, one_mul]

end FormalGerms

section ShortValue

variable {T K S Q J : Type} [Fintype T] {r : T → ℕ} {n : ℕ}
  [Field K] [CommRing S] [Algebra K S] [Fintype Q] [Fintype J]

abbrev Row (T : Type) (r : T → ℕ) := Σ t : T, Fin (r t)

/-- The literal column restriction used by the source's colOf. -/
def columnExponent (m : Letter T r n →₀ ℕ) (b : Fin n) : Row T r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun l => m ⟨l.1, l.2, b⟩

@[simp] theorem columnExponent_apply (m : Letter T r n →₀ ℕ)
    (b : Fin n) (l : Row T r) :
    columnExponent m b l = m ⟨l.1, l.2, b⟩ := rfl

/-- All four source normalizers remain visible, in their original order. -/
def shortNormalizer (β : K) (index N D : ℕ) : K :=
  β⁻¹ * (index : K)⁻¹ * (Nat.card Q : K)⁻¹ * ((N : K) ^ D)⁻¹

/-- The finite ShortValAt expression before descent from the evaluation
algebra. Q is the actual level-function set and J indexes the lattice lifts. -/
def rawShortValue (β : K) (index N : ℕ) (w : Q → K)
    (jet : Q → J → Fin n → (Row T r →₀ ℕ) → S)
    (P : MvPolynomial (Letter T r n) K) : S :=
  algebraMap K S (shortNormalizer (Q := Q) β index N P.totalDegree) *
    ∑ q, algebraMap K S (w q) *
      ∑ j, ∑ m ∈ P.support, algebraMap K S (P.coeff m) *
        ∏ b, jet q j b (columnExponent m b)

/-- The finite sums agree with the source's exact finsum expression. -/
theorem rawShortValue_eq_source_formula (β : K) (index N : ℕ) (w : Q → K)
    (jet : Q → J → Fin n → (Row T r →₀ ℕ) → S)
    (P : MvPolynomial (Letter T r n) K) :
    rawShortValue β index N w jet P =
      algebraMap K S (β⁻¹ * (index : K)⁻¹ * (Nat.card Q : K)⁻¹ *
        ((N : K) ^ P.totalDegree)⁻¹) *
        ∑ᶠ q, algebraMap K S (w q) *
          ∑ j, ∑ m ∈ P.support, algebraMap K S (P.coeff m) *
            ∏ b, jet q j b (columnExponent m b) := by
  simp only [rawShortValue, shortNormalizer, finsum_eq_sum_of_fintype]

/-- Construct the single linear operator for the prescribed homogeneous
degree. Its column values and every normalization factor are explicit. -/
def shortValueLinear (β : K) (index N D : ℕ) (w : Q → K)
    (jet : Q → J → Fin n → (Row T r →₀ ℕ) → S) :
    MvPolynomial (Letter T r n) K →ₗ[K] S :=
  shortNormalizer (Q := Q) β index N D •
    ∑ q, w q • ∑ j,
      coefficientContraction (fun m => ∏ b, jet q j b (columnExponent m b))

theorem shortValueLinear_apply (β : K) (index N D : ℕ) (w : Q → K)
    (jet : Q → J → Fin n → (Row T r →₀ ℕ) → S)
    (P : MvPolynomial (Letter T r n) K) :
    shortValueLinear β index N D w jet P =
      algebraMap K S (shortNormalizer (Q := Q) β index N D) *
        ∑ q, algebraMap K S (w q) *
          ∑ j, ∑ m ∈ P.support, algebraMap K S (P.coeff m) *
            ∏ b, jet q j b (columnExponent m b) := by
  classical
  simp only [shortValueLinear, LinearMap.smul_apply, LinearMap.sum_apply,
    coefficientContraction_apply, Algebra.smul_def]

/-- The zero polynomial causes no exception to the fixed-degree formula:
its coefficient contraction is zero even though its totalDegree is zero. -/
theorem rawShortValue_eq_linear_of_homogeneous (β : K) (index N D : ℕ)
    (w : Q → K) (jet : Q → J → Fin n → (Row T r →₀ ℕ) → S)
    (P : MvPolynomial (Letter T r n) K) (hP : P.IsHomogeneous D) :
    rawShortValue β index N w jet P = shortValueLinear β index N D w jet P := by
  classical
  by_cases hP0 : P = 0
  · subst P
    simp [rawShortValue]
  · rw [rawShortValue, shortValueLinear_apply, hP.totalDegree hP0]

/-- The original finite-sum linearity, now obtained from the explicitly
constructed operator rather than assumed as a theta-section property. -/
theorem rawShortValue_sum {I : Type} [Fintype I]
    (β : K) (index N D : ℕ) (w : Q → K)
    (jet : Q → J → Fin n → (Row T r →₀ ℕ) → S)
    (c : I → K) (P : I → MvPolynomial (Letter T r n) K)
    (hP : ∀ i, (P i).IsHomogeneous D) :
    rawShortValue β index N w jet (∑ i, c i • P i) =
      ∑ i, algebraMap K S (c i) * rawShortValue β index N w jet (P i) := by
  classical
  have hsum : (∑ i, c i • P i).IsHomogeneous D := by
    change (∑ i, c i • P i) ∈ homogeneousSubmodule (Letter T r n) K D
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hP i)
  rw [rawShortValue_eq_linear_of_homogeneous β index N D w jet _ hsum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Algebra.smul_def,
    rawShortValue_eq_linear_of_homogeneous β index N D w jet _ (hP i)]

theorem rawShortValue_eq_linear_of_mem_HHa
    (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ)
    (β : K) (index N : ℕ) (w : Q → K)
    (jet : Q → J → Fin n → (Row T r →₀ ℕ) → S)
    (P : MvPolynomial (Letter T r n) K) (hP : P ∈ HHa r n K cc isX a) :
    rawShortValue β index N w jet P =
      shortValueLinear β index N (∑ t, ∑ i : Fin (r t), a t i) w jet P :=
  rawShortValue_eq_linear_of_homogeneous β index N _ w jet P
    (isHomogeneous_of_rowDeg hP.2.2)

/-- Compute every column jet from the same formal group, action, gauge and
chosen section germs. The derivative order multiplier is the original N². -/
def shortValueOfFormalGerms [Algebra ℚ S] {d : ℕ}
    (β : K) (index N : ℕ) (w : Q → K)
    (F : Fin d → Series S 2 d) (actW0 : Fin d → Series S 1 d)
    (h : Series S 2 d) (u : Row T r → Fin d → S)
    (germ : Q → J → Fin n → Series S 1 d)
    (P : MvPolynomial (Letter T r n) K) : S :=
  rawShortValue β index N w
    (fun q j b => formalColumnJet F actW0 h (N ^ 2) (germ q j b) u) P

/-- The computed column jets give exactly the monomial nabVal occurrences
in ShortValAt, with the original N² section-power parameter. -/
theorem shortValueOfFormalGerms_eq_source_formula [Algebra ℚ S] {d : ℕ}
    (β : K) (index N : ℕ) (w : Q → K)
    (F : Fin d → Series S 2 d) (actW0 : Fin d → Series S 1 d)
    (h : Series S 2 d) (u : Row T r → Fin d → S)
    (germ : Q → J → Fin n → Series S 1 d)
    (P : MvPolynomial (Letter T r n) K) :
    shortValueOfFormalGerms β index N w F actW0 h u germ P =
      algebraMap K S (β⁻¹ * (index : K)⁻¹ * (Nat.card Q : K)⁻¹ *
        ((N : K) ^ P.totalDegree)⁻¹) *
        ∑ᶠ q, algebraMap K S (w q) *
          ∑ j, ∑ m ∈ P.support, algebraMap K S (P.coeff m) *
            ∏ b, formalNablaValue F actW0 h (N ^ 2) (germ q j b) u
              (monomial (columnExponent m b) 1) := by
  simp only [shortValueOfFormalGerms, rawShortValue_eq_source_formula,
    formalNablaValue_monomial]

theorem shortValueOfFormalGerms_sum [Algebra ℚ S] {d : ℕ}
    {I : Type} [Fintype I]
    (β : K) (index N D : ℕ) (w : Q → K)
    (F : Fin d → Series S 2 d) (actW0 : Fin d → Series S 1 d)
    (h : Series S 2 d) (u : Row T r → Fin d → S)
    (germ : Q → J → Fin n → Series S 1 d)
    (c : I → K) (P : I → MvPolynomial (Letter T r n) K)
    (hP : ∀ i, (P i).IsHomogeneous D) :
    shortValueOfFormalGerms β index N w F actW0 h u germ (∑ i, c i • P i) =
      ∑ i, algebraMap K S (c i) *
        shortValueOfFormalGerms β index N w F actW0 h u germ (P i) :=
  rawShortValue_sum β index N D w _ c P hP

end ShortValue

end RHLean.Geometry.NativeTheta.JetEvaluation

end

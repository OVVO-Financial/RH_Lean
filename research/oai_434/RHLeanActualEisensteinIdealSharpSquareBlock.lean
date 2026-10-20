import OAI.NumberTheory.DirichletL.Hecke.LocalEulerIdentities

/-!
# OpenAI Lean 4.34.1: ACTUAL ideal-norm fiber = #919 norm source

THIS SOURCE IS TO COMPILE AGAINST openai/math/lean (Lean 4.34.1),
NOT against RH_Lean's currently pinned Lean 4.24.0. Its dependency
is the ORIGINAL Lean theorem
  ShortDraftHeckeBridge.normFiberCoeff_baseChange_eq_pairInverseCoeff
whose proof includes actual Eisenstein prime ideals, splitting,
inert/ramified primes, prime-square multiplicities, and the unit source.

The equality here uses genuine Ideal O with the actual
UniqueFactorizationMonoid.moebius on those ideals. Not a constructed
scalar proxy or invented sextic character.

For the PRINCIPAL norm source choose modulus-one χ=1. In OAI's
definitions the baseChange character is χ_{-3}, and the inverse pair
  pairAF 1 (baseChangeChar 1)
is the same arithmetic Dirichlet product
  μ_Z * (χ_{-3} μ_Z)
used by RH_Lean's constructed EisensteinNormCoefficients.

The physical square interval weight is applied AFTER the actual ideal
norm is taken and BEFORE all ideal labels are grouped. This equality
is term-by-term at every positive norm, with no analytic bound
or new source identification axiom.
-/

noncomputable section
open scoped BigOperators
namespace OAI
namespace ShortDraftHeckeBridge

/-- The ACTUAL Eisenstein ideal norm-fiber coefficient. -/
def rhleanActualEisensteinIdealNormFiber (n : ℕ) : ℂ :=
  normFiberCoeff (baseChangeWeight (1 : DirichletCharacter ℂ 1)) n

/-- The REAL principal quadratic pair-inverse coefficient, with
    OAI's genuine Dirichlet characters and Moebius coefficients. -/
def rhleanPrincipalPairNormCoefficient (n : ℕ) : ℂ :=
  pairAF (1 : DirichletCharacter ℂ 1)
    (baseChangeChar (1 : DirichletCharacter ℂ 1)) n

/-- PRIMARY PHYSICAL COEFFICIENT SEMANTICS: no hcoeff assumption!
    This is specialized directly from OAI's already-proved real-ideal
    theorem and its Dirichlet convolution agreement. -/
theorem rhlean_actual_ideal_norm_fiber_eq_principal_pairAF
    (n : ℕ) (hn : n ≠ 0) :
    rhleanActualEisensteinIdealNormFiber n =
      rhleanPrincipalPairNormCoefficient n := by
  unfold rhleanActualEisensteinIdealNormFiber
    rhleanPrincipalPairNormCoefficient
  calc
    normFiberCoeff
        (baseChangeWeight (1 : DirichletCharacter ℂ 1)) n =
      pairInverseCoeff (1 : DirichletCharacter ℂ 1)
        (baseChangeChar (1 : DirichletCharacter ℂ 1)) n :=
          normFiberCoeff_baseChange_eq_pairInverseCoeff
            (1 : DirichletCharacter ℂ 1) n hn
    _ = pairAF (1 : DirichletCharacter ℂ 1)
          (baseChangeChar (1 : DirichletCharacter ℂ 1)) n :=
            (pairAF_eq_pairInverseCoeff
              (1 : DirichletCharacter ℂ 1)
              (baseChangeChar (1 : DirichletCharacter ℂ 1)) n).symm

/-- The ORIGINAL half-open sharp square-block mask, in the complete
    TRUE ideal-fiber source. No smooth OAI probe is pretended equal. -/
def rhleanOriginalSquareBlockMask (R n : ℕ) : ℂ :=
  if R ^ 2 ≤ n ∧ n < (R + 1) ^ 2 then 1 else 0

/-- The true sharp physical coefficient on ONE ideal norm, with
    quadratic base-change rational cofactor d and genuine χ_-3(d). -/
def rhleanActualIdealSharpNormTerm (R U m : ℕ) : ℂ :=
  rhleanActualEisensteinIdealNormFiber m *
    ∑ d ∈ Finset.Icc 1 U,
      chiMinusThree d * rhleanOriginalSquareBlockMask R (m * d)

/-- The same physical source represented in the exact pairAF
    coordinates, without changing the cutoff or reweighting any n. -/
def rhleanPairAFSharpNormTerm (R U m : ℕ) : ℂ :=
  rhleanPrincipalPairNormCoefficient m *
    ∑ d ∈ Finset.Icc 1 U,
      chiMinusThree d * rhleanOriginalSquareBlockMask R (m * d)

/-- The true n-th ideal fiber contribution equals the entire pair
    coefficient at that SAME n and physical square-block multiplier. -/
theorem rhlean_actual_ideal_sharp_block_term_by_term
    (R U m : ℕ) (hm : 1 ≤ m) :
    rhleanActualIdealSharpNormTerm R U m =
      rhleanPairAFSharpNormTerm R U m := by
  unfold rhleanActualIdealSharpNormTerm rhleanPairAFSharpNormTerm
  rw [rhlean_actual_ideal_norm_fiber_eq_principal_pairAF m (by omega)]

/-- Exactly ALL norm-fiber terms, without any character averaging,
    mean/variance approximation, or missing square-block boundary. -/
theorem rhlean_actual_ideal_sharp_block_ALL_norms
    (R U : ℕ) :
    (∑ m ∈ Finset.Icc 1 U,
      rhleanActualIdealSharpNormTerm R U m) =
    ∑ m ∈ Finset.Icc 1 U,
      rhleanPairAFSharpNormTerm R U m := by
  apply Finset.sum_congr rfl
  intro m hm
  exact rhlean_actual_ideal_sharp_block_term_by_term
    R U m (Finset.mem_Icc.mp hm).1

/-- All ordered NORM PAIRS retain their signed complex product; the
    norm-fiber substitution is applied separately to each endpoint,
    before any absolute-value/moment inequality. -/
theorem rhlean_actual_ideal_sharp_block_ALL_norm_pairs
    (R U : ℕ) :
    (∑ m ∈ Finset.Icc 1 U, ∑ n ∈ Finset.Icc 1 U,
      rhleanActualIdealSharpNormTerm R U m *
        rhleanActualIdealSharpNormTerm R U n) =
    ∑ m ∈ Finset.Icc 1 U, ∑ n ∈ Finset.Icc 1 U,
      rhleanPairAFSharpNormTerm R U m *
        rhleanPairAFSharpNormTerm R U n := by
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [rhlean_actual_ideal_sharp_block_term_by_term
    R U m (Finset.mem_Icc.mp hm).1,
      rhlean_actual_ideal_sharp_block_term_by_term
        R U n (Finset.mem_Icc.mp hn).1]

#print axioms rhlean_actual_ideal_norm_fiber_eq_principal_pairAF
#print axioms rhlean_actual_ideal_sharp_block_term_by_term
#print axioms rhlean_actual_ideal_sharp_block_ALL_norms
#print axioms rhlean_actual_ideal_sharp_block_ALL_norm_pairs

end ShortDraftHeckeBridge
end OAI

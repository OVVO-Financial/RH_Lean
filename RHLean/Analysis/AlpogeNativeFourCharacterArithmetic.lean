import Mathlib
import RHLean.Analysis.NativePNTSignedSecondSelberg
import RHLean.Analysis.FiniteTorusFourierPairing

/-!
# Alpoge's FOUR CHARACTER TRACE rebuilt over RHLean's arithmetic

This is NOT an import or a re-branding of the external proof.
The physical population is RHLean's ACTUAL von Mangoldt prime-power
sum. The characters are REAL DirichletCharacter values on integers,
not invented independent matrix labels or additive characters mistaken
for multiplicative ones.

The character-color identity 1+chiB-chiA-chiA*chiB = 4*indicator
is proved on the genuinely unramified quadratic (±1) class. Every
nonquadratic/nonunit character value is returned as a literal finite
signed complement. The entire principal Gz is expressed via RHLean's
COMPLETE signed second Selberg recurrence.

No source power-saving, geometric HostFacts or RH theorem is assumed.
-/

noncomputable section
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- True physical von Mangoldt coefficient (including all prime powers)
and Alpoge's exact triangular kernel x/n-1. -/
def alpogeNativePrimePowerWeight (x : ℝ) (n : ℕ) : ℝ :=
  Λ n * (x / (n : ℝ) - 1)

/-- Alpoge's principal finite weighted prime-power source. -/
def alpogeNativePrincipalPrimeSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, alpogeNativePrimePowerWeight x n

/-- The same prime source twisted by an ACTUAL multiplicative
Dirichlet character on integers, with nonunits still present. -/
def alpogeNativeTwistedPrimeSum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
    (alpogeNativePrimePowerWeight x n : ℂ) * χ n

/-- The native version of Alpoge's Gz, with its actual Euler gamma term. -/
def alpogeNativeGzArithmetic (x : ℝ) : ℝ :=
  x * nativeLambdaRecip ⌊x⌋₊ - nativePsi ⌊x⌋₊ -
    x * Real.log x + (1 + Real.eulerMascheroniConstant) * x

/-- No approximations: finite weighted prime powers are exactly
x times the native reciprocal Lambda channel minus native psi. -/
theorem alpogeNativePrincipalPrimeSum_eq (x : ℝ) :
    alpogeNativePrincipalPrimeSum x =
      x * nativeLambdaRecip ⌊x⌋₊ - nativePsi ⌊x⌋₊ := by
  unfold alpogeNativePrincipalPrimeSum alpogeNativePrimePowerWeight
    nativeLambdaRecip nativePsi
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

theorem alpogeNativeGzArithmetic_eq_principal (x : ℝ) :
    alpogeNativeGzArithmetic x =
      alpogeNativePrincipalPrimeSum x -
        x * Real.log x + (1 + Real.eulerMascheroniConstant) * x := by
  rw [alpogeNativePrincipalPrimeSum_eq]
  rfl

/-- The true arithmetic GPsi nonprincipal channel. The constant ell
is the supplied logarithmic L-derivative; it is kept in the formula
rather than assigned an unproved analytic value. -/
def alpogeNativeGchiArithmetic {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (ell : ℂ) (x : ℝ) : ℂ :=
  alpogeNativeTwistedPrimeSum χ x + (x : ℂ) * ell

/-- Four genuine Dirichlet characters: 1, B, A, A*B. The last
coefficient is evaluated as a product, retaining the correct
multiplicative prime-power structure. -/
def alpogeNativeFourCharacterKernel {q : ℕ} [NeZero q]
    (χA χB : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  1 + χB n - χA n - χA n * χB n

def alpogeNativeFourCharacterTrace {q : ℕ} [NeZero q]
    (χA χB : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
    (alpogeNativePrimePowerWeight x n : ℂ) *
      alpogeNativeFourCharacterKernel χA χB n

/-- Arithmetic analogue of Alpoge Gsig, but with TRUE Dirichlet
twists rather than symbolic Frobenius witness data. -/
def alpogeNativeFourGsig {q : ℕ} [NeZero q]
    (χA χB : DirichletCharacter ℂ q)
    (ellA ellB ellAB : ℂ) (x : ℝ) : ℂ :=
  (alpogeNativeGzArithmetic x : ℂ) +
    alpogeNativeGchiArithmetic χB ellB x -
    alpogeNativeGchiArithmetic χA ellA x -
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      (alpogeNativePrimePowerWeight x n : ℂ) *
        (χA n * χB n) + (0 : ℂ)) -
    (x : ℂ) * ellAB

/-- The genuine 1+B-A-AB four-way finite source is EXACTLY one sum.
No arithmetic coefficient or prime-power cross term is discarded. -/
theorem alpogeNativeFourTrace_eq_four_sums
    {q : ℕ} [NeZero q]
    (χA χB : DirichletCharacter ℂ q) (x : ℝ) :
    alpogeNativeFourCharacterTrace χA χB x =
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (alpogeNativePrimePowerWeight x n : ℂ)) +
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (alpogeNativePrimePowerWeight x n : ℂ) * χB n) -
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (alpogeNativePrimePowerWeight x n : ℂ) * χA n) -
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (alpogeNativePrimePowerWeight x n : ℂ) * (χA n * χB n)) := by
  unfold alpogeNativeFourCharacterTrace alpogeNativeFourCharacterKernel
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- Exact four-channel algebra; the original principal logarithmic
main term and ALL three analytic ell constants are returned. -/
theorem alpogeNativeFourGsig_eq_trace (q : ℕ) [NeZero q]
    (χA χB : DirichletCharacter ℂ q)
    (ellA ellB ellAB : ℂ) (x : ℝ) :
    alpogeNativeFourGsig χA χB ellA ellB ellAB x =
      alpogeNativeFourCharacterTrace χA χB x +
        (((-x * Real.log x +
          (1 + Real.eulerMascheroniConstant) * x : ℝ) : ℂ)) +
        (x : ℂ) * (ellB - ellA - ellAB) := by
  have hprincipal :
      (alpogeNativePrincipalPrimeSum x : ℂ) =
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          (alpogeNativePrimePowerWeight x n : ℂ) := by
    unfold alpogeNativePrincipalPrimeSum
    norm_cast
  rw [alpogeNativeFourTrace_eq_four_sums]
  unfold alpogeNativeFourGsig alpogeNativeGchiArithmetic
    alpogeNativeTwistedPrimeSum
  rw [alpogeNativeGzArithmetic_eq_principal]
  push_cast
  rw [hprincipal]
  simp only [add_zero]
  ring

/-- Actual Dirichlet-character trace for any finite character family.
No principal-mode omission, no assumed group cardinality. -/
def alpogeNativeFiniteCharacterTrace {q : ℕ} [NeZero q]
    (T : Finset (DirichletCharacter ℂ q))
    (a : DirichletCharacter ℂ q → ℂ) (x : ℝ) : ℂ :=
  ∑ χ ∈ T, a χ * alpogeNativeTwistedPrimeSum χ x

/-- Exact native coefficient after character averaging, at integer n. -/
def alpogeNativeCharacterTraceCoefficient {q : ℕ} [NeZero q]
    (T : Finset (DirichletCharacter ℂ q))
    (a : DirichletCharacter ℂ q → ℂ) (n : ℕ) : ℂ :=
  ∑ χ ∈ T, a χ * χ n

/-- Full finite character Fubini, preserving every prime power and
all complex phases in Alpoge's own four-color arithmetic. -/
theorem alpogeNativeFiniteCharacterTrace_eq_source
    {q : ℕ} [NeZero q]
    (T : Finset (DirichletCharacter ℂ q))
    (a : DirichletCharacter ℂ q → ℂ) (x : ℝ) :
    alpogeNativeFiniteCharacterTrace T a x =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (alpogeNativePrimePowerWeight x n : ℂ) *
          alpogeNativeCharacterTraceCoefficient T a n := by
  unfold alpogeNativeFiniteCharacterTrace
    alpogeNativeTwistedPrimeSum alpogeNativeCharacterTraceCoefficient
  calc
    (∑ χ ∈ T, a χ *
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          (alpogeNativePrimePowerWeight x n : ℂ) * χ n) =
        ∑ χ ∈ T, ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          a χ * ((alpogeNativePrimePowerWeight x n : ℂ) * χ n) := by
      apply Finset.sum_congr rfl
      intro χ _hχ
      rw [Finset.mul_sum]
    _ = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ χ ∈ T,
          a χ * ((alpogeNativePrimePowerWeight x n : ℂ) * χ n) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _hχ
      ring

/-- Alpoge's four-character sign factor, BEFORE applying it to
prime-power arithmetic. -/
def alpogeNativeFourSign (a b : ℂ) : ℂ := 1 + b - a - a * b

/-- For true binary character signs, exactly the distinguished class
(a=-1,b=1) survives, with the original coefficient FOUR. -/
theorem alpogeNativeFourSign_binary
    (a b : ℂ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    alpogeNativeFourSign a b =
      if a = -1 ∧ b = 1 then 4 else 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    norm_num [alpogeNativeFourSign]

/-- Physical unramified quadratic sites. Values 0 at ramified
primes are NOT silently treated as ±1. -/
def alpogeNativeGoodSite {q : ℕ} [NeZero q]
    (χA χB : DirichletCharacter ℂ q) (n : ℕ) : Prop :=
  (χA n = 1 ∨ χA n = -1) ∧ (χB n = 1 ∨ χB n = -1)

/-- The entire BAD or ramified return is explicitly a signed sum.
It includes actual p-powers where one character vanishes or takes
a nonbinary phase. -/
def alpogeNativeFourBadReturn {q : ℕ} [NeZero q]
    (χA χB : DirichletCharacter ℂ q) (x : ℝ) : ℂ := by
  classical
  exact ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
      (fun n => ¬ alpogeNativeGoodSite χA χB n),
      (alpogeNativePrimePowerWeight x n : ℂ) *
        alpogeNativeFourCharacterKernel χA χB n

/-- The genuine physical class distinguished by four characters.
The GOOD restriction enforces quadratic/unramified arithmetic. -/
def alpogeNativeFourSelected {q : ℕ} [NeZero q]
    (χA χB : DirichletCharacter ℂ q) (x : ℝ) : ℂ := by
  classical
  exact ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
      (fun n => alpogeNativeGoodSite χA χB n ∧
        χA n = -1 ∧ χB n = 1),
      (alpogeNativePrimePowerWeight x n : ℂ)

/-- EXACT arithmetic character projector with FULL ramification and
nonquadratic response returned. Unlike the old 2I-J sample matrix,
this is an actual prime-power census with multiplicative χ-values. -/
theorem alpogeNativeFourTrace_eq_selected_add_bad {q : ℕ} [NeZero q]
    (χA χB : DirichletCharacter ℂ q) (x : ℝ) :
    alpogeNativeFourCharacterTrace χA χB x =
      4 * alpogeNativeFourSelected χA χB x +
        alpogeNativeFourBadReturn χA χB x := by
  classical
  let S := Finset.Icc 1 ⌊x⌋₊
  let good := alpogeNativeGoodSite χA χB
  let f := fun n : ℕ =>
    (alpogeNativePrimePowerWeight x n : ℂ) *
      alpogeNativeFourCharacterKernel χA χB n
  have hsplit : (∑ n ∈ S, f n) =
      (∑ n ∈ S.filter good, f n) +
        (∑ n ∈ S.filter (fun n => ¬ good n), f n) :=
    (Finset.sum_filter_add_sum_filter_not (s := S)
      (p := good) (f := f)).symm
  have hgood :
      (∑ n ∈ S.filter good, f n) =
        4 * (∑ n ∈ S.filter
          (fun n => good n ∧ χA n = -1 ∧ χB n = 1),
          (alpogeNativePrimePowerWeight x n : ℂ)) := by
    calc
      (∑ n ∈ S.filter good, f n) =
          ∑ n ∈ S, if good n then f n else 0 := by
        simp only [Finset.sum_filter]
      _ = ∑ n ∈ S, if good n ∧ χA n = -1 ∧ χB n = 1
          then 4 * (alpogeNativePrimePowerWeight x n : ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro n _hn
        by_cases hg : good n
        · have hp := alpogeNativeFourSign_binary
            (χA n) (χB n) hg.1 hg.2
          have hkernel :
              alpogeNativeFourCharacterKernel χA χB n =
                if χA n = -1 ∧ χB n = 1 then 4 else 0 := by
            exact hp
          dsimp [f]
          rw [hkernel]
          by_cases hc : χA n = -1 ∧ χB n = 1
          · simp [hg, hc]
            ring
          · simp [hg, hc]
        · simp [hg]
      _ = 4 * (∑ n ∈ S.filter
          (fun n => good n ∧ χA n = -1 ∧ χB n = 1),
          (alpogeNativePrimePowerWeight x n : ℂ)) := by
        rw [Finset.sum_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _hn
        by_cases hc : good n ∧ χA n = -1 ∧ χB n = 1
        · simp [hc]
        · simp [hc]
  have hresult :
      (∑ n ∈ S, f n) =
      4 * (∑ n ∈ S.filter
        (fun n => good n ∧ χA n = -1 ∧ χB n = 1),
        (alpogeNativePrimePowerWeight x n : ℂ)) +
      (∑ n ∈ S.filter (fun n => ¬ good n), f n) := by
    rw [hsplit, hgood]
  simpa [S, good, f, alpogeNativeFourCharacterTrace,
    alpogeNativeFourSelected, alpogeNativeFourBadReturn] using hresult

/-- Full signed Selberg source already proved unconditionally in RHLean.
This is the complete K2+first-Selberg+floor contribution. -/
def alpogeNativeSignedSource (N : ℕ) : ℝ :=
  nativePNTSignedSelbergRemainder N * Real.log (N : ℝ) -
    nativePNTLambdaSignedSelbergRemainderMass N +
    nativePNTSignedSecondSelbergKernelErrorMass N -
    nativePNTLambdaFloorLogSignedDefectMass N

theorem alpogeNativeSignedSource_eq_error (N : ℕ) :
    alpogeNativeSignedSource N =
      nativePNTError N * (Real.log (N : ℝ)) ^ 2 := by
  unfold alpogeNativeSignedSource
  exact (nativePNTError_mul_log_sq_eq_signedSecondSelberg N).symm

/-- SAME COMPLETE physical source in the original Gz observable at
every real x, with its precise scalar floor correction. -/
theorem alpogeNativeGz_mul_log_sq_eq_full_signed (x : ℝ) :
    alpogeNativeGzArithmetic x * (Real.log (⌊x⌋₊ : ℝ)) ^ 2 =
      (x * (nativeLambdaRecip ⌊x⌋₊ - Real.log x +
         Real.eulerMascheroniConstant) + (x - (⌊x⌋₊ : ℝ))) *
         (Real.log (⌊x⌋₊ : ℝ)) ^ 2 -
       alpogeNativeSignedSource ⌊x⌋₊ := by
  rw [alpogeNativeSignedSource_eq_error]
  unfold alpogeNativeGzArithmetic nativePNTError
  ring



/-!
## Native quadratic positivity and the FULL ramified arithmetic return

This is a proved (not postulated) finite positivity step of the
Stepanov/character argument. Algebraic quadraticity, \`chi^2=1\`,
is all that is required. There is no hypothesis on prime
distribution, zeta zeros, theta lifts or spectral bounds.
-/

/-- Every genuine quadratic Dirichlet character has signs ±1 on
units. This is derived from the CHARACTER's square, not postulated
independent prime labels. -/
theorem alpogeNativeQuadraticCharacter_unit_values
    {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1)
    (n : ℕ) (hn : IsUnit (n : ZMod q)) :
    χ n = 1 ∨ χ n = -1 := by
  have hpow : (χ n) ^ 2 = 1 := by
    calc
      (χ n) ^ 2 = (χ ^ 2) (n : ZMod q) := by
        exact (MulChar.pow_apply' χ (by norm_num : (2 : ℕ) ≠ 0)
          (n : ZMod q)).symm
      _ = (1 : DirichletCharacter ℂ q) (n : ZMod q) := by
        rw [hχ]
      _ = 1 := MulChar.one_apply hn
  exact sq_eq_one_iff.mp hpow

/-- At a nonunit EVERY Dirichlet character modulo q vanishes.
Therefore Alpoge's four-way kernel is EXACTLY one, independently of
which two characters were selected. The ramified terms are not an
uncontrolled complex phase. -/
theorem alpogeNativeFourKernel_at_nonunit
    {q : ℕ} [NeZero q]
    (χA χB : DirichletCharacter ℂ q) (n : ℕ)
    (hn : ¬ IsUnit (n : ZMod q)) :
    alpogeNativeFourCharacterKernel χA χB n = 1 := by
  have hA : χA n = 0 := MulChar.map_nonunit χA hn
  have hB : χB n = 0 := MulChar.map_nonunit χB hn
  simp [alpogeNativeFourCharacterKernel, hA, hB]

/-- For GENUINE quadratic characters, the GOOD portion is precisely
the unramified integer population. No site is classified by fiat. -/
theorem alpogeNativeQuadraticGood_iff_unit
    {q : ℕ} [NeZero q]
    (χA χB : DirichletCharacter ℂ q)
    (hA : χA ^ 2 = 1) (hB : χB ^ 2 = 1) (n : ℕ) :
    alpogeNativeGoodSite χA χB n ↔ IsUnit (n : ZMod q) := by
  constructor
  · intro hg
    by_contra hn
    have hz : χA n = 0 := MulChar.map_nonunit χA hn
    rcases hg.1 with hh | hh <;> simp [hz] at hh
  · intro hn
    exact ⟨alpogeNativeQuadraticCharacter_unit_values χA hA n hn,
      alpogeNativeQuadraticCharacter_unit_values χB hB n hn⟩

/-- The actual four-character projector is {0,4} on unramified
sites, and exactly 1 on ramified sites. This makes the positive
part of Alpoge's four-character/Fourier step arithmetic, not
a conditional trace-interface claim. -/
theorem alpogeNativeFourKernel_quadratic
    {q : ℕ} [NeZero q]
    (χA χB : DirichletCharacter ℂ q)
    (hA : χA ^ 2 = 1) (hB : χB ^ 2 = 1) (n : ℕ) :
    alpogeNativeFourCharacterKernel χA χB n =
      if IsUnit (n : ZMod q) then
        (if χA n = -1 ∧ χB n = 1 then 4 else 0)
      else 1 := by
  by_cases hu : IsUnit (n : ZMod q)
  · simpa [hu, alpogeNativeFourCharacterKernel, alpogeNativeFourSign]
      using alpogeNativeFourSign_binary (χA n) (χB n)
        (alpogeNativeQuadraticCharacter_unit_values χA hA n hu)
        (alpogeNativeQuadraticCharacter_unit_values χB hB n hu)
  · simp [hu, alpogeNativeFourKernel_at_nonunit χA χB n hu]

/-- The entire ORIGINAL prime-power source on ramified integers.
Unlike a generic BAD_RETURN it is real, has a fixed positive sign,
and contains every p^k with p dividing the conductor modulus. -/
def alpogeNativeRamifiedPrimePowerMass
    (q : ℕ) [NeZero q] (x : ℝ) : ℝ := by
  classical
  exact ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
    (fun (n : ℕ) => ¬ IsUnit (n : ZMod q)),
    alpogeNativePrimePowerWeight x n

/-- For quadratic characters the entire formerly opaque BAD_RETURN
is exactly the real ramified prime-power mass. -/
theorem alpogeNativeFourBadReturn_eq_ramified
    {q : ℕ} [NeZero q]
    (χA χB : DirichletCharacter ℂ q)
    (hA : χA ^ 2 = 1) (hB : χB ^ 2 = 1) (x : ℝ) :
    alpogeNativeFourBadReturn χA χB x =
      (alpogeNativeRamifiedPrimePowerMass q x : ℂ) := by
  classical
  have hs :
      (Finset.Icc 1 ⌊x⌋₊).filter
        (fun n => ¬ alpogeNativeGoodSite χA χB n) =
      (Finset.Icc 1 ⌊x⌋₊).filter
        (fun (n : ℕ) => ¬ IsUnit (n : ZMod q)) := by
    ext n
    simp [alpogeNativeQuadraticGood_iff_unit χA χB hA hB n]
  unfold alpogeNativeFourBadReturn alpogeNativeRamifiedPrimePowerMass
  rw [hs]
  calc
    (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
       (fun (n : ℕ) => ¬ IsUnit (n : ZMod q)),
       (alpogeNativePrimePowerWeight x n : ℂ) *
          alpogeNativeFourCharacterKernel χA χB n) =
        ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
          (fun (n : ℕ) => ¬ IsUnit (n : ZMod q)),
          (alpogeNativePrimePowerWeight x n : ℂ) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnu : ¬ IsUnit (n : ZMod q) := (Finset.mem_filter.mp hn).2
      rw [alpogeNativeFourKernel_at_nonunit χA χB n hnu]
      ring
    _ = (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
          (fun (n : ℕ) => ¬ IsUnit (n : ZMod q)),
          alpogeNativePrimePowerWeight x n : ℝ) := by norm_cast

/-- Completely arithmetic reconstruction of the signed character
average: 4 times the selected unramified class, PLUS the exactly
identified ramified source; not a discarded or assumed error. -/
theorem alpogeNativeFourTrace_quadratic_exact
    {q : ℕ} [NeZero q]
    (χA χB : DirichletCharacter ℂ q)
    (hA : χA ^ 2 = 1) (hB : χB ^ 2 = 1) (x : ℝ) :
    alpogeNativeFourCharacterTrace χA χB x =
      4 * alpogeNativeFourSelected χA χB x +
        (alpogeNativeRamifiedPrimePowerMass q x : ℂ) := by
  rw [alpogeNativeFourTrace_eq_selected_add_bad,
    alpogeNativeFourBadReturn_eq_ramified χA χB hA hB]

/-- The ACTUAL Λ(n)(x/n-1) signal is nonnegative at each physical
integer under the sharp floor cutoff. -/
theorem alpogeNativePrimePowerWeight_nonneg
    (x : ℝ) (hx : 0 ≤ x) (n : ℕ)
    (hn : n ∈ Finset.Icc 1 ⌊x⌋₊) :
    0 ≤ alpogeNativePrimePowerWeight x n := by
  have hn0nat : 0 < n := by
    have h1 := (Finset.mem_Icc.mp hn).1
    omega
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn0nat
  have hnx : (n : ℝ) ≤ x := by
    exact (by exact_mod_cast (Finset.mem_Icc.mp hn).2 : (n : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans
      (Nat.floor_le hx)
  have hdiv : 1 ≤ x / (n : ℝ) := by
    apply (le_div_iff₀ hn0).2
    simpa using hnx
  unfold alpogeNativePrimePowerWeight
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (sub_nonneg.mpr hdiv)

/-- The full ramified part has a proved POSITIVE sign, not an assumed
divisibility/covolume saving. -/
theorem alpogeNativeRamifiedPrimePowerMass_nonneg
    (q : ℕ) [NeZero q] (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ alpogeNativeRamifiedPrimePowerMass q x := by
  classical
  unfold alpogeNativeRamifiedPrimePowerMass
  apply Finset.sum_nonneg
  intro n hn
  exact alpogeNativePrimePowerWeight_nonneg x hx n
    (Finset.mem_filter.mp hn).1

/-- A FINITE paid upper bound on the ramified part. The bound is
weak (the full reciprocal Λ mass), but fully unconditional and includes
ALL prime powers. It must not be mistaken for the missing critical
geometric/covolume bound. -/
theorem alpogeNativeRamifiedPrimePowerMass_le_reciprocal
    (q : ℕ) [NeZero q] (x : ℝ) (hx : 0 ≤ x) :
    alpogeNativeRamifiedPrimePowerMass q x ≤
      x * nativeLambdaRecip ⌊x⌋₊ := by
  classical
  have hpoint (n : ℕ) :
      alpogeNativePrimePowerWeight x n ≤
        x * (Λ n / (n : ℝ)) := by
    have hLambda : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    have heq : alpogeNativePrimePowerWeight x n =
        x * (Λ n / (n : ℝ)) - Λ n := by
      unfold alpogeNativePrimePowerWeight
      ring
    rw [heq]
    linarith [hLambda]
  unfold alpogeNativeRamifiedPrimePowerMass
  calc
    (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
       (fun (n : ℕ) => ¬ IsUnit (n : ZMod q)),
       alpogeNativePrimePowerWeight x n) ≤
        ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
          (fun (n : ℕ) => ¬ IsUnit (n : ZMod q)),
          x * (Λ n / (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro n _hn
      exact hpoint n
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          x * (Λ n / (n : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
      intro n _hn _hnot
      exact mul_nonneg hx (div_nonneg
        ArithmeticFunction.vonMangoldt_nonneg (by positivity))
    _ = x * nativeLambdaRecip ⌊x⌋₊ := by
      unfold nativeLambdaRecip
      rw [Finset.mul_sum]

/-- The upper-side character trace really has an unconditional
positivity theorem on RHLean's original prime-power arithmetic. -/
theorem alpogeNativeFourTrace_quadratic_re_nonneg
    {q : ℕ} [NeZero q]
    (χA χB : DirichletCharacter ℂ q)
    (hA : χA ^ 2 = 1) (hB : χB ^ 2 = 1)
    (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ (alpogeNativeFourCharacterTrace χA χB x).re := by
  have hs : 0 ≤ (alpogeNativeFourSelected χA χB x).re := by
    classical
    unfold alpogeNativeFourSelected
    simp only [Complex.re_sum, Complex.ofReal_re]
    apply Finset.sum_nonneg
    intro n hn
    exact alpogeNativePrimePowerWeight_nonneg x hx n
      (Finset.mem_filter.mp hn).1
  have hr := alpogeNativeRamifiedPrimePowerMass_nonneg q x hx
  rw [alpogeNativeFourTrace_quadratic_exact χA χB hA hB]
  norm_num [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im] at *
  linarith

end RHLean.Analysis

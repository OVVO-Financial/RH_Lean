import Mathlib
import «research.VF_MID_ALIGNED_STEP_GRAPH»
import «research.PRIME_WHEEL_ROUGH_SEAT_SQRT_SPECIALIZATION»
import RHLean.Proof.PostRootPartnerLogAlignment
import RHLean.Analysis.NativePNTSquarePrefixContraction
import RHLean.Analysis.DynamicVioleBaseline
import RHLean.Analysis.NativePNTSignedSecondSelbergFrontierCharge

/-!
# Actual-prime root-to-square contraction attack

This file records the exact endpoint geometry needed to compare the continuous-Li
root-to-square contraction with the actual-prime square-endpoint chronology.

There are three points.

1. The repository endpoint `squareRootEndpoint R = R^2 - 1` and the literal
   square endpoint `R^2` have exactly the same actual-prime carrier above the
   root.  The missing endpoint is the composite square itself.

2. More strongly, for every prime `q > R`, the reciprocal child cutoff is
   unchanged:
   `floor((R^2-1)/q) = floor(R^2/q)`.
   Thus the off-by-one is not an analytic error and costs no part of the
   VF vertical alignment budget.

3. The chronological Euler-hazard normalization already present in the repo is
   strictly subunit on every finite list of genuine primes:
   `0 <= hazard < 1`.  This scalar fact alone is not a closure: on the older
   canonical-rough covariance carrier the repository proves a post-root
   no-contraction law, so that route is deliberately not used here.

4. On the *native PNT / protected-VF carrier*, every actual high owner `q > R`
   sees a child cutoff `B = floor((R^2-1)/q) < R < q`.  Hence `q` is fresh
   for every positive cofactor `m <= B`.  The already-compiled reciprocal
   Möbius law therefore contracts every completed child fibre by exactly
   `1 - 1/q`, and the direct protected square-block correlation has the same
   Euler factor with one explicit response-difference defect.

This is the correct socket for the direct VF attack.  No RH-scale estimate is
assumed or asserted here.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Actual primes strictly above the root and through the literal square. -/
def vfMidActualRootSquarePrimeCarrier (R : ℕ) : Finset ℕ :=
  (Finset.Ioc R (R ^ 2)).filter Nat.Prime

/-- The same carrier in the repository's canonical pre-square convention. -/
def vfMidActualPreSquarePrimeCarrier (R : ℕ) : Finset ℕ :=
  (Finset.Ioc R (squareRootEndpoint R)).filter Nat.Prime

private theorem square_not_prime_of_two_le
    {R : ℕ} (hR : 2 ≤ R) :
    ¬ Nat.Prime (R ^ 2) := by
  intro hprime
  have hdiv : R ^ 2 ∣ R * R := by
    simp [pow_two]
  have hRdiv : R ^ 2 ∣ R :=
    (hprime.dvd_mul.mp hdiv).elim id id
  have hle : R ^ 2 ≤ R :=
    Nat.le_of_dvd (by omega : 0 < R) hRdiv
  nlinarith

/-- **The pre-square and square actual-prime carriers are exactly equal.**
The only integer added by moving the endpoint from `R^2-1` to `R^2` is
`R^2`, which is composite for `R >= 2`. -/
theorem vfMidActualPreSquarePrimeCarrier_eq_rootSquare
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidActualPreSquarePrimeCarrier R =
      vfMidActualRootSquarePrimeCarrier R := by
  ext q
  simp only [vfMidActualPreSquarePrimeCarrier,
    vfMidActualRootSquarePrimeCarrier, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hRq, hqX⟩, hqPrime⟩
    have hXle : squareRootEndpoint R ≤ R ^ 2 := by
      unfold squareRootEndpoint
      omega
    exact ⟨⟨hRq, hqX.trans hXle⟩, hqPrime⟩
  · rintro ⟨⟨hRq, hqSq⟩, hqPrime⟩
    have hqNe : q ≠ R ^ 2 := by
      intro hq
      subst q
      exact square_not_prime_of_two_le hR hqPrime
    have hqPre : q ≤ squareRootEndpoint R := by
      unfold squareRootEndpoint
      omega
    exact ⟨⟨hRq, hqPre⟩, hqPrime⟩

/-- A prime strictly above `R` cannot divide `R^2`. -/
theorem not_dvd_square_of_root_lt_prime
    {R q : ℕ} (hqPrime : q.Prime) (hRq : R < q) :
    ¬ q ∣ R ^ 2 := by
  intro hdiv
  have hdiv' : q ∣ R * R := by
    simpa [pow_two] using hdiv
  have hqR : q ∣ R :=
    (hqPrime.dvd_mul.mp hdiv').elim id id
  have hqLe : q ≤ R :=
    Nat.le_of_dvd (by omega : 0 < R) hqR
  omega

/-- **The reciprocal child is also endpoint-invariant.**
For an actual prime owner above the root, subtracting the final composite
square changes neither the owner set nor its quotient child. -/
theorem squareRootEndpoint_div_eq_square_div_of_root_lt_prime
    {R q : ℕ} (hqPrime : q.Prime) (hRq : R < q) :
    squareRootEndpoint R / q = R ^ 2 / q := by
  let k : ℕ := R ^ 2 / q
  have hqPos : 0 < q := hqPrime.pos
  have hupper0 : R ^ 2 < q * (k + 1) := by
    dsimp [k]
    exact (Nat.div_lt_iff_lt_mul hqPos).1 (Nat.lt_succ_self _)
  have hlower0 : q * k ≤ R ^ 2 := by
    dsimp [k]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (R ^ 2) q
  have hlowerNe : q * k ≠ R ^ 2 := by
    intro heq
    have hdvd : q ∣ R ^ 2 := by
      refine ⟨k, ?_⟩
      simpa [Nat.mul_comm] using heq.symm
    exact not_dvd_square_of_root_lt_prime hqPrime hRq hdvd
  have hlower : q * k ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  have hupper : squareRootEndpoint R < (k + 1) * q := by
    unfold squareRootEndpoint
    have hs : R ^ 2 - 1 < R ^ 2 := by
      have : 0 < R ^ 2 := by positivity
      omega
    calc
      R ^ 2 - 1 < R ^ 2 := hs
      _ < q * (k + 1) := hupper0
      _ = (k + 1) * q := by ring
  have hdiv : squareRootEndpoint R / q = k := by
    apply Nat.div_eq_of_lt_le
    · exact hupper
    · simpa [Nat.mul_comm] using hlower
  simpa [k] using hdiv

/-- Prime-list Euler products are strictly positive. -/
theorem canonicalRoughPrimeListEulerProduct_pos
    (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) :
    0 < canonicalRoughPrimeListEulerProduct ps := by
  induction ps with
  | nil =>
      simp [canonicalRoughPrimeListEulerProduct]
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have htail : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      have hpRpos : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast hp.pos
      have hpRone : (1 : ℝ) < (p : ℝ) := by
        exact_mod_cast hp.one_lt
      have hfrac : (1 : ℝ) / (p : ℝ) < 1 := by
        exact (div_lt_one hpRpos).2 hpRone
      have hfactor : 0 < canonicalRoughEulerFactor p := by
        unfold canonicalRoughEulerFactor
        linarith
      simp only [canonicalRoughPrimeListEulerProduct]
      exact mul_pos hfactor (ih htail)

/-- Prime-list Euler products are at most one. -/
theorem canonicalRoughPrimeListEulerProduct_le_one
    (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) :
    canonicalRoughPrimeListEulerProduct ps ≤ 1 := by
  induction ps with
  | nil =>
      simp [canonicalRoughPrimeListEulerProduct]
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have htail : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      have hfactor0 : 0 ≤ canonicalRoughEulerFactor p :=
        canonicalRoughEulerFactor_nonneg hp
      have hfactor1 : canonicalRoughEulerFactor p ≤ 1 :=
        canonicalRoughEulerFactor_le_one hp
      have htail0 : 0 ≤ canonicalRoughPrimeListEulerProduct ps :=
        (canonicalRoughPrimeListEulerProduct_pos ps htail).le
      have htail1 := ih htail
      simp only [canonicalRoughPrimeListEulerProduct]
      calc
        canonicalRoughEulerFactor p * canonicalRoughPrimeListEulerProduct ps
            ≤ 1 * canonicalRoughPrimeListEulerProduct ps :=
          mul_le_mul_of_nonneg_right hfactor1 htail0
        _ ≤ 1 := by simpa using htail1

/-- **Strict actual-prime Euler-hazard budget.**
Unlike the raw transport sum, the chronological hazard-normalized prime ledger
has a genuinely subunit total coefficient on every finite prime schedule. -/
theorem postRootEulerHazardMass_nonneg_lt_one_of_prime_list
    (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) :
    0 ≤ postRootEulerHazardMass ps ∧
      postRootEulerHazardMass ps < 1 := by
  rw [postRootEulerHazardMass_eq_one_sub_eulerProduct]
  have hpos := canonicalRoughPrimeListEulerProduct_pos ps hprime
  have hle := canonicalRoughPrimeListEulerProduct_le_one ps hprime
  constructor <;> linarith

/-- Specialization: any chronological list drawn from the actual root-to-square
prime carrier inherits the strict Euler-hazard budget.  Completeness or ordering
of the list is irrelevant for this scalar estimate. -/
theorem vfMidActualRootSquarePrimeSchedule_hazard_nonneg_lt_one
    (R : ℕ) (ps : List ℕ)
    (hmem : ∀ p ∈ ps, p ∈ vfMidActualRootSquarePrimeCarrier R) :
    0 ≤ postRootEulerHazardMass ps ∧
      postRootEulerHazardMass ps < 1 := by
  apply postRootEulerHazardMass_nonneg_lt_one_of_prime_list
  intro p hp
  exact (Finset.mem_filter.mp (hmem p hp)).2

/-! ## Native PNT / direct protected-block high-owner contraction -/

/-- Every positive cofactor in an actual high owner's reciprocal child is
strictly smaller than that owner.  Thus the owner prime is automatically fresh
throughout the complete child fibre. -/
theorem vfMidActualHighPrimeChild_lt_owner
    {R q m : ℕ} (hR : 2 ≤ R) (hq : q.Prime) (hRq : R < q)
    (hm : m ∈ Finset.Icc 1 (squareRootEndpoint R / q)) :
    m < q := by
  have hchild :
      squareRootEndpoint R / q < R :=
    squareRootEndpoint_div_lt_root_of_root_lt hR hRq
  exact (Finset.mem_Icc.mp hm).2.trans_lt (hchild.trans hRq)

/-- Hence every positive cofactor in that child is coprime to the actual
high-owner prime. -/
theorem vfMidActualHighPrimeChild_coprime
    {R q m : ℕ} (hR : 2 ≤ R) (hq : q.Prime) (hRq : R < q)
    (hm : m ∈ Finset.Icc 1 (squareRootEndpoint R / q)) :
    Nat.Coprime m q := by
  have hmpos : 0 < m := by
    exact Nat.lt_of_lt_of_le (by omega)
      (Finset.mem_Icc.mp hm).2
  have hmq := vfMidActualHighPrimeChild_lt_owner hR hq hRq hm
  exact (Nat.coprime_of_lt_prime (Nat.ne_of_gt hmpos) hmq hq).symm

/-- **Exact actual-prime contraction on the completed lower child.**
For every high owner `q > R`, adjoining `q` to the complete reciprocal
Möbius child through `floor((R^2-1)/q)` multiplies that child by exactly
`1 - 1/q`.  No Li replacement, density estimate, norm, or asymptotic input
appears. -/
theorem vfMidActualHighPrimeChildReciprocalFiber_adjoin_eq_euler
    (R q : ℕ) (F : ℕ → ℝ)
    (hR : 2 ≤ R) (hq : q.Prime) (hRq : R < q) :
    nativeMobiusAdjoinedPrimeReciprocalFiber
        (Finset.Icc 1 (squareRootEndpoint R / q)) q F =
      (1 - 1 / (q : ℝ)) *
        nativeMobiusReciprocalFiber
          (Finset.Icc 1 (squareRootEndpoint R / q)) F := by
  apply nativeMobiusAdjoinedPrimeReciprocalFiber_eq
  · exact hq
  · intro m hm
    exact (Finset.mem_Icc.mp hm).1
  · intro m hm
    exact vfMidActualHighPrimeChild_coprime hR hq hRq hm

/-- Reciprocal parent mass of the direct adjacent-square protected correlation
restricted to the completed child of one actual high owner. -/
def vfMidActualHighPrimeProtectedParentReciprocalMass
    (R q : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (squareRootEndpoint R / q),
    nativePNTSignedSquareBlockCorrelationReciprocalSummand
      ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m

/-- Parent-plus-child mass on the same completed high-owner fibre. -/
def vfMidActualHighPrimeProtectedPairedReciprocalMass
    (R q : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (squareRootEndpoint R / q),
    (nativePNTSignedSquareBlockCorrelationReciprocalSummand
        ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m +
      nativePNTSignedSquareBlockCorrelationReciprocalSummand
        ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) (m * q))

/-- Exact response-difference leakage left by the direct protected-block Euler
pairing on one actual high-owner child. -/
def vfMidActualHighPrimeProtectedDefectMass
    (R q : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (squareRootEndpoint R / q),
    nativePNTSignedSquareBlockFreshPrimePhysicalDefect
      ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m q

/-- **Direct protected-block Euler step on every completed actual high-owner
child.**  This is on the same reciprocal correlation whose Abel return gives
the protected block used by the square-psi / VF descent.  All loss from pure
`1 - 1/q` contraction is isolated in one signed response-difference defect
mass, with no absolute value taken. -/
theorem vfMidActualHighPrimeProtectedPairedReciprocalMass_eq_euler_add_defect
    (R q : ℕ) (hR : 2 ≤ R) (hq : q.Prime) (hRq : R < q) :
    vfMidActualHighPrimeProtectedPairedReciprocalMass R q =
      (1 - 1 / (q : ℝ)) *
          vfMidActualHighPrimeProtectedParentReciprocalMass R q +
        vfMidActualHighPrimeProtectedDefectMass R q := by
  unfold vfMidActualHighPrimeProtectedPairedReciprocalMass
    vfMidActualHighPrimeProtectedParentReciprocalMass
    vfMidActualHighPrimeProtectedDefectMass
  rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < m := by
    exact Nat.lt_of_lt_of_le (by omega)
      (Finset.mem_Icc.mp hm).2
  have hcop := vfMidActualHighPrimeChild_coprime hR hq hRq hm
  exact
    nativePNTSignedSquareBlockCorrelationReciprocalSummand_add_mul_freshPrime
      ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2)
      hmpos hq hcop

/-! ## Adjacent-square response sign and monotonicity -/

/-- Positive logarithmic response mass of one cofactor on the literal adjacent
square block.  At the right endpoint the native PNT error on every divisor in
the block is exactly `-1`, so the signed cofactor response is the negative of
this quantity. -/
def vfMidSquareProtectedResponseLogMass (R m : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Ioc (R ^ 2) ((R + 1) ^ 2)).filter (fun d => m ∣ d),
    Real.log ((d / m : ℕ) : ℝ)

/-- Every divisor in an adjacent square block has right-endpoint quotient one. -/
theorem vfMidSquareBlock_rightEndpoint_div_eq_one
    {R d : ℕ} (hR : 3 ≤ R)
    (hd : d ∈ Finset.Ioc (R ^ 2) ((R + 1) ^ 2)) :
    (R + 1) ^ 2 / d = 1 := by
  rcases Finset.mem_Ioc.mp hd with ⟨hdlo, hdhi⟩
  have hlo : 1 * d ≤ (R + 1) ^ 2 := by simpa using hdhi
  have hsub : (R + 1) ^ 2 < 2 * R ^ 2 := by
    nlinarith
  have hhi : (R + 1) ^ 2 < (1 + 1) * d := by
    nlinarith
  exact Nat.div_eq_of_lt_le hlo hhi

/-- **At the literal right square endpoint every protected cofactor response is
a negative log mass.** -/
theorem vfMidSquareProtectedCofactorResponse_eq_neg_logMass
    (R m : ℕ) (hR : 3 ≤ R) :
    nativePNTSignedSquareBlockCofactorResponse
        ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m =
      -vfMidSquareProtectedResponseLogMass R m := by
  unfold nativePNTSignedSquareBlockCofactorResponse
    vfMidSquareProtectedResponseLogMass
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdI := (Finset.mem_filter.mp hd).1
  rw [vfMidSquareBlock_rightEndpoint_div_eq_one hR hdI,
    nativePNTError_one]
  ring

/-- The logarithmic response mass is nonnegative on every positive cofactor. -/
theorem vfMidSquareProtectedResponseLogMass_nonneg
    (R m : ℕ) (hm : 1 ≤ m) :
    0 ≤ vfMidSquareProtectedResponseLogMass R m := by
  unfold vfMidSquareProtectedResponseLogMass
  apply Finset.sum_nonneg
  intro d hd
  rcases Finset.mem_filter.mp hd with ⟨hdI, hmd⟩
  have hdpos : 0 < d := by
    have := (Finset.mem_Ioc.mp hdI).1
    positivity
  have hmle : m ≤ d := Nat.le_of_dvd hdpos hmd
  have hquot : 1 ≤ d / m :=
    (Nat.one_le_div_iff (by omega : 0 < m)).2 hmle
  exact Real.log_nonneg (by exact_mod_cast hquot)

/-- Hence the direct adjacent-square protected response is always nonpositive
before the Möbius sign is applied. -/
theorem vfMidSquareProtectedCofactorResponse_nonpos
    (R m : ℕ) (hR : 3 ≤ R) (hm : 1 ≤ m) :
    nativePNTSignedSquareBlockCofactorResponse
        ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m ≤ 0 := by
  rw [vfMidSquareProtectedCofactorResponse_eq_neg_logMass R m hR]
  exact neg_nonpos.mpr (vfMidSquareProtectedResponseLogMass_nonneg R m hm)

/-- Multiplying a positive cofactor by a genuine prime can only decrease its
positive adjacent-square log response mass. -/
theorem vfMidSquareProtectedResponseLogMass_mul_prime_le
    (R m q : ℕ) (hm : 1 ≤ m) (hq : q.Prime) :
    vfMidSquareProtectedResponseLogMass R (m * q) ≤
      vfMidSquareProtectedResponseLogMass R m := by
  let child : Finset ℕ :=
    (Finset.Ioc (R ^ 2) ((R + 1) ^ 2)).filter (fun d => m * q ∣ d)
  let parent : Finset ℕ :=
    (Finset.Ioc (R ^ 2) ((R + 1) ^ 2)).filter (fun d => m ∣ d)
  have hsub : child ⊆ parent := by
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hdI, hmq⟩
    apply Finset.mem_filter.mpr
    refine ⟨hdI, ?_⟩
    exact dvd_trans (by exact ⟨q, by ring⟩) hmq
  have hpoint :
      ∀ d ∈ child,
        Real.log ((d / (m * q) : ℕ) : ℝ) ≤
          Real.log ((d / m : ℕ) : ℝ) := by
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hdI, hmq⟩
    have hdpos : 0 < d := by
      have := (Finset.mem_Ioc.mp hdI).1
      positivity
    have hmqpos : 0 < m * q := Nat.mul_pos (by omega) hq.pos
    have hmqle : m * q ≤ d := Nat.le_of_dvd hdpos hmq
    have hchild1 : 1 ≤ d / (m * q) :=
      (Nat.one_le_div_iff hmqpos).2 hmqle
    have hmMq : m ≤ m * q := by
      nlinarith [hq.two_le]
    have hdiv :
        d / (m * q) ≤ d / m :=
      Nat.div_le_div_left hmMq (by omega : 0 < m)
    have hchildPos : (0 : ℝ) < ((d / (m * q) : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < d / (m * q) by omega)
    exact Real.log_le_log hchildPos (by exact_mod_cast hdiv)
  unfold vfMidSquareProtectedResponseLogMass
  change (∑ d ∈ child, Real.log ((d / (m * q) : ℕ) : ℝ)) ≤
    ∑ d ∈ parent, Real.log ((d / m : ℕ) : ℝ)
  calc
    (∑ d ∈ child, Real.log ((d / (m * q) : ℕ) : ℝ))
        ≤ ∑ d ∈ child, Real.log ((d / m : ℕ) : ℝ) := by
          exact Finset.sum_le_sum hpoint
    _ ≤ ∑ d ∈ parent, Real.log ((d / m : ℕ) : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
      intro d hdParent _hdChild
      rcases Finset.mem_filter.mp hdParent with ⟨hdI, hmd⟩
      have hdpos : 0 < d := by
        have := (Finset.mem_Ioc.mp hdI).1
        positivity
      have hmle : m ≤ d := Nat.le_of_dvd hdpos hmd
      have hquot : 1 ≤ d / m :=
        (Nat.one_le_div_iff (by omega : 0 < m)).2 hmle
      exact Real.log_nonneg (by exact_mod_cast hquot)

/-- The child protected response has no larger absolute magnitude than its
parent response. -/
theorem abs_vfMidSquareProtectedCofactorResponse_mul_prime_le
    (R m q : ℕ) (hR : 3 ≤ R) (hm : 1 ≤ m) (hq : q.Prime) :
    |nativePNTSignedSquareBlockCofactorResponse
        ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) (m * q)| ≤
      |nativePNTSignedSquareBlockCofactorResponse
        ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m| := by
  rw [vfMidSquareProtectedCofactorResponse_eq_neg_logMass R (m * q) hR,
    vfMidSquareProtectedCofactorResponse_eq_neg_logMass R m hR]
  have hchild0 :=
    vfMidSquareProtectedResponseLogMass_nonneg R (m * q)
      (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hq.ne_zero))
  have hparent0 := vfMidSquareProtectedResponseLogMass_nonneg R m hm
  rw [abs_neg, abs_of_nonneg hchild0, abs_neg, abs_of_nonneg hparent0]
  exact vfMidSquareProtectedResponseLogMass_mul_prime_le R m q hm hq

/-- **Pointwise actual-prime high-owner tail contraction.**
On the literal adjacent-square protected correlation, a fresh high-prime child
has opposite Möbius sign and no larger physical response mass.  Its reciprocal
summand therefore costs at most `1/q` times the parent summand. -/
theorem abs_vfMidActualHighPrimeProtectedChild_le_inv_mul_parent
    (R m q : ℕ) (hR : 3 ≤ R) (hm : 1 ≤ m)
    (hq : q.Prime) (hcop : Nat.Coprime m q) :
    |nativePNTSignedSquareBlockCorrelationReciprocalSummand
        ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) (m * q)| ≤
      (1 / (q : ℝ)) *
        |nativePNTSignedSquareBlockCorrelationReciprocalSummand
          ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m| := by
  have hmpos : 0 < m := by omega
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  have hmRpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hresp :=
    abs_vfMidSquareProtectedCofactorResponse_mul_prime_le
      R m q hR hm hq
  unfold nativePNTSignedSquareBlockCorrelationReciprocalSummand
  change
    |(((μ (m * q) : ℤ) : ℝ) *
        nativePNTSignedSquareBlockCofactorResponse
          ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) (m * q)) /
          ((m * q : ℕ) : ℝ)| ≤
      (1 / (q : ℝ)) *
        |(((μ m : ℤ) : ℝ) *
          nativePNTSignedSquareBlockCofactorResponse
            ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m) / (m : ℝ)|
  rw [nativeMobius_adjoin_prime m q hq hcop]
  push_cast
  rw [abs_div, abs_mul, abs_neg, abs_div, abs_mul]
  have hmqcast : (((m * q : ℕ) : ℝ)) = (m : ℝ) * (q : ℝ) := by norm_num
  rw [hmqcast, abs_mul, abs_of_pos hmRpos, abs_of_pos hqpos,
    abs_of_pos hmRpos]
  have hmu : 0 ≤ |(((μ m : ℤ) : ℝ))| := abs_nonneg _
  have hden : 0 ≤ (1 / (q : ℝ)) * (|(((μ m : ℤ) : ℝ))| / (m : ℝ)) := by
    positivity
  calc
    |(((μ m : ℤ) : ℝ))| *
          |nativePNTSignedSquareBlockCofactorResponse
            ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) (m * q)| /
        ((m : ℝ) * (q : ℝ))
        =
      (1 / (q : ℝ)) *
        ((|(((μ m : ℤ) : ℝ))| / (m : ℝ)) *
          |nativePNTSignedSquareBlockCofactorResponse
            ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) (m * q)|) := by
          field_simp
          ring
    _ ≤ (1 / (q : ℝ)) *
        ((|(((μ m : ℤ) : ℝ))| / (m : ℝ)) *
          |nativePNTSignedSquareBlockCofactorResponse
            ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m|) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_left hresp (by positivity)
          · positivity
    _ = (1 / (q : ℝ)) *
        (|(((μ m : ℤ) : ℝ))| *
          |nativePNTSignedSquareBlockCofactorResponse
            ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m| / (m : ℝ)) := by
          field_simp
          ring

/-- **Fixed-parent actual high-tail bound.**
The complete post-root child tail of one low parent is controlled by the actual
reciprocal-prime mass of its legal star.  This is the direct protected-VF
counterpart of the continuous-Li root-to-square high-tail estimate. -/
theorem abs_sum_vfMidActualHighPrimeProtectedChildren_le
    (R m : ℕ) (hR : 3 ≤ R) (hm : 1 ≤ m) :
    |∑ q ∈ vfMidActualHighPrimeStarSet R m,
        nativePNTSignedSquareBlockCorrelationReciprocalSummand
          ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) (m * q)| ≤
      vfMidActualHighPrimeStarReciprocalMass R m *
        |nativePNTSignedSquareBlockCorrelationReciprocalSummand
          ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m| := by
  calc
    |∑ q ∈ vfMidActualHighPrimeStarSet R m,
        nativePNTSignedSquareBlockCorrelationReciprocalSummand
          ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) (m * q)|
        ≤ ∑ q ∈ vfMidActualHighPrimeStarSet R m,
            |nativePNTSignedSquareBlockCorrelationReciprocalSummand
              ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) (m * q)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ vfMidActualHighPrimeStarSet R m,
          (1 / (q : ℝ)) *
            |nativePNTSignedSquareBlockCorrelationReciprocalSummand
              ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m| := by
      apply Finset.sum_le_sum
      intro q hqStar
      have hqData := Finset.mem_filter.mp hqStar
      have hcarrier := Finset.mem_filter.mp hqData.1
      have hqPrime : q.Prime := hcarrier.2
      have hcop :=
        vfMidActualHighPrimeStar_parent_coprime (by omega : 2 ≤ R) hm hqStar
      exact abs_vfMidActualHighPrimeProtectedChild_le_inv_mul_parent
        R m q hR hm hqPrime hcop
    _ = vfMidActualHighPrimeStarReciprocalMass R m *
        |nativePNTSignedSquareBlockCorrelationReciprocalSummand
          ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m| := by
      unfold vfMidActualHighPrimeStarReciprocalMass
      rw [Finset.sum_mul]

/-! ## High-owner star compression -/

/-- High owner primes whose child of one fixed positive parent still fits below
the pre-square endpoint.  Since every owner is above the root, no product of
two distinct owners can occur below `R^2-1`. -/
def vfMidActualHighPrimeStarSet (R m : ℕ) : Finset ℕ :=
  (vfMidActualPreSquarePrimeCarrier R).filter fun q =>
    m * q ≤ squareRootEndpoint R

/-- Reciprocal owner mass of one completed high-prime star. -/
def vfMidActualHighPrimeStarReciprocalMass (R m : ℕ) : ℝ :=
  ∑ q ∈ vfMidActualHighPrimeStarSet R m, 1 / (q : ℝ)

/-- The direct protected-correlation mass of one parent together with all of
its completed actual high-prime children. -/
def vfMidActualHighPrimeProtectedStarMass (R m : ℕ) : ℝ :=
  nativePNTSignedSquareBlockCorrelationReciprocalSummand
      ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m +
    ∑ q ∈ vfMidActualHighPrimeStarSet R m,
      nativePNTSignedSquareBlockCorrelationReciprocalSummand
        ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) (m * q)

/-- Total signed response-difference defect carried by one high-owner star. -/
def vfMidActualHighPrimeProtectedStarDefectMass (R m : ℕ) : ℝ :=
  ∑ q ∈ vfMidActualHighPrimeStarSet R m,
    nativePNTSignedSquareBlockFreshPrimePhysicalDefect
      ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m q

/-- A legal high-owner child forces its fixed parent strictly below the root. -/
theorem vfMidActualHighPrimeStar_parent_lt_root
    {R m q : ℕ} (hR : 2 ≤ R) (hm : 1 ≤ m)
    (hq : q ∈ vfMidActualHighPrimeStarSet R m) :
    m < R := by
  have hqData := Finset.mem_filter.mp hq
  have hcarrier :=
    Finset.mem_filter.mp hqData.1
  have hRq : R < q := (Finset.mem_Ioc.mp hcarrier.1).1
  have hmq : m * q ≤ squareRootEndpoint R := hqData.2
  unfold squareRootEndpoint at hmq
  nlinarith

/-- Hence every owner in one legal star is fresh for the fixed parent. -/
theorem vfMidActualHighPrimeStar_parent_coprime
    {R m q : ℕ} (hR : 2 ≤ R) (hm : 1 ≤ m)
    (hq : q ∈ vfMidActualHighPrimeStarSet R m) :
    Nat.Coprime m q := by
  have hqData := Finset.mem_filter.mp hq
  have hcarrier := Finset.mem_filter.mp hqData.1
  have hqPrime : q.Prime := hcarrier.2
  have hRq : R < q := (Finset.mem_Ioc.mp hcarrier.1).1
  have hmR := vfMidActualHighPrimeStar_parent_lt_root hR hm hq
  have hmq : m < q := hmR.trans hRq
  exact (Nat.coprime_of_lt_prime (by omega : m ≠ 0) hmq hqPrime).symm

/-- **Exact actual-prime star compression on the direct protected
correlation.**  Because two high owners cannot form a mixed child below the
square, every child attaches directly to the same low parent.  Summing the
one-prime reciprocal Euler laws therefore leaves exactly the coefficient

  `1 - sum_{q in star} 1/q`

on the parent, plus the complete signed physical-defect star.  No norm or
prime-density replacement has been taken. -/
theorem vfMidActualHighPrimeProtectedStarMass_eq
    (R m : ℕ) (hR : 2 ≤ R) (hm : 1 ≤ m) :
    vfMidActualHighPrimeProtectedStarMass R m =
      (1 - vfMidActualHighPrimeStarReciprocalMass R m) *
          nativePNTSignedSquareBlockCorrelationReciprocalSummand
            ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m +
        vfMidActualHighPrimeProtectedStarDefectMass R m := by
  let v : ℕ → ℝ := fun n =>
    nativePNTSignedSquareBlockCorrelationReciprocalSummand
      ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) n
  let D : ℕ → ℝ := fun q =>
    nativePNTSignedSquareBlockFreshPrimePhysicalDefect
      ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m q
  let S : Finset ℕ := vfMidActualHighPrimeStarSet R m
  have hchild :
      (∑ q ∈ S, v (m * q)) =
        ∑ q ∈ S, (-(1 / (q : ℝ)) * v m + D q) := by
    apply Finset.sum_congr rfl
    intro q hq
    have hqData := Finset.mem_filter.mp hq
    have hcarrier := Finset.mem_filter.mp hqData.1
    have hqPrime : q.Prime := hcarrier.2
    have hcop := vfMidActualHighPrimeStar_parent_coprime hR hm hq
    have hpair :=
      nativePNTSignedSquareBlockCorrelationReciprocalSummand_add_mul_freshPrime
        ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2)
        (by omega : 0 < m) hqPrime hcop
    change v m + v (m * q) =
      (1 - 1 / (q : ℝ)) * v m + D q at hpair
    linarith
  unfold vfMidActualHighPrimeProtectedStarMass
    vfMidActualHighPrimeStarReciprocalMass
    vfMidActualHighPrimeProtectedStarDefectMass
  change v m + ∑ q ∈ S, v (m * q) =
    (1 - ∑ q ∈ S, 1 / (q : ℝ)) * v m + ∑ q ∈ S, D q
  rw [hchild, Finset.sum_add_distrib]
  have hscale :
      (∑ q ∈ S, -(1 / (q : ℝ)) * v m) =
        -(∑ q ∈ S, 1 / (q : ℝ)) * v m := by
    rw [← Finset.sum_mul]
    congr 1
    rw [← Finset.sum_neg_distrib]
  rw [hscale]
  ring

/-- Distinct high owners cannot coexist in a pre-square child product.  This is
the geometric reason the completed post-root family is a star at fixed parent,
not a two-high-prime Boolean face. -/
theorem vfMidActualHighPrimeStar_no_two_owner_child
    {R m q r : ℕ} (hm : 1 ≤ m)
    (hq : q ∈ vfMidActualPreSquarePrimeCarrier R)
    (hr : r ∈ vfMidActualPreSquarePrimeCarrier R)
    (hqr : q ≠ r) :
    ¬ m * q * r ≤ squareRootEndpoint R := by
  intro hfit
  have hqData := Finset.mem_filter.mp hq
  have hrData := Finset.mem_filter.mp hr
  have hRq : R < q := (Finset.mem_Ioc.mp hqData.1).1
  have hRr : R < r := (Finset.mem_Ioc.mp hrData.1).1
  unfold squareRootEndpoint at hfit
  nlinarith

/-- The fixed VF alignment phase never changes square-block increments.  This is
restated here only to keep the endpoint conclusion adjacent to the actual-prime
carrier lemmas above. -/
theorem vfMidInitialAnchor_preserves_square_increment
    {R : ℕ} (hR : 2 ≤ R) :
    vfMidAlignedMass vfMidInitialAnchor (R + 1) -
        vfMidAlignedMass vfMidInitialAnchor R =
      vfMidBandMass R := by
  rw [vfMidAlignedMass_succ vfMidInitialAnchor hR]
  ring

end RHLean.Proof

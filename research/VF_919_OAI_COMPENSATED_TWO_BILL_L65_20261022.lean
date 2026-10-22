import Mathlib
import «research.VF_919_OAI_GROUPED_HOLDER_SIXTH_SOURCE_20261022»

/-!
# Source-honest two-bill conditional ell^(6/5) estimate

The already-grouped OAI compensated fiber b(m) is decomposed into two
source-specific physical bills:
    b(m) = shift(m) + Euler(m).
The original local identity does NOT prove a Z^(-sigma) bound for either.

What is proved here, independently and exactly:
  (i) finite ell^(6/5) norm of the grouped sum, from actual pointwise
      shift and Euler bills multiplied by the prime-slot multiplicity tau;
 (ii) the D^(1/3+c) Z^(-sigma) exponent arithmetic WHEN the needed
      pointwise scale and multiplicity MOMENT estimates are supplied.

The missing source obligations are not wrapped in invented statements:
  * source-specific alignment of physical windows at child/parent scale;
  * verified derivative bound AND slot-band width eta_P = O(Z^-sigma);
  * BOTH terms of ProbeLocal.normalized_cancellation;
  * physical normalization and masks; actual prime representation tau;
  * a separate finite ideal-count / tau^(6/5) moment bound.
No real analytic or Hecke estimates are imported from the target high-row
bound, and a generic finite sum inequality is not called an OAI proof.
-/

noncomputable section
open scoped Classical BigOperators

namespace RHLean.Analysis

/-- Once the SOURCE-SPECIFIC shift and Euler bills have been bounded
    pointwise against the SAME actual prime-slot multiplicity, the
    already-compensated fiber sum has the exact weighted ell^(6/5)
    bound. The coefficient is shift+Euler, NOT the ungrouped atoms.
    The factor T_tau is a proven independent multiplicity norm, never
    replaced by the mean tau without a justified moment bound. -/
theorem oai_grouped_fiber_l65_bound
    {α : Type*} (carrier : Finset α)
    (shift euler : α → ℂ) (tau : α → ℝ)
    (Ashift Aeuler Ttau : ℝ)
    (hAshift : 0 ≤ Ashift) (hAeuler : 0 ≤ Aeuler)
    (htau : ∀ m ∈ carrier, 0 ≤ tau m)
    (hShift : ∀ m ∈ carrier, ‖shift m‖ ≤ Ashift * tau m)
    (hEuler : ∀ m ∈ carrier, ‖euler m‖ ≤ Aeuler * tau m)
    (hTauMoment :
      (∑ m ∈ carrier, tau m ^ (6 / 5 : ℝ)) ^
        (5 / 6 : ℝ) ≤ Ttau) :
    (∑ m ∈ carrier, ‖shift m + euler m‖ ^ (6 / 5 : ℝ)) ^
      (5 / 6 : ℝ) ≤ (Ashift + Aeuler) * Ttau := by
  let A := Ashift + Aeuler
  have hA : 0 ≤ A := add_nonneg hAshift hAeuler
  have hPoint (m : α) (hm : m ∈ carrier) :
      ‖shift m + euler m‖ ≤ A * tau m := by
    calc
      _ ≤ ‖shift m‖ + ‖euler m‖ := norm_add_le _ _
      _ ≤ Ashift * tau m + Aeuler * tau m :=
        add_le_add (hShift m hm) (hEuler m hm)
      _ = A * tau m := by dsimp [A]; ring
  have hSum :
      (∑ m ∈ carrier, ‖shift m + euler m‖ ^ (6 / 5 : ℝ)) ≤
        A ^ (6 / 5 : ℝ) *
          (∑ m ∈ carrier, tau m ^ (6 / 5 : ℝ)) := by
    calc
      _ ≤ ∑ m ∈ carrier, (A * tau m) ^ (6 / 5 : ℝ) := by
        apply Finset.sum_le_sum
        intro m hm
        exact Real.rpow_le_rpow (norm_nonneg _) (hPoint m hm)
          (by norm_num)
      _ = ∑ m ∈ carrier,
          A ^ (6 / 5 : ℝ) * tau m ^ (6 / 5 : ℝ) := by
        apply Finset.sum_congr rfl
        intro m hm
        exact Real.mul_rpow hA (htau m hm)
      _ = _ := by rw [Finset.mul_sum]
  have hTauSumNonneg :
      0 ≤ ∑ m ∈ carrier, tau m ^ (6 / 5 : ℝ) := by
    apply Finset.sum_nonneg
    intro m hm
    exact Real.rpow_nonneg (htau m hm) _
  have hCoeffSumNonneg :
      0 ≤ ∑ m ∈ carrier, ‖shift m + euler m‖ ^ (6 / 5 : ℝ) := by
    positivity
  have hroot :
      (∑ m ∈ carrier, ‖shift m + euler m‖ ^ (6 / 5 : ℝ)) ^
        (5 / 6 : ℝ) ≤
        (A ^ (6 / 5 : ℝ) *
          (∑ m ∈ carrier, tau m ^ (6 / 5 : ℝ))) ^ (5 / 6 : ℝ) :=
    Real.rpow_le_rpow hCoeffSumNonneg hSum (by norm_num)
  have hpow : (A ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) = A := by
    rw [← Real.rpow_mul hA]
    norm_num
  have hTauNonneg :
      0 ≤ (∑ m ∈ carrier, tau m ^ (6 / 5 : ℝ)) ^
          (5 / 6 : ℝ) := by positivity
  calc
    _ ≤ (A ^ (6 / 5 : ℝ) *
          (∑ m ∈ carrier, tau m ^ (6 / 5 : ℝ))) ^ (5 / 6 : ℝ) :=
      hroot
    _ = A *
        (∑ m ∈ carrier, tau m ^ (6 / 5 : ℝ)) ^
          (5 / 6 : ℝ) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hA _) hTauSumNonneg, hpow]
    _ ≤ A * Ttau := mul_le_mul_of_nonneg_left hTauMoment hA
    _ = (Ashift + Aeuler) * Ttau := rfl

/-- Algebraically, a bound D^(-1/2)*Z^(-sigma) for both *combined*
    physical bills and a real independent tau moment of
    D^(5/6+c) yield D^(1/3+c) Z^(-sigma) in the ell^(6/5)
    coefficient norm. Those two premise bounds are the OPEN original
    Stage-II analytic work; a fixed-width prime slot cannot supply the
    first simply by being called a narrow window. -/
theorem oai_grouped_fiber_l65_power_budget
    {α : Type*} (carrier : Finset α)
    (shift euler : α → ℂ) (tau : α → ℝ)
    (Ashift Aeuler D Z sigma c : ℝ)
    (hAshift : 0 ≤ Ashift) (hAeuler : 0 ≤ Aeuler)
    (hD : 0 < D) (_hZ : 0 < Z)
    (htau : ∀ m ∈ carrier, 0 ≤ tau m)
    (hShift : ∀ m ∈ carrier, ‖shift m‖ ≤ Ashift * tau m)
    (hEuler : ∀ m ∈ carrier, ‖euler m‖ ≤ Aeuler * tau m)
    (hAmp : Ashift + Aeuler ≤ D ^ (-(1 / 2 : ℝ)) * Z ^ (-sigma))
    (hTauMoment :
      (∑ m ∈ carrier, tau m ^ (6 / 5 : ℝ)) ^
        (5 / 6 : ℝ) ≤ D ^ ((5 / 6 : ℝ) + c)) :
    (∑ m ∈ carrier, ‖shift m + euler m‖ ^ (6 / 5 : ℝ)) ^
      (5 / 6 : ℝ) ≤ D ^ ((1 / 3 : ℝ) + c) * Z ^ (-sigma) := by
  have hTwo := oai_grouped_fiber_l65_bound
    carrier shift euler tau Ashift Aeuler
    (D ^ ((5 / 6 : ℝ) + c))
    hAshift hAeuler htau hShift hEuler hTauMoment
  calc
    _ ≤ (Ashift + Aeuler) * D ^ ((5 / 6 : ℝ) + c) := hTwo
    _ ≤ (D ^ (-(1 / 2 : ℝ)) * Z ^ (-sigma)) *
        D ^ ((5 / 6 : ℝ) + c) :=
      mul_le_mul_of_nonneg_right hAmp (Real.rpow_nonneg hD.le _)
    _ = D ^ ((1 / 3 : ℝ) + c) * Z ^ (-sigma) := by
      have hcancel :
          D ^ (-(1 / 2 : ℝ)) * D ^ (1 / 2 : ℝ) = 1 := by
        rw [← Real.rpow_add hD]
        norm_num
      calc
        (D ^ (-(1 / 2 : ℝ)) * Z ^ (-sigma)) *
          D ^ ((5 / 6 : ℝ) + c) =
          (D ^ (-(1 / 2 : ℝ)) * D ^ (1 / 2 : ℝ)) *
          (D ^ ((1 / 3 : ℝ) + c) * Z ^ (-sigma)) := by
            rw [show ((5 / 6 : ℝ) + c) =
              (1 / 2 : ℝ) + ((1 / 3 : ℝ) + c) by ring,
              Real.rpow_add hD]
            ring
        _ = D ^ ((1 / 3 : ℝ) + c) * Z ^ (-sigma) := by
          rw [hcancel, one_mul]

/-- THE USER-REQUESTED REPLACEMENT for premature triangle inequality:
    bound the exact SIGNED/RECOMBINED local physical coefficient
    `bill(m) = shift(m)+Euler(m)` itself, then take ell^(6/5).
    Neither individual bill is assumed small. Thus potentially large
    opposite-signed terms may cancel pointwise BEFORE Holder. -/
theorem oai_grouped_recombined_single_bill_l65_bound
    {α : Type*} (carrier : Finset α)
    (bill : α → ℂ) (tau : α → ℝ)
    (A Ttau : ℝ) (hA : 0 ≤ A)
    (htau : ∀ m ∈ carrier, 0 ≤ tau m)
    (hCombined : ∀ m ∈ carrier, ‖bill m‖ ≤ A * tau m)
    (hTauMoment :
      (∑ m ∈ carrier, tau m ^ (6 / 5 : ℝ)) ^
        (5 / 6 : ℝ) ≤ Ttau) :
    (∑ m ∈ carrier, ‖bill m‖ ^ (6 / 5 : ℝ)) ^
      (5 / 6 : ℝ) ≤ A * Ttau := by
  have hZero : ∀ m ∈ carrier,
      ‖(0 : ℂ)‖ ≤ (0 : ℝ) * tau m := by
    intro m hm
    simp
  have h := oai_grouped_fiber_l65_bound
    carrier bill (fun _ => 0) tau A 0 Ttau
    hA (le_refl _) htau hCombined hZero hTauMoment
  simpa only [add_zero] using h

/-- Exact exponent budget on ONLY the already recombined local
    coefficient. The one-prime original OAI power estimate supplies
    a candidate for hCombined, while the physical source normalization
    and multiplicity moment remain visible arithmetic premises. -/
theorem oai_grouped_recombined_single_bill_l65_power_budget
    {α : Type*} (carrier : Finset α)
    (bill : α → ℂ) (tau : α → ℝ)
    (A D Z sigma c : ℝ)
    (hA : 0 ≤ A) (hD : 0 < D) (hZ : 0 < Z)
    (htau : ∀ m ∈ carrier, 0 ≤ tau m)
    (hCombined : ∀ m ∈ carrier, ‖bill m‖ ≤ A * tau m)
    (hAmp : A ≤ D ^ (-(1 / 2 : ℝ)) * Z ^ (-sigma))
    (hTauMoment :
      (∑ m ∈ carrier, tau m ^ (6 / 5 : ℝ)) ^
        (5 / 6 : ℝ) ≤ D ^ ((5 / 6 : ℝ) + c)) :
    (∑ m ∈ carrier, ‖bill m‖ ^ (6 / 5 : ℝ)) ^
      (5 / 6 : ℝ) ≤ D ^ ((1 / 3 : ℝ) + c) * Z ^ (-sigma) := by
  have hZero : ∀ m ∈ carrier,
      ‖(0 : ℂ)‖ ≤ (0 : ℝ) * tau m := by
    intro m hm
    simp
  have h := oai_grouped_fiber_l65_power_budget
    carrier bill (fun _ => 0) tau A 0 D Z sigma c
    hA (le_refl _) hD hZ htau hCombined hZero
    (by simpa only [add_zero] using hAmp) hTauMoment
  simpa only [add_zero] using h

/-! ## Correct order of operations: first recombine, THEN bound the coefficient -/

/-- Use ONE pointwise bound on the signed, already-recombined physical
    correction.  Unlike the legacy two-bill consumer above, this statement
    never assumes a separate upper bound on either correction summand.
    The multiplicity moment is still an independent arithmetic obligation. -/
theorem oai_grouped_fiber_l65_recombined_bound
    {α : Type*} (carrier : Finset α)
    (combined : α → ℂ) (tau : α → ℝ)
    (A Ttau : ℝ) (hA : 0 ≤ A)
    (htau : ∀ m ∈ carrier, 0 ≤ tau m)
    (hCombined : ∀ m ∈ carrier, ‖combined m‖ ≤ A * tau m)
    (hTauMoment :
      (∑ m ∈ carrier, tau m ^ (6 / 5 : ℝ)) ^
        (5 / 6 : ℝ) ≤ Ttau) :
    (∑ m ∈ carrier, ‖combined m‖ ^ (6 / 5 : ℝ)) ^
      (5 / 6 : ℝ) ≤ A * Ttau := by
  have hZero :
      ∀ m ∈ carrier, ‖(0 : ℂ)‖ ≤ (0 : ℝ) * tau m := by
    simp
  have h := oai_grouped_fiber_l65_bound
    carrier combined (fun _ => 0) tau A 0 Ttau
    hA (le_refl (0 : ℝ)) htau hCombined hZero hTauMoment
  simpa only [add_zero] using h

/-- The exponent-budget acceptance theorem with the CORRECT single-bill
    hypothesis.  In particular it allows cancellation between the exact
    ProbeLocal.first and second residuals BEFORE taking a norm.  This
    only proves the implication from a pointwise SOURCE-specific estimate
    and a separate tau^(6/5) moment; neither is manufactured here. -/
theorem oai_grouped_fiber_l65_power_budget_recombined
    {α : Type*} (carrier : Finset α)
    (combined : α → ℂ) (tau : α → ℝ)
    (D Z sigma c : ℝ)
    (hD : 0 < D) (_hZ : 0 < Z)
    (htau : ∀ m ∈ carrier, 0 ≤ tau m)
    (hCombined :
      ∀ m ∈ carrier,
        ‖combined m‖ ≤
          (D ^ (-(1 / 2 : ℝ)) * Z ^ (-sigma)) * tau m)
    (hTauMoment :
      (∑ m ∈ carrier, tau m ^ (6 / 5 : ℝ)) ^
        (5 / 6 : ℝ) ≤ D ^ ((5 / 6 : ℝ) + c)) :
    (∑ m ∈ carrier, ‖combined m‖ ^ (6 / 5 : ℝ)) ^
      (5 / 6 : ℝ) ≤ D ^ ((1 / 3 : ℝ) + c) * Z ^ (-sigma) := by
  have hA : 0 ≤ D ^ (-(1 / 2 : ℝ)) * Z ^ (-sigma) := by
    positivity
  have hBound := oai_grouped_fiber_l65_recombined_bound
    carrier combined tau
      (D ^ (-(1 / 2 : ℝ)) * Z ^ (-sigma))
      (D ^ ((5 / 6 : ℝ) + c))
      hA htau hCombined hTauMoment
  calc
    _ ≤ (D ^ (-(1 / 2 : ℝ)) * Z ^ (-sigma)) *
          D ^ ((5 / 6 : ℝ) + c) := hBound
    _ = D ^ ((1 / 3 : ℝ) + c) * Z ^ (-sigma) := by
      have hcancel :
          D ^ (-(1 / 2 : ℝ)) * D ^ (1 / 2 : ℝ) = 1 := by
        rw [← Real.rpow_add hD]
        norm_num
      calc
        (D ^ (-(1 / 2 : ℝ)) * Z ^ (-sigma)) *
            D ^ ((5 / 6 : ℝ) + c) =
            (D ^ (-(1 / 2 : ℝ)) * D ^ (1 / 2 : ℝ)) *
              (D ^ ((1 / 3 : ℝ) + c) * Z ^ (-sigma)) := by
            rw [show ((5 / 6 : ℝ) + c) =
              (1 / 2 : ℝ) + ((1 / 3 : ℝ) + c) by ring,
              Real.rpow_add hD]
            ring
        _ = D ^ ((1 / 3 : ℝ) + c) * Z ^ (-sigma) := by
          rw [hcancel, one_mul]

/-- Ergonomic drop-in: the two named local residuals are assembled
    BEFORE the pointwise bound is assumed, instead of receiving
    independent triangle-inequality estimates. -/
theorem oai_grouped_fiber_l65_power_budget_one_bill
    {α : Type*} (carrier : Finset α)
    (first second : α → ℂ) (tau : α → ℝ)
    (D Z sigma c : ℝ)
    (hD : 0 < D) (hZ : 0 < Z)
    (htau : ∀ m ∈ carrier, 0 ≤ tau m)
    (hRecombined :
      ∀ m ∈ carrier,
        ‖first m + second m‖ ≤
          (D ^ (-(1 / 2 : ℝ)) * Z ^ (-sigma)) * tau m)
    (hTauMoment :
      (∑ m ∈ carrier, tau m ^ (6 / 5 : ℝ)) ^
        (5 / 6 : ℝ) ≤ D ^ ((5 / 6 : ℝ) + c)) :
    (∑ m ∈ carrier, ‖first m + second m‖ ^ (6 / 5 : ℝ)) ^
      (5 / 6 : ℝ) ≤ D ^ ((1 / 3 : ℝ) + c) * Z ^ (-sigma) :=
  oai_grouped_fiber_l65_power_budget_recombined
    carrier (fun m => first m + second m) tau D Z sigma c
    hD hZ htau hRecombined hTauMoment


/-!
## Independent scalar one-prime dyadic rate: 7/8 versus 5/6

The pointwise original-OAI one-prime remainder can cost P^(-7/8)
on a dyadic prime-ideal band of size O(P). Even the weak cardinal bound
#slots <= C*P then gives the true finite ell^(6/5) rate P^(-1/24).

This result concerns the ONE-PRIME, NO-COFACTOR scalar band. It does not
identify the complete Gaussian/Mellin coefficients with these b(p),
bound effective-ideal multiplicities or prove the uniform sixth moment.
-/

/-- A genuine POWER rate for a finite one-prime band follows from the
    7/8 pointwise power and the linear slot count.  Both hypotheses are
    explicit, and the 1/24 comes from 7/8 - 5/6, not a target energy
    assumption.  Actual Hecke source admission is a separate theorem. -/
theorem oai_one_prime_dyadic_l65_power_rate
    {α : Type*} (slots : Finset α) (b : α → ℂ)
    (P C : ℝ)
    (hP : 1 ≤ P) (hC : 0 ≤ C)
    (hCard : (slots.card : ℝ) ≤ C * P)
    (hLocal : ∀ p ∈ slots,
      ‖b p‖ ≤ 720 * P ^ (-(7 / 8 : ℝ))) :
    (∑ p ∈ slots, ‖b p‖ ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) ≤
      720 * C ^ (5 / 6 : ℝ) * P ^ (-(1 / 24 : ℝ)) := by
  have hP0 : 0 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  let A : ℝ := 720 * P ^ (-(7 / 8 : ℝ))
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have htau : ∀ p ∈ slots, 0 ≤ (1 : ℝ) := by
    intro p hp
    norm_num
  have hPoint : ∀ p ∈ slots, ‖b p‖ ≤ A * (1 : ℝ) := by
    intro p hp
    simpa [A] using hLocal p hp
  have hOneNorm :
      (∑ p ∈ slots, (1 : ℝ) ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) ≤
        (slots.card : ℝ) ^ (5 / 6 : ℝ) := by
    simp
  have hOnePrime := oai_grouped_fiber_l65_recombined_bound
    slots b (fun _ => (1 : ℝ))
    A ((slots.card : ℝ) ^ (5 / 6 : ℝ))
    hA htau hPoint hOneNorm
  have hCountPow :
      (slots.card : ℝ) ^ (5 / 6 : ℝ) ≤
        (C * P) ^ (5 / 6 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hCard (by norm_num)
  have hSimplify :
      P ^ (-(7 / 8 : ℝ)) * P ^ (5 / 6 : ℝ) =
        P ^ (-(1 / 24 : ℝ)) := by
    rw [← Real.rpow_add hPpos]
    congr 1
    ring
  calc
    _ ≤ A * (slots.card : ℝ) ^ (5 / 6 : ℝ) := hOnePrime
    _ ≤ A * (C * P) ^ (5 / 6 : ℝ) :=
      mul_le_mul_of_nonneg_left hCountPow hA
    _ = 720 * C ^ (5 / 6 : ℝ) * P ^ (-(1 / 24 : ℝ)) := by
      dsimp [A]
      rw [Real.mul_rpow hC hP0]
      calc
        (720 * P ^ (-(7 / 8 : ℝ))) *
            (C ^ (5 / 6 : ℝ) * P ^ (5 / 6 : ℝ)) =
            720 * C ^ (5 / 6 : ℝ) *
              (P ^ (-(7 / 8 : ℝ)) * P ^ (5 / 6 : ℝ)) := by ring
        _ = _ := by rw [hSimplify]

/-! ## Independent convex multiplicity payment from an arithmetic cap -/

/-- For the true effective-ideal multiplicity `tau`, a UNIFORM cap K
    and a genuine carrier-cardinality count imply its convex ell^(6/5)
    moment. No Jensen reversal, average multiplicity substitution, or
    unproved source counting is involved in the finite inequality.
    Establishing K and the actual ideal-support count remains source work. -/
theorem oai_tau_l65_le_cap_mul_card_root
    {α : Type*} (carrier : Finset α) (tau : α → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (htau : ∀ m ∈ carrier, 0 ≤ tau m)
    (hcap : ∀ m ∈ carrier, tau m ≤ K) :
    (∑ m ∈ carrier, tau m ^ (6 / 5 : ℝ)) ^
      (5 / 6 : ℝ) ≤
      K * ((carrier.card : ℝ) ^ (5 / 6 : ℝ)) := by
  have hsum :
      (∑ m ∈ carrier, tau m ^ (6 / 5 : ℝ)) ≤
        (carrier.card : ℝ) * K ^ (6 / 5 : ℝ) := by
    calc
      _ ≤ ∑ m ∈ carrier, K ^ (6 / 5 : ℝ) := by
        apply Finset.sum_le_sum
        intro m hm
        exact Real.rpow_le_rpow (htau m hm) (hcap m hm)
          (by norm_num)
      _ = (carrier.card : ℝ) * K ^ (6 / 5 : ℝ) := by
        simp
  have hsum_nonneg :
      0 ≤ ∑ m ∈ carrier, tau m ^ (6 / 5 : ℝ) := by
    apply Finset.sum_nonneg
    intro m hm
    exact Real.rpow_nonneg (htau m hm) _
  have hcard : 0 ≤ (carrier.card : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ ((carrier.card : ℝ) * K ^ (6 / 5 : ℝ)) ^
          (5 / 6 : ℝ) :=
      Real.rpow_le_rpow hsum_nonneg hsum (by norm_num)
    _ = ((carrier.card : ℝ) ^ (5 / 6 : ℝ)) *
          ((K ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ)) := by
      rw [Real.mul_rpow hcard (Real.rpow_nonneg hK _)]
    _ = K * ((carrier.card : ℝ) ^ (5 / 6 : ℝ)) := by
      rw [← Real.rpow_mul hK]
      norm_num
      ring

end RHLean.Analysis

#print axioms RHLean.Analysis.oai_grouped_fiber_l65_bound
#print axioms RHLean.Analysis.oai_grouped_fiber_l65_power_budget

#print axioms RHLean.Analysis.oai_grouped_recombined_single_bill_l65_bound
#print axioms RHLean.Analysis.oai_grouped_recombined_single_bill_l65_power_budget
#print axioms RHLean.Analysis.oai_grouped_fiber_l65_recombined_bound
#print axioms RHLean.Analysis.oai_grouped_fiber_l65_power_budget_recombined
#print axioms RHLean.Analysis.oai_grouped_fiber_l65_power_budget_one_bill
#print axioms RHLean.Analysis.oai_one_prime_dyadic_l65_power_rate

#print axioms RHLean.Analysis.oai_tau_l65_le_cap_mul_card_root

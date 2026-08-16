import Mathlib
import RHLean.Proof.SquareRootMertensEndpointAmplification
import RHLean.Analysis.SquarePrefixMertensBridge

/-!
# Fixed square-root amplification closes the Mertens energy exponent

The open square-root endpoint theorem allows an arbitrary fixed absolute
amplification constant `A`:

`(M(R^2-1)-1)^2 <= A * R^2 * K_R`,

where `K_R` controls the shifted critical energy on all lower arguments `y<R`.
A subunit contraction is not required.  For each `epsilon > 0`, choose an onset
at which `4*A <= R^epsilon`.  Strong induction on the physical integer `x`
then closes the full shifted Mertens estimate.  The unfinished part of one
square block contributes only `O(R^2)` after squaring.

Thus the fixed-amplification endpoint statement implies the repository's
standard Mertens energy criterion.  The only number-theoretic input is the open
endpoint statement itself; everything here is deterministic square-root
bookkeeping.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators Topology

namespace RHLean.Proof

/-- Shifted complex Mertens energy.  The shift by one is the exceptional source
omitted from the canonical ancestry universe. -/
def shiftedMertensEnergy (x : ℕ) : ℝ :=
  ‖RHLean.Analysis.mertensSummatory x - 1‖ ^ 2

/-- The shifted complex energy is the real square of the integer Mertens
numerator used by the endpoint amplification theorem. -/
theorem shiftedMertensEnergy_eq_intSquare (x : ℕ) :
    shiftedMertensEnergy x =
      (((mertensSummatoryInt x - 1 : ℤ) : ℝ) ^ 2) := by
  unfold shiftedMertensEnergy
  rw [← mertensSummatoryInt_cast x]
  have hcast :
      (((mertensSummatoryInt x : ℤ) : ℂ) - 1) =
        (((mertensSummatoryInt x - 1 : ℤ) : ℂ)) := by
    push_cast
    ring
  rw [hcast, Complex.norm_intCast]
  exact sq_abs (((mertensSummatoryInt x - 1 : ℤ) : ℝ))

/-- Crude shifted bound used only on the finite base range. -/
theorem norm_shiftedMertens_le_succ (x : ℕ) :
    ‖RHLean.Analysis.mertensSummatory x - 1‖ ≤ (x + 1 : ℝ) := by
  have hM := RHLean.Analysis.norm_mertensSummatory_sub_le 0 x (Nat.zero_le x)
  rw [RHLean.Analysis.mertensSummatory_zero, sub_zero] at hM
  calc
    ‖RHLean.Analysis.mertensSummatory x - 1‖ ≤
        ‖RHLean.Analysis.mertensSummatory x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = ‖RHLean.Analysis.mertensSummatory x‖ + 1 := by norm_num
    _ ≤ (x : ℝ) + 1 := add_le_add_right hM 1
    _ = (x + 1 : ℝ) := by push_cast; ring

private theorem shifted_norm_sq_add_le_two (u v : ℂ) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have hnorm := norm_add_le u v
  have hu : 0 ≤ ‖u‖ := norm_nonneg _
  have hv : 0 ≤ ‖v‖ := norm_nonneg _
  have huv : 0 ≤ ‖u + v‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

private theorem rpow_sq_one_add (r ε : ℝ) (hr : 0 ≤ r) :
    Real.rpow (r ^ 2) (1 + ε) = Real.rpow r (2 + 2 * ε) := by
  have htwo : Real.rpow r (2 : ℝ) = r ^ (2 : ℕ) :=
    Real.rpow_natCast r 2
  calc
    Real.rpow (r ^ 2) (1 + ε) =
        Real.rpow (Real.rpow r (2 : ℝ)) (1 + ε) := by
      congr 1
      exact htwo.symm
    _ = Real.rpow r ((2 : ℝ) * (1 + ε)) :=
      (Real.rpow_mul hr (2 : ℝ) (1 + ε)).symm
    _ = Real.rpow r (2 + 2 * ε) := by ring_nf

private theorem rpow_two_add_two_mul_eq_sq_mul_rpow_sq
    (r ε : ℝ) (hr : 0 < r) :
    Real.rpow r (2 + 2 * ε) =
      r ^ 2 * (Real.rpow r ε) ^ 2 := by
  calc
    Real.rpow r (2 + 2 * ε) =
        Real.rpow r (2 + (2 * ε)) := by congr 1 <;> ring
    _ = Real.rpow r 2 * Real.rpow r (2 * ε) :=
      Real.rpow_add (x := r) hr 2 (2 * ε)
    _ = r ^ 2 * Real.rpow r (ε + ε) := by
      rw [Real.rpow_natCast]
      congr 2 <;> ring
    _ = r ^ 2 * (Real.rpow r ε * Real.rpow r ε) := by
      rw [Real.rpow_add (x := r) hr ε ε]
    _ = r ^ 2 * (Real.rpow r ε) ^ 2 := by ring

/-- A fixed absolute endpoint amplification constant gives the full shifted
Mertens critical-energy bound, with an arbitrarily small exponent loss. -/
theorem shiftedMertensEnergyBounded_of_squareRootEndpointAmplification
    (hamp : SquareRootMertensEndpointAmplificationStatement) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ x : ℕ,
          shiftedMertensEnergy x ≤
            C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by
  rintro ε hε
  rcases hamp with ⟨A, hA, hamp⟩
  have htend :
      Filter.Tendsto (fun R : ℕ => Real.rpow (R : ℝ) ε)
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ R : ℕ in Filter.atTop,
      4 * A ≤ Real.rpow (R : ℝ) ε :=
    (tendsto_atTop.1 htend) (4 * A)
  rcases (eventually_atTop.1 hevent) with ⟨N, hN⟩
  let R0 : ℕ := max 2 N
  let C : ℝ := 36 + ((R0 ^ 2 + 1 : ℕ) : ℝ)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hC36 : 36 ≤ C := by
    dsimp [C]
    positivity
  have hCR0 : ((R0 ^ 2 + 1 : ℕ) : ℝ) ≤ C := by
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
      by_cases hxbase : x < R0 ^ 2
      · have hnorm := norm_shiftedMertens_le_succ x
        have hx1Nat : x + 1 ≤ R0 ^ 2 + 1 :=
          Nat.succ_le_succ hxbase.le
        have hx1 : (x + 1 : ℝ) ≤ ((R0 ^ 2 + 1 : ℕ) : ℝ) := by
          exact_mod_cast hx1Nat
        have hsq : shiftedMertensEnergy x ≤ (x + 1 : ℝ) ^ 2 := by
          unfold shiftedMertensEnergy
          have hnonneg : 0 ≤ ‖RHLean.Analysis.mertensSummatory x - 1‖ := norm_nonneg _
          have hxnonneg : 0 ≤ (x + 1 : ℝ) := by positivity
          nlinarith [sq_nonneg (‖RHLean.Analysis.mertensSummatory x - 1‖ -
            (x + 1 : ℝ))]
        have hxC : (x + 1 : ℝ) ≤ C := hx1.trans hCR0
        have hxpos : 0 ≤ (x + 1 : ℝ) := by positivity
        have hlin : (x + 1 : ℝ) ^ 2 ≤ C * (x + 1 : ℝ) := by
          have hmul := mul_nonneg hxpos (sub_nonneg.mpr hxC)
          nlinarith
        have hbasePow :
            (x + 1 : ℝ) ≤ Real.rpow (x + 1 : ℝ) (1 + ε) := by
          have hbase : (1 : ℝ) ≤ (x + 1 : ℝ) := by positivity
          have hexp : (1 : ℝ) ≤ 1 + ε := by linarith
          simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le hbase hexp
        exact hsq.trans (hlin.trans
          (mul_le_mul_of_nonneg_left hbasePow hC))
      · have hxlarge : R0 ^ 2 ≤ x := Nat.le_of_not_gt hxbase
        let R : ℕ := Nat.sqrt x
        have hR0 : R0 ≤ R := by
          by_contra hnot
          have hRlt : R < R0 := Nat.lt_of_not_ge hnot
          have hxlt : x < (R + 1) ^ 2 := by
            dsimp [R]
            exact Nat.lt_succ_sqrt' x
          have hsquares : (R + 1) ^ 2 ≤ R0 ^ 2 :=
            Nat.pow_le_pow_left (by omega) 2
          exact (Nat.not_lt_of_ge hxlarge) (hxlt.trans_le hsquares)
        have h2R0 : 2 ≤ R0 := by
          dsimp [R0]
          omega
        have hNR0 : N ≤ R0 := by
          dsimp [R0]
          omega
        have hR2 : 2 ≤ R := h2R0.trans hR0
        have hRpos : 0 < (R : ℝ) := by exact_mod_cast (show 0 < R by omega)
        have hRnonneg : 0 ≤ (R : ℝ) := le_of_lt hRpos
        have hRsq : R ^ 2 ≤ x := by
          dsimp [R]
          exact Nat.sqrt_le' x
        have hxltNext : x < (R + 1) ^ 2 := by
          dsimp [R]
          exact Nat.lt_succ_sqrt' x
        have hNleR : N ≤ R := hNR0.trans hR0
        have honset : 4 * A ≤ Real.rpow (R : ℝ) ε := hN R hNleR
        let K : ℝ := C * Real.rpow (R : ℝ) ε
        have hKnonneg : 0 ≤ K := by
          dsimp [K]
          exact mul_nonneg hC (Real.rpow_nonneg hRnonneg ε)
        have hEnvelope : LowerMertensCriticalEnvelope R K := by
          refine ⟨hKnonneg, ?_⟩
          intro y hyR
          have hRleSq : R ≤ R ^ 2 := by
            calc
              R = R * 1 := by ring
              _ ≤ R * R := Nat.mul_le_mul_left R (by omega)
              _ = R ^ 2 := by ring
          have hRx : R ≤ x := hRleSq.trans hRsq
          have hyx : y < x := hyR.trans_le hRx
          have hiy := ih y hyx
          rw [shiftedMertensEnergy_eq_intSquare] at hiy
          have hy1R : y + 1 ≤ R := by omega
          have hpowMono :
              Real.rpow (y + 1 : ℝ) ε ≤ Real.rpow (R : ℝ) ε :=
            Real.rpow_le_rpow (by positivity) (by exact_mod_cast hy1R) (by linarith)
          have hfactor :
              Real.rpow (y + 1 : ℝ) (1 + ε) =
                (y + 1 : ℝ) * Real.rpow (y + 1 : ℝ) ε := by
            calc
              Real.rpow (y + 1 : ℝ) (1 + ε) =
                  Real.rpow (y + 1 : ℝ) 1 *
                    Real.rpow (y + 1 : ℝ) ε :=
                Real.rpow_add (x := (y + 1 : ℝ)) (by positivity) 1 ε
              _ = (y + 1 : ℝ) * Real.rpow (y + 1 : ℝ) ε := by
                rw [Real.rpow_one]
          rw [hfactor] at hiy
          dsimp [K]
          have hcy : 0 ≤ C * (y + 1 : ℝ) := by positivity
          calc
            (((mertensSummatoryInt y - 1 : ℤ) : ℝ) ^ 2) ≤
                C * ((y + 1 : ℝ) * Real.rpow (y + 1 : ℝ) ε) := hiy
            _ = (C * (y + 1 : ℝ)) * Real.rpow (y + 1 : ℝ) ε := by ring
            _ ≤ (C * (y + 1 : ℝ)) * Real.rpow (R : ℝ) ε :=
              mul_le_mul_of_nonneg_left hpowMono hcy
            _ = (C * Real.rpow (R : ℝ) ε) * (y + 1 : ℝ) := by ring
        have hendpointInt := hamp R K hR2 hEnvelope
        let e : ℕ := squareRootEndpoint R
        have heLe : e ≤ x := by
          dsimp [e, squareRootEndpoint]
          exact (Nat.sub_le _ _).trans hRsq
        have hendpoint :
            shiftedMertensEnergy e ≤ A * (R : ℝ) ^ 2 * K := by
          rw [shiftedMertensEnergy_eq_intSquare]
          exact hendpointInt
        have hrpowSq :
            (R : ℝ) ^ 2 * (Real.rpow (R : ℝ) ε) ^ 2 =
              Real.rpow ((R : ℝ) ^ 2) (1 + ε) := by
          rw [rpow_sq_one_add (R : ℝ) ε hRnonneg,
            rpow_two_add_two_mul_eq_sq_mul_rpow_sq (R : ℝ) ε hRpos]
        have htargetBase : ((R : ℝ) ^ 2) ≤ (x + 1 : ℝ) := by
          exact_mod_cast (hRsq.trans (Nat.le_succ x))
        have htargetPow :
            Real.rpow ((R : ℝ) ^ 2) (1 + ε) ≤
              Real.rpow (x + 1 : ℝ) (1 + ε) :=
          Real.rpow_le_rpow (by positivity) htargetBase (by linarith)
        have hendpointTarget :
            2 * shiftedMertensEnergy e ≤
              (C / 2) * Real.rpow (x + 1 : ℝ) (1 + ε) := by
          have hhalf : 2 * A ≤ Real.rpow (R : ℝ) ε / 2 := by linarith
          let T : ℝ := C * (R : ℝ) ^ 2 * Real.rpow (R : ℝ) ε
          have hT : 0 ≤ T := by
            dsimp [T]
            positivity
          have hmul := mul_le_mul_of_nonneg_right hhalf hT
          have hscale :
              2 * (A * (R : ℝ) ^ 2 * K) ≤
                (C / 2) *
                  ((R : ℝ) ^ 2 * (Real.rpow (R : ℝ) ε) ^ 2) := by
            dsimp [K, T] at hmul ⊢
            convert hmul using 1 <;> ring
          calc
            2 * shiftedMertensEnergy e ≤ 2 * (A * (R : ℝ) ^ 2 * K) := by
              linarith
            _ ≤ (C / 2) *
                  ((R : ℝ) ^ 2 * (Real.rpow (R : ℝ) ε) ^ 2) := hscale
            _ = (C / 2) * Real.rpow ((R : ℝ) ^ 2) (1 + ε) := by rw [hrpowSq]
            _ ≤ (C / 2) * Real.rpow (x + 1 : ℝ) (1 + ε) :=
              mul_le_mul_of_nonneg_left htargetPow (by linarith)
        have hgapNat : x - e ≤ 3 * R := by
          dsimp [e, squareRootEndpoint]
          have hsquare : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
          rw [hsquare] at hxltNext
          omega
        have hgap := RHLean.Analysis.norm_mertensSummatory_sub_le e x heLe
        have hgapR :
            ‖RHLean.Analysis.mertensSummatory x -
                RHLean.Analysis.mertensSummatory e‖ ≤ 3 * (R : ℝ) :=
          hgap.trans (by exact_mod_cast hgapNat)
        have hgapSq :
            ‖RHLean.Analysis.mertensSummatory x -
                RHLean.Analysis.mertensSummatory e‖ ^ 2 ≤
              9 * (R : ℝ) ^ 2 := by
          have hn : 0 ≤ ‖RHLean.Analysis.mertensSummatory x -
              RHLean.Analysis.mertensSummatory e‖ := norm_nonneg _
          have hR0real : 0 ≤ (R : ℝ) := by positivity
          nlinarith [sq_nonneg (‖RHLean.Analysis.mertensSummatory x -
            RHLean.Analysis.mertensSummatory e‖ - 3 * (R : ℝ))]
        have hbasePow :
            (x + 1 : ℝ) ≤ Real.rpow (x + 1 : ℝ) (1 + ε) := by
          have hbase : (1 : ℝ) ≤ (x + 1 : ℝ) := by positivity
          have hexp : (1 : ℝ) ≤ 1 + ε := by linarith
          simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le hbase hexp
        have hgapTarget :
            2 * ‖RHLean.Analysis.mertensSummatory x -
                RHLean.Analysis.mertensSummatory e‖ ^ 2 ≤
              (C / 2) * Real.rpow (x + 1 : ℝ) (1 + ε) := by
          have hRtoX : (R : ℝ) ^ 2 ≤ (x + 1 : ℝ) := htargetBase
          have hC2 : 18 ≤ C / 2 := by linarith
          have h18 : 18 * (R : ℝ) ^ 2 ≤ (C / 2) * (x + 1 : ℝ) := by
            calc
              18 * (R : ℝ) ^ 2 ≤ 18 * (x + 1 : ℝ) :=
                mul_le_mul_of_nonneg_left hRtoX (by norm_num)
              _ ≤ (C / 2) * (x + 1 : ℝ) :=
                mul_le_mul_of_nonneg_right hC2 (by positivity)
          calc
            2 * ‖RHLean.Analysis.mertensSummatory x -
                RHLean.Analysis.mertensSummatory e‖ ^ 2 ≤
                18 * (R : ℝ) ^ 2 := by nlinarith
            _ ≤ (C / 2) * (x + 1 : ℝ) := h18
            _ ≤ (C / 2) * Real.rpow (x + 1 : ℝ) (1 + ε) :=
              mul_le_mul_of_nonneg_left hbasePow (by linarith)
        calc
          shiftedMertensEnergy x =
              ‖(RHLean.Analysis.mertensSummatory e - 1) +
                (RHLean.Analysis.mertensSummatory x -
                  RHLean.Analysis.mertensSummatory e)‖ ^ 2 := by
            unfold shiftedMertensEnergy
            congr 1
            ring
          _ ≤ 2 * shiftedMertensEnergy e +
                2 * ‖RHLean.Analysis.mertensSummatory x -
                  RHLean.Analysis.mertensSummatory e‖ ^ 2 :=
            shifted_norm_sq_add_le_two _ _
          _ ≤ (C / 2) * Real.rpow (x + 1 : ℝ) (1 + ε) +
                (C / 2) * Real.rpow (x + 1 : ℝ) (1 + ε) :=
            add_le_add hendpointTarget hgapTarget
          _ = C * Real.rpow (x + 1 : ℝ) (1 + ε) := by ring

/-- The fixed endpoint amplification theorem therefore implies the repository's
standard complex Mertens energy criterion. -/
theorem mertensEnergyBounded_of_squareRootEndpointAmplification
    (hamp : SquareRootMertensEndpointAmplificationStatement) :
    RHLean.Analysis.MertensEnergyBoundedStatement := by
  intro ε hε
  rcases shiftedMertensEnergyBounded_of_squareRootEndpointAmplification
      hamp ε hε with ⟨C, hC, hshift⟩
  refine ⟨2 * C + 2, by positivity, ?_⟩
  intro x
  have hdecomp :
      RHLean.Analysis.mertensSummatory x =
        (RHLean.Analysis.mertensSummatory x - 1) + 1 := by ring
  have hsq := shifted_norm_sq_add_le_two
    (RHLean.Analysis.mertensSummatory x - 1) (1 : ℂ)
  rw [← hdecomp] at hsq
  have hbasePow :
      1 ≤ Real.rpow (x + 1 : ℝ) (1 + ε) := by
    have hbase : (1 : ℝ) ≤ (x + 1 : ℝ) := by positivity
    have hexp : 0 ≤ 1 + ε := by linarith
    exact Real.one_le_rpow hbase hexp
  calc
    ‖RHLean.Analysis.mertensSummatory x‖ ^ 2 ≤
        2 * shiftedMertensEnergy x + 2 := by
      simpa [shiftedMertensEnergy] using hsq
    _ ≤ 2 * (C * Real.rpow (x + 1 : ℝ) (1 + ε)) + 2 := by
      linarith [hshift x]
    _ ≤ (2 * C + 2) * Real.rpow (x + 1 : ℝ) (1 + ε) := by
      nlinarith

end RHLean.Proof

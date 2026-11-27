import RHLean.Analysis.AlpogeNativeSignedWidthPayment
import RHLean.Geometry.NativeThetaFock

/-! The rank-one finite test at nominal source widths. At p one inertia
representative serves every site and every exponent. The scalar is a product
of wheel gcds on actual downstream integers. Its multiplicity is bounded
above by the inertia-averaged positive cuts. The integral coefficient and
the independent Fock norm below refer to the same divided-power jet. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open RHLean.Geometry.NativeTheta.Fock

namespace RHLean.Analysis.AlpogeThin.RankOne

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
private abbrev G (H : Type*) := AlpogeNativeE0 × H

/-- Quotient slots after the target width and before the source width divided
by the actual prime power. Rounding the lower endpoint up gives the
one-sided depth needed by the inverse-ratio estimate. -/
def slots (y v : ℝ) (n : ℕ) : Finset ℕ := Finset.Ioc ⌈v⌉₊ ⌊y/(n:ℝ)⌋₊

theorem slots_le (y v : ℝ) (n : ℕ) (hy : 0 ≤ y) :
    ((slots y v n).card:ℝ) ≤ alpogeASKPos (y/(n:ℝ)) v := by
  rw [slots, Nat.card_Ioc]
  by_cases h : ⌈v⌉₊ ≤ ⌊y/(n:ℝ)⌋₊
  · rw [Nat.cast_sub h]
    exact (sub_le_sub (Nat.floor_le (div_nonneg hy (Nat.cast_nonneg _))) (Nat.le_ceil v)).trans
      (le_max_left _ _)
  · rw [Nat.sub_eq_zero_of_le (le_of_not_ge h), Nat.cast_zero]
    exact le_max_right _ _

/-- On an actual multiple, admitting p to any earlier coprime wheel
inserts exactly the single gcd factor used in the test below. -/
theorem gcd_admission (W p n : ℕ) (hc : W.Coprime p) (hn : p ∣ n) :
    n.gcd (W*p) = n.gcd W * p := by
  rw [Nat.Coprime.gcd_mul n hc, Nat.gcd_eq_right hn]

private def target (σ g : G H) : G H := σ + alpogeNativePartner (0 : H) g

private def places (I : AddSubgroup (G H)) := Finset.univ.filter (fun u => u ∈ I)

/-- One common inertia representative for all nominal sites and all
exponents at p. Split or ineligible colours have zero contribution. -/
def chartMass (w : G H → ℝ) (F : ℕ → G H) (N p : ℕ) (u : G H) : ℝ :=
  ∑ σ ∈ alpogeNativePhiSet H, ∑ e ∈ Finset.Icc 1 N,
    let g := e • F p + u
    if alpogeNativeInPhi g then 0 else alpogeASKPos (w σ / ((p^e:ℕ):ℝ)) (w (target σ g))

def forced (I : ℕ → AddSubgroup (G H)) (F : ℕ → G H) (w : G H → ℝ) (N p : ℕ) : ℝ :=
  (∑ u ∈ places (I p), chartMass w F N p u) / ((places (I p)).card:ℝ)

/-- Each slot is a concrete downstream integer k p^e. The successive
wheel factors are multiplied, including repeated prime-power layers. -/
def chartRead (w : G H → ℝ) (F : ℕ → G H) (N p : ℕ) (u : G H) : ℕ :=
  ∏ σ ∈ alpogeNativePhiSet H, ∏ e ∈ Finset.Icc 1 N,
    let g := e • F p + u
    if alpogeNativeInPhi g then 1 else
      ∏ k ∈ slots (w σ) (w (target σ g)) (p^e), (k*p^e).gcd p

def chartDepth (w : G H → ℝ) (F : ℕ → G H) (N p : ℕ) (u : G H) : ℕ :=
  ∑ σ ∈ alpogeNativePhiSet H, ∑ e ∈ Finset.Icc 1 N,
    let g := e • F p + u
    if alpogeNativeInPhi g then 0 else (slots (w σ) (w (target σ g)) (p^e)).card

theorem chartRead_eq (w : G H → ℝ) (F : ℕ → G H) (N p : ℕ) (u : G H) :
    chartRead w F N p u = p^(chartDepth w F N p u) := by
  classical
  unfold chartRead chartDepth
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun e he => ?_
  dsimp only
  split_ifs with hg
  · simp
  · have h (k : ℕ) : (k*p^e).gcd p = p :=
      Nat.gcd_eq_right ((dvd_pow_self p (by have := (Finset.mem_Icc.mp he).1; omega : e ≠ 0)).trans
        (dvd_mul_left _ _))
    simp [h]

theorem chartDepth_le (w : G H → ℝ) (F : ℕ → G H) (N p : ℕ) (u : G H)
    (hw : ∀ σ ∈ alpogeNativePhiSet H, 0 ≤ w σ) :
    (chartDepth w F N p u:ℝ) ≤ chartMass w F N p u := by
  classical
  unfold chartDepth chartMass
  push_cast
  refine Finset.sum_le_sum fun σ hσ => Finset.sum_le_sum fun e _ => ?_
  dsimp only
  split_ifs <;> simp only [Nat.cast_zero, le_refl]
  exact slots_le _ _ _ (hw σ hσ)

/-- A place may choose its test. The same inertia chart works for every
summand at that prime, including ramified primes. -/
theorem exists_chart (I : ℕ → AddSubgroup (G H)) (F : ℕ → G H) (w : G H → ℝ) (N p : ℕ)
    (hw : ∀ σ ∈ alpogeNativePhiSet H, 0 ≤ w σ) :
    ∃ u ∈ I p, (chartDepth w F N p u:ℝ) ≤ forced I F w N p := by
  classical
  let S := places (I p)
  have hs : S.Nonempty := ⟨0, by simp [S, places]⟩
  obtain ⟨u, hu, hmin⟩ := S.exists_min_image (chartMass w F N p) hs
  refine ⟨u, (Finset.mem_filter.mp hu).2, (chartDepth_le w F N p u hw).trans ?_⟩
  apply (le_div_iff₀ (show 0 < (S.card:ℝ) by exact_mod_cast hs.card_pos)).2
  calc
    _ = ∑ _v ∈ S, chartMass w F N p u := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ _ := Finset.sum_le_sum fun v hv => hmin v hv

/-- The integral top-derivative test on the divided-power lattice reads
the same scalar that occurs in the squared archimedean Fock norm. -/
def dividedJet {S : Type*} (α : S →₀ ℕ) (c : ℝ) : MvPolynomial S ℝ :=
  MvPolynomial.monomial α (c/(multiFactorial α:ℝ))

theorem jet_read_norm {S : Type*} (α : S →₀ ℕ) (c scale : ℝ) :
    (multiFactorial α:ℝ) * (dividedJet α c).coeff α = c ∧
    fockNormSq (scale • dividedJet α c) = (scale*c)^2/(multiFactorial α:ℝ) := by
  classical
  have h : (multiFactorial α:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (multiFactorial_pos α).ne'
  constructor
  · simp [dividedJet, field, h]
  · rw [dividedJet, MvPolynomial.smul_monomial, fockNormSq_monomial]
    simp only [smul_eq_mul, Real.norm_eq_abs, sq_abs]
    field [h]

/-- A single integer, obtained from all selected wheel reads, supplies
every finite valuation and the norm of the same divided-power jet. -/
theorem common_jet (I : ℕ → AddSubgroup (G H)) (F : ℕ → G H) (w : G H → ℝ) (N : ℕ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hw : ∀ σ ∈ alpogeNativePhiSet H, 0 ≤ w σ)
    (α : G H →₀ ℕ) (scale : ℝ) (hs : 0 < scale) :
    ∃ u : ℕ → G H, (∀ p, u p ∈ I p) ∧
      let A := ∏ p ∈ P, chartRead w F N p (u p)
      0 < A ∧ (∀ p ∈ P, (A.factorization p:ℝ) ≤ forced I F w N p) ∧
      (multiFactorial α:ℝ) * (dividedJet α A).coeff α = A ∧
      Real.log (fockNormSq (scale • dividedJet α A)) ≤
        -Real.log (multiFactorial α) + 2*Real.log scale +
          ∑ p ∈ P, 2*forced I F w N p*Real.log p := by
  classical
  choose u hu hdepth using fun p => exists_chart I F w N p hw
  refine ⟨u, hu, ?_⟩
  dsimp only
  let d := fun p => chartDepth w F N p (u p)
  let A := ∏ p ∈ P, p^(d p)
  simp_rw [chartRead_eq]
  have hp p (h : p ∈ P) : 0 < p^(d p) := pow_pos (hP p h).pos _
  have ha : 0 < A := Finset.prod_pos hp
  have ha' : 0 < (A:ℝ) := by exact_mod_cast ha
  have hfac (p) (h : p ∈ P) : A.factorization p = d p := by
    change (∏ i ∈ P, i^(d i)).factorization p = d p
    rw [Nat.factorization_prod_apply (fun i hi => (hp i hi).ne')]
    rw [Finset.sum_eq_single_of_mem p h]
    · exact Nat.factorization_pow_self (hP p h)
    · intro i hi hne
      simp [Nat.factorization_pow, Nat.Prime.factorization (hP i hi), Finsupp.single_eq_of_ne hne.symm]
  refine ⟨ha, fun p h => (by rw [show (∏ i ∈ P, i ^ chartDepth w F N i (u i)) = A from rfl, hfac p h]; exact hdepth p),
    (jet_read_norm α A scale).1, ?_⟩
  change Real.log (fockNormSq (scale • dividedJet α A)) ≤ _
  rw [(jet_read_norm α A scale).2, Real.log_div (pow_pos (mul_pos hs ha') _).ne'
    (Nat.cast_ne_zero.mpr (multiFactorial_pos α).ne'), Real.log_pow, Real.log_mul hs.ne' ha'.ne']
  have logA : Real.log (A:ℝ) = ∑ p ∈ P, (d p:ℝ)*Real.log p := by
    simp only [A, Nat.cast_prod, Nat.cast_pow]
    rw [Real.log_prod (fun i hi => (pow_pos (show 0 < (i:ℝ) by exact_mod_cast (hP i hi).pos) _).ne')]
    simp only [Real.log_pow]
  rw [logA]
  have cost : 2*(∑ p ∈ P, (d p:ℝ)*Real.log p) ≤ ∑ p ∈ P, 2*forced I F w N p*Real.log p := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p _ => by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hdepth p) (by norm_num))
        (Real.log_natCast_nonneg p)
  linarith only [cost]

end RHLean.Analysis.AlpogeThin.RankOne

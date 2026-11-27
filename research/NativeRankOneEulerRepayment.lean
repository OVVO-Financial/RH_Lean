import RHLean.Analysis.AlpogeNativeThickFreezing
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
  split_ifs
  · exact le_rfl
  · simpa only [Nat.cast_pow] using slots_le (w σ) (w (target σ (e • F p+u))) (p^e) (hw σ hσ)

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
  · simp [dividedJet, field]
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
    rw [Real.log_prod (s := P) (f := fun i : ℕ => (i:ℝ)^(d i))
      (fun i hi => (pow_pos (show 0 < (i:ℝ) by exact_mod_cast (hP i hi).pos) _).ne')]
    simp only [Real.log_pow]
  rw [logA]
  have cost : 2*(∑ p ∈ P, (d p:ℝ)*Real.log p) ≤ ∑ p ∈ P, 2*forced I F w N p*Real.log p := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p _ => by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hdepth p) (by norm_num))
        (Real.log_natCast_nonneg p)
  norm_num only [Nat.cast_ofNat]
  linarith only [cost]

omit [DecidableEq H] in
/-- Changing an inertia representative is exactly translation in the unaltered
colour kernel. The coefficient 2 is the original two-bit character factor. -/
private theorem coset_sum (I : AddSubgroup (G H)) (a : G H) (f : G H → ℝ) :
    (∑ g : G H, if g-a ∈ I then f g else 0) = ∑ u ∈ places I, f (a+u) := by
  classical
  let E := Equiv.addLeft a
  have h := Equiv.sum_comp E (fun g : G H => if g-a ∈ I then f g else 0)
  simpa [E, places, Finset.sum_filter] using h.symm

private theorem site_census (I : ℕ → AddSubgroup (G H)) (F : ℕ → G H) (w : G H → ℝ)
    (N : ℕ) (σ : G H)
    (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 < w (σ+ρ))
    (hN : ∀ ρ, alpogeNativeInPhi ρ → w σ / w (σ+ρ) ≤ N) :
    (alpogeNativeFullKernelASK I F N (w σ) 0 (fun ρ => w (σ+ρ))).re =
      ∑ p ∈ (Finset.range (N+1)).filter Nat.Prime, ∑ j ∈ Finset.Icc 1 N,
        Real.log p * (2/((places (I p)).card:ℝ)) *
          ∑ u ∈ places (I p), if alpogeNativeInPhi (j • F p+u) then 0 else
            alpogeASKPos (w σ/((p^j:ℕ):ℝ)) (w (target σ (j • F p+u))) := by
  classical
  rw [alpogeNativeFullKernelASK_eq_primePowerCensus I F N (w σ) 0 _ hw hN]
  unfold alpogeNativePrimePowerCensusASK
  simp only [Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun j _ => ?_
  let c : ℝ := 2/((places (I p)).card:ℝ)
  let f := fun g : G H => alpogeASKPos (w σ/((p^j:ℕ):ℝ)) (w (target σ g))
  have term (g : G H) :
      (if g-j • F p ∈ I p then (2:ℂ)/((places (I p)).card:ℂ) else 0) *
          alpogeNativeSiteCut (w σ) (fun ρ => w (σ+ρ)) 0 (p^j) g =
        ((if g-j • F p ∈ I p then c*f g else 0 : ℝ):ℂ) := by
    split_ifs <;> simp [c, f, alpogeNativeSiteCut, alpogeASKPos, target]
  change ((Real.log p:ℂ) * ∑ g ∈ Finset.univ.filter (fun g : G H => ¬alpogeNativeInPhi g),
    (if g-j • F p ∈ I p then (2:ℂ)/((places (I p)).card:ℂ) else 0) * _).re = _
  simp_rw [term]
  rw [← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [mul_assoc]
  apply congrArg (Real.log p * ·)
  change _ = c*∑ u ∈ places (I p), if alpogeNativeInPhi (j • F p+u) then 0 else f (j • F p+u)
  rw [← coset_sum (I p) (j • F p) (fun g => if alpogeNativeInPhi g then 0 else f g),
    Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : alpogeNativeInPhi g <;> by_cases hI : g-j • F p ∈ I p <;> simp [hg, hI]

/-- The rank-one positive term is the original full ASK summed at nominal
site widths. The cutoff, every proper power and each ramified inertia
multiplicity agree before taking a single inequality. -/
theorem forced_sum_eq_nominal_ask (I : ℕ → AddSubgroup (G H)) (F : ℕ → G H)
    (w : G H → ℝ) (N : ℕ)
    (hw : ∀ σ ∈ alpogeNativePhiSet H, ∀ ρ, alpogeNativeInPhi ρ → 0 < w (σ+ρ))
    (hN : ∀ σ ∈ alpogeNativePhiSet H, ∀ ρ, alpogeNativeInPhi ρ → w σ / w (σ+ρ) ≤ N) :
    (∑ p ∈ (Finset.range (N+1)).filter Nat.Prime, 2*forced I F w N p * Real.log p) =
      ∑ σ ∈ alpogeNativePhiSet H, (alpogeNativeFullKernelASK I F N (w σ) 0 (fun ρ => w (σ+ρ))).re := by
  classical
  symm
  rw [Finset.sum_congr rfl (fun σ hσ => site_census I F w N σ (hw σ hσ) (hN σ hσ)), Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  let Z := fun (σ : G H) (e : ℕ) (u : G H) => if alpogeNativeInPhi (e • F p+u) then 0 else
    alpogeASKPos (w σ/((p^e:ℕ):ℝ)) (w (target σ (e • F p+u)))
  let S := places (I p)
  have reorder : (∑ σ ∈ alpogeNativePhiSet H, ∑ e ∈ Finset.Icc 1 N, ∑ u ∈ S, Z σ e u) =
      ∑ u ∈ S, ∑ σ ∈ alpogeNativePhiSet H, ∑ e ∈ Finset.Icc 1 N, Z σ e u := by
    calc
      _ = ∑ σ ∈ alpogeNativePhiSet H, ∑ u ∈ S, ∑ e ∈ Finset.Icc 1 N, Z σ e u :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  simp_rw [← Finset.mul_sum]
  change (Real.log p*(2/(S.card:ℝ)))*(∑ σ ∈ alpogeNativePhiSet H, ∑ e ∈ Finset.Icc 1 N, ∑ u ∈ S, Z σ e u) =
    2*((∑ u ∈ S, ∑ σ ∈ alpogeNativePhiSet H, ∑ e ∈ Finset.Icc 1 N, Z σ e u)/(S.card:ℝ))*Real.log p
  rw [reorder]
  ring

/-- In the ordinary interval metric a coordinate indicator has squared norm
w. At a nominal integral order m ≤ w, the dilation of the untwisted jet has
squared norm at least one: this metric cannot supply the negative jet term
of Separation without independently justified metric transport. -/
theorem interval_jet_norm_ge_one (w : ℝ) (m : ℕ) (hw : (m:ℝ) ≤ w) :
    1 ≤ fockNormSq ((Real.sqrt w ^ m) • dividedJet (Finsupp.single () m) 1) := by
  rw [(jet_read_norm (Finsupp.single () m) 1 (Real.sqrt w ^ m)).2, multiFactorial_single, mul_one,
    ← pow_mul, Nat.mul_comm m 2, pow_mul, Real.sq_sqrt ((Nat.cast_nonneg m).trans hw)]
  apply (one_le_div (by exact_mod_cast m.factorial_pos)).2
  exact (show (m.factorial:ℝ) ≤ (m:ℝ)^m by exact_mod_cast Nat.factorial_le_pow m).trans
    (pow_le_pow_left₀ (Nat.cast_nonneg m) hw _)

/-- Scaling by the nonzero common Euler reading preserves this line. A
primitive test on it is fixed by its rank-one projector in any compatible
inner product. On the unit Fock metric its squared norm forces the exact
finite denominator when multiplied by a class factor h and a clearing d. -/
theorem primitive_line_denominator {S : Type*} (α : S →₀ ℕ) (A : ℕ) (hA : 0 < A) (h d : ℕ) :
    Submodule.span ℝ {dividedJet α A} = Submodule.span ℝ {dividedJet α 1} ∧
    ((∃ z : ℕ, ((d*h:ℕ):ℝ) * fockNormSq (dividedJet α 1) = z) ↔ multiFactorial α ∣ d*h) := by
  classical
  have hz : (multiFactorial α:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (multiFactorial_pos α).ne'
  have scaled : dividedJet α A = (A:ℝ) • dividedJet α 1 := by
    simp [dividedJet, MvPolynomial.smul_monomial, div_eq_mul_inv]
  refine ⟨scaled ▸ Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr
    (show (A:ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hA.ne')) _, ?_⟩
  have norm : fockNormSq (dividedJet α 1) = 1/(multiFactorial α:ℝ) := by
    simpa using (jet_read_norm α 1 1).2
  rw [norm, mul_one_div]
  constructor
  · rintro ⟨z, h⟩
    refine ⟨z, ?_⟩
    have heq := (div_eq_iff hz).1 h
    exact_mod_cast heq.trans (mul_comm _ _)
  · rintro ⟨z, h⟩
    refine ⟨z, (div_eq_iff hz).2 ?_⟩
    exact_mod_cast h.trans (Nat.mul_comm _ _)

/-- At the first admissible integer order ceil(w), the raw interval metric
has squared norm at least one half, even though its unit-coordinate jet
has squared norm 1/(ceil(w))!. -/
theorem nominal_ceil_norm_ge_half (w : ℝ) (hw : 1 ≤ w) :
    1/2 ≤ fockNormSq ((Real.sqrt w ^ ⌈w⌉₊) • dividedJet (Finsupp.single () ⌈w⌉₊) 1) := by
  have hw0 : 0 ≤ w := zero_le_one.trans hw
  have hceil := Nat.ceil_lt_add_one hw0
  rw [(jet_read_norm _ 1 _).2, multiFactorial_single, mul_one, ← pow_mul, Nat.mul_comm _ 2,
    pow_mul, Real.sq_sqrt hw0]
  cases hm : ⌈w⌉₊ with
  | zero => norm_num
  | succ k =>
    rw [hm, Nat.cast_succ] at hceil
    have hk : (k:ℝ) ≤ w := by linarith
    have hf : (k.factorial:ℝ) ≤ w^k := (show (k.factorial:ℝ) ≤ (k:ℝ)^k by
      exact_mod_cast Nat.factorial_le_pow k).trans (pow_le_pow_left₀ (Nat.cast_nonneg k) hk _)
    apply (le_div_iff₀ (by exact_mod_cast (k+1).factorial_pos : 0 < ((k+1).factorial:ℝ))).2
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one, pow_succ]
    nlinarith only [mul_le_mul (show (k:ℝ)+1 ≤ 2*w by linarith) hf (Nat.cast_nonneg _)
      (by linarith : 0 ≤ 2*w)]

/-- Attach the common test to the full native nominal ASK. The metric
dilation here uses the L2 length of each nominal interval indicator. -/
theorem nominal_jet (I : ℕ → AddSubgroup (G H)) (F : ℕ → G H) (w : G H → ℝ) (N : ℕ)
    (α : G H →₀ ℕ) (hα : α.support ⊆ alpogeNativePhiSet H)
    (hpos : ∀ σ ∈ alpogeNativePhiSet H, 0 < w σ)
    (hw : ∀ σ ∈ alpogeNativePhiSet H, ∀ ρ, alpogeNativeInPhi ρ → 0 < w (σ+ρ))
    (hN : ∀ σ ∈ alpogeNativePhiSet H, ∀ ρ, alpogeNativeInPhi ρ → w σ / w (σ+ρ) ≤ N) :
    let P := (Finset.range (N+1)).filter Nat.Prime
    let scale := α.prod (fun σ m => Real.sqrt (w σ) ^ m)
    ∃ u : ℕ → G H, (∀ p, u p ∈ I p) ∧
      let A := ∏ p ∈ P, chartRead w F N p (u p)
      0 < A ∧ (∀ p ∈ P, (A.factorization p:ℝ) ≤ forced I F w N p) ∧
      (multiFactorial α:ℝ) * (dividedJet α A).coeff α = A ∧
      Real.log (fockNormSq (scale • dividedJet α A)) ≤
        -Real.log (multiFactorial α) + 2*Real.log scale +
          ∑ σ ∈ alpogeNativePhiSet H, (alpogeNativeFullKernelASK I F N (w σ) 0 (fun ρ => w (σ+ρ))).re := by
  classical
  dsimp only
  rw [← forced_sum_eq_nominal_ask I F w N hw hN]
  exact common_jet I F w N _ (fun _ hp => (Finset.mem_filter.mp hp).2)
    (fun σ hσ => (hpos σ hσ).le) α _ (Finset.prod_pos fun σ hσ =>
      pow_pos (Real.sqrt_pos.2 (hpos σ (hα hσ))) _)

/-- Take the first admissible order at each positive site of the actual
translated thick/thin dyadic host. The unmodified ledger cutoff
ceil(Amax/beta) bounds every nominal ratio. -/
theorem dyadic_nominal_jet (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (T2 : Finset (AlpogeNativeDyadicH e)) (t : AlpogeNativeDyadicH e)
    (a Amax x x₁ : ℝ) (ha : 0 < a) (hamax : a ≤ Amax) (hx : 1 ≤ x) (hx₁ : x ≤ x₁) :
    let D := alpogeNativeHostData e q d
    let β := a/x₁
    let w := alpogeNativeFreezeThick T2 t (a/x) (fun _ => β)
    let N := ⌈Amax/β⌉₊
    let α := Finsupp.equivFunOnFinite.symm (fun σ => if σ ∈ alpogeNativePhiSet (AlpogeNativeDyadicH e)
      then ⌈w σ⌉₊ else 0)
    let scale := α.prod (fun σ m => Real.sqrt (w σ)^m)
    let P := (Finset.range (N+1)).filter Nat.Prime
    ∃ u : ℕ → G (AlpogeNativeDyadicH e), (∀ p, u p ∈ D.inertia p) ∧
      let A := ∏ p ∈ P, chartRead w D.frob N p (u p)
      0 < A ∧ (∀ p ∈ P, (A.factorization p:ℝ) ≤ forced D.inertia D.frob w N p) ∧
      (multiFactorial α:ℝ) * (dividedJet α A).coeff α = A ∧
      Real.log (fockNormSq (scale • dividedJet α A)) ≤
        -Real.log (multiFactorial α) + 2*Real.log scale +
          ∑ σ ∈ alpogeNativePhiSet (AlpogeNativeDyadicH e),
            (alpogeNativeFullKernelASK D.inertia D.frob N (w σ) 0 (fun ρ => w (σ+ρ))).re := by
  classical
  let β := a/x₁
  let w := alpogeNativeFreezeThick T2 t (a/x) (fun _ => β)
  have hxx : 0 < x := zero_lt_one.trans_le hx
  have hβ : 0 < β := div_pos ha (hxx.trans_le hx₁)
  have hw (σ) : β ≤ w σ ∧ w σ ≤ Amax := by
    have hv : β ≤ a/x := div_le_div_of_nonneg_left ha.le hxx hx₁
    have hA := (div_le_self ha.le hx).trans hamax
    change β ≤ (if _ then a/x else β) ∧ (if _ then a/x else β) ≤ Amax
    split_ifs <;> exacts [⟨hv, hA⟩, ⟨le_rfl, hv.trans hA⟩]
  apply nominal_jet
  · intro σ hσ
    by_contra h
    exact Finsupp.mem_support_iff.mp hσ (by simp [h])
  · exact fun σ _ => hβ.trans_le (hw σ).1
  · exact fun σ _ ρ _ => hβ.trans_le (hw (σ+ρ)).1
  · intro σ _ ρ _
    exact (div_le_div₀ (ha.le.trans hamax) (hw σ).2 hβ (hw (σ+ρ)).1).trans (Nat.le_ceil _)

/-- The Riesz vector of the top derivative in the interval coordinates
with positive dilation s. It is fixed independently of the character. -/
def derivativeVector {S : Type*} (α : S →₀ ℕ) (s : ℝ) : MvPolynomial S ℂ :=
  MvPolynomial.monomial α (s:ℂ)⁻¹

def measuredTest {S : Type*} (α : S →₀ ℕ) (s : ℝ) (z : ℂ) : MvPolynomial S ℂ :=
  MvPolynomial.monomial α ((s:ℂ)*z/(multiFactorial α:ℂ))

theorem derivative_pair {S : Type*} (α : S →₀ ℕ) (s : ℝ) (z : ℂ) (hs : 0 < s) :
    fockInner (measuredTest α s z) (derivativeVector α s) = z ∧
      fockNormSq (derivativeVector α s) = (multiFactorial α:ℝ)/s^2 := by
  classical
  have hf : (multiFactorial α:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (multiFactorial_pos α).ne'
  have hsc : (s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  constructor
  · rw [measuredTest, derivativeVector, fockInner_monomial_right, MvPolynomial.coeff_monomial]
    simp only [ite_true, map_inv₀, Complex.conj_ofReal]
    field [hf, hsc]
  · rw [derivativeVector, fockNormSq_monomial, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs, inv_pow, div_eq_mul_inv]

/-- For a rational squared dilation the actual derivative norm has the
correct all-place orientation. W is rational at every embedding and W
times the squared norm is literally one, hence integral at every place. -/
theorem rational_derivative_height {S : Type*} (α : S →₀ ℕ) (r : ℚ) (hr : 0 < r) :
    let W := (r:ℂ)/(multiFactorial α:ℂ)
    W ≠ 0 ∧ (∀ σ : ℂ ≃+* ℂ, Real.log ‖σ W‖ = Real.log (r:ℝ) - Real.log (multiFactorial α)) ∧
      W * (fockNormSq (derivativeVector α (Real.sqrt (r:ℝ))):ℂ) = 1 := by
  dsimp only
  have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
  have hrc : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hf : (multiFactorial α:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (multiFactorial_pos α).ne'
  refine ⟨div_ne_zero hrc hf, ?_, ?_⟩
  · intro σ
    have hn : ‖(r:ℂ)‖ = (r:ℝ) := by
      rw [show (r:ℂ) = ((r:ℝ):ℂ) by norm_cast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr']
    rw [map_div₀, map_ratCast, map_natCast, norm_div, hn, Complex.norm_natCast,
      Real.log_div hr'.ne' (Nat.cast_ne_zero.mpr (multiFactorial_pos α).ne')]
  · rw [(derivative_pair α _ 0 (Real.sqrt_pos.2 hr')).2, Real.sq_sqrt hr'.le]
    push_cast
    field [hrc, hf]

/-- Unnormalised twisted class sum on the finite native inertia group. -/
def classTest {C : Type*} [AddCommGroup C] [Fintype C] (a : C → ℕ) (u : C) (χ : AddChar C ℂ) : ℂ :=
  ∑ v, χ v * (a (u+v):ℂ)

/-- The character numerator is integral and its size at every archimedean
embedding is bounded by the sum of the actual readings. -/
theorem classTest_bounds {C : Type*} [AddCommGroup C] [Fintype C] (a : C → ℕ)
    (u : C) (χ : AddChar C ℂ) : IsIntegral ℤ (classTest a u χ) ∧
      ∀ σ : ℂ ≃+* ℂ, ‖σ (classTest a u χ)‖ ≤ ∑ v, (a (u+v):ℝ) := by
  have hroot (v : C) : χ v ^ Fintype.card C = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
  constructor
  · change (∑ v, χ v * (a (u+v):ℂ)) ∈ integralClosure ℤ ℂ
    apply Subalgebra.sum_mem
    intro v _
    exact (IsIntegral.of_pow Fintype.card_pos (hroot v ▸ isIntegral_one)).mul (isIntegral_natCast _)
  · intro σ
    rw [classTest, map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
    have h : (σ (χ v))^Fintype.card C = 1 := by rw [← map_pow, hroot, map_one]
    rw [map_mul, map_natCast, norm_mul, Complex.norm_eq_one_of_pow_eq_one h Fintype.card_ne_zero,
      one_mul, Complex.norm_natCast]

/-- Complete character inversion and the ultrametric triangle inequality
select a twist after the place. The exact class divisor is retained. -/
theorem exists_classTest_ge {C L : Type*} [AddCommGroup C] [Fintype C]
    [NormedField L] [IsUltrametricDist L] (ι : ℂ →+* L) (a : C → ℕ) (u : C) :
    ∃ χ : AddChar C ℂ, ‖ι (a u:ℂ)‖ ≤ ‖ι (classTest a u χ / (Fintype.card C:ℂ))‖ := by
  classical
  have hc : (Fintype.card C:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have inv : (∑ χ : AddChar C ℂ, classTest a u χ / (Fintype.card C:ℂ)) = (a u:ℂ) := by
    simp only [classTest, ← Finset.sum_div]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, AddChar.sum_apply_eq_ite]
    simp [ite_mul, hc]
  obtain ⟨χ, _, hχ⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty Finset.univ_nonempty
    (fun χ : AddChar C ℂ => ι (classTest a u χ / (Fintype.card C:ℂ)))
  exact ⟨χ, by simpa only [← map_sum, inv] using hχ⟩

/-- Vary just the p-chart of the wheel jet, freezing every other reading.
The same global integer from common_jet is detected by an integral
character numerator on this genuine inertia group, at every place. -/
theorem common_jet_twisted_read {L : Type*} [NormedField L] [IsUltrametricDist L]
    (ι : ℂ →+* L) (I : ℕ → AddSubgroup (G H)) (F : ℕ → G H) (w : G H → ℝ)
    (N : ℕ) (P : Finset ℕ) (u : ℕ → G H) (hu : ∀ p, u p ∈ I p) (p : ℕ) (hp : p ∈ P)
    (α : G H →₀ ℕ) (scale : ℝ) (hs : 0 < scale) :
    let a := fun v : I p => (∏ q ∈ P.erase p, chartRead w F N q (u q)) * chartRead w F N p v
    let b := (⟨u p, hu p⟩ : I p)
    let A := ∏ q ∈ P, chartRead w F N q (u q)
    let T := derivativeVector α scale
    fockNormSq T = (multiFactorial α:ℝ)/scale^2 ∧ ∃ χ : AddChar (I p) ℂ,
      let z := fockInner (measuredTest α scale (classTest a b χ)) T
      IsIntegral ℤ z ∧ ‖ι (A:ℂ)‖ ≤ ‖ι (z / (Fintype.card (I p):ℂ))‖ ∧
      ∀ σ : ℂ ≃+* ℂ, ‖σ z‖ ≤ ∑ v, (a (b+v):ℝ) := by
  classical
  dsimp only
  let a := fun v : I p => (∏ q ∈ P.erase p, chartRead w F N q (u q)) * chartRead w F N p v
  let b : I p := ⟨u p, hu p⟩
  obtain ⟨χ, h⟩ := exists_classTest_ge ι a b
  have val : a b = ∏ q ∈ P, chartRead w F N q (u q) := Finset.prod_erase_mul P _ hp
  rw [val] at h
  refine ⟨(derivative_pair α scale 0 hs).2, χ, ?_⟩
  rw [(derivative_pair α scale (classTest a b χ) hs).1]
  exact ⟨(classTest_bounds a b χ).1, h, (classTest_bounds a b χ).2⟩

end RHLean.Analysis.AlpogeThin.RankOne

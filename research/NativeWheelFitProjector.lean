import «research.NativeRankOneEulerRepayment»

/-! The joint local comparison at the pinned Sernau fit-family cut.
A normalized inertia-character test is measured before choosing a direction.
On the native conductor its trivial character attains the largest p-adic
test norm at every profile, including both kinds of ramification. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open RHLean.Geometry.NativeTheta.Fock

namespace RHLean.Analysis.AlpogeThin.WheelFit

open RankOne
private abbrev G (e : ℕ) := AlpogeNativeE0 × AlpogeNativeDyadicH e

def channel {C : Type*} [AddCommGroup C] [Fintype C] (a : C → ℕ) (χ : AddChar C ℂ) : ℂ :=
  (∑ v, χ v * (a v:ℂ))/(Fintype.card C:ℂ)

private theorem channel_const {C : Type*} [AddCommGroup C] [Fintype C] (a : ℕ) (χ : AddChar C ℂ) :
    channel (fun _ => a) χ = if χ = 0 then (a:ℂ) else 0 := by
  classical
  rw [channel, ← Finset.sum_mul, AddChar.sum_eq_ite]
  split_ifs <;> simp [Fintype.card_ne_zero]

private theorem place_rat (p : ℕ) [Fact p.Prime] (ι : ℂ →+* PadicAlgCl p) (r : ℚ) :
    ‖ι (r:ℂ)‖ = (padicNorm p r:ℝ) := by
  rw [map_ratCast, ← Padic.eq_padicNorm, ← PadicAlgCl.norm_extends]
  norm_cast

private theorem root_unit {C : Type*} [AddCommGroup C] [Fintype C] {L : Type*} [NormedField L]
    (ι : ℂ →+* L) (χ : AddChar C ℂ) (v : C) : ‖ι (χ v)‖ = 1 := by
  apply IsOfFinOrder.norm_eq_one
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨Fintype.card C, Fintype.card_pos, ?_⟩
  rw [← map_pow, ← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one, map_one]

private theorem two_norm {C : Type*} [AddCommGroup C] [Fintype C] (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (ι : ℂ →+* PadicAlgCl p) (v : C) (k : ℕ) :
    (∀ χ : AddChar C ℂ, ‖ι ((1+χ v*(p:ℂ)^k)/2)‖ ≤ 1) ∧
      ‖ι ((1+(p:ℂ)^k)/2)‖ = 1 := by
  have hr2 := place_rat p ι 2
  have htwo : ‖ι 2‖ = 1 := by
    have hrat : padicNorm p (2:ℚ) = 1 := padicNorm.padicNorm_of_prime_of_ne (p := p) (q := 2) hp
    change ‖ι 2‖ = ((padicNorm p (2:ℚ):ℚ):ℝ) at hr2
    rwa [hrat, Rat.cast_one] at hr2
  have hp0 : ‖ι (p:ℂ)‖ < 1 := by
    have h := place_rat p ι (p:ℚ)
    simpa only [Rat.cast_natCast, ← Padic.eq_padicNorm, Rat.cast_natCast] using
      h.trans_lt (by exact_mod_cast padicNorm.padicNorm_p_lt_one_of_prime (p := p))
  constructor
  · intro χ
    rw [map_div₀, map_add, map_one, map_mul, map_pow, norm_div, htwo, div_one]
    refine (IsUltrametricDist.norm_add_le_max ..).trans (max_le (norm_one.le) ?_)
    rw [norm_mul, root_unit, one_mul, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hp0.le
  · cases k with
    | zero => norm_num
    | succ k =>
      rw [map_div₀, map_add, map_one, map_pow, norm_div, htwo, div_one]
      have hlt : ‖ι (p:ℂ) ^ (k+1)‖ < ‖(1 : PadicAlgCl p)‖ := by
        rw [norm_one, norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) hp0 (Nat.succ_ne_zero k)
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le, norm_one]

private theorem phi_depth (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime] (w : G e → ℝ)
    (u : G e) (hu : alpogeNativeInPhi u) (hF : alpogeNativeInPhi ((alpogeNativeHostData e q d).frob p)) :
    chartDepth w (alpogeNativeHostData e q d).frob N p u = 0 := by
  unfold chartDepth
  refine Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun i _ => ?_
  apply ite_eq_left
  change i • ((alpogeNativeHostData e q d).frob p).1.1 + u.1.1 = 0
  rw [show ((alpogeNativeHostData e q d).frob p).1.1 = 0 from hF, show u.1.1 = 0 from hu,
    nsmul_zero, add_zero]

private theorem phi_read (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime] (w : G e → ℝ)
    (u : G e) (hu : alpogeNativeInPhi u) (hF : alpogeNativeInPhi ((alpogeNativeHostData e q d).frob p)) :
    chartRead w (alpogeNativeHostData e q d).frob N p u = 1 := by
  rw [chartRead_eq, phi_depth e q d N p w u hu hF, pow_zero]

/-- The single trivial inertia character achieves the largest local test
norm for every width profile and every power of that character. -/
theorem dyadic_all_channels (e q d p N : ℕ) [Fact q.Prime] [Fact d.Prime] [Fact p.Prime]
    (hH : Formalism.FrobeniusOrbits.HostHyp q d) (ι : ℂ →+* PadicAlgCl p) (w : G e → ℝ) :
    let D := alpogeNativeHostData e q d
    let f := fun v : D.inertia p => chartRead w D.frob N p v
    (∀ χ, ‖ι (channel f χ)‖ ≤ ‖ι (f 0:ℂ)‖) ∧ ∀ j : ℕ,
      ‖ι (channel f (j • (0 : AddChar (D.inertia p) ℂ)))‖ = ‖ι (f 0:ℂ)‖ := by
  classical
  let D := alpogeNativeHostData e q d
  let f := fun v : D.inertia p => chartRead w D.frob N p v
  have constant (hc : ∀ v, f v = f 0) :
      (∀ χ, ‖ι (channel f χ)‖ ≤ ‖ι (f 0:ℂ)‖) ∧ ∀ j : ℕ,
        ‖ι (channel f (j • (0 : AddChar (D.inertia p) ℂ)))‖ = ‖ι (f 0:ℂ)‖ := by
    have heq (χ) : channel f χ = (if χ = 0 then (f 0:ℂ) else 0) :=
      (congrArg (fun a => channel a χ) (funext hc)).trans (channel_const _ _)
    constructor
    · intro χ
      rw [heq]
      split_ifs <;> simp
    · intro j
      simp [heq]
  by_cases hbad : p ∣ alpogeNativeHostN e q d
  · by_cases hd : p = d
    · subst p
      let v : D.inertia d := ⟨nativeDyadicDInvolution e,
        (nativeDyadicHostData_mem_inertia_d e q d hH _).2 (Or.inr rfl)⟩
      have hv : v ≠ 0 := fun he => nativeDyadicDInvolution_ne_zero e (congrArg Subtype.val he)
      have hu : (Finset.univ : Finset (D.inertia d)) = {0,v} := by
        ext i
        have hi := (nativeDyadicHostData_mem_inertia_d e q d hH i).1 i.property
        rcases hi with h | h
        · simp [show i = 0 from Subtype.ext h]
        · simp [show i = v from Subtype.ext h]
      have hf : f 0 = 1 := phi_read e q d N d w 0 rfl (nativeDyadicHostData_frob_d_inPhi e q d hH)
      have hc : Fintype.card (D.inertia d) = 2 := by
        change Finset.univ.card = 2
        rw [hu]
        simp [Ne.symm hv]
      let k := chartDepth w D.frob N d v
      have form (χ : AddChar (D.inertia d) ℂ) : channel f χ = (1+χ v*(d:ℂ)^k)/2 := by
        rw [channel, hu, hc, Finset.sum_insert (by simpa using Ne.symm hv), Finset.sum_singleton, hf]
        simp [f, chartRead_eq, k]
      have hd2 : d ≠ 2 := by have := hH.2.2.2.1; omega
      obtain ⟨all, best⟩ := two_norm d hd2 ι v k
      constructor
      · intro χ
        change ‖ι (channel f χ)‖ ≤ ‖ι (f 0:ℂ)‖
        simpa only [form, hf, Nat.cast_one, map_one, norm_one] using all χ
      · intro j
        change ‖ι (channel f (j • 0))‖ = ‖ι (f 0:ℂ)‖
        simpa [form, hf] using best
    · have hA : p ∣ 2^(e+2)*q := ((Fact.out : p.Prime).dvd_mul.mp hbad).resolve_right
        (fun h => hd ((Nat.prime_dvd_prime_iff_eq Fact.out hH.2.1).1 h))
      obtain ⟨hI,hF⟩ := nativeDyadicHostData_typeI e q d p hH Fact.out hA
      have one (v : D.inertia p) : f v = 1 := phi_read e q d N p w v (hI _ v.property) hF
      exact constant fun v => (one v).trans (one 0).symm
  · have ht : D.inertia p ≤ ⊥ := (nativeDyadicHostData_inertia_unramified e q d p Fact.out hbad).le
    exact constant fun v => congrArg f (Subtype.ext (AddSubgroup.mem_bot.mp (ht v.property)))

/-- The integral reading at the common zero representative, prior to
selection of the prime, place, direction or power. -/
def wheel (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime] (P : Finset ℕ) (w : G e → ℝ) : ℕ :=
  ∏ l ∈ P, chartRead w (alpogeNativeHostData e q d).frob N l 0

/-- Zero realizes the depth allowance simultaneously at every actual
prime. Conductor primes have zero depth at this representative, and
unramified inertia has only this representative. -/
theorem zero_depth_le (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime] [Fact p.Prime]
    (hH : Formalism.FrobeniusOrbits.HostHyp q d) (w : G e → ℝ)
    (hw : ∀ σ ∈ alpogeNativePhiSet (AlpogeNativeDyadicH e), 0 ≤ w σ) :
    let D := alpogeNativeHostData e q d
    (chartDepth w D.frob N p 0:ℝ) ≤ forced D.inertia D.frob w N p := by
  let D := alpogeNativeHostData e q d
  obtain ⟨v,hv,hcost⟩ := exists_chart D.inertia D.frob w N p hw
  by_cases hb : p ∣ alpogeNativeHostN e q d
  · have hf : alpogeNativeInPhi (D.frob p) := by
      by_cases h : p = d
      · subst p; exact nativeDyadicHostData_frob_d_inPhi e q d hH
      · exact (nativeDyadicHostData_typeI e q d p hH Fact.out
          (((Fact.out : p.Prime).dvd_mul.mp hb).resolve_right
            (fun k => h ((Nat.prime_dvd_prime_iff_eq Fact.out hH.2.1).1 k)))).2
    change (chartDepth w D.frob N p 0:ℝ) ≤ _
    rw [phi_depth e q d N p w 0 rfl hf, Nat.cast_zero]
    exact (Nat.cast_nonneg _).trans hcost
  · have hz : v = 0 := by
      change v ∈ (alpogeNativeHostData e q d).inertia p at hv
      rwa [nativeDyadicHostData_inertia_unramified e q d p Fact.out hb, AddSubgroup.mem_bot] at hv
    simpa only [hz] using hcost

/-- The same physical wheel integer has the exact prime depths used
by the common class character, before the all-nominal ASK sum. -/
theorem wheel_depths (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime] (P : Finset ℕ)
    (hp : ∀ p ∈ P, p.Prime) (w : G e → ℝ) (p : ℕ) (h : p ∈ P) :
    (wheel e q d N P w).factorization p = chartDepth w (alpogeNativeHostData e q d).frob N p 0 := by
  let D := alpogeNativeHostData e q d
  unfold wheel
  simp_rw [chartRead_eq]
  rw [Nat.factorization_prod_apply (fun l hl => (pow_pos (hp l hl).pos _).ne')]
  rw [Finset.sum_eq_single_of_mem p h]
  · exact Nat.factorization_pow_self (hp p h)
  · intro l hl hne
    simp [Nat.factorization_pow, Nat.Prime.factorization (hp l hl), Finsupp.single_eq_of_ne hne.symm]

/-- Vary only the admitted factor at the place p. Outside the cutoff its
class test is the transform of a constant. -/
def readAt (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime] (P : Finset ℕ) (w : G e → ℝ)
    (p : ℕ) (χ : AddChar ((alpogeNativeHostData e q d).inertia p) ℂ) : ℂ :=
  (wheel e q d N (P.erase p) w:ℂ) * channel (fun u =>
    if p ∈ P then chartRead w (alpogeNativeHostData e q d).frob N p u else 1) χ

theorem common_read (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime] [Fact p.Prime]
    (hH : Formalism.FrobeniusOrbits.HostHyp q d) (ι : ℂ →+* PadicAlgCl p) (P : Finset ℕ) (w : G e → ℝ) :
    (∀ χ, ‖ι (readAt e q d N P w p χ)‖ ≤ ‖ι (wheel e q d N P w:ℂ)‖) ∧
      ‖ι (readAt e q d N P w p 0)‖ = ‖ι (wheel e q d N P w:ℂ)‖ := by
  classical
  by_cases hp : p ∈ P
  · have fac : wheel e q d N P w = wheel e q d N (P.erase p) w *
        chartRead w (alpogeNativeHostData e q d).frob N p 0 := (Finset.prod_erase_mul P _ hp).symm
    obtain ⟨all,best⟩ := dyadic_all_channels e q d p N hH ι w
    simp only [readAt, ite_eq_left hp, fac, Nat.cast_mul, map_mul, norm_mul]
    exact ⟨fun χ => mul_le_mul_of_nonneg_left (all χ) (norm_nonneg _), congrArg (_ * ·) (by simpa using best 0)⟩
  · simp only [readAt, Finset.erase_eq_of_notMem hp, ite_eq_right hp, channel_const, Nat.cast_one]
    constructor
    · intro χ
      split_ifs <;> simp
    · simp

/-- The literal tested rank-one pairing. h is a separate class multiplier. -/
def tested {S : Type*} (α : S →₀ ℕ) (r : ℚ) (h : ℕ) (z z' : ℂ) : ℂ :=
  (h:ℂ) * fockInner (measuredTest α (Real.sqrt (r:ℝ)) z)
    (derivativeProjection α (measuredTest α (Real.sqrt (r:ℝ)) z'))

def payment {S : Type*} (α : S →₀ ℕ) (r : ℚ) (h A : ℕ) : ℚ :=
  ((h:ℚ)*r/(multiFactorial α:ℚ))*(A:ℚ)^2

private theorem tested_eq {S : Type*} (α : S →₀ ℕ) (r : ℚ) (hr : 0 ≤ r) (h : ℕ) (z z' : ℂ) :
    tested α r h z z' = ((((h:ℚ)*r/(multiFactorial α:ℚ)):ℚ):ℂ)*z*starRingEnd ℂ z' := by
  have sq : ((Real.sqrt (r:ℝ):ℂ))^2 = (r:ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by exact_mod_cast hr)]
    norm_cast
  rw [tested, projected_test_pair, sq]
  push_cast
  ring

/-- Every paired test is controlled by a rational number read from the
same wheel and metric. Trivial characters attain the bound at every
place, simultaneously for all directions. The second test is measured
through the conjugate embedding, as in the compact rank-one proof. -/
theorem exact_projector_price (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime] [Fact p.Prime]
    (hH : Formalism.FrobeniusOrbits.HostHyp q d) (ι : ℂ →+* PadicAlgCl p) (P : Finset ℕ) (w : G e → ℝ)
    {S : Type*} (α : S →₀ ℕ) (r : ℚ) (hr : 0 < r) (h : ℕ) :
    let z := readAt e q d N P w p
    let Q := payment α r h (wheel e q d N P w)
    (∀ χ ψ, ‖ι (tested α r h (z χ) (z ψ))‖ ≤ (padicNorm p Q:ℝ)) ∧
      ‖ι (tested α r h (z 0) (z 0))‖ = (padicNorm p Q:ℝ) := by
  let z := readAt e q d N P w p
  let A := wheel e q d N P w
  let c := (h:ℚ)*r/(multiFactorial α:ℚ)
  let κ := ι.comp (starRingEnd ℂ)
  have hc : ‖κ (A:ℂ)‖ = ‖ι (A:ℂ)‖ := by simp [κ]
  obtain ⟨first, f0⟩ := common_read e q d N p hH ι P w
  obtain ⟨second, s0⟩ := common_read e q d N p hH κ P w
  have entry χ ψ : ‖ι (tested α r h (z χ) (z ψ))‖ =
      ‖ι (c:ℂ)‖ * ‖ι (z χ)‖ * ‖κ (z ψ)‖ := by
    rw [tested_eq α r hr.le, map_mul, map_mul, norm_mul, norm_mul]
    rfl
  have price : (padicNorm p (payment α r h A):ℝ) = ‖ι (c:ℂ)‖ * ‖ι (A:ℂ)‖ * ‖ι (A:ℂ)‖ := by
    rw [← place_rat p ι]
    change ‖ι (((c*(A:ℚ)^2:ℚ):ℂ))‖ = _
    push_cast
    rw [map_mul, map_pow, norm_mul, norm_pow]
    ring
  change (∀ χ ψ, ‖ι (tested α r h (z χ) (z ψ))‖ ≤ _) ∧ ‖ι (tested α r h (z 0) (z 0))‖ = _
  rw [price]
  constructor
  · intro χ ψ
    rw [entry]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (first χ) (norm_nonneg _))
      ((second ψ).trans_eq hc) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · rw [entry]
    change _ * ‖ι (readAt e q d N P w p 0)‖ * ‖κ (readAt e q d N P w p 0)‖ = _
    rw [f0, s0, hc]

/-- Mixed tests in integral coordinates on a single family of distinct
measured Fock monomials. The full row space has class multiplier one. -/
def rowMatrix {S : Type*} {n : ℕ} (α : Fin n → S →₀ ℕ) (r : Fin n → ℚ)
    (z z' : Fin n → ℂ) (U V : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℂ :=
  U.map (Int.castRingHom ℂ) *
    Matrix.of (fun i j => fockInner (measuredTest (α i) (Real.sqrt (r i:ℝ)) (z i))
      (derivativeProjection (α j) (measuredTest (α j) (Real.sqrt (r j:ℝ)) (z' j)))) *
    (V.map (Int.castRingHom ℂ)).transpose

theorem row_det {S : Type*} {n : ℕ} (α : Fin n → S →₀ ℕ) (hi : Function.Injective α)
    (r : Fin n → ℚ) (z z' : Fin n → ℂ) (U V : Matrix (Fin n) (Fin n) ℤ) :
    (rowMatrix α r z z' U V).det =
      (U.det:ℂ)*(∏ i, tested (α i) (r i) 1 (z i) (z' i))*(V.det:ℂ) := by
  classical
  have diag : Matrix.of (fun i j => fockInner (measuredTest (α i) (Real.sqrt (r i:ℝ)) (z i))
      (derivativeProjection (α j) (measuredTest (α j) (Real.sqrt (r j:ℝ)) (z' j)))) =
      Matrix.diagonal (fun i => tested (α i) (r i) 1 (z i) (z' i)) := by
    ext i j
    by_cases h : i = j
    · subst j; simp [tested]
    · simp [derivativeProjection, measuredTest, fockInner_monomial_right,
        hi.ne h, hi.ne (Ne.symm h), Matrix.diagonal, h]
  rw [rowMatrix, diag, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
    ← RingHom.map_det, ← RingHom.map_det]
  rfl

/-- The full row determinant and every rank-one test share the same
attaining character. Integral changes of the two test tables are included,
and the determinant receives every direction's squared wheel reading. -/
theorem exact_row_price (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime] [Fact p.Prime]
    (hH : Formalism.FrobeniusOrbits.HostHyp q d) (ι : ℂ →+* PadicAlgCl p) (P : Finset ℕ)
    {S : Type*} {n : ℕ} (w : Fin n → G e → ℝ) (α : Fin n → S →₀ ℕ) (hi : Function.Injective α)
    (r : Fin n → ℚ) (hr : ∀ i, 0 < r i) :
    let z := fun (χ : Fin n → AddChar ((alpogeNativeHostData e q d).inertia p) ℂ) i =>
      readAt e q d N P (w i) p (χ i)
    let Q := fun i => payment (α i) (r i) 1 (wheel e q d N P (w i))
    (∀ χ ψ U V, ‖ι ((rowMatrix α r (z χ) (z ψ) U V).det)‖ ≤ ∏ i, (padicNorm p (Q i):ℝ)) ∧
      ‖ι ((rowMatrix α r (z 0) (z 0) 1 1).det)‖ = ∏ i, (padicNorm p (Q i):ℝ) := by
  classical
  let b i := exact_projector_price e q d N p hH ι P (w i) (α i) (r i) (hr i) 1
  dsimp only
  constructor
  · intro χ ψ U V
    rw [row_det α hi, map_mul, map_mul, map_intCast, map_intCast, norm_mul, norm_mul,
      map_prod, norm_prod]
    have hu := IsUltrametricDist.norm_intCast_le_one (PadicAlgCl p) U.det
    have hv := IsUltrametricDist.norm_intCast_le_one (PadicAlgCl p) V.det
    exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)) hv).trans
      ((mul_le_of_le_one_left (Finset.prod_nonneg fun _ _ => norm_nonneg _) hu).trans
      (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => (b i).1 (χ i) (ψ i)))
  · rw [row_det α hi, Matrix.det_one, Int.cast_one, one_mul, mul_one, map_prod, norm_prod]
    exact Finset.prod_congr rfl fun i _ => (b i).2

/-- This is the simultaneous fit comparison on the measured monomial
space. The class multiplier occurs only on the rank-one side. The full
determinant has the original dimension times the auxiliary rank in its
exponent. All character tests are quantified before the bound. -/
theorem joint_budget_iff (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime] [Fact p.Prime]
    (hH : Formalism.FrobeniusOrbits.HostHyp q d) (ι : ℂ →+* PadicAlgCl p) (P : Finset ℕ)
    {S : Type*} {n : ℕ} (w : Fin n → G e → ℝ) (α : Fin n → S →₀ ℕ) (hi : Function.Injective α)
    (r : Fin n → ℚ) (hr : ∀ i, 0 < r i) (h : Fin n → ℕ) (auxRank : ℕ) (β : ℝ) :
    let A := fun i => wheel e q d N P (w i)
    let z := fun i => readAt e q d N P (w i) p
    let rz := fun (χ : Fin n → AddChar ((alpogeNativeHostData e q d).inertia p) ℂ) i => z i (χ i)
    ((∀ i χ ψ, ‖ι (tested (α i) (r i) (h i) (z i χ) (z i ψ))‖ ≤ Real.exp β) ∧
      ∀ χ ψ U V, ‖ι ((rowMatrix α r (rz χ) (rz ψ) U V).det)‖ ≤ Real.exp ((n:ℝ)*(auxRank*β))) ↔
    ((∀ i, (padicNorm p (payment (α i) (r i) (h i) (A i)):ℝ) ≤ Real.exp β) ∧
      (∏ i, (padicNorm p (payment (α i) (r i) 1 (A i)):ℝ)) ≤ Real.exp ((n:ℝ)*(auxRank*β))) := by
  let one i := exact_projector_price e q d N p hH ι P (w i) (α i) (r i) (hr i) (h i)
  let row := exact_row_price e q d N p hH ι P w α hi r hr
  constructor
  · rintro ⟨hl,hd⟩
    exact ⟨fun i => (one i).2.symm.le.trans (hl i 0 0), row.2.symm.le.trans (hd 0 0 1 1)⟩
  · rintro ⟨hl,hd⟩
    exact ⟨fun i χ ψ => ((one i).1 χ ψ).trans (hl i), fun χ ψ U V => (row.1 χ ψ U V).trans hd⟩

/-- Least common clearing of the rational diagonal readings. Its
factorization is a single per-prime allowance, shared by all rows. -/
def rowLCM {n : ℕ} (Q : Fin n → ℚ) : ℕ := Finset.univ.lcm fun i => (Q i).den

theorem finite_row_budget (M : ℕ) (T : Finset ℕ) :
    (∑ p ∈ T, (M.factorization p:ℝ)*Real.log p) ≤ Real.log M := by
  classical
  rw [Real.log_nat_eq_sum_factorization]
  let S := M.factorization.support ∪ T
  rw [Finsupp.sum_of_support_subset _ (show M.factorization.support ⊆ S from Finset.subset_union_left)
    (fun (p t : ℕ) => (t:ℝ)*Real.log p) (by simp)]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
    (fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))

theorem rowLCM_local {n : ℕ} (Q : Fin n → ℚ) (i : Fin n) (p : ℕ) [Fact p.Prime] :
    (padicNorm p (Q i):ℝ) ≤ Real.exp (((rowLCM Q).factorization p:ℝ)*Real.log p) := by
  let M := rowLCM Q
  have hm : M ≠ 0 := Finset.lcm_ne_zero_iff.mpr fun i _ => (Q i).den_ne_zero
  obtain ⟨k,hk⟩ : (Q i).den ∣ M := Finset.dvd_lcm (Finset.mem_univ i)
  have hmul : (M:ℚ)*(Q i) = (((Q i).num*(k:ℤ):ℤ):ℚ) := by
    rw [hk, Nat.cast_mul, mul_right_comm, mul_comm ((Q i).den:ℚ), Rat.mul_den_eq_num]
    push_cast
    rfl
  have hb : padicNorm p (M:ℚ)*padicNorm p (Q i) ≤ 1 := by
    rw [← padicNorm.mul, hmul]
    exact padicNorm.of_int _
  have hp0 : 0 < (p:ℚ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have pnorm : padicNorm p (M:ℚ) = ((p:ℚ)^M.factorization p)⁻¹ := by
    rw [padicNorm.eq_zpow_of_nonzero (Nat.cast_ne_zero.mpr hm), Nat.factorization_def M Fact.out,
      padicValRat.of_nat, zpow_neg, zpow_natCast]
  rw [pnorm, inv_mul_eq_div] at hb
  have hq := (div_le_one (pow_pos hp0 _)).1 hb
  rw [Real.exp_nat_mul, Real.exp_log (show 0 < (p:ℝ) by exact_mod_cast hp0)]
  exact_mod_cast hq

/-- Construct a single summable allowance for the two native tested
spaces at every prime and embedding. Its independently measured total
is log(M). Comparison of this total or the sharper joint criterion with
the compact per-direction budget is the remaining economic question. -/
theorem common_native_allowance (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hH : Formalism.FrobeniusOrbits.HostHyp q d) (P : Finset ℕ)
    {S : Type*} {n : ℕ} (w : Fin n → G e → ℝ) (α : Fin n → S →₀ ℕ) (hi : Function.Injective α)
    (r : Fin n → ℚ) (hr : ∀ i, 0 < r i) (h : Fin n → ℕ) (auxRank : ℕ) (ha : 1 ≤ auxRank) :
    let A := fun i => wheel e q d N P (w i)
    let M := rowLCM fun i => payment (α i) (r i) 1 (A i)
    let γ := fun p => (M.factorization p:ℝ)*Real.log p
    (∀ T : Finset ℕ, ∑ p ∈ T, γ p ≤ Real.log M) ∧
      ∀ p : ℕ, ∀ [Fact p.Prime], ∀ ι : ℂ →+* PadicAlgCl p,
        let z := fun i => readAt e q d N P (w i) p
        let rz := fun (χ : Fin n → AddChar ((alpogeNativeHostData e q d).inertia p) ℂ) i => z i (χ i)
        (∀ i χ ψ, ‖ι (tested (α i) (r i) (h i) (z i χ) (z i ψ))‖ ≤ Real.exp (γ p)) ∧
        ∀ χ ψ U V, ‖ι ((rowMatrix α r (rz χ) (rz ψ) U V).det)‖ ≤
          Real.exp ((n:ℝ)*(auxRank*γ p)) := by
  let A := fun i => wheel e q d N P (w i)
  let Q := fun i => payment (α i) (r i) 1 (A i)
  let M := rowLCM Q
  let γ := fun p => (M.factorization p:ℝ)*Real.log p
  refine ⟨finite_row_budget M, ?_⟩
  intro p _ ι
  apply (joint_budget_iff e q d N p hH ι P w α hi r hr h auxRank (γ p)).2
  have localBound (i) : (padicNorm p (Q i):ℝ) ≤ Real.exp (γ p) := rowLCM_local Q i p
  constructor
  · intro i
    have eq : payment (α i) (r i) (h i) (A i) = (h i:ℚ)*Q i := by dsimp [Q, payment]; ring
    rw [eq, padicNorm.mul, Rat.cast_mul]
    have hunit : padicNorm p (h i:ℚ) ≤ 1 := by exact_mod_cast padicNorm.of_int (p := p) (h i:ℤ)
    exact (mul_le_of_le_one_left (by exact_mod_cast padicNorm.nonneg (p := p) (Q i))
      (by exact_mod_cast hunit)).trans (localBound i)
  · calc
      _ ≤ ∏ _i : Fin n, Real.exp (γ p) := Finset.prod_le_prod
        (fun i _ => by exact_mod_cast padicNorm.nonneg (p := p) (Q i)) fun i _ => localBound i
      _ = Real.exp ((n:ℝ)*γ p) := by simp [Real.exp_nat_mul]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hg : 0 ≤ γ p := mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
        exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hg (by exact_mod_cast ha))
          (Nat.cast_nonneg _)

/-- A distinct thick-site translate gives a distinct measured direction
when the two integral orders differ. This family realizes joint rank on
the actual modular-unit host and uses its original thick-site mask. -/
def singletonOrders {e : ℕ} (t : AlpogeNativeDyadicH e) (b l : ℝ) : G e →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun σ => if alpogeNativeInPhi σ then
    ⌈alpogeNativeFreezeThick {0} t b (fun _ => l) σ⌉₊ else 0)

theorem singletonOrders_injective {e : ℕ} (b l : ℝ) (h : ⌈b⌉₊ ≠ ⌈l⌉₊) :
    Function.Injective (fun t : AlpogeNativeDyadicH e => singletonOrders t b l) := by
  intro t u hu
  by_contra hne
  have eq := DFunLike.congr_fun hu (((0,1),t) : G e)
  simpa [singletonOrders, alpogeNativeInPhi, alpogeNativeFreezeThick, alpogeNativeThickPositiveSites,
    hne, Ne.symm hne, h] using eq

end RHLean.Analysis.AlpogeThin.WheelFit

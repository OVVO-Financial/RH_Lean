import «research.NativeAnchoredSlotMetric»
import RHLean.Analysis.NativePNTSelberg

/-! The original negative MAIN on the selected dyadic character host.
The character estimate uses the primitive twist of the selected pair. The other
input is the number of genuine thin widths. The original ASK is kept separate. -/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ArithmeticFunction.vonMangoldt
open Filter

namespace RHLean.Analysis.AlpogeThin.SlotProjector

set_option maxHeartbeats 2000000 in
private theorem canonical_class_bound (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    {ε Y Z x : ℝ} (pair : UpperTheory.Top.PairGood 1 ε Y Z q d) (hY : Y ≤ x) (hZ : x ≤ Z) :
    ‖alpogeNativeCanonicalHostEll (alpogeNativeRecMap e q d) (alpogeNativeChC (AlpogeNativeDyadicH e))‖
      ≤ 4*Real.log x := by
  let χ := alpogeNativeDirChar (H := AlpogeNativeDyadicH e) (alpogeNativeRecMap e q d)
    (nativeDyadicTwoBitCharacter e 0 1)
  let : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  have twist : nativeDyadicTwoBitCharacter e 0 1 = alpogeNativeChC (AlpogeNativeDyadicH e) := by
    simp [nativeDyadicTwoBitCharacter]
  rw [← twist]
  change ‖Formalism.HC.An.logDerivativeAtOne χ.primitiveCharacter‖ ≤ 4*Real.log x
  exact (pair.bounds (1 : DirichletCharacter ℂ 1) 0 1 (Or.inr (by decide))
    χ.conductor χ.primitiveCharacter (nativeDyadicTwoBitCharacter_induces e q d 0 1) x hY hZ).2

private theorem thin_sites_of_partner {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (T : Finset H) (u t : H) (a L : ℝ) (w : AlpogeNativeE0 × H → ℝ)
    (h : ∀ g ∈ (Finset.univ.filter fun g : AlpogeNativeE0 × H => ¬alpogeNativeInPhi g) \ alpogeNativeProjectionThickColours T u t,
      L ≤ a/w (alpogeNativePartner t g)) :
    ∀ ρ ∈ alpogeNativePhiSet H \ alpogeNativeThickPositiveSites T u, L ≤ a/w ρ := by
  classical
  intro ρ hρ
  let g := ρ - alpogeNativeTopPl t - alpogeNativeCconj H
  have read : alpogeNativePartner t g = ρ := by dsimp [alpogeNativePartner, g]; abel
  have hp := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hρ).1).2
  change ρ.1.1 = 0 at hp
  have hg : ¬alpogeNativeInPhi g := by
    change ¬ ρ.1.1 - 0 - (1:ZMod 2) = 0
    rw [hp]
    decide
  have off : g ∉ alpogeNativeProjectionThickColours T u t := fun ht =>
    (Finset.mem_sdiff.mp hρ).2 (read ▸ (alpogeNativeFreezing_partner_mem_iff T u t g).2 ht)
  simpa only [read] using h g (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hg⟩,off⟩)

private theorem half_thin_log {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (T : Finset H) (u : H) (a L : ℝ) (ha : 0 < a) (hL : 0 ≤ L)
    (w : AlpogeNativeE0 × H → ℝ)
    (hp : ∀ ρ ∈ alpogeNativePhiSet H, 0 < w ρ)
    (ht : ∀ ρ ∈ alpogeNativeThickPositiveSites T u, w ρ ≤ a)
    (hn : ∀ ρ ∈ alpogeNativePhiSet H \ alpogeNativeThickPositiveSites T u,
      Real.exp L ≤ a / w ρ) :
    L/2 ≤ Real.log a - (1/((alpogeNativePhiSet H).card:ℝ))*
      ∑ ρ ∈ alpogeNativePhiSet H, Real.log (w ρ) := by
  classical
  let P := alpogeNativePhiSet H
  let T' := alpogeNativeThickPositiveSites T u
  let f := fun ρ => Real.log a - Real.log (w ρ)
  have sub : T' ⊆ P := by
    intro ρ hρ
    obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp hρ
    simp [P, alpogeNativePhiSet, alpogeNativeInPhi]
  have hcard : (Fintype.card H) ≤ (P \ T').card := by
    rw [Finset.card_sdiff_of_subset sub, show P.card = 2*Fintype.card H from alpogeNativeProjectionPhi_card,
      show T'.card = T.card from alpogeNativeThickPositiveSites_card T u]
    have h := Finset.card_le_univ T
    omega
  have lower : ((P \ T').card:ℝ)*L ≤ ∑ ρ ∈ P \ T', f ρ := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro ρ hρ
    have h := Real.log_le_log (Real.exp_pos L) (hn ρ hρ)
    rwa [Real.log_exp, Real.log_div ha.ne' (hp ρ (Finset.mem_sdiff.mp hρ).1).ne'] at h
  have thick : 0 ≤ ∑ ρ ∈ T', f ρ := Finset.sum_nonneg fun ρ hρ =>
    sub_nonneg.mpr (Real.log_le_log (hp ρ (sub hρ)) (ht ρ hρ))
  have allSites : (Fintype.card H:ℝ)*L ≤ ∑ ρ ∈ P, f ρ := by
    rw [← Finset.sum_sdiff sub]
    linarith only [lower, thick, mul_le_mul_of_nonneg_right (show (Fintype.card H:ℝ) ≤ (P \ T').card by
      exact_mod_cast hcard) hL]
  have total : (∑ ρ ∈ P, f ρ) = (P.card:ℝ)*Real.log a - ∑ ρ ∈ P, Real.log (w ρ) := by
    simp only [f, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have c : (P.card:ℝ) = 2*(Fintype.card H:ℝ) := by exact_mod_cast (alpogeNativeProjectionPhi_card (H := H))
  have hH : 0 < (Fintype.card H:ℝ) := by exact_mod_cast Fintype.card_pos
  change L/2 ≤ Real.log a - (1/(P.card:ℝ))*_
  rw [total, c] at allSites
  rw [c]
  field_simp [hH.ne']
  linarith only [allSites]

/-- A row estimate on the actual class character and all the original widths.
It is uniform over the selected pairs and over the position of the window. -/
theorem signedMain_row (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
      {Y Z : ℝ} (_pair : UpperTheory.Top.PairGood 1 ε Y Z q d), Y ≤ x → x ≤ Z →
      ∀ (T : Finset (AlpogeNativeDyadicH e)) (u : AlpogeNativeDyadicH e) (a : ℝ)
        (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ), 0 < a →
        (∀ ρ ∈ alpogeNativePhiSet _, 0 < w ρ) →
        (∀ ρ ∈ alpogeNativeThickPositiveSites T u, w ρ ≤ a) →
        (∀ ρ ∈ alpogeNativePhiSet _ \ alpogeNativeThickPositiveSites T u, Real.exp (x^(ε/3))/3 ≤ a/w ρ) →
        a*(4*Real.log x+x^(ε/3)/4) ≤ (alpogeNativeMAIN
          (alpogeNativeCanonicalHostEll (alpogeNativeRecMap e q d)) a w).re := by
  have hr : 0 < ε/3 := by positivity
  filter_upwards [(isLittleO_log_rpow_atTop hr).bound (by norm_num : (0:ℝ) < 1/64),
    (tendsto_rpow_atTop hr).eventually_ge_atTop (8*Real.log 3+32), eventually_ge_atTop (1:ℝ)]
    with x hlog hbig hx
  rw [Real.norm_of_nonneg (Real.log_nonneg hx), Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hlog
  intro e q d _ _ Y Z pair hY hZ T u a w ha hp ht hn
  let ell := alpogeNativeCanonicalHostEll (H := AlpogeNativeDyadicH e) (alpogeNativeRecMap e q d)
  have hc := (abs_le.mp ((Complex.abs_re_le_norm _).trans (canonical_class_bound e q d pair hY hZ))).1
  have hl := half_thin_log T u a (x^(ε/3)-Real.log 3) ha
    (by linarith only [hbig, Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)]) w hp ht (by
      intro ρ hρ
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ) < 3)]
      exact hn ρ hρ)
  have scalar : 4*Real.log x+x^(ε/3)/4 ≤ Real.log a - 1 - Real.eulerMascheroniConstant +
      (ell (alpogeNativeChC _)).re - (1/((alpogeNativePhiSet (AlpogeNativeDyadicH e)).card:ℝ))*
        ∑ ρ ∈ alpogeNativePhiSet _, Real.log (w ρ) := by
    change -(4*Real.log x) ≤ (ell (alpogeNativeChC _)).re at hc
    linarith only [hlog, hbig, hc, hl, Real.eulerMascheroniConstant_lt_two_thirds,
      Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)]
  simp only [alpogeNativeMAIN, Complex.re_ofReal_mul, Complex.sub_re, Complex.add_re, Complex.ofReal_re]
  change _ ≤ a * _
  exact mul_le_mul_of_nonneg_left scalar ha.le

/-- All coefficients through the specified cutoff, including proper powers
and ramified colours, bounded using the native reciprocal Mangoldt sum. -/
theorem kernelASK_prefix {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (I : ℕ → AddSubgroup (AlpogeNativeE0 × H)) (F : ℕ → AlpogeNativeE0 × H)
    (M : ℕ) (hM : 1 ≤ M) (a : ℝ) (ha : 0 ≤ a) (t : H)
    (v : AlpogeNativeE0 × H → ℝ) (hv : ∀ ρ, 0 ≤ v ρ) :
    (alpogeNativeFullKernelASK I F M a t v).re ≤ 2*a*(Real.log M+Real.log 4+2) := by
  classical
  rw [alpogeNativeFullKernelASK_re_eq_weighted]
  let G := Finset.univ.filter (fun g : AlpogeNativeE0 × H => ¬alpogeNativeInPhi g)
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 M, (2*a)*(Λ n/(n:ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have harg : 0 ≤ a/(n:ℝ) := div_nonneg ha (Nat.cast_nonneg n)
      calc
        _ ≤ ∑ g ∈ G, alpogeNativeASKRealWeight I F n g*(a/n) := by
          exact Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_left
            (max_le (sub_le_self _ (hv _)) harg) (alpogeNativeASKRealWeight_nonneg I F n g)
        _ = (∑ g ∈ G, alpogeNativeASKRealWeight I F n g)*(a/n) := (Finset.sum_mul _ _ _).symm
        _ ≤ (2*Λ n)*(a/n) := mul_le_mul_of_nonneg_right (alpogeNativeASKRealWeight_sum_le_two_lambda I F n) harg
        _ = _ := by ring
    _ = (2*a)*nativeLambdaRecip M := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [(nativeLambdaRecip_sub_log_bounds M hM).2])
      (by positivity)

/-- Above the paid prefix every original thick reading vanishes. This uses
the lower log grid and the actual height collar at the original cutoff. -/
theorem thick_above_prefix (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ (a b w η : ℝ) (n : ℕ), 0 < b → b ≤ w → a ≤ (x+1)*b →
      0 < η → η ≤ 1 → ⌊Real.exp (x^(ε/3)/16)⌋₊ < n →
      alpogeASKPos (a/(n:ℝ)) (alpogeNativeLowerLogWidth η w) = 0 := by
  have hr : 0 < ε/3 := by positivity
  filter_upwards [(isLittleO_log_rpow_atTop hr).bound (by norm_num : (0:ℝ) < 1/64),
    Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_ge_atTop (2:ℝ)] with x hlog h1 hx
  have hx0 : 0 < x := by linarith
  have hln := Real.log_nonneg (by linarith : 1 ≤ x)
  rw [Real.norm_of_nonneg hln, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hlog
  intro a b w η n hb hbw ha hη hη1 hn
  let v := alpogeNativeLowerLogWidth η w
  have hw := hb.trans_le hbw
  have hv : 0 < v := Real.exp_pos _
  have floorUp := (div_lt_iff₀ hη).mp (Int.lt_floor_add_one (Real.log w / η))
  have grid : w ≤ Real.exp 1*v := by
    rw [← Real.exp_log hw, show v = Real.exp ((⌊Real.log w/η⌋:ℤ)*η) from rfl, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith only [floorUp,hη1])
  have cutoff : (x+1)*Real.exp 1 ≤ Real.exp (x^(ε/3)/16) := by
    have h := Real.log_le_log (by linarith : 0 < x+1) (by nlinarith : x+1 ≤ x*x)
    rw [Real.log_mul hx0.ne' hx0.ne'] at h
    calc
      _ = Real.exp (Real.log (x+1)+1) := by rw [Real.exp_add, Real.exp_log (by linarith : 0 < x+1)]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [h,h1,hlog])
  have hn' : Real.exp (x^(ε/3)/16) < (n:ℝ) := (Nat.floor_lt (Real.exp_pos _).le).mp hn
  have hn0 := (Real.exp_pos _).trans hn'
  have hcut : a ≤ (n:ℝ)*v := calc
    _ ≤ (x+1)*b := ha
    _ ≤ (x+1)*(Real.exp 1*v) := mul_le_mul_of_nonneg_left (hbw.trans grid) (by linarith)
    _ = ((x+1)*Real.exp 1)*v := (mul_assoc _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (cutoff.trans hn'.le) hv.le
  exact max_eq_right (sub_nonpos.mpr ((div_le_iff₀ hn0).2 (by simpa only [mul_comm v (n:ℝ)] using hcut)))

/-- Actual clipped wheel depths fit inside one factorial of the original
integer prefix. This estimates their total and introduces no section transport. -/
theorem wheel_prefix_log_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (N c : ℕ) :
    ∑ p ∈ P, Real.log ((p^(N/p-c):ℕ):ℝ) ≤ (N:ℝ)*Real.log N := by
  classical
  let D := fun p : ℕ => p^(N/p-c)
  have hd p (hp : p ∈ P) : 0 < D p := pow_pos (hP p hp).pos _
  have divides : (∏ p ∈ P, D p) ∣ N.factorial := by
    apply Finset.prod_dvd_of_isRelPrime
    · intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp (Nat.coprime_pow_primes _ _ (hP p hp) (hP q hq) hpq)
    · intro p hp
      let : Fact p.Prime := ⟨hP p hp⟩
      have hv := (padicValNat_mul_div_factorial (p := p) N).symm.trans (padicValNat_factorial_mul (N/p))
      have lower : N/p-c ≤ padicValNat p N.factorial := by omega
      exact (pow_dvd_pow p lower).trans pow_padicValNat_dvd
  have hn : (∏ p ∈ P, D p) ≤ N^N := (Nat.le_of_dvd (Nat.factorial_pos _) divides).trans N.factorial_le_pow
  have h := Real.log_le_log (show 0 < ((∏ p ∈ P, D p:ℕ):ℝ) by exact_mod_cast Finset.prod_pos hd)
    (show ((∏ p ∈ P, D p:ℕ):ℝ) ≤ ((N^N:ℕ):ℝ) by exact_mod_cast hn)
  rw [Nat.cast_prod, Real.log_prod (fun p hp => by exact_mod_cast (hd p hp).ne'), Nat.cast_pow, Real.log_pow] at h
  exact h

/-- The negative MAIN summand of the original subgroup top excess with its original divisor. -/
def normalizedNegMain {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H] {n : ℕ}
    (tops T : Finset H) (a : H → ℝ) (b : ℝ) (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (v : H → Fin n → AlpogeNativeE0 × H → ℝ) : ℝ :=
  ((1/(Fintype.card (⊤ : AddSubgroup H):ℝ))*∑ u : (⊤ : AddSubgroup H), ∑ t ∈ tops, ∑ j : Fin n,
    -(alpogeNativeMAIN ell (a t) (v u j)).re) / alpogeNativeProjectionDivisor tops T n b

private theorem normalize_rows {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H] {n : ℕ}
    (tops T : Finset H) (b x : ℝ) (R : H → H → Fin n → ℝ) (ht : tops.Nonempty) (hT : T.Nonempty)
    (hn : 0 < n) (hb : 0 < b) (hx : 1 ≤ x)
    (hrow : ∀ (u : H) t, t ∈ tops → ∀ j, R u t j ≤ -(4*x*b*Real.log x)) :
    ((1/(Fintype.card (⊤ : AddSubgroup H):ℝ))*∑ u : (⊤ : AddSubgroup H), ∑ t ∈ tops, ∑ j : Fin n,
      R u t j) / alpogeNativeProjectionDivisor tops T n b ≤ -(8*x*Real.log x) := by
  let A0 : AddSubgroup H := ⊤
  let M := 4*x*b*Real.log x
  have hU : 0 < (Fintype.card A0:ℝ) := by exact_mod_cast Fintype.card_pos
  have hlog := Real.log_nonneg hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hQ := alpogeNativeProjectionDivisor_pos tops T ht hT n hn b hb
  have hsum : (∑ u : A0, ∑ t ∈ tops, ∑ j : Fin n, R u t j) ≤
      ∑ _u : A0, ∑ _t ∈ tops, ∑ _j : Fin n, -M := by
    exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun t ht' =>
      Finset.sum_le_sum fun j _ => hrow u t ht' j
  have hDelta : alpogeNativeProjectionDensity T ≤ 1 := by
    unfold alpogeNativeProjectionDensity
    apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos : 0 < (Fintype.card H:ℝ))).2
    simpa only [one_mul] using (show (T.card:ℝ) ≤ Fintype.card H by exact_mod_cast Finset.card_le_univ T)
  apply (div_le_iff₀ hQ).2
  calc
    _ ≤ (1/(Fintype.card A0:ℝ))*∑ _u : A0, ∑ _t ∈ tops, ∑ _j : Fin n, -M :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = -((tops.card:ℝ)*n*M) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [hU.ne']
    _ ≤ -((tops.card:ℝ)*n*M*alpogeNativeProjectionDensity T) := by
      apply neg_le_neg
      exact mul_le_of_le_one_right (by dsimp only [M]; positivity) hDelta
    _ = _ := by unfold alpogeNativeProjectionDivisor; dsimp [M]; ring

private theorem prefix_real_bound (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime)
    (x : ℝ) (hx : 10 ≤ x) :
    let c := ⌊Real.sqrt x⌋₊
    ∑ p ∈ P, Real.log ((p^(⌊(c:ℝ)*x⌋₊/p-c):ℕ):ℝ) ≤ 2*(c:ℝ)*x*Real.log x := by
  intro c
  let N := ⌊(c:ℝ)*x⌋₊
  have hx0 : 0 < x := by linarith
  have hc : 1 ≤ (c:ℝ) := by
    have hs : 2 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0.le).2 (by linarith)
    have hf := Nat.lt_floor_add_one (Real.sqrt x)
    dsimp only [c]
    linarith
  have hlog := Real.log_nonneg (by linarith : 1 ≤ x)
  have hcx : (c:ℝ) ≤ x :=
    (Nat.floor_le (Real.sqrt_nonneg x)).trans (Real.sqrt_le_self_iff.mpr (Or.inr (by linarith)))
  have hN : (N:ℝ) ≤ (c:ℝ)*x := Nat.floor_le (by positivity)
  have hN0 : 0 < (N:ℝ) := by
    have hf := Nat.lt_floor_add_one ((c:ℝ)*x)
    have h1 := mul_le_mul_of_nonneg_right hc hx0.le
    dsimp only [N]
    linarith
  have hln : Real.log N ≤ 2*Real.log x := by
    have h := Real.log_le_log hN0 (hN.trans (mul_le_mul_of_nonneg_right hcx hx0.le))
    rwa [Real.log_mul hx0.ne' hx0.ne', ← two_mul] at h
  calc
    _ ≤ (N:ℝ)*Real.log N := wheel_prefix_log_bound P hp N c
    _ ≤ (N:ℝ)*(2*Real.log x) := mul_le_mul_of_nonneg_left hln hN0.le
    _ ≤ ((c:ℝ)*x)*(2*Real.log x) := mul_le_mul_of_nonneg_right hN (by positivity)
    _ = _ := by ring

/-- The measured complementary volume bounds the original negative MAIN on
the very same rounded rows and pair. Each summand in the right side is the
relative log of the level-one minimum on the original quotient-slot block. -/
theorem complementary_bounds_signedMain (ε : ℝ) (he : 0 < ε) (he1 : ε ≤ 1) :
    ∀ᶠ x : ℝ in atTop, ∀ (e q d n : ℕ) [Fact q.Prime] [Fact d.Prime]
      {Y Z : ℝ} (_pair : UpperTheory.Top.PairGood 1 ε Y Z q d), Y ≤ x → x ≤ Z →
      ∀ (tops T : Finset (AlpogeNativeDyadicH e)) (a : AlpogeNativeDyadicH e → ℝ)
        (w : AlpogeNativeDyadicH e → Fin n → AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ) (η : ℝ),
      let b := Real.exp (x^ε)
      let c := ⌊Real.sqrt x⌋₊
      let P := highThickPrimes e q d x
      let g := fun p => ((alpogeNativeHostData e q d).frob p).2
      let V := occupied tops P g
      let p := primeAt tops P g
      let r := fun s : ↥V => (partnerPrimes tops P g s.val).card-1
      let D := fun (s : ↥V) (i : Fin (r s+1)) => p s i ^ (⌊(c:ℝ)*x⌋₊/p s i-c)
      let cut := fun (s : ↥V) (i : Fin (r s+1)) => a (s.val-g (p s i))/(p s i:ℝ)
      let S := fun (s : ↥V) (j : ↥(siteRows T n s.val)) => bands (cut s) (w j.val.1 j.val.2 ((0,1),s.val))
      let k := ((T.card*n:ℕ):ℝ)
      let v := fun u j ρ => alpogeNativeLowerLogWidth η (w u j ρ)
      let ell := alpogeNativeCanonicalHostEll (H := AlpogeNativeDyadicH e) (alpogeNativeRecMap e q d)
      0 < η → tops.Nonempty → T.Nonempty → 0 < n →
      (∀ t ∈ tops, a t ∈ Set.Icc (x*b) ((x+1)*b)) →
      (∀ u j ρ, ρ ∈ alpogeNativeThickPositiveSites T u → w u j ρ ∈ Set.Icc b (b*(1+1/x))) →
      (∀ u j ρ, ρ ∈ alpogeNativePhiSet _ → 0 < w u j ρ) →
      (∀ u j t, t ∈ tops → ∀ g ∈ (Finset.univ.filter fun g : AlpogeNativeE0 × AlpogeNativeDyadicH e =>
          ¬alpogeNativeInPhi g) \ alpogeNativeProjectionThickColours T u t,
        Real.exp (x^(ε/3))/3 ≤ a t/w u j (alpogeNativePartner t g)) →
      let C := 4*(∑ s : ↥V, ∑ j : ↥(siteRows T n s.val), complementaryLog (S s j) (D s))/((c:ℝ)*k*tops.card)
      normalizedNegMain tops T a b ell v ≤ C ∧
      ∀ M : ℕ, (M:ℝ) ≤ Real.exp (x^(ε/3)/16) →
        alpogeNativePhysicalSubgroupTopExcess (⊤ : AddSubgroup (AlpogeNativeDyadicH e))
          (alpogeNativeHostData e q d).inertia (alpogeNativeHostData e q d).frob ell M tops a v /
          alpogeNativeProjectionDivisor tops T n b ≤ C := by
  classical
  filter_upwards [signedMain_row ε he, highThick_frame ε he he1, eventually_ge_atTop (10:ℝ),
    (tendsto_rpow_atTop (by positivity : 0 < ε/3)).eventually_ge_atTop (16*(Real.log 4+2))]
    with x row frame hx hlarge
  intro e q d n _ _ Y Z pair hY hZ tops T a w η b c P g V p r D cut S k v ell hη ht hT hn ha hw hpos hthin C
  have hx0 : 0 < x := by linarith
  have hb : 0 < b := Real.exp_pos _
  have hlog := Real.log_nonneg (by linarith : 1 ≤ x)
  let host := alpogeNativeHostData e q d
  have rowMargin (u t) (ht' : t ∈ tops) j :
      (a t)*(4*Real.log x+x^(ε/3)/4) ≤ (alpogeNativeMAIN ell (a t) (v u j)).re := by
    have hta : 0 < a t := (mul_pos hx0 hb).trans_le (ha t ht').1
    have hthick (ρ) (hρ : ρ ∈ alpogeNativeThickPositiveSites T u) : w u j ρ ≤ a t := by
      have hxinv : 1/x ≤ 1 := (div_le_iff₀ hx0).2 (by linarith)
      have hscale := mul_le_mul_of_nonneg_left (by linarith only [hx,hxinv] : 1+1/x ≤ x) hb.le
      exact (hw u j ρ hρ).2.trans (hscale.trans (by simpa only [mul_comm b x] using (ha t ht').1))
    have hmain := row e q d pair hY hZ T u (a t) (w u j) hta (hpos u j) hthick
      (thin_sites_of_partner T u t (a t) _ (w u j) (hthin u j t ht'))
    have monotone : (alpogeNativeMAIN ell (a t) (w u j)).re ≤ (alpogeNativeMAIN ell (a t) (v u j)).re := by
      apply alpogeNativeMAIN_re_antitone_width ell _ hta.le _ _
      · intro ρ _; exact Real.exp_pos _
      · intro ρ hρ
        have hp := hpos u j ρ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hρ⟩)
        exact (Real.exp_le_exp.mpr ((le_div_iff₀ hη).mp (Int.floor_le (Real.log (w u j ρ)/η)))).trans
          (Real.exp_log hp).le
    exact hmain.trans monotone
  have short (u t) (ht' : t ∈ tops) j :
      4*x*b*Real.log x+(a t)*(x^(ε/3)/4) ≤ (alpogeNativeMAIN ell (a t) (v u j)).re := by
    have h := rowMargin u t ht' j
    nlinarith only [h, mul_le_mul_of_nonneg_right (ha t ht').1 hlog]
  obtain ⟨hS,_,_,_,_,vol,_,_⟩ := frame e q d n 1 tops T a w Nat.zero_lt_one ha hw
  have primes (l) (hl : l ∈ P) : l.Prime :=
    (Nat.mem_primesLE.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).1).2
  have hD (s : ↥V) (i : Fin (r s+1)) : 0 < D s i := by
    have hm : p s i ∈ partnerPrimes tops P g s.val := Finset.orderEmbOfFin_mem ..
    exact pow_pos (primes _ (Finset.mem_filter.mp hm).1).pos _
  have opp : (∑ s : ↥V, ∑ j : ↥(siteRows T n s.val), complementaryLog (S s j) (D s)) =
      -(∑ s : ↥V, ∑ j : ↥(siteRows T n s.val), logVolume (S s j) (D s)) := by
    simp_rw [fun s j => complementaryLog_eq (S s j) (D s) (hS s j) (hD s), Finset.sum_neg_distrib]
  have hc : 0 < (c:ℝ) := by
    have hs : 2 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0.le).2 (by linarith)
    have hf := Nat.lt_floor_add_one (Real.sqrt x)
    dsimp only [c]
    linarith
  have hk : 0 < k := by
    change 0 < ((T.card*n:ℕ):ℝ)
    exact_mod_cast Nat.mul_pos hT.card_pos hn
  have ht0 : 0 < (tops.card:ℝ) := by exact_mod_cast ht.card_pos
  have hmass := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (prefix_real_bound P primes x hx) ht0.le) hk.le
  have upper := (sub_nonneg.mp vol.1).trans hmass
  have comp : -(8*x*Real.log x) ≤ C := by
    dsimp only [C]
    rw [opp]
    apply (le_div_iff₀ (mul_pos (mul_pos hc hk) ht0)).2
    change (∑ s : ↥V, ∑ j : ↥(siteRows T n s.val), logVolume (S s j) (D s)) ≤
      k*((tops.card:ℝ)*(2*(c:ℝ)*x*Real.log x)) at upper
    linarith only [upper]
  constructor
  · apply le_trans _ comp
    apply normalize_rows tops T b x (fun u t j => -(alpogeNativeMAIN ell (a t) (v u j)).re) ht hT hn hb (by linarith)
    intro u t ht' j
    have hat := (mul_pos hx0 hb).trans_le (ha t ht').1
    have nonneg : 0 ≤ a t*(x^(ε/3)/4) := by positivity
    linarith only [short u t ht' j, nonneg]
  · intro M hM
    apply le_trans _ comp
    apply normalize_rows tops T b x (fun u t j => (alpogeNativeFullKernelASK host.inertia host.frob M
      (a t) t (v u j) - alpogeNativeMAIN ell (a t) (v u j)).re) ht hT hn hb (by linarith)
    intro u t ht' j
    have hat := (mul_pos hx0 hb).trans_le (ha t ht').1
    have hprefix : (alpogeNativeFullKernelASK host.inertia host.frob M (a t) t (v u j)).re ≤
        a t*(x^(ε/3)/4) := by
      by_cases hM1 : 1 ≤ M
      · have hln := Real.log_le_log (show 0 < (M:ℝ) by exact_mod_cast hM1) hM
        rw [Real.log_exp] at hln
        apply (kernelASK_prefix host.inertia host.frob M hM1 _ hat.le t (v u j) (fun _ => (Real.exp_pos _).le)).trans
        nlinarith only [mul_le_mul_of_nonneg_left (by linarith only [hlarge,hln] :
          2*(Real.log M+Real.log 4+2) ≤ x^(ε/3)/4) hat.le]
      · have hz : M = 0 := by omega
        rw [hz, alpogeNativeFullKernelASK_re_eq_weighted]
        simp only [Finset.Icc_eq_empty_of_lt Nat.zero_lt_one, Finset.sum_empty]
        positivity
    rw [Complex.sub_re]
    linarith only [hprefix, short u t ht' j]


end RHLean.Analysis.AlpogeThin.SlotProjector

import «research.NativeAnchoredSlotMetric»
import «research.NativePrincipalCrossingBalance»
import RHLean.Analysis.NativePNTSquarePrefixTailReciprocalBound

/-! Integral recovery of the layer-constant signed test on the original sorted
prime cuts. The two endpoint thresholds price all its boundary jumps. -/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace RHLean.Analysis.AlpogeThin.SlotProjector.WheelNNS

def intervalTest {r : ℕ} (p : Fin (r+1) → ℕ) (L U : ℝ) (i : Fin (r+1)) : ℤ :=
  if L ≤ (p i:ℝ) ∧ (p i:ℝ) < U then 1 else 0

def changes {r : ℕ} (p : Fin (r+1) → ℕ) (L U : ℝ) : Finset (Fin r) :=
  Finset.univ.filter (fun j => intervalTest p L U j.succ ≠ intervalTest p L U j.castSucc)

private def threshold {r : ℕ} (p : Fin (r+1) → ℕ) (t : ℝ) : Finset (Fin r) :=
  Finset.univ.filter (fun j => (p j.castSucc:ℝ) < t ∧ t ≤ (p j.succ:ℝ))

private theorem threshold_unique {r : ℕ} (p : Fin (r+1) → ℕ) (hp : Monotone p) (t : ℝ) :
    (threshold p t).card ≤ 1 := by
  have same (i j : Fin r) (hi : i ∈ threshold p t) (hj : j ∈ threshold p t) : ¬i < j := by
    intro lt
    have ord : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; exact lt
    have pv : (p i.succ:ℝ) ≤ p j.castSucc := by exact_mod_cast hp ord
    exact (not_lt_of_ge ((Finset.mem_filter.mp hi).2.2.trans pv)) (Finset.mem_filter.mp hj).2.1
  exact Finset.card_le_one.mpr fun i hi j hj => le_antisymm (le_of_not_gt (same j i hj hi))
    (le_of_not_gt (same i j hi hj))

theorem changes_card {r : ℕ} (p : Fin (r+1) → ℕ) (hp : Monotone p) (L U : ℝ) :
    (changes p L U).card ≤ 2 := by
  have sub : changes p L U ⊆ threshold p L ∪ threshold p U := by
    intro j hj
    have diff := (Finset.mem_filter.mp hj).2
    have ord : (p j.castSucc:ℝ) ≤ p j.succ := by exact_mod_cast hp (show j.castSucc < j.succ from Fin.castSucc_lt_succ).le
    simp only [Finset.mem_union,threshold,Finset.mem_filter,Finset.mem_univ,true_and]
    by_contra! no
    have ll : L ≤ (p j.succ:ℝ) ↔ L ≤ (p j.castSucc:ℝ) := by constructor <;> intro m <;> grind
    have uu : (p j.succ:ℝ) < U ↔ (p j.castSucc:ℝ) < U := by constructor <;> intro m <;> grind
    exact diff (by simp only [intervalTest,ll,uu])
  exact (Finset.card_le_card sub).trans ((Finset.card_union_le ..).trans
    (Nat.add_le_add (threshold_unique p hp L) (threshold_unique p hp U)))

/-- A test multiple belongs to the single, simultaneous anchored recovery
image exactly when all its changed boundaries divide that multiple. -/
theorem interval_clearing_iff {r : ℕ} (p : Fin (r+1) → ℕ) (L U : ℝ) (d : Fin r → ℕ) (m : ℕ) :
    (∃ A, anchoredRecovery (fun j => (d j:ℤ)) A = fun i => (m:ℤ)*intervalTest p L U i) ↔
      ∀ j ∈ changes p L U, d j ∣ m := by
  rw [anchoredRecovery_image]
  have localIff (j : Fin r) :
      ((d j:ℤ) ∣ layerJump (fun i => (m:ℤ)*intervalTest p L U i) j) ↔
        (j ∈ changes p L U → d j ∣ m) := by
    by_cases left : L ≤ (p j.castSucc:ℝ) ∧ (p j.castSucc:ℝ) < U <;>
      by_cases right : L ≤ (p j.succ:ℝ) ∧ (p j.succ:ℝ) < U <;>
      simp [layerJump,changes,intervalTest,left,right]
  exact forall_congr' localIff

def clearing {r : ℕ} (p : Fin (r+1) → ℕ) (L U : ℝ) (d : Fin r → ℕ) : ℕ :=
  ∏ j ∈ changes p L U, d j

theorem interval_recovered {r : ℕ} (p : Fin (r+1) → ℕ) (L U : ℝ) (d : Fin r → ℕ) :
    ∃ A, anchoredRecovery (fun j => (d j:ℤ)) A =
      fun i => (clearing p L U d:ℤ)*intervalTest p L U i :=
  (interval_clearing_iff ..).2 fun _ hj => Finset.dvd_prod_of_mem _ hj

private theorem clearing_price {r : ℕ} (p : Fin (r+1) → ℕ) (hp : Monotone p) (L U : ℝ)
    (d : Fin r → ℕ) (hd : ∀ j, 0 < d j) (B : ℝ) (hB : 0 ≤ B)
    (price : ∀ j ∈ changes p L U, Real.log (d j:ℝ) ≤ B) : Real.log (clearing p L U d:ℝ) ≤ 2*B := by
  rw [clearing,Nat.cast_prod,Real.log_prod (fun j _ => by exact_mod_cast (hd j).ne')]
  calc
    _ ≤ ∑ _j ∈ changes p L U, B := Finset.sum_le_sum price
    _ = ((changes p L U).card:ℝ)*B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast changes_card p hp L U) hB

/-- Price all the original moving interval tests on the same sorted prime
block and at the same shift. The weighted sum of their actual clearing
logs uses the original cofactor weights. This does not identify a rowwise
clearing sum with a single simultaneous denominator. -/
theorem weighted_interval_price {r : ℕ} (p : Fin (r+1) → ℕ) (hp : StrictMono p) (c R : ℕ)
    (x a shift : ℝ) (hx : 1 ≤ x) (hprime : ∀ i, (p i).Prime) (hhigh : ∀ i, Real.sqrt x ≤ p i)
    (hpx : ∀ i, (p i:ℝ) ≤ x) :
    let d := fun j : Fin r => (p j.succ)^(⌊(c:ℝ)*x⌋₊/(p j.succ)-c)
    let v := fun k => PrincipalCofactor.oddCofactor k+shift
    (∑ k ∈ Finset.Ico 1 R, PrincipalCofactor.cellWeight k*
      Real.log (clearing p (a/(v k+1)) (a/v k) d:ℝ)) ≤
      2*((c:ℝ)*Real.sqrt x*Real.log x)*(1+Real.log R) := by
  intro d v
  let B := (c:ℝ)*Real.sqrt x*Real.log x
  have B0 : 0 ≤ B := mul_nonneg (by positivity) (Real.log_nonneg hx)
  have hd j : 0 < d j := pow_pos (hprime _).pos _
  have price (j) : Real.log (d j:ℝ) ≤ B :=
    (Real.log_le_iff_le_exp (by exact_mod_cast hd j)).2
      (MeasuredCut.wheel_factor_le _ c x (hprime _) hx (hhigh _) (hpx _))
  have bound k := clearing_price p hp.monotone (a/(v k+1)) (a/v k) d hd B B0 (fun j _ => price j)
  have weight (k : ℕ) (hk : k ∈ Finset.Ico 1 R) : PrincipalCofactor.cellWeight k ≤ 1/(k:ℝ) := by
    have pos : 0 < (k:ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hk).1
    exact one_div_le_one_div_of_le pos (by dsimp [PrincipalCofactor.oddCofactor]; linarith :
      (k:ℝ) ≤ 2*(PrincipalCofactor.oddCofactor k+1))
  calc
    _ ≤ ∑ k ∈ Finset.Ico 1 R, (1/(k:ℝ))*(2*B) := by
      refine Finset.sum_le_sum fun k hk => ?_
      exact (mul_le_mul_of_nonneg_left (bound k) (by dsimp [PrincipalCofactor.cellWeight,
        PrincipalCofactor.oddCofactor]; positivity)).trans (mul_le_mul_of_nonneg_right (weight k hk) (by positivity))
    _ = (2*B)*(∑ k ∈ Finset.Ico 1 R, 1/(k:ℝ)) := by rw [← Finset.sum_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((nativeTailReciprocalIco_le 1 R le_rfl).trans (harmonic_le_one_add_log R)) (by positivity)


/-- Exact archimedean squared norm of the recovered interval in the original
slot metric. The logarithmic price includes the same finite multiplier and
the actual size of the parent interval. Empty tests have zero energy. -/
theorem interval_energy {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) (p : Fin (r+1) → ℕ) (L U : ℝ) (m : ℕ) (pos : 0 < m) :
    let J := Finset.univ.filter fun i => L ≤ (p i:ℝ) ∧ (p i:ℝ) < U
    let S := bands h v
    let E := slotEnergy S (fun i => (m:ℝ)*(intervalTest p L U i:ℝ))
    E = (m:ℝ)^2*(∑ i ∈ J, ((S i).card:ℝ)) ∧
      Real.log (1+E) ≤ 2*Real.log (m:ℝ)+Real.log (1+(⌊h 0⌋₊-⌈v⌉₊:ℕ):ℝ) := by
  intro J S E
  have eq : E = (m:ℝ)^2*(∑ i ∈ J, ((S i).card:ℝ)) := by
    dsimp only [E,slotEnergy,J]
    rw [Finset.sum_filter,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hit : L ≤ (p i:ℝ) ∧ (p i:ℝ) < U <;> simp [intervalTest,hit,mul_comm]
  refine ⟨eq, ?_⟩
  obtain ⟨emb,_⟩ := original_addresses h v hne
  have len : (∑ i, (S i).card) = ⌊h 0⌋₊-⌈v⌉₊ := by
    simpa only [Address,Fintype.card_sigma,Fintype.card_coe,Nat.card_Ioc] using Fintype.card_congr emb
  have subset : (∑ i ∈ J, ((S i).card:ℝ)) ≤ ((⌊h 0⌋₊-⌈v⌉₊:ℕ):ℝ) := by
    rw [← len,Nat.cast_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J) (fun _ _ _ => Nat.cast_nonneg _)
  have m1 : (1:ℝ) ≤ m := by exact_mod_cast pos
  have e0 : 0 ≤ E := by rw [eq]; positivity
  have m2 : (1:ℝ) ≤ (m:ℝ)^2 := by nlinarith only [m1,sq_nonneg ((m:ℝ)-1)]
  have norm : 1+E ≤ (m:ℝ)^2*(1+((⌊h 0⌋₊-⌈v⌉₊:ℕ):ℝ)) := by
    rw [eq,mul_add,mul_one]
    exact add_le_add m2 (mul_le_mul_of_nonneg_left subset (sq_nonneg _))
  calc
    _ ≤ _ := Real.log_le_log (by linarith : 0 < 1+E) norm
    _ = _ := by rw [Real.log_mul (by positivity) (by positivity),Real.log_pow]; norm_num


/-- The cutoff includes exactly the retained first primes, with the same half-open
moving endpoints as the principal curvature. -/
def lowerCut (M : ℕ) (a v : ℝ) : ℝ := max ((M.sqrt:ℝ)+1) (a/(v+1))
def upperCut (M : ℕ) (a v : ℝ) : ℝ := min ((M:ℝ)+1) (a/v)

theorem clipped_hit (M p : ℕ) (hp : p.Prime) (a v : ℝ) :
    (lowerCut M a v ≤ (p:ℝ) ∧ (p:ℝ) < upperCut M a v) ↔
    p ∈ PrincipalCofactor.retainedFirstPrimes M ∧ a/(v+1) ≤ (p:ℝ) ∧ (p:ℝ) < a/v := by
  rw [lowerCut,upperCut,max_le_iff,lt_min_iff,PrincipalCofactor.mem_retainedFirstPrimes]
  have minP : (M.sqrt:ℝ)+1 ≤ p ↔ M.sqrt < p := by exact_mod_cast (Iff.rfl : M.sqrt+1 ≤ p ↔ M.sqrt < p)
  have maxP : (p:ℝ) < (M:ℝ)+1 ↔ p ≤ M := by exact_mod_cast (Nat.lt_succ_iff : p < M+1 ↔ p ≤ M)
  simp only [minP,maxP,hp,hp.one_le,true_and,and_true]
  tauto

private theorem changed_lower {r : ℕ} (p : Fin (r+1) → ℕ) (hp : Monotone p) (L U : ℝ)
    (j : Fin r) (hj : j ∈ changes p L U) : L ≤ (p j.succ:ℝ) := by
  by_contra! low
  have ord : (p j.castSucc:ℝ) ≤ p j.succ := by exact_mod_cast hp (show j.castSucc ≤ j.succ from Fin.castSucc_lt_succ.le)
  have diff := (Finset.mem_filter.mp hj).2
  simp [intervalTest,not_le.mpr low,not_le.mpr (ord.trans_lt low)] at diff

/-- One integral source scale for every broad contrast at the fixed common shift. -/
def broadClearing {r : ℕ} (p : Fin (r+1) → ℕ) (d : Fin r → ℕ) (M K : ℕ) (s : ℝ) : ℕ :=
  ∏ k ∈ Finset.Ico 1 K, clearing p (lowerCut M (PrincipalCofactor.evenEndpoint M) (PrincipalCofactor.oddCofactor k+s))
    (upperCut M (PrincipalCofactor.evenEndpoint M) (PrincipalCofactor.oddCofactor k+s)) d

/-- Same integral operator, same multiplier, all cofactor tests and all the
original layer amplitudes. Changing the width at this site does not enter
the multiplier. -/
theorem broad_recovered {r : ℕ} (p : Fin (r+1) → ℕ) (d : Fin r → ℕ) (M K : ℕ) (s : ℝ) :
    ∃ A : ℕ → Fin (r+1) → ℤ, ∀ k ∈ Finset.Ico 1 K,
      anchoredRecovery (fun j => (d j:ℤ)) (A k) = fun i =>
        (broadClearing p d M K s:ℤ)*intervalTest p
          (lowerCut M (PrincipalCofactor.evenEndpoint M) (PrincipalCofactor.oddCofactor k+s))
          (upperCut M (PrincipalCofactor.evenEndpoint M) (PrincipalCofactor.oddCofactor k+s)) i := by
  classical
  let A := fun k => intervalTest p (lowerCut M (PrincipalCofactor.evenEndpoint M) (PrincipalCofactor.oddCofactor k+s))
    (upperCut M (PrincipalCofactor.evenEndpoint M) (PrincipalCofactor.oddCofactor k+s))
  have ex (k : ℕ) (hk : k ∈ Finset.Ico 1 K) : ∃ B, anchoredRecovery (fun j => (d j:ℤ)) B =
      fun i => (broadClearing p d M K s:ℤ)*A k i := by
    apply (interval_clearing_iff ..).2
    intro j hj
    exact (Finset.dvd_prod_of_mem d hj).trans (Finset.dvd_prod_of_mem _ hk)
  exact ⟨fun k => if hk : k ∈ Finset.Ico 1 K then (ex k hk).choose else 0,
    fun k hk => by simpa only [dif_pos hk] using (ex k hk).choose_spec⟩

private theorem depth_at_crossing (p c : ℕ) (x a v : ℝ) (hp : p.Prime) (hx : 1 ≤ x)
    (ha : 0 < a) (hv : 0 < v) (hd : a/v ≤ (p:ℝ)) (hpx : (p:ℝ) ≤ x) :
    Real.log ((p^(⌊(c:ℝ)*x⌋₊/p-c):ℕ):ℝ) ≤ ((c:ℝ)*x*v/a)*Real.log x := by
  let e := ⌊(c:ℝ)*x⌋₊/p-c
  have times : (e:ℝ)*(p:ℝ) ≤ (c:ℝ)*x := by
    have n : e*p ≤ ⌊(c:ℝ)*x⌋₊ := (Nat.mul_le_mul_right p (Nat.sub_le ..)).trans (Nat.div_mul_le_self _ _)
    exact (show (e:ℝ)*(p:ℝ) ≤ (⌊(c:ℝ)*x⌋₊:ℝ) by exact_mod_cast n).trans
      (Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hx)))
  have depth : (e:ℝ) ≤ (c:ℝ)*x*v/a := by
    apply (le_div_iff₀ ha).2
    calc
      _ ≤ (e:ℝ)*((p:ℝ)*v) := mul_le_mul_of_nonneg_left ((div_le_iff₀ hv).1 hd) (Nat.cast_nonneg _)
      _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right times hv.le
  rw [Nat.cast_pow,Real.log_pow]
  exact mul_le_mul depth (Real.log_le_log (by exact_mod_cast hp.pos) hpx) (Real.log_natCast_nonneg _)
    (by positivity)

/-- Pay for an actual common product, including repeated prime powers. Its
dependence on the original frame scale x and the ancestor endpoint a is explicit. -/
theorem broad_price {r : ℕ} (p : Fin (r+1) → ℕ) (hp : StrictMono p) (c M K : ℕ)
    (x s : ℝ) (hx : 1 ≤ x) (hs : s ∈ Set.Icc 0 1) (ha : 0 < PrincipalCofactor.evenEndpoint M)
    (hprime : ∀ i, (p i).Prime) (hpx : ∀ i, (p i:ℝ) ≤ x) :
    let a := PrincipalCofactor.evenEndpoint M
    let d := fun j : Fin r => (p j.succ)^(⌊(c:ℝ)*x⌋₊/(p j.succ)-c)
    Real.log (broadClearing p d M K s:ℝ) ≤ 10*(c:ℝ)*x*(K:ℝ)^2/a*Real.log x := by
  intro a d
  let v := fun k => PrincipalCofactor.oddCofactor k+s
  let L := fun k => lowerCut M a (v k)
  let U := fun k => upperCut M a (v k)
  let B := (c:ℝ)*x*(5*K)/a*Real.log x
  have log0 := Real.log_nonneg hx
  have x0 := zero_le_one.trans hx
  have B0 : 0 ≤ B := by dsimp [B]; positivity
  have hd j : 0 < d j := pow_pos (hprime _).pos _
  have pos k : 0 < clearing p (L k) (U k) d := Finset.prod_pos fun j _ => hd j
  have per (k : ℕ) (hk : k ∈ Finset.Ico 1 K) : Real.log (clearing p (L k) (U k) d:ℝ) ≤ 2*B := by
    apply clearing_price p hp.monotone _ _ d hd B B0
    intro j hj
    have low : a/(v k+1) ≤ (p j.succ:ℝ) := (le_max_right _ _).trans (changed_lower p hp.monotone _ _ j hj)
    have kv : v k+1 ≤ 5*(K:ℝ) := by
      have step : (k:ℝ)+1 ≤ K := by exact_mod_cast (Finset.mem_Ico.mp hk).2
      dsimp [v,PrincipalCofactor.oddCofactor]
      linarith only [step,hs.2,Nat.cast_nonneg (α := ℝ) k]
    have vpos : 0 < v k+1 := by dsimp [v,PrincipalCofactor.oddCofactor]; linarith only [Nat.cast_nonneg (α := ℝ) k,hs.1]
    exact (depth_at_crossing _ c x a (v k+1) (hprime _) hx ha vpos low (hpx _)).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left kv (mul_nonneg (Nat.cast_nonneg c) x0)) ha.le) log0)
  change Real.log ((∏ k ∈ Finset.Ico 1 K, clearing p (L k) (U k) d:ℕ):ℝ) ≤ _
  rw [Nat.cast_prod, Real.log_prod (fun k _ => by exact_mod_cast (pos k).ne')]
  calc
    _ ≤ ∑ _k ∈ Finset.Ico 1 K, 2*B := Finset.sum_le_sum per
    _ = ((K-1:ℕ):ℝ)*(2*B) := by simp
    _ ≤ (K:ℝ)*(2*B) := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le K 1) (by positivity)
    _ = _ := by dsimp [B]; ring

/-- Balance the log of the common integral multiplier and the fine curvature
charge on the original frame scale, for each dyadic ancestor independently
of its distance from that scale. -/
theorem balanced_crossing_recovery {r : ℕ} (p : Fin (r+1) → ℕ) (hp : StrictMono p)
    (c M R : ℕ) (x s : ℝ) (hx : 1 ≤ x) (hs : s ∈ Set.Icc 0 1)
    (hm : 0 < PrincipalCofactor.evenEndpoint M) (hprime : ∀ i, (p i).Prime)
    (hpx : ∀ i, (p i:ℝ) ≤ x) :
    let a := PrincipalCofactor.evenEndpoint M
    let K := ⌈Real.sqrt (a/Real.sqrt x)⌉₊
    let d := fun j : Fin r => (p j.succ)^(⌊(c:ℝ)*x⌋₊/(p j.succ)-c)
    Real.log (broadClearing p d M K s:ℝ) ≤ 40*(c:ℝ)*Real.sqrt x*Real.log x ∧
      ∑ k ∈ Finset.Ico K R, |PrincipalCofactor.crossingBalance M k| ≤
        (Real.log 4+1)*Real.sqrt x := by
  intro a K d
  let t := Real.sqrt x
  let u := Real.sqrt (a/t)
  have tp : 0 < t := Real.sqrt_pos.2 (zero_lt_one.trans_le hx)
  have up : 0 < u := Real.sqrt_pos.2 (div_pos hm tp)
  have tsq : t^2=x := Real.sq_sqrt (zero_le_one.trans hx)
  have usq : u^2=a/t := Real.sq_sqrt (div_pos hm tp).le
  have ceil : u ≤ K := Nat.le_ceil _
  have le : a ≤ (K:ℝ)^2*t := by
    rw [← div_le_iff₀ tp, ← usq]
    exact pow_le_pow_left₀ up.le ceil 2
  constructor
  · by_cases small : K ≤ 1
    · rw [broadClearing,Finset.Ico_eq_empty_of_le small,Finset.prod_empty,Nat.cast_one,Real.log_one]
      exact mul_nonneg (by positivity) (Real.log_nonneg hx)
    · have u1 : 1 < u := by
        by_contra! h
        exact small (Nat.ceil_le.mpr (by simpa using h))
      have ku : (K:ℝ) ≤ 2*u := by linarith only [(Nat.ceil_lt_add_one up.le).le,u1]
      have square := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) K) ku 2
      have Ksq : (K:ℝ)^2 ≤ 4*(a/t) := by nlinarith only [square,usq]
      have ratio : x*(K:ℝ)^2/a ≤ 4*t := by
        apply (div_le_iff₀ hm).2
        calc
          _ ≤ x*(4*(a/t)) := mul_le_mul_of_nonneg_left Ksq (zero_le_one.trans hx)
          _ = 4*t*a := by rw [← tsq]; field_simp [tp.ne']; ring
      calc
        _ ≤ _ := broad_price p hp c M K x s hx hs hm hprime hpx
        _ = (10*(c:ℝ))*(x*(K:ℝ)^2/a)*Real.log x := by ring
        _ ≤ (10*(c:ℝ))*(4*t)*Real.log x :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ratio (by positivity)) (Real.log_nonneg hx)
        _ = _ := by dsimp [t]; ring
  · by_cases kr : K ≤ R
    · have dk : (K:ℝ) ≤ PrincipalCofactor.oddCofactor K := by dsimp [PrincipalCofactor.oddCofactor]; linarith only [Nat.cast_nonneg (α := ℝ) K]
      have dp : 0 < PrincipalCofactor.oddCofactor K := up.trans_le (ceil.trans dk)
      have low := le.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) dk 2) tp.le)
      have frac : (a/PrincipalCofactor.oddCofactor K)*(1/PrincipalCofactor.oddCofactor K) ≤ t := by
        rw [mul_one_div,div_div,div_le_iff₀ (mul_pos dp dp)]
        nlinarith only [low]
      exact (PrincipalCofactor.fine_crossing_price M K R kr).trans
        (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left frac
          (show 0 ≤ Real.log 4+1 by linarith only [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)]))
    · rw [Finset.Ico_eq_empty_of_le (le_of_not_ge kr),Finset.sum_empty]
      exact mul_nonneg (by linarith only [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)]) tp.le

/-- A single simultaneous multiplier at each actual occupied site. Charge both
its finite log and an upper bound for the archimedean log norm of every
recovered column. The count of original translated fibres and the divisor
are the same as in the measured high-thick comparison. -/
theorem highThick_common_price (e q d n M : ℕ) [Fact q.Prime] [Fact d.Prime]
    (tops T : Finset (AlpogeNativeDyadicH e)) (a : AlpogeNativeDyadicH e → ℝ)
    (w : AlpogeNativeDyadicH e → Fin n → AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (x b s : ℝ) (hx : 1 ≤ x) (hb : 1 ≤ b) (hs : s ∈ Set.Icc 0 1)
    (hm : 0 < PrincipalCofactor.evenEndpoint M) (ha : ∀ t ∈ tops, a t ∈ Set.Icc (x*b) ((x+1)*b))
    (ht : tops.Nonempty) (hT : T.Nonempty) (hn : 0 < n) :
    let P := highThickPrimes e q d x
    let g := fun l => ((alpogeNativeHostData e q d).frob l).2
    let V := occupied tops P g
    let p := primeAt tops P g
    let K := ⌈Real.sqrt (PrincipalCofactor.evenEndpoint M/Real.sqrt x)⌉₊
    let c := ⌊Real.sqrt x⌋₊
    let d' := fun (y : ↥V) (j : Fin ((partnerPrimes tops P g y.val).card-1)) =>
      (p y j.succ)^(⌊(c:ℝ)*x⌋₊/(p y j.succ)-c)
    let m := fun y : ↥V => broadClearing (p y) (d' y) M K s
    let size := fun (y : ↥V) (j : ↥(siteRows T n y.val)) =>
      ⌊a (y.val-g (p y 0))/(p y 0:ℝ)⌋₊-⌈w j.val.1 j.val.2 ((0,1),y.val)⌉₊
    let k := ((T.card*n:ℕ):ℝ)
    (∑ y : ↥V, ∑ j : ↥(siteRows T n y.val),
      Real.log (m y:ℝ)+Real.log (1+(m y:ℝ)^2*(size y j:ℝ))/2) / ((c:ℝ)*k*tops.card) ≤
      ((V.card:ℝ)/tops.card)*(80*Real.sqrt x*Real.log x + Real.log (1+(x+1)*b)/(2*c)) := by
  classical
  intro P g V p K c d' m size k
  have info := highThick_primeAt e q d x tops
  have x0 := zero_le_one.trans hx
  have b0 := zero_le_one.trans hb
  have cpos : 0 < (c:ℝ) := by
    have one : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx
    exact_mod_cast (show 1 ≤ c from (Nat.le_floor_iff (Real.sqrt_nonneg x)).2 (by simpa using one))
  have kp : 0 < k := by change 0 < ((T.card*n:ℕ):ℝ); exact_mod_cast Nat.mul_pos hT.card_pos hn
  have tp : (0:ℝ) < tops.card := by exact_mod_cast ht.card_pos
  let B := 40*(c:ℝ)*Real.sqrt x*Real.log x
  let height := 1+(x+1)*b
  have cost (y : ↥V) : Real.log (m y:ℝ) ≤ B :=
    (balanced_crossing_recovery (p y) (p y).strictMono c M 0 x s hx hs hm
      (fun i => (info y i).1) (fun i => by linarith only [(info y i).2.2.1])).1
  have pos (y : ↥V) : 0 < m y := Finset.prod_pos fun l _ =>
    Finset.prod_pos fun j _ => pow_pos (info y j.succ).1.pos _
  have per (y : ↥V) (j : ↥(siteRows T n y.val)) :
      Real.log (m y:ℝ)+Real.log (1+(m y:ℝ)^2*(size y j:ℝ))/2 ≤ 2*B+Real.log height/2 := by
    let u := a (y.val-g (p y 0))
    let l := p y 0
    have ub : u ∈ Set.Icc (x*b) ((x+1)*b) := ha _ (info y 0).2.2.2.2
    have up : 0 ≤ u := (mul_nonneg x0 b0).trans ub.1
    have lc : (1:ℝ) ≤ l := by exact_mod_cast (info y 0).1.one_le
    have bound : (size y j:ℝ) ≤ (x+1)*b := calc
      _ ≤ (⌊u/(l:ℝ)⌋₊:ℝ) := by exact_mod_cast Nat.sub_le _ _
      _ ≤ u/(l:ℝ) := Nat.floor_le (div_nonneg up (zero_le_one.trans lc))
      _ ≤ u := div_le_self up lc
      _ ≤ _ := ub.2
    have one : (1:ℝ) ≤ m y := by exact_mod_cast pos y
    have m2 : (1:ℝ) ≤ (m y:ℝ)^2 := by nlinarith only [one,sq_nonneg ((m y:ℝ)-1)]
    have big : 1+(m y:ℝ)^2*(size y j:ℝ) ≤ (m y:ℝ)^2*height := by
      dsimp only [height]
      rw [mul_add,mul_one]
      exact add_le_add m2 (mul_le_mul_of_nonneg_left bound (sq_nonneg _))
    have logs := Real.log_le_log (by positivity) big
    have hpos : 0 < height := by dsimp [height]; positivity
    rw [Real.log_mul (by positivity) hpos.ne',Real.log_pow] at logs
    linarith only [logs,cost y]
  have count : (∑ y : ↥V, ∑ _j : ↥(siteRows T n y.val), (2*B+Real.log height/2)) =
      (V.card:ℝ)*(k*(2*B+Real.log height/2)) := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,siteRows_card,nsmul_eq_mul,k]
  apply (div_le_iff₀ (mul_pos (mul_pos cpos kp) tp)).2
  calc
    _ ≤ _ := Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun j _ => per y j
    _ = _ := count
    _ = _ := by dsimp only [B,height]; field_simp [tp.ne',cpos.ne']; ring

end RHLean.Analysis.AlpogeThin.SlotProjector.WheelNNS

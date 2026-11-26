import RHLean.Geometry.NativeThetaCuspHeisenberg
import RHLean.Geometry.NativeThetaCuspVacuum

/-!
# Exact finite Heisenberg projection and vacuum overlap

This is the finite orbit proof behind the source level-test overlap. It
uses the actual rational Schwartz–Bruhat Haar inner product. The orbit
projection is constructed as a finite average and its coefficient is
computed from the actual subgroup relative index. No overlap estimate or
rank/mass equality is assumed.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/
TensorLatticeVacuaExistUnique.lean (`Good.finite`, `Good.proj`,
`Good.ip_eq_zero`, `Good.overlap`). The proof is cut at rational symplectic
coordinates; the native ambient, conjugate-level shift and common phase
are constructed separately. The source mirror states no license;
attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Matrix Complex NumberField
open scoped ComplexConjugate BigOperators Classical Real

namespace RHLean.Geometry.NativeTheta.Cusp.FiniteOverlap

section Product

variable {κ ι : Type} [Fintype κ] [Fintype ι] {φ φ' ψ : Matrix κ ι ℚ → ℂ}

theorem sb_mul_conj (h : IsSB φ) (h' : IsSB ψ) : IsSB (fun x => φ x * conj (ψ x)) := (isSB_algebra_haar_linear ℚ κ ι φ (fun x => conj (ψ x)) h (isSB_algebra_haar_linear ℚ κ ι ψ ψ h' h').2.2.2.1).2.2.1

theorem sb_smul (c : ℂ) (h : IsSB φ) : IsSB (c • φ) := (isSB_algebra_haar_linear ℚ κ ι φ φ h h).2.1 c

theorem ip_smul_left (c : ℂ) (h : IsSB φ) (h' : IsSB ψ) : ip (c • φ) ψ = c * ip φ ψ := by
  have hm := sb_mul_conj h h'
  have e : (fun x => (c • φ) x * conj (ψ x)) = c • fun x => φ x * conj (ψ x) := by
    funext x; simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  unfold ip; rw [e]; exact (isSB_algebra_haar_linear ℚ κ ι _ _ hm hm).2.2.2.2.2.1 c

theorem ip_add_left (h : IsSB φ) (h₂ : IsSB φ') (h' : IsSB ψ) :
    ip (φ + φ') ψ = ip φ ψ + ip φ' ψ := by
  have hm := sb_mul_conj h h'
  have hm' := sb_mul_conj h₂ h'
  have e : (fun x => (φ + φ') x * conj (ψ x)) =
      (fun x => φ x * conj (ψ x)) + fun x => φ' x * conj (ψ x) := by
    funext x; simp only [Pi.add_apply, add_mul]
  unfold ip; rw [e]; exact (isSB_algebra_haar_linear ℚ κ ι _ _ hm hm').2.2.2.2.1

theorem ip_conj (h : IsSB φ) (h' : IsSB ψ) : ip ψ φ = conj (ip φ ψ) := by
  have hm := sb_mul_conj h h'
  have e : (fun x => ψ x * conj (φ x)) = fun x => conj (φ x * conj (ψ x)) := by
    funext x; simp only [map_mul, RCLike.conj_conj, mul_comm]
  unfold ip; rw [e]; exact (isSB_algebra_haar_linear ℚ κ ι _ _ hm hm).2.2.2.2.2.2.1

theorem ip_smul_right (c : ℂ) (h : IsSB φ) (h' : IsSB ψ) :
    ip φ (c • ψ) = conj c * ip φ ψ := by
  have hm := sb_mul_conj h h'
  have e : (fun x => φ x * conj ((c • ψ) x)) = conj c • fun x => φ x * conj (ψ x) := by
    funext x; simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
  unfold ip; rw [e]; exact (isSB_algebra_haar_linear ℚ κ ι _ _ hm hm).2.2.2.2.2.1 (conj c)

theorem sum_sb_ip (s : Finset (Matrix κ ι ℚ → ℂ)) (hs : ∀ φ ∈ s, IsSB φ) (h' : IsSB ψ) :
    IsSB (∑ φ ∈ s, φ) ∧ ip (∑ φ ∈ s, φ) ψ = ∑ φ ∈ s, ip φ ψ := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨isSB_zero, ?_⟩
    have := ip_smul_left (0 : ℂ) (isSB_zero (κ := κ) (ι := ι) (K := ℚ)) h'
    simpa using this
  | insert a s ha ih =>
    have ha' := hs a (Finset.mem_insert_self a s)
    obtain ⟨h1, h2⟩ := ih fun φ hφ => hs φ (Finset.mem_insert_of_mem hφ)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨(isSB_algebra_haar_linear ℚ κ ι _ _ ha' h1).1, by rw [ip_add_left ha' h1 h', h2]⟩

theorem heisS_fix {R : ℕ} (h : HasLevel R φ) {a b : Matrix κ ι ℚ} (ha : IntM a)
    (hb : IntM b) : heisS (((2 * R : ℕ) : ℚ) • a) (((2 * R : ℕ) : ℚ) • b) φ = φ := by
  classical
  funext x
  have hint : ∀ {q : ℚ}, IsIntegral ℤ q → ∃ z : ℤ, q = z := fun hq => by
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq
    exact ⟨z, by rw [← hz]; simp⟩
  have hcast : ∀ z : ℤ, IsIntegral ℤ (z : ℚ) := fun z => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℚ) (x := z))
  have hper : φ (x - ((2 * R : ℕ) : ℚ) • b) = φ x := by
    have hy : IntM ((-2 : ℚ) • b) := fun k i => by
      obtain ⟨z, hz⟩ := hint (hb k i)
      simp only [Matrix.smul_apply, smul_eq_mul, hz]
      simpa using hcast (-2 * z)
    rw [← h.2 x _ hy]
    congr 1
    rw [smul_smul, sub_eq_add_neg, ← neg_smul]
    congr 2
    push_cast; ring
  simp only [heisS]
  rw [hper]
  by_cases hx : φ x = 0
  · rw [hx, zero_mul]
  have hRx := h.1 x hx
  choose Xz hXz using fun k i => hint (hRx k i)
  choose Az hAz using fun k i => hint (ha k i)
  choose Bz hBz using fun k i => hint (hb k i)
  obtain ⟨M, key⟩ : ∃ M : ℤ, (∑ k, (2 * (x k ⬝ᵥ (((2 * R : ℕ) : ℚ) • a) k) -
      (((2 * R : ℕ) : ℚ) • a) k ⬝ᵥ (((2 * R : ℕ) : ℚ) • b) k) : ℚ) = 2 * (M : ℚ) := by
    refine ⟨∑ k, ∑ i, (2 * Xz k i * Az k i - 2 * (R : ℤ) ^ 2 * Az k i * Bz k i), ?_⟩
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e := hXz k i
    simp only [Matrix.smul_apply, smul_eq_mul] at e
    rw [hAz, hBz]
    linear_combination 4 * (Az k i : ℚ) * e
  rw [key]
  have : cexp (↑π * I * (((2 * (M : ℚ) : ℚ)) : ℂ)) = 1 := by
    rw [show (↑π * I * (((2 * (M : ℚ) : ℚ)) : ℂ)) = (M : ℂ) * (2 * π * I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I M
  rw [this, mul_one]

end Product

section Groups

variable {G α : Type} [AddCommGroup G]

theorem finite_image_of_fg {A : AddSubgroup G} (hA : A.FG) (f : G → α) {N : ℕ} (hN : 0 < N)
    (hf : ∀ a ∈ A, ∀ b ∈ A, f (a + N • b) = f a) : (f '' A).Finite := by
  classical
  obtain ⟨S, hS⟩ := hA
  have hspan : ∀ x, x ∈ A ↔ x ∈ Submodule.span ℤ (S : Set G) := fun x => by
    rw [← hS, ← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup]
  have hmemS : ∀ d : S → ℤ, (∑ s : S, d s • (s : G)) ∈ A := fun d =>
    (hspan _).2 (Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span s.2))
  let rep : (S → Fin N) → G := fun d => ∑ s : S, (((d s : ℕ) : ℤ)) • (s : G)
  refine (Set.finite_range (f ∘ rep)).subset ?_
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_finset'.1 ((hspan a).1 ha)
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have hnn : ∀ s, 0 ≤ c s % (N : ℤ) := fun s => Int.emod_nonneg _ hN'.ne'
  refine ⟨fun s => ⟨(c s % (N : ℤ)).toNat, ?_⟩, ?_⟩
  · have h1 := Int.emod_lt_of_pos (c s) hN'
    have h0 := hnn s
    omega
  · have hdec : a = (∑ s : S, (c s % (N : ℤ)) • (s : G)) + N • ∑ s : S, (c s / (N : ℤ)) • (s : G) := by
      rw [← hc, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← natCast_zsmul, smul_smul, ← add_smul]
      congr 1
      rw [Int.emod_add_mul_ediv]
    have e : rep (fun s => ⟨(c s % (N : ℤ)).toNat, by
        have h1 := Int.emod_lt_of_pos (c s) hN'
        have h0 := hnn s
        omega⟩) = ∑ s : S, (c s % (N : ℤ)) • (s : G) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Int.toNat_of_nonneg (hnn s)]
    show f (rep _) = f a
    rw [e, hdec]
    exact (hf _ (hmemS _) _ (hmemS _)).symm

theorem ncard_image_eq {A A' : AddSubgroup G} (f : G → α)
    (hf : ∀ a ∈ A, ∀ b ∈ A, f a = f b ↔ -a + b ∈ A') : (f '' A).ncard = A'.relIndex A := by
  rw [← Nat.card_coe_set_eq, AddSubgroup.relIndex, AddSubgroup.index]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.lift (fun a : A => (⟨f a, a, a.2, rfl⟩ : f '' A)) ?_) ⟨?_, ?_⟩)
  · intro a b hab
    have h1 : -(a : G) + b ∈ A' := by
      have := QuotientAddGroup.leftRel_apply.1 hab
      simpa [AddSubgroup.mem_addSubgroupOf] using this
    exact Subtype.ext ((hf a a.2 b b.2).2 h1)
  · intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y
    have h1 := congrArg Subtype.val hxy
    have h2 : f a = f b := h1
    refine QuotientAddGroup.eq.2 ?_
    rw [AddSubgroup.mem_addSubgroupOf]
    simpa using (hf a a.2 b b.2).1 h2
  · rintro ⟨_, a, ha, rfl⟩
    exact ⟨QuotientAddGroup.mk ⟨a, ha⟩, rfl⟩

end Groups

section Main

variable {κ ι : Type} [Fintype κ] [Fintype ι]

abbrev Position := Matrix κ ι ℚ × Matrix κ ι ℚ
abbrev TestFunction := Matrix κ ι ℚ → ℂ

def omega (y y' : Position (κ := κ) (ι := ι)) : ℚ :=
  ∑ k, (y.1 k ⬝ᵥ y'.2 k - y'.1 k ⬝ᵥ y.2 k)

theorem omega_swap (y y' : Position (κ := κ) (ι := ι)) : omega y' y = -omega y y' := by
  simp only [omega, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

@[simp] theorem omega_self (y : Position (κ := κ) (ι := ι)) : omega y y = 0 := by
  simp [omega]

def heis (y : Position (κ := κ) (ι := ι)) (φ : TestFunction (κ := κ) (ι := ι)) :=
  heisS y.1 y.2 φ

theorem heis_smul (y : Position (κ := κ) (ι := ι)) (c : ℂ) (φ : (TestFunction (κ := κ) (ι := ι))) :
    heis y (c • φ) = c • heis y φ := by
  funext x
  simp only [heis, heisS, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem heis_sum (y : Position (κ := κ) (ι := ι)) (s : Finset (TestFunction (κ := κ) (ι := ι))) :
    heis y (∑ φ ∈ s, φ) = ∑ φ ∈ s, heis y φ := by
  funext x
  simp only [heis, heisS, Finset.sum_apply, Finset.sum_mul]

/-- The exact algebraic properties supplied by a self-dual lattice and
its common integral quadratic phase. -/
def Good (ε : Position (κ := κ) (ι := ι) → ℂ) (A : AddSubgroup (Position (κ := κ) (ι := ι))) : Prop :=
  A.FG ∧ (∀ y, y ∈ A ↔ ∀ y' ∈ A, ∃ k : ℤ, omega y y' = k) ∧
    ∀ y ∈ A, ε y ^ 2 = 1 ∧ ∀ y' ∈ A,
      ε (y + y') = ε y * ε y' * cexp (π * I * ((omega y y' : ℚ) : ℂ))

def IsVac (ε : Position (κ := κ) (ι := ι) → ℂ) (A : AddSubgroup (Position (κ := κ) (ι := ι)))
    (v : (TestFunction (κ := κ) (ι := ι))) : Prop := IsSB v ∧ ip v v = 1 ∧ ∀ y ∈ A, ε y • heis y v = v

/-- The actual finite-orbit average, with its actual cardinal denominator. -/
def projA (ε : Position (κ := κ) (ι := ι) → ℂ) (A : AddSubgroup (Position (κ := κ) (ι := ι)))
    (φ : (TestFunction (κ := κ) (ι := ι))) : (TestFunction (κ := κ) (ι := ι)) :=
  ((((fun y => ε y • heis y φ) '' A).ncard : ℕ) : ℂ)⁻¹ •
    ∑ᶠ ψ ∈ (fun y => ε y • heis y φ) '' A, ψ

variable {ε : Position (κ := κ) (ι := ι) → ℂ} {A A' : AddSubgroup (Position (κ := κ) (ι := ι))}

theorem Good.eps_two (hA : Good ε A) {y} (hy : y ∈ A) : ε (2 • y) = 1 := by
  rw [two_nsmul, (hA.2.2 y hy).2 y hy, omega_self]
  simp only [Rat.cast_zero, mul_zero, Complex.exp_zero, mul_one]
  rw [← sq]
  exact (hA.2.2 y hy).1

theorem Good.vac (hA : Good ε A) : ∃ v : (TestFunction (κ := κ) (ι := ι)), IsVac ε A v ∧
    ∀ v', IsSB v' → (∀ y ∈ A, ε y • heis y v' = v') → ∃ c : ℂ, v' = c • v := by
  have hnorm : ∀ y ∈ A, ‖ε y‖ = 1 := by
    intro y hy
    have h2 := congrArg norm (hA.2.2 y hy).1
    rw [norm_pow, norm_one] at h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  obtain ⟨v, hv1, hv2, hv3, hv4⟩ := Vac.vacuum κ ι A ε hA.1 hA.2.1
    hnorm (fun y hy => (hA.2.2 y hy).2) ⟨2, two_pos, fun y hy => hA.eps_two hy⟩
  exact ⟨v, ⟨hv1, hv2, hv3⟩, hv4⟩

theorem Good.uniq (hA : Good ε A) {v v' : (TestFunction (κ := κ) (ι := ι))} (hv : IsVac ε A v)
    (hv' : IsSB v') (h : ∀ y ∈ A, ε y • heis y v' = v') : v' = ip v' v • v := by
  obtain ⟨v₀, hv₀, huniq⟩ := Good.vac hA
  obtain ⟨c, rfl⟩ := huniq v hv.1 hv.2.2
  obtain ⟨c', rfl⟩ := huniq v' hv' h
  have h1 := hv.2.1
  rw [ip_smul_left c hv₀.1 (sb_smul c hv₀.1), ip_smul_right c hv₀.1 hv₀.1, hv₀.2.1] at h1
  rw [ip_smul_left c' hv₀.1 (sb_smul c hv₀.1), ip_smul_right c hv₀.1 hv₀.1, hv₀.2.1,
    smul_smul]
  congr 1
  linear_combination -c' * h1

theorem laws (y : Position (κ := κ) (ι := ι)) {φ : (TestFunction (κ := κ) (ι := ι))} (hφ : IsSB φ) :
    IsSB (heis y φ) ∧ heis 0 φ = φ ∧
      (∀ y', heis y (heis y' φ) =
        cexp (π * I * ((omega y y' : ℚ) : ℂ)) • heis (y + y') φ) ∧
      ∀ ψ, IsSB ψ → ip (heis y φ) (heis y ψ) = ip φ ψ := by
  obtain ⟨h1, _, h3, h4, h5⟩ := heisS_laws κ ι y.1 y.2 φ hφ
  exact ⟨h1, h4, fun y' => h3 y'.1 y'.2, h5⟩

theorem rho_sb (y : Position (κ := κ) (ι := ι)) {φ : (TestFunction (κ := κ) (ι := ι))} (hφ : IsSB φ) :
    IsSB (ε y • heis y φ) := sb_smul _ (laws y hφ).1

theorem rho_zero (hε0 : ε 0 = 1) {φ : (TestFunction (κ := κ) (ι := ι))} (hφ : IsSB φ) :
    ε 0 • heis 0 φ = φ := by
  rw [hε0, one_smul]
  exact (laws 0 hφ).2.1

theorem rho_ip (hεunit : ∀ y, ε y * conj (ε y) = 1)
    (y : Position (κ := κ) (ι := ι)) {φ ψ : (TestFunction (κ := κ) (ι := ι))} (hφ : IsSB φ) (hψ : IsSB ψ) :
    ip (ε y • heis y φ) (ε y • heis y ψ) = ip φ ψ := by
  obtain ⟨h1, _, _, h4⟩ := laws y hφ
  have h1' := (laws y hψ).1
  rw [ip_smul_left _ h1 (sb_smul _ h1'), ip_smul_right _ h1 h1', ← mul_assoc,
    hεunit, one_mul, h4 ψ hψ]

theorem Good.rho_rho (hA : Good ε A) {y y'} (hy : y ∈ A) (hy' : y' ∈ A)
    {φ : (TestFunction (κ := κ) (ι := ι))} (hφ : IsSB φ) :
    ε y • heis y (ε y' • heis y' φ) = ε (y + y') • heis (y + y') φ := by
  rw [heis_smul, (laws y hφ).2.2.1 y', smul_smul, smul_smul, (hA.2.2 y hy).2 y' hy']

theorem Good.finite (hA : Good ε A) {φ : (TestFunction (κ := κ) (ι := ι))} (hφ : IsSB φ) :
    ((fun y => ε y • heis y φ) '' A).Finite := by
  obtain ⟨R, hR, hlev⟩ := hφ
  obtain ⟨D1, hD1, hD1'⟩ := Vac.exists_den_fg
    (A.map (AddMonoidHom.fst _ _)) (Vac.fg_map hA.1 _)
  obtain ⟨D2, hD2, hD2'⟩ := Vac.exists_den_fg
    (A.map (AddMonoidHom.snd _ _)) (Vac.fg_map hA.1 _)
  have hint : ∀ b ∈ A, IntM (((D1 * D2 : ℕ) : ℚ) • b.1) ∧
      IntM (((D1 * D2 : ℕ) : ℚ) • b.2) := by
    intro b hb
    have h1 := hD1' _ (AddSubgroup.mem_map_of_mem _ hb)
    have h2 := hD2' _ (AddSubgroup.mem_map_of_mem _ hb)
    constructor
    · have := Vac.intM_smul D2 h1
      rwa [smul_smul, ← Nat.cast_mul, mul_comm D2 D1] at this
    · have := Vac.intM_smul D1 h2
      rwa [smul_smul, ← Nat.cast_mul] at this
  have hc : ∀ x : Matrix κ ι ℚ,
      (2 * (R * (D1 * D2))) • x =
        ((2 * R : ℕ) : ℚ) • (((D1 * D2 : ℕ) : ℚ) • x) := fun x => by
    rw [smul_smul, ← Nat.cast_smul_eq_nsmul ℚ]
    congr 1
    push_cast
    ring
  refine finite_image_of_fg hA.1 _ (N := 2 * (R * (D1 * D2))) (by positivity)
    fun a ha b hb => ?_
  have hNb : (2 * (R * (D1 * D2))) • b ∈ A := AddSubgroup.nsmul_mem _ hb _
  have hfix : ε ((2 * (R * (D1 * D2))) • b) •
      heis ((2 * (R * (D1 * D2))) • b) φ = φ := by
    have he : ε ((2 * (R * (D1 * D2))) • b) = 1 := by
      rw [← smul_smul]
      exact Good.eps_two hA (AddSubgroup.nsmul_mem _ hb _)
    rw [he, one_smul]
    change heisS ((2 * (R * (D1 * D2))) • b.1)
      ((2 * (R * (D1 * D2))) • b.2) φ = φ
    rw [hc, hc]
    exact heisS_fix hlev (hint b hb).1 (hint b hb).2
  change ε (a + _) • heis (a + _) φ = ε a • heis a φ
  rw [← Good.rho_rho hA ha hNb ⟨R, hR, hlev⟩, hfix]

theorem Good.proj (hε0 : ε 0 = 1) (hεunit : ∀ y, ε y * conj (ε y) = 1) (hA : Good ε A) {φ v : (TestFunction (κ := κ) (ι := ι))} (hφ : IsSB φ) (hv : IsVac ε A v) :
    IsSB (projA ε A φ) ∧ projA ε A φ = ip φ v • v := by
  set O := (fun y => ε y • heis y φ) '' (A : Set ((Position (κ := κ) (ι := ι)))) with hO
  have hfin : O.Finite := Good.finite hA hφ
  have hmemO : ∀ ψ ∈ hfin.toFinset, IsSB ψ := by
    intro ψ hψ
    rw [Set.Finite.mem_toFinset] at hψ
    obtain ⟨y, -, rfl⟩ := hψ
    exact rho_sb y hφ
  obtain ⟨hsum, hip⟩ := sum_sb_ip hfin.toFinset hmemO hv.1
  have hipφ : ∀ ψ ∈ hfin.toFinset, ip ψ v = ip φ v := by
    intro ψ hψ
    rw [Set.Finite.mem_toFinset] at hψ
    obtain ⟨y, hy, rfl⟩ := hψ
    conv_lhs => rw [← hv.2.2 y hy]
    exact rho_ip hεunit y hφ hv.1
  rw [Finset.sum_congr rfl hipφ, Finset.sum_const, nsmul_eq_mul] at hip
  have hfix : ∀ z ∈ A, ε z • heis z (∑ ψ ∈ hfin.toFinset, ψ) = ∑ ψ ∈ hfin.toFinset, ψ := by
    intro z hz
    rw [heis_sum, Finset.smul_sum]
    refine Finset.sum_nbij' (fun ψ => ε z • heis z ψ)
      (fun ψ => ε (-z) • heis (-z) ψ) ?_ ?_ ?_ ?_ ?_
    · intro ψ hψ
      simp only [Set.Finite.mem_toFinset] at hψ ⊢
      obtain ⟨y, hy, rfl⟩ := hψ
      exact ⟨z + y, add_mem hz hy, (Good.rho_rho hA hz hy hφ).symm⟩
    · intro ψ hψ
      simp only [Set.Finite.mem_toFinset] at hψ ⊢
      obtain ⟨y, hy, rfl⟩ := hψ
      exact ⟨-z + y, add_mem (neg_mem hz) hy, (Good.rho_rho hA (neg_mem hz) hy hφ).symm⟩
    · intro ψ hψ
      have h1 := hmemO ψ hψ
      rw [Good.rho_rho hA (neg_mem hz) hz h1, neg_add_cancel, rho_zero hε0 h1]
    · intro ψ hψ
      have h1 := hmemO ψ hψ
      rw [Good.rho_rho hA hz (neg_mem hz) h1, add_neg_cancel, rho_zero hε0 h1]
    · intro ψ hψ; rfl
  have hU := Good.uniq hA hv hsum hfix
  have hcard : (hfin.toFinset.card : ℂ) ≠ 0 := by
    have h0 : φ ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]; exact ⟨0, zero_mem A, rho_zero hε0 hφ⟩
    exact_mod_cast (Finset.card_pos.2 ⟨φ, h0⟩).ne'
  have hproj : projA ε A φ = ((hfin.toFinset.card : ℂ))⁻¹ • ∑ ψ ∈ hfin.toFinset, ψ := by
    rw [projA, finsum_mem_eq_finite_toFinset_sum _ hfin, Set.ncard_eq_toFinset_card O hfin]
  refine ⟨hproj ▸ sb_smul _ hsum, ?_⟩
  rw [hproj, hU, hip, smul_smul, inv_mul_cancel_left₀ hcard]

theorem Good.ip_eq_zero (hεunit : ∀ y, ε y * conj (ε y) = 1) (hA : Good ε A) {v : (TestFunction (κ := κ) (ι := ι))} (hv : IsVac ε A v) {y}
    (hy : y ∉ A) : ip (ε y • heis y v) v = 0 := by
  have hnot : ¬ ∀ y' ∈ A, ∃ k : ℤ, omega y y' = k := fun H => hy ((hA.2.1 y).2 H)
  push Not at hnot
  obtain ⟨y', hy', hk⟩ := hnot
  have hvs := hv.1
  have hfix := hv.2.2 y' hy'
  obtain ⟨hHv, -, hc1, -⟩ := laws y hvs
  obtain ⟨-, -, hc2, -⟩ := laws y' hvs
  have hsu : IsSB (ε y • heis y v) := sb_smul _ hHv
  have hsw := omega_swap y y'
  set t : ℚ := omega y y' with ht
  have key : ε y' • heis y' (ε y • heis y v) =
      cexp (-(2 * π * I * t)) • (ε y • heis y v) := by
    have e1 : ε y' • heis y' (ε y • heis y v) =
        (ε y' * ε y * cexp (π * I * ((omega y' y : ℚ) : ℂ))) •
          heis (y' + y) v := by
      rw [heis_smul, hc2 y, smul_smul, smul_smul]
    have e2 : ε y • heis y v =
        (ε y * ε y' * cexp (π * I * ((omega y y' : ℚ) : ℂ))) •
          heis (y + y') v := by
      conv_lhs => rw [← hfix]
      rw [heis_smul, hc1 y', smul_smul, smul_smul]
    rw [e1, e2, smul_smul, add_comm y' y, hsw]
    congr 1
    have : cexp (↑π * I * ((-t : ℚ) : ℂ)) = cexp (-(2 * π * I * t)) * cexp (↑π * I * (t : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; ring
  have hl : cexp (-(2 * π * I * t)) ≠ 1 := by
    intro h1
    rw [Complex.exp_neg, inv_eq_one] at h1
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 h1
    apply hk m
    have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : ((t : ℚ) : ℂ) = (m : ℂ) := by
      apply mul_left_cancel₀ h2; rw [hm]; ring
    exact_mod_cast this
  have hip := rho_ip hεunit (ε := ε) y' hsu hvs
  rw [key, hfix, ip_smul_left _ hsu hvs] at hip
  have : (cexp (-(2 * π * I * t)) - 1) * ip (ε y • heis y v) v = 0 := by
    rw [sub_mul, hip, one_mul, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) hl
  · exact h

theorem Good.overlap (hε0 : ε 0 = 1) (hεunit : ∀ y, ε y * conj (ε y) = 1) (hA : Good ε A) (hA' : Good ε A') {v v' : (TestFunction (κ := κ) (ι := ι))}
    (hv : IsVac ε A v) (hv' : IsVac ε A' v') :
    (A'.relIndex A : ℝ) * ‖ip v v'‖ ^ 2 = 1 := by
  have hv's := hv'.1
  have hfin : ((fun y => ε y • heis y v') '' (A : Set ((Position (κ := κ) (ι := ι))))).Finite :=
    Good.finite hA hv's
  have hinv : ∀ z ∈ A, ∀ ψ, IsSB ψ →
      ε (-z) • heis (-z) (ε z • heis z ψ) = ψ := fun z hz ψ hψ => by
    rw [Good.rho_rho hA (neg_mem hz) hz hψ, neg_add_cancel, rho_zero hε0 hψ]
  have hstab : ∀ z ∈ A, ε z • heis z v' = v' ↔ z ∈ A' := by
    intro z hz
    constructor
    · intro h
      by_contra hz'
      have h0 := Good.ip_eq_zero hεunit hA' hv' hz'
      rw [h, hv'.2.1] at h0
      exact one_ne_zero h0
    · intro h; exact hv'.2.2 z h
  have hfeq : ∀ a ∈ A, ∀ b ∈ A, (fun y => ε y • heis y v') a =
      (fun y => ε y • heis y v') b ↔ -a + b ∈ A' := by
    intro a ha b hb
    simp only
    have hc : -a + b ∈ A := add_mem (neg_mem ha) hb
    constructor
    · intro h
      rw [← hstab _ hc, ← Good.rho_rho hA (neg_mem ha) hb hv's, ← h, hinv a ha v' hv's]
    · intro h
      conv_rhs => rw [show b = a + (-a + b) by abel]
      rw [← Good.rho_rho hA ha hc hv's, hv'.2.2 _ h]
  set T := hfin.toFinset with hT
  have hmemT : ∀ ψ ∈ T, IsSB ψ := by
    intro ψ hψ
    rw [hT, Set.Finite.mem_toFinset] at hψ
    obtain ⟨y, -, rfl⟩ := hψ
    exact rho_sb y hv's
  have horth : ∀ χ ∈ T, ∀ ψ ∈ T, ip χ ψ = if χ = ψ then 1 else 0 := by
    intro χ hχ ψ hψ
    rw [hT, Set.Finite.mem_toFinset] at hχ hψ
    obtain ⟨b, hb, rfl⟩ := hχ
    obtain ⟨a, ha, rfl⟩ := hψ
    have hb' := rho_sb b hv's (ε := ε)
    have ha' := rho_sb a hv's (ε := ε)
    rw [← rho_ip hεunit (-a) hb' ha', hinv a ha v' hv's,
      Good.rho_rho hA (neg_mem ha) hb hv's]
    have hc : -a + b ∈ A := add_mem (neg_mem ha) hb
    by_cases h : -a + b ∈ A'
    · rw [hv'.2.2 _ h, hv'.2.1, ite_eq_left (((hfeq a ha b hb).2 h).symm)]
    · rw [Good.ip_eq_zero hεunit hA' hv' h, ite_eq_right]
      intro he
      exact h ((hfeq a ha b hb).1 he.symm)
  obtain ⟨hS, -⟩ := sum_sb_ip T hmemT hv's
  have hSψ : ∀ ψ ∈ T, ip (∑ χ ∈ T, χ) ψ = 1 := by
    intro ψ hψ
    rw [(sum_sb_ip T hmemT (hmemT ψ hψ)).2, Finset.sum_congr rfl fun χ hχ => horth χ hχ ψ hψ,
      Finset.sum_ite_eq', ite_eq_left hψ]
  have hSS : ip (∑ χ ∈ T, χ) (∑ χ ∈ T, χ) = T.card := by
    rw [(sum_sb_ip T hmemT hS).2, Finset.sum_congr rfl fun ψ hψ => by
      rw [ip_conj hS (hmemT ψ hψ), hSψ ψ hψ, map_one], Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (T.card : ℂ) ≠ 0 := by
    have h0 : v' ∈ T := by
      rw [hT, Set.Finite.mem_toFinset]; exact ⟨0, zero_mem A, rho_zero hε0 hv's⟩
    exact_mod_cast (Finset.card_pos.2 ⟨v', h0⟩).ne'
  have hproj : projA ε A v' = ((T.card : ℂ))⁻¹ • ∑ ψ ∈ T, ψ := by
    rw [projA, finsum_mem_eq_finite_toFinset_sum _ hfin, Set.ncard_eq_toFinset_card _ hfin]
  have hP := (Good.proj hε0 hεunit hA hv's hv).2
  have e1 := congrArg (fun ψ => ip ψ ψ) hP
  rw [hproj, ip_smul_left _ hS (sb_smul _ hS), ip_smul_right _ hS hS, hSS,
    ip_smul_left _ hv.1 (sb_smul _ hv.1), ip_smul_right _ hv.1 hv.1, hv.2.1] at e1
  have e2 : ip v' v * conj (ip v' v) = ((T.card : ℂ))⁻¹ := by
    have : conj ((T.card : ℂ)⁻¹) = (T.card : ℂ)⁻¹ := by simp
    rw [this, inv_mul_cancel₀ hcard, mul_one, mul_one] at e1
    exact e1.symm
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at e2
  have e3 : ‖ip v' v‖ ^ 2 = ((T.card : ℝ))⁻¹ := Complex.ofReal_injective (by rw [e2]; simp)
  have hcr : (T.card : ℝ) ≠ 0 := by exact_mod_cast hcard
  rw [← ncard_image_eq _ hfeq, Set.ncard_eq_toFinset_card _ hfin, ← hT, ip_conj hv's hv.1,
    Complex.norm_conj, e3, mul_inv_cancel₀ hcr]


end Main

end RHLean.Geometry.NativeTheta.Cusp.FiniteOverlap

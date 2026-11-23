import RHLean.Geometry.NativeThetaCuspFiniteLevel
import RHLean.Geometry.NativeThetaCuspTensorVacua
import RHLean.Geometry.NativeThetaCuspSeriesHolomorphic
import RHLean.Geometry.NativeThetaCuspWeil

/-!
# Exact Haar norm of the full finite level theta family

The finite theta vector is the sum of actual Heisenberg translates of the
constructed shifted tensor vacuum. Its translate representatives are lifted
from every invertible matrix over the actual split-five quotient. Their
orthogonality is proved from the self-dual tensor lattice and the distinct
quotient columns. Consequently its exact squared norm is the cardinality of
that full finite group, for every auxiliary lattice in the original family.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LevelTestFunctionFiniteSumEquivariant.lean
(`what₂`, finite representative construction), and
src/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThetaTestFunctionNormAndOverlapBound.lean
(`sum_left`, `ip_sum_diag`, `phi_norm_overlap`). The construction uses the
full-GL trivial-character instance and the already proved native tensor
vacua. It does not identify this analytic family with a geometric cover's
coefficient-matched character or claim Petersson normalization. The source
mirror states no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField Module Matrix Complex
open scoped Pointwise BigOperators Classical ComplexConjugate Real

namespace RHLean.Geometry.NativeTheta.Cusp.FiniteLevelNorm

open FiniteOverlap

section Gram

variable {κ ι α : Type} [Fintype κ] [Fintype ι]

theorem sum_left (s : Finset α) (f : α → Matrix κ ι ℚ → ℂ) {ψ : Matrix κ ι ℚ → ℂ}
    (hs : ∀ a ∈ s, IsSB (f a)) (hψ : IsSB ψ) :
    IsSB (∑ a ∈ s, f a) ∧ ip (∑ a ∈ s, f a) ψ = ∑ a ∈ s, ip (f a) ψ := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨isSB_zero, ?_⟩
    simpa using (ip_smul_left 0 hψ hψ)
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun b hb => hs b (Finset.mem_insert_of_mem hb)
    have h3 := hs a (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ip_add_left h3 h1 hψ, h2]
    exact ⟨(isSB_algebra_haar_linear ℚ κ ι _ _ h3 h1).1, rfl⟩

theorem ip_sum_diag (s : Finset α) (f f' : α → Matrix κ ι ℚ → ℂ)
    (hf : ∀ a ∈ s, IsSB (f a)) (hf' : ∀ a ∈ s, IsSB (f' a))
    (h : ∀ a ∈ s, ∀ b ∈ s, ip (f a) (f' b) ≠ 0 → a = b) :
    ip (∑ a ∈ s, f a) (∑ a ∈ s, f' a) = ∑ a ∈ s, ip (f a) (f' a) := by
  rw [(sum_left s f hf (sum_left s f' hf' isSB_zero).1).2]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [ip_conj (sum_left s f' hf' isSB_zero).1 (hf a ha),
    (sum_left s f' hf' (hf a ha)).2, map_sum,
    Finset.sum_eq_single_of_mem a ha, ← ip_conj (hf' a ha) (hf a ha)]
  intro b hb hba
  rw [← ip_conj (hf' b hb) (hf a ha)]
  by_contra h0
  exact hba (h a ha b hb h0).symm

theorem heis_neg_heis {v : Matrix κ ι ℚ → ℂ} (hv : IsSB v)
    (y : Position (κ := κ) (ι := ι)) : heis (-y) (heis y v) = v := by
  have hz : omega (-y) y = 0 := by simp [omega, dotProduct]
  rw [(laws (-y) hv).2.2.1 y, hz, Rat.cast_zero, mul_zero, Complex.exp_zero,
    one_smul, neg_add_cancel, (laws 0 hv).2.1]

/-- Off-diagonal translates are orthogonal because their actual difference
is outside the self-dual vacuum lattice. -/
theorem translated_ip_eq_zero
    {ε : Position (κ := κ) (ι := ι) → ℂ}
    {A : AddSubgroup (Position (κ := κ) (ι := ι))}
    (hε : ∀ y, ε y * conj (ε y) = 1) (hA : Good ε A)
    {v : Matrix κ ι ℚ → ℂ} (hv : IsVac ε A v)
    {y y' : Position (κ := κ) (ι := ι)} (hy : y - y' ∉ A) :
    ip (heis y v) (heis y' v) = 0 := by
  have h0 := Good.ip_eq_zero hε hA hv hy
  rw [ip_smul_left _ (laws (y - y') hv.1).1 hv.1] at h0
  have hε0 : ε (y - y') ≠ 0 := by
    intro h
    have he := hε (y - y')
    rw [h, zero_mul] at he
    exact zero_ne_one he
  have h0' : ip (heis (y - y') v) v = 0 := (mul_eq_zero.mp h0).resolve_left hε0
  have hu := (laws (-y') (laws y hv.1).1).2.2.2 _ (laws y' hv.1).1
  rw [heis_neg_heis hv, (laws (-y') hv.1).2.2.1 y,
    show -y' + y = y - y' by abel,
    ip_smul_left _ (laws (y - y') hv.1).1 hv.1, h0', mul_zero] at hu
  exact hu.symm

/-- The full finite orbit contributes its exact cardinal mass. -/
theorem finite_translates_norm [Fintype α]
    {ε : Position (κ := κ) (ι := ι) → ℂ}
    {A : AddSubgroup (Position (κ := κ) (ι := ι))}
    (hε : ∀ y, ε y * conj (ε y) = 1) (hA : Good ε A)
    {v : Matrix κ ι ℚ → ℂ} (hv : IsVac ε A v)
    (y : α → Position (κ := κ) (ι := ι))
    (hsep : ∀ a b, y a - y b ∈ A → a = b) :
    IsSB (∑ a, heis (y a) v) ∧
      ip (∑ a, heis (y a) v) (∑ a, heis (y a) v) = (Nat.card α : ℂ) := by
  have hs : ∀ a ∈ (Finset.univ : Finset α), IsSB (heis (y a) v) :=
    fun a _ => (laws (y a) hv.1).1
  refine ⟨(sum_left Finset.univ _ hs isSB_zero).1, ?_⟩
  rw [ip_sum_diag Finset.univ _ _ hs hs (fun a _ b _ hab => ?_)]
  · simp only [(laws _ hv.1).2.2.2 v hv.1, hv.2.1, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]
  · by_contra hne
    exact hab (translated_ip_eq_zero hε hA hv (fun hm => hne (hsep a b hm)))

/-- The source normalization uses the actual Haar squared norm. -/
def unitv (v : Matrix κ ι ℚ → ℂ) : Matrix κ ι ℚ → ℂ :=
  ((Real.sqrt (ip v v).re : ℂ))⁻¹ • v

theorem isVac_smul
    {ε : Position (κ := κ) (ι := ι) → ℂ}
    {A : AddSubgroup (Position (κ := κ) (ι := ι))}
    {v : Matrix κ ι ℚ → ℂ} (hv : IsVac ε A v) {c : ℂ} (hc : ‖c‖ = 1) :
    IsVac ε A (c • v) := by
  refine ⟨sb_smul c hv.1, ?_, fun y hy => ?_⟩
  · rw [ip_smul_left c hv.1 (sb_smul c hv.1), ip_smul_right c hv.1 hv.1,
      hv.2.1, mul_one, Complex.mul_conj', hc]
    simp
  · rw [heis_smul, smul_comm, hv.2.2 y hy]

theorem unitv_smul
    {ε : Position (κ := κ) (ι := ι) → ℂ}
    {A : AddSubgroup (Position (κ := κ) (ι := ι))}
    {v : Matrix κ ι ℚ → ℂ} (hv : IsVac ε A v) (c : ℂ) :
    unitv (c • v) = (c / ‖c‖) • v := by
  rw [unitv, ip_smul_left c hv.1 (sb_smul c hv.1), ip_smul_right c hv.1 hv.1,
    hv.2.1, mul_one, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re,
    Real.sqrt_sq (norm_nonneg c), smul_smul, div_eq_inv_mul]

/-- Normalized finite projection transports the same base vacuum to the
other actual self-dual lattice. Nonvanishing follows from the exact index
overlap, rather than being an extra hypothesis. -/
theorem normalized_projection_vac
    {ε : Position (κ := κ) (ι := ι) → ℂ}
    {A₀ A : AddSubgroup (Position (κ := κ) (ι := ι))}
    (hε0 : ε 0 = 1) (hε : ∀ y, ε y * conj (ε y) = 1)
    (hA₀ : Good ε A₀) (hA : Good ε A)
    {v₀ : Matrix κ ι ℚ → ℂ} (hv₀ : IsVac ε A₀ v₀) :
    IsVac ε A (unitv (projA ε A v₀)) := by
  obtain ⟨v, hv, -⟩ := Good.vac hA
  have hip : ip v₀ v ≠ 0 := by
    intro hz
    have h := Good.overlap hε0 hε hA₀ hA hv₀ hv
    simp [hz] at h
  rw [(Good.proj hε0 hε hA hv₀.1 hv).2, unitv_smul hv]
  apply isVac_smul hv
  rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr hip)]

end Gram

open RHLean.Analysis.AlpogeThin
open Formalism.HC Formalism.FrobeniusOrbits NativeRawHostPolarization
open NativePrescribedHermitian NativeIntegralSymplectic
open AuxiliaryLattices TensorLattices ShiftedLattice FiniteLevel

variable {φ : Frame} (H : HostRaw φ)

section Integral

variable {r n : ℕ} {L : Lt H.E r} (D : FullLevel H L)

theorem cop_nat {s : ℕ} (hs : s.Coprime 5) :
    IsCoprime (Ideal.span {(s : 𝓞 H.E)}) D.P := by
  obtain ⟨a, b, hab⟩ : IsCoprime (s : ℤ) (5 : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr hs
  refine Ideal.isCoprime_iff_exists.mpr
    ⟨a * s, Ideal.mul_mem_left _ _ (Ideal.subset_span rfl),
      b * 5, Ideal.mul_mem_left _ _ D.five_mem, ?_⟩
  exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 H.E) hab

theorem mem_of_coprime_multiple {s : 𝓞 H.E} {x : Fin r → H.E}
    (hx : x ∈ L) (hs : IsCoprime (Ideal.span {s}) D.P)
    (hsx : s • x ∈ D.P • L) : x ∈ D.P • L := by
  obtain ⟨a, ha, p, hp, hap⟩ := Ideal.isCoprime_iff_exists.mp hs
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  rw [← one_smul (𝓞 H.E) x, ← hap, add_smul, mul_smul]
  exact add_mem ((D.P • L).smul_mem _ hsx) (Submodule.smul_mem_smul hp hx)

theorem mem_level_of_mem_shift {x : Fin r → H.E} (hx : x ∈ L)
    (hshift : x ∈ idq D.P (H.conj • D.P) L) : x ∈ D.P • L := by
  obtain ⟨p, hp, c, hc, hpc⟩ := Ideal.isCoprime_iff_exists.mp D.cop
  rw [← one_smul (𝓞 H.E) x, ← hpc, add_smul]
  exact add_mem (Submodule.smul_mem_smul hp hx) (hshift c hc)

/-- One actual congruence multiplier simultaneously clears every tensor
row and puts every integral row matrix into the auxiliary tensor lattice. -/
theorem tensor_clear_and_scale {Λ : Lt H.E n} (hΛ : Λ ∈ Vset H n 5) :
    ∃ s : ℕ, 0 < s ∧ s.Coprime 5 ∧
      (∀ (N : Lt H.E r) (y : Matrix (Fin n) (Fin r) H.E),
        y ∈ tens Λ N → ∀ i, (s : 𝓞 H.E) • y i ∈ N) ∧
      ∀ (N : Lt H.E r) (y : Matrix (Fin n) (Fin r) H.E),
        (∀ i, y i ∈ N) → (s : H.E) • y ∈ tens Λ N := by
  obtain ⟨s, hs, hcop, _, h2⟩ := hΛ.2.2
  refine ⟨s, hs, hcop, fun N y hy i => ?_, fun N y hy => ?_⟩
  · have ht := (mem_tens_iff H hΛ N y).mp hy
      ((s : H.E) • Pi.single i 1) (h2 _ (Submodule.subset_span ⟨i, rfl⟩))
    have he : ctr H y ((s : H.E) • Pi.single i 1) = (s : 𝓞 H.E) • y i := by
      ext j
      simp [ctr, Finset.sum_apply, Algebra.smul_def]
    rwa [he] at ht
  · let A := (tens Λ N).comap
      (DistribSMul.toAddMonoidHom (Matrix (Fin n) (Fin r) H.E) (s : H.E))
    have ht : tens (stdL H n) N ≤ A := tens_le fun v hv u hu => by
      change (s : H.E) • vecMulVec v u ∈ tens Λ N
      rw [← smul_vecMulVec]
      exact pure_mem (h2 v hv) hu
    exact ht ((mem_tens_stdL H N y).mpr hy)

/-- The integral columns occupy the first r rows; the remaining rows
vanish exactly as in the source finite level coefficient. -/
def rows (C : Ideal (𝓞 H.E)) (hC : IsCoprime D.P C) (a : D.Group) :
    Matrix (Fin n) (Fin r) H.E := fun i =>
  if hi : i.val < r then D.liftColumn C hC a ⟨i.val, hi⟩ else 0

theorem rows_mem (C : Ideal (𝓞 H.E)) (hC : IsCoprime D.P C)
    (a : D.Group) (i : Fin n) : rows H D C hC a i ∈ C • L := by
  unfold rows
  split_ifs with hi
  · exact D.liftColumn_mem C hC a _
  · exact zero_mem _

theorem rows_castLE (hn : r ≤ n) (C : Ideal (𝓞 H.E)) (hC : IsCoprime D.P C)
    (a : D.Group) (i : Fin r) :
    rows H D C hC a (Fin.castLE hn i) =
      (D.liftColumn C hC a i : Fin r → H.E) := by
  simp only [rows, Fin.coe_castLE, dite_eq_left i.isLt]

theorem rows_tensor {Λ : Lt H.E n} {s : ℕ}
    (hscale : ∀ (N : Lt H.E r) (y : Matrix (Fin n) (Fin r) H.E),
      (∀ i, y i ∈ N) → (s : H.E) • y ∈ tens Λ N)
    (C : Ideal (𝓞 H.E))
    (hC : IsCoprime D.P (C * Ideal.span {(s : 𝓞 H.E)})) (a : D.Group) :
    rows H D (C * Ideal.span {(s : 𝓞 H.E)}) hC a ∈ tens Λ (C • L) := by
  have hl (i : Fin n) : ∃ z ∈ C • L,
      (s : 𝓞 H.E) • z = rows H D (C * Ideal.span {(s : 𝓞 H.E)}) hC a i := by
    have hi := rows_mem H D (C * Ideal.span {(s : 𝓞 H.E)}) hC a i
    rw [mul_comm C, Submodule.mul_smul, Submodule.ideal_span_singleton_smul] at hi
    exact Submodule.mem_smul_pointwise_iff_exists.mp hi
  choose z hz he using hl
  have heq : rows H D (C * Ideal.span {(s : 𝓞 H.E)}) hC a = (s : H.E) • z := by
    ext i j
    exact (congrFun (he i) j).symm
  rw [heq]
  exact hscale _ z hz

/-- Distinct full quotient matrices cannot differ by a vector in the
actual shifted auxiliary tensor lattice. -/
theorem rows_separate {Λ : Lt H.E n} {s : ℕ} (hs : s.Coprime 5)
    (hclear : ∀ (N : Lt H.E r) (y : Matrix (Fin n) (Fin r) H.E),
      y ∈ tens Λ N → ∀ i, (s : 𝓞 H.E) • y i ∈ N)
    (hn : r ≤ n) (C : Ideal (𝓞 H.E)) (hC : IsCoprime D.P C)
    (a a' : D.Group)
    (h : rows H D C hC a - rows H D C hC a' ∈ tens Λ (idq D.P (H.conj • D.P) L)) :
    a = a' := by
  apply D.column_injective
  intro i
  rw [← D.liftColumn_mk C hC a i, ← D.liftColumn_mk C hC a' i]
  apply Submodule.Quotient.eq.mpr
  apply (mem_ideal_smul_top L D.P _).mpr
  have hx : (D.liftColumn C hC a i : Fin r → H.E) -
      (D.liftColumn C hC a' i : Fin r → H.E) ∈ L :=
    L.sub_mem (D.liftColumn C hC a i).2 (D.liftColumn C hC a' i).2
  apply mem_of_coprime_multiple H D hx (cop_nat H D hs)
  apply mem_level_of_mem_shift H D (L.smul_mem _ hx)
  have ht := hclear _ _ h (Fin.castLE hn i)
  change (s : 𝓞 H.E) •
    (rows H D C hC a (Fin.castLE hn i) - rows H D C hC a' (Fin.castLE hn i)) ∈ _ at ht
  rw [rows_castLE H D hn, rows_castLE H D hn] at ht
  exact ht

end Integral

section NativeFamily

variable [IsCMField H.E]
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (G : NativeGeometricHost H.E)
    (hΨ : ∀ τ : H.E →+* ℂ, G.InPsi τ ↔ τ ∈ H.cmType)
    (hconj : ∀ (τ : H.E →+* ℂ) (x : H.E), τ (H.conj x) = conj (τ x))
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m)
    {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Basis (ι ⊕ ι) ℤ (prescribedLattice H B k m))
    (hb : IsSymplecticBasis
      (prescribedGeometricDatum H B hB G hΨ hconj hbar k m j hk hj).EF b)
    (D : FullLevel H (prescribedLattice H B k m))

include hΨ hconj hbar hk hj hb in
omit [DecidableEq ι] in
theorem base_vacuum_exists :
    ∃ v : Matrix (Fin n) ι ℚ → ℂ,
      IsVac (ShiftedVacua.phase H B hB G k m j b)
        (TensorVacua.lattice H B hB k m b (stdL H n)
          (idq D.P (H.conj • D.P) (prescribedLattice H B k m))) v := by
  have hL := twisted_selfDual H B hB (negTail (k + m - 1) (m - j))
  have hL' := selfDual_idq H (negTail (k + m - 1) (m - j))
    D.ne_bot D.proper D.cop hL
  exact (Good.vac (TensorVacua.good_tensor H B hB G
    hΨ hconj hbar k m j hk hj b hb (stdL_mem_Vset H n 5) hL')).imp fun v hv => hv.1

omit [DecidableEq ι] in
/-- One base vacuum is fixed before the auxiliary lattice varies. -/
def baseVacuum : Matrix (Fin n) ι ℚ → ℂ :=
  Classical.choose (base_vacuum_exists H B hB G hΨ hconj hbar k m j hk hj b hb D)

omit [DecidableEq ι] in
theorem baseVacuum_spec :
    IsVac (ShiftedVacua.phase H B hB G k m j b)
      (TensorVacua.lattice H B hB k m b (stdL H n)
        (idq D.P (H.conj • D.P) (prescribedLattice H B k m)))
      (baseVacuum H B hB G hΨ hconj hbar k m j hk hj b hb D) :=
  Classical.choose_spec (base_vacuum_exists H B hB G hΨ hconj hbar k m j hk hj b hb D)

omit [IsCMField H.E] [DecidableEq ι] in
/-- The finite sum uses every element of the constructed full quotient
group and the original Heisenberg action in the common actual coordinates. -/
def thetaSum (y : D.Group → Matrix (Fin n) (Fin (k + m - 1)) H.E)
    (v : Matrix (Fin n) ι ℚ → ℂ) : Matrix (Fin n) ι ℚ → ℂ :=
  ∑ᶠ a : D.Group, heis (ShiftedVacua.coordinates H B hB b (y a)) v

include hΨ hconj hbar hk hj hb in
/-- Every auxiliary lattice has a genuine full-level theta vector, with
all quotient columns present, its exact Haar norm, a nonzero holomorphic
theta function and the proved rational symplectic transformation law. -/
theorem exists_full_level_theta (hn : k + m - 1 ≤ n) (heven : Even n)
    {Λ : Lt H.E n} (hΛ : Λ ∈ Vset H n 5) :
    ∃ (v : Matrix (Fin n) ι ℚ → ℂ)
      (y : D.Group → Matrix (Fin n) (Fin (k + m - 1)) H.E),
      IsVac (ShiftedVacua.phase H B hB G k m j b)
        (TensorVacua.lattice H B hB k m b Λ
          (idq D.P (H.conj • D.P) (prescribedLattice H B k m))) v ∧
      v = unitv (projA (ShiftedVacua.phase H B hB G k m j b)
        (TensorVacua.lattice H B hB k m b Λ
          (idq D.P (H.conj • D.P) (prescribedLattice H B k m)))
        (baseVacuum H B hB G hΨ hconj hbar k m j hk hj b hb D)) ∧
      (∀ a, y a ∈ tens Λ ((Ideal.span {(2 : 𝓞 H.E)} * (H.conj • D.P)) •
        prescribedLattice H B k m)) ∧
      (∀ a (i : Fin (k + m - 1)), ∃ x : prescribedLattice H B k m,
        y a (Fin.castLE hn i) = x ∧
          D.reduction x = fun t =>
            (a : Matrix (Fin (k + m - 1)) (Fin (k + m - 1)) (𝓞 H.E ⧸ D.P)) t i) ∧
      let f := thetaSum H B hB k m b D y v
      IsSB f ∧ ip f f = (Nat.card D.Group : ℂ) ∧
        (∀ τ ∈ Siegel ι, Differentiable ℂ (thS f τ) ∧ ∃ ζ, thS f τ ζ ≠ 0) ∧
        ∀ σ ∈ Matrix.symplecticGroup ι ℚ, ∃ f' : Matrix (Fin n) ι ℚ → ℂ,
          IsSB f' ∧ TransS σ f f' ∧ ip f' f' = (Nat.card D.Group : ℂ) := by
  let : Fintype D.Group := Fintype.ofFinite _
  let L := prescribedLattice H B k m
  let L' := idq D.P (H.conj • D.P) L
  let ε := ShiftedVacua.phase H B hB G k m j b (κ := Fin n)
  let A := TensorVacua.lattice H B hB k m b Λ L'
  let e := ShiftedVacua.coordinates H B hB b (κ := Fin n)
  have hL := twisted_selfDual H B hB (negTail (k + m - 1) (m - j))
  have hL' := selfDual_idq H (negTail (k + m - 1) (m - j))
    D.ne_bot D.proper D.cop hL
  have hA : Good ε A := TensorVacua.good_tensor H B hB G
    hΨ hconj hbar k m j hk hj b hb hΛ hL'
  have hA₀ : Good ε (TensorVacua.lattice H B hB k m b (stdL H n) L') :=
    TensorVacua.good_tensor H B hB G hΨ hconj hbar k m j hk hj b hb
      (stdL_mem_Vset H n 5) hL'
  have hε0 : ε 0 = 1 := ShiftedVacua.phase_zero H B hB G k m j b
  have hε : ∀ z, ε z * conj (ε z) = 1 :=
    ShiftedVacua.phase_mul_conj H B hB G k m j b
  let v := unitv (projA ε A (baseVacuum H B hB G hΨ hconj hbar k m j hk hj b hb D))
  have hv : IsVac ε A v := normalized_projection_vac hε0 hε hA₀ hA
    (baseVacuum_spec H B hB G hΨ hconj hbar k m j hk hj b hb D)
  obtain ⟨s, _, hs, hclear, hscale⟩ := tensor_clear_and_scale H hΛ
  let C : Ideal (𝓞 H.E) := Ideal.span {(2 : 𝓞 H.E)} * (H.conj • D.P)
  have hC : IsCoprime D.P (C * Ideal.span {(s : 𝓞 H.E)}) :=
    D.cop_two_conjugate.mul_right (cop_nat H D hs).symm
  let y : D.Group → Matrix (Fin n) (Fin (k + m - 1)) H.E :=
    rows H D (C * Ideal.span {(s : 𝓞 H.E)}) hC
  have hsep : ∀ a a', e (y a) - e (y a') ∈ A → a = a' := by
    intro a a' ha
    have hm : y a - y a' ∈ tens Λ L' := by
      apply (AddSubgroup.mem_map_iff_mem e.injective).mp
      simpa only [map_sub] using ha
    exact rows_separate H D hs hclear hn _ hC a a' hm
  obtain ⟨hsb, hip⟩ := finite_translates_norm hε hA hv (fun a => e (y a)) hsep
  have hf : IsSB (thetaSum H B hB k m b D y v) := by
    simpa only [thetaSum, finsum_eq_sum] using hsb
  have hnorm : ip (thetaSum H B hB k m b D y v) (thetaSum H B hB k m b D y v) =
      (Nat.card D.Group : ℂ) := by
    simpa only [thetaSum, finsum_eq_sum] using hip
  refine ⟨v, y, hv, rfl, fun a => rows_tensor H D hscale C hC a,
    fun a i => ?_, hf, hnorm, ?_, ?_⟩
  · refine ⟨D.liftColumn _ hC a i, rows_castLE H D hn _ hC a i, ?_⟩
    funext t
    exact D.liftColumn_reduction _ hC a i t
  · intro τ hτ
    refine ⟨ThetaHol.differentiable_thS hf hτ, ThetaHol.exists_thS_ne_zero hf ?_ hτ⟩
    intro hz
    have hzero : ip (0 : Matrix (Fin n) ι ℚ → ℂ) 0 = 0 := by
      simpa using (ip_smul_left (φ := 0) (ψ := 0) (0 : ℂ) isSB_zero isSB_zero)
    have hc : (Nat.card D.Group : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr D.group_card_pos.ne'
    apply hc
    rw [← hnorm, hz]
    exact hzero
  · intro σ hσ
    obtain ⟨ω, hω⟩ := exists_weil_of_symplectic (Fin n) ι σ
      (by simpa only [Fintype.card_fin] using heven) hσ
    obtain ⟨hωsb, hωtr, hωip⟩ := hω _ hf
    exact ⟨_, hωsb, hωtr, (hωip _ hf).trans hnorm⟩

end NativeFamily

/-- The native host, original projective trace lattice, symplectic basis,
split-five full level and every finite theta vector are constructed
together. The displayed mass is the cardinality of that actual finite GL.
The cusp descent and Petersson identification remain separate. -/
theorem exists_native_full_level_family
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (B : Ideal (𝓞 (nativeDyadicHostRaw e q d he hH).E))
    (hB : let H := nativeDyadicHostRaw e q d he hH
      differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j n : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m)
    (hn : k + m - 1 ≤ n) (heven : Even n) :
    let H := nativeDyadicHostRaw e q d he hH
    let _ : IsCMField (nativeDyadicHostAx e q d he hH).E :=
      (nativeDyadicHostAx e q d he hH).der.cm
    let D := nativeDyadicPrescribedGeometricDatum e q d he hH B hB k m j hk hj
    let g := finrank ℚ H.E / 2 * (D.p + D.q)
    ∃ (C : FullLevel H (prescribedLattice H B k m))
      (b : Basis (Fin g ⊕ Fin g) ℤ D.La), IsSymplecticBasis D.EF b ∧
      ∀ Λ ∈ Vset H n 5, ∃ f : Matrix (Fin n) (Fin g) ℚ → ℂ,
        IsSB f ∧ ip f f = (Nat.card C.Group : ℂ) ∧
          (∀ τ ∈ Siegel (Fin g), Differentiable ℂ (thS f τ) ∧ ∃ ζ, thS f τ ζ ≠ 0) ∧
          ∀ σ ∈ Matrix.symplecticGroup (Fin g) ℚ,
            ∃ f' : Matrix (Fin n) (Fin g) ℚ → ℂ,
              IsSB f' ∧ TransS σ f f' ∧ ip f' f' = (Nat.card C.Group : ℂ) := by
  let H := nativeDyadicHostRaw e q d he hH
  let _ : IsCMField (nativeDyadicHostAx e q d he hH).E :=
    (nativeDyadicHostAx e q d he hH).der.cm
  let G := nativeDyadicGeometricHostOfDerived e q d he hH
  obtain ⟨b, hb, _⟩ :=
    ShiftedVacua.exists_native_shifted_vacua e q d he hH B hB k m j hk hj n
  obtain ⟨C⟩ := exists_native_full_level e q d he hH B hB (k + m - 1)
  refine ⟨C, b, hb, fun Λ hΛ => ?_⟩
  obtain ⟨v, y, _, _, _, _, hsb, hip, hhol, hcov⟩ :=
    exists_full_level_theta H B hB G
      (nativeDyadicGeometricHostOfDerived_inPsi e q d he hH)
      (nativeDyadicHostRaw_prescribed_embedding_conj e q d he hH)
      (nativeDyadicGeometricHost_bar_eq e q d he hH)
      k m j hk hj b hb C hn heven hΛ
  exact ⟨thetaSum H B hB k m b C y v, hsb, hip, hhol, hcov⟩

end RHLean.Geometry.NativeTheta.Cusp.FiniteLevelNorm

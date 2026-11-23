import RHLean.Geometry.NativeThetaPeriodTorsion

/-!
# Finite-order freeness on the actual native period quotient

A real-linear map preserving the native period lattice induces an additive
map on its genuine complex torus. Unipotence on the full rational `g`-level
is transported through `L / gL ≃ (V / P(L))[g]`. The primary-torsion theorem
then fixes every `g`-power torsion point. For a lattice vector `l`, this
forces `alpha(l) - l` into `g^a L` for every `a`. The actual free integer
basis proves that intersection is zero. Full real span of the constructed
periods then proves identity on the whole ambient space and torus.

The final theorem uses the same `prescribedPeriodMap`, integral lattice,
and real tensor equivalence already constructed natively. Its rank is
`(k + m - 1) * [E : Q]`. It retains finite order and unipotence on the
FULL rational-prime quotient as explicit action hypotheses.

The original geometric supplier
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/`
`LevelAutomorphismUnipotentFixesComplexPointEqOne.lean`,
`GlobalTheory.UnipFree.free`, at Alpöge source
`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`, instead starts with unipotence
at one norm-`g` ideal and uses the corresponding ideal-primary Tate group.
That weaker ideal-level premise is not silently substituted here. An
actual moduli stabilizer's compatible lift and full-level unipotence still
need construction before applying this theorem to its geometric orbit.
-/

set_option autoImplicit false

noncomputable section

open NumberField
open scoped TensorProduct Pointwise

namespace RHLean.Geometry.NativeThetaPeriodTorsion

section IntegerSeparation

variable {L : Type} [AddCommGroup L] [Module.Free ℤ L]

/-- A free integral lattice is separated by its actual prime-power
multiples. No topology or chosen quotient cardinality is assumed. -/
theorem eq_zero_of_mem_all_power_ranges (g : ℕ) (hg : 1 < g) (x : L)
    (hx : ∀ a : ℕ, x ∈ (nsmulAddMonoidHom (α := L) (g ^ a)).range) :
    x = 0 := by
  let b := Module.Free.chooseBasis ℤ L
  apply b.ext_elem
  intro i
  rw [map_zero, Finsupp.zero_apply]
  obtain ⟨y, hy⟩ := hx (b.repr x i).natAbs
  change g ^ (b.repr x i).natAbs • y = x at hy
  have hd : ((g ^ (b.repr x i).natAbs : ℕ) : ℤ) ∣ b.repr x i := by
    refine ⟨b.repr y i, ?_⟩
    have hi := congrArg (fun z => b.repr z i) hy
    simpa only [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul] using hi.symm
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd
  simpa only [Int.natAbs_natCast] using
    (Nat.lt_pow_self hg : (b.repr x i).natAbs < g ^ (b.repr x i).natAbs)

end IntegerSeparation

section Action

variable {L V : Type} [AddCommGroup L] [AddCommGroup V] [Module ℝ V]

/-- The actual real-linear lattice action descends to its period quotient. -/
def quotientMap (P : L →+ V) (F : V →ₗ[ℝ] V) (α : L →+ L)
    (hFP : ∀ l, F (P l) = P (α l)) : PeriodQuotient P →+ PeriodQuotient P :=
  QuotientAddGroup.map P.range P.range F.toAddMonoidHom (by
    rintro _ ⟨l, rfl⟩
    exact ⟨α l, (hFP l).symm⟩)

theorem quotientMap_mk (P : L →+ V) (F : V →ₗ[ℝ] V) (α : L →+ L)
    (hFP : ∀ l, F (P l) = P (α l)) (v : V) :
    quotientMap P F α hFP (QuotientAddGroup.mk' P.range v) =
      QuotientAddGroup.mk' P.range (F v) := rfl

theorem quotientMap_iterate_mk (P : L →+ V) (F : V →ₗ[ℝ] V) (α : L →+ L)
    (hFP : ∀ l, F (P l) = P (α l)) (n : ℕ) (v : V) :
    (quotientMap P F α hFP)^[n] (QuotientAddGroup.mk' P.range v) =
      QuotientAddGroup.mk' P.range (F^[n] v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, quotientMap_mk,
      Function.iterate_succ_apply']

/-- The canonical torsion parametrization intertwines the same integral
and quotient actions. -/
theorem quotientMap_torsionParam (P : L →+ V) (F : V →ₗ[ℝ] V) (α : L →+ L)
    (hFP : ∀ l, F (P l) = P (α l)) (g : ℕ) (hg : g ≠ 0) (l : L) :
    quotientMap P F α hFP (torsionParam P g hg l : PeriodQuotient P) =
      (torsionParam P g hg (α l) : PeriodQuotient P) := by
  change QuotientAddGroup.mk' P.range (F ((g : ℝ)⁻¹ • P l)) =
    QuotientAddGroup.mk' P.range ((g : ℝ)⁻¹ • P (α l))
  rw [map_smul, hFP]

/-- Nilpotence modulo the actual full rational level supplies unipotence
on its canonically identified torsion subgroup. -/
theorem quotientMap_unipotent_of_lattice (P : L →+ V) (hP : Function.Injective P)
    (F : V →ₗ[ℝ] V) (α : L →+ L) (hFP : ∀ l, F (P l) = P (α l))
    (g u : ℕ) (hg : g ≠ 0)
    (hu : ∀ l : L, (fun z => α z - z)^[u] l ∈
      (nsmulAddMonoidHom (α := L) g).range) :
    ∀ x : PeriodQuotient P, g • x = 0 →
      (fun z => quotientMap P F α hFP z - z)^[u] x = 0 := by
  have hs : Function.Semiconj
      (fun l => (torsionParam P g hg l : PeriodQuotient P))
      (fun l => α l - l) (fun z => quotientMap P F α hFP z - z) := by
    intro l
    change (torsionParam P g hg (α l - l) : PeriodQuotient P) = _
    rw [map_sub]
    change (torsionParam P g hg (α l) : PeriodQuotient P) -
      (torsionParam P g hg l : PeriodQuotient P) = _
    rw [quotientMap_torsionParam]
  intro x hx
  obtain ⟨l, hl⟩ := torsionParam_surjective P g hg (⟨x, hx⟩ : torsion P g)
  have hl' : (torsionParam P g hg l : PeriodQuotient P) = x :=
    congrArg Subtype.val hl
  have hz : torsionParam P g hg ((fun z => α z - z)^[u] l) = 0 := by
    have h := hu l
    rw [torsionParam_ker P hP g hg] at h
    exact h
  rw [← hl', ← hs.iterate_right u l]
  exact congrArg Subtype.val hz

/-- Fixing the actual primary points forces identity on every original
integral vector, through integer divisibility in its own free basis. -/
theorem latticeAction_eq_id_of_primary_fixed [Module.Free ℤ L]
    (P : L →+ V) (hP : Function.Injective P)
    (F : V →ₗ[ℝ] V) (α : L →+ L) (hFP : ∀ l, F (P l) = P (α l))
    (g : ℕ) (hg : 1 < g)
    (hfix : ∀ x : PeriodQuotient P, (∃ a : ℕ, g ^ a • x = 0) →
      quotientMap P F α hFP x = x) :
    α = AddMonoidHom.id L := by
  ext l
  change α l = l
  apply sub_eq_zero.mp
  apply eq_zero_of_mem_all_power_ranges g hg
  intro a
  have hga : g ^ a ≠ 0 := pow_ne_zero _ (by omega)
  have ht : g ^ a • (torsionParam P (g ^ a) hga l : PeriodQuotient P) = 0 :=
    (torsionParam P (g ^ a) hga l).2
  have h := hfix (torsionParam P (g ^ a) hga l) ⟨a, ht⟩
  have he : torsionParam P (g ^ a) hga (α l) = torsionParam P (g ^ a) hga l :=
    Subtype.ext ((quotientMap_torsionParam P F α hFP (g ^ a) hga l).symm.trans h)
  rw [torsionParam_ker P hP (g ^ a) hga]
  change torsionParam P (g ^ a) hga (α l - l) = 0
  rw [map_sub, he, sub_self]

/-- Full real span transfers identity from the original periods to the
entire ambient vector space. -/
theorem linearMap_eq_id_of_period (P : L →+ V)
    (hspan : Submodule.span ℝ (Set.range P) = ⊤) (F : V →ₗ[ℝ] V)
    (hF : ∀ l, F (P l) = P l) : F = LinearMap.id := by
  have hle : Submodule.span ℝ (Set.range P) ≤ (F - LinearMap.id).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, rfl⟩
    change F (P l) - P l = 0
    rw [hF, sub_self]
  rw [hspan] at hle
  ext v
  have hv := hle (show v ∈ (⊤ : Submodule ℝ V) from Submodule.mem_top)
  change F v - v = 0 at hv
  exact sub_eq_zero.mp hv

private theorem linearMap_pow_apply_eq_iterate (F : V →ₗ[ℝ] V) (n : ℕ) (v : V) :
    (F ^ n) v = F^[n] v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, Function.iterate_succ_apply']

private theorem linearMap_pow_period (P : L →+ V) (F : V →ₗ[ℝ] V) (α : L →+ L)
    (hFP : ∀ l, F (P l) = P (α l)) (n : ℕ) (l : L) :
    (F ^ n) (P l) = P (α^[n] l) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, hFP, Function.iterate_succ_apply']

/-- The source finite order on the lattice also controls its actual
ambient lift and induced quotient action. -/
theorem quotientMap_finite_order (P : L →+ V)
    (hspan : Submodule.span ℝ (Set.range P) = ⊤)
    (F : V →ₗ[ℝ] V) (α : L →+ L) (hFP : ∀ l, F (P l) = P (α l))
    (n : ℕ) (hα : ∀ l, α^[n] l = l) :
    ∀ x : PeriodQuotient P, (quotientMap P F α hFP)^[n] x = x := by
  have hpow : F ^ n = LinearMap.id :=
    linearMap_eq_id_of_period P hspan (F ^ n) (fun l => by
      rw [linearMap_pow_period P F α hFP, hα])
  intro x
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective P.range x
  rw [quotientMap_iterate_mk, ← linearMap_pow_apply_eq_iterate, hpow]
  rfl

/-- The integral action, its real-linear lift and its entire period-quotient
action are all the identity. Every torsion input is derived from the lattice. -/
theorem finite_order_unipotent_periodAction_eq_id
    [Module.Free ℤ L] [Module.Finite ℤ L]
    (P : L →+ V) (hP : Function.Injective P)
    (hspan : Submodule.span ℝ (Set.range P) = ⊤)
    (F : V →ₗ[ℝ] V) (α : L →+ L) (hFP : ∀ l, F (P l) = P (α l))
    (n g u : ℕ) (hn : 0 < n) (hαn : ∀ l, α^[n] l = l)
    (hg : g.Prime) (hrg : Module.finrank ℤ L + 2 ≤ g)
    (hu : ∀ l : L, (fun z => α z - z)^[u] l ∈
      (nsmulAddMonoidHom (α := L) g).range) :
    F = LinearMap.id ∧ α = AddMonoidHom.id L ∧
      quotientMap P F α hFP = AddMonoidHom.id (PeriodQuotient P) := by
  have hfix := finite_order_unipotent_primary_eq_id P hP (quotientMap P F α hFP)
    n g u hn (quotientMap_finite_order P hspan F α hFP n hαn) hg hrg
    (quotientMap_unipotent_of_lattice P hP F α hFP g u hg.ne_zero hu)
  have hα := latticeAction_eq_id_of_primary_fixed P hP F α hFP g hg.one_lt hfix
  have hF : F = LinearMap.id := linearMap_eq_id_of_period P hspan F (fun l => by
    rw [hFP, hα]
    rfl)
  refine ⟨hF, hα, ?_⟩
  ext x
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective P.range x
  rw [quotientMap_mk, hF]
  rfl

end Action

/-- Full span is proved from the actual real tensor equivalence. -/
theorem periodOfRealEquiv_span {L : Type} [AddCommGroup L] [Module.Free ℤ L]
    {d : ℕ} (e : (ℝ ⊗[ℤ] L) ≃ₗ[ℝ] (Fin d → ℂ)) :
    Submodule.span ℝ (Set.range (NativeGeometricPeriods.periodOfRealEquiv e)) = ⊤ := by
  let b := Module.Free.chooseBasis ℤ L
  let c := (b.baseChange ℝ).map e
  have hc : ∀ i, c i = NativeGeometricPeriods.periodOfRealEquiv e (b i) := by
    intro i
    simp [c, NativeGeometricPeriods.periodOfRealEquiv_apply]
  rw [eq_top_iff, ← c.span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨b i, (hc i).symm⟩

end RHLean.Geometry.NativeThetaPeriodTorsion

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry.NativeThetaPeriodTorsion

variable {φ : Frame} (H : HostRaw φ)

theorem prescribedPeriodMap_span (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (k m j : ℕ) :
    Submodule.span ℝ (Set.range (prescribedPeriodMap H B hB k m j)) = ⊤ := by
  letI := twistedLattice_free_int H B (k + m - 1)
  exact periodOfRealEquiv_span (twistedPeriodRealEquiv H B hB (k + m - 1) (m - j))

/-- Whole-torus finite-order freeness on the actual native prescribed
periods. The full rational-level unipotence and the full integer rank
condition are retained literally. -/
theorem prescribedPeriod_finite_order_unipotent_eq_id
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j : ℕ)
    (F : (Fin ((cmTypeFinset H).card * (k + m - 1)) → ℂ) →ₗ[ℝ]
      (Fin ((cmTypeFinset H).card * (k + m - 1)) → ℂ))
    (α : prescribedLattice H B k m →+ prescribedLattice H B k m)
    (hFP : ∀ l, F (prescribedPeriodMap H B hB k m j l) =
      prescribedPeriodMap H B hB k m j (α l))
    (n g u : ℕ) (hn : 0 < n) (hαn : ∀ l, α^[n] l = l)
    (hg : g.Prime)
    (hrg : (k + m - 1) * Module.finrank ℚ H.E + 2 ≤ g)
    (hu : ∀ l, (fun z => α z - z)^[u] l ∈
      (nsmulAddMonoidHom (α := prescribedLattice H B k m) g).range) :
    F = LinearMap.id ∧ α = AddMonoidHom.id (prescribedLattice H B k m) ∧
      quotientMap (prescribedPeriodMap H B hB k m j) F α hFP =
        AddMonoidHom.id (PeriodQuotient (prescribedPeriodMap H B hB k m j)) := by
  letI := twistedLattice_free_int H B (k + m - 1)
  letI := twistedLattice_finite_int H B (k + m - 1)
  apply finite_order_unipotent_periodAction_eq_id
    (prescribedPeriodMap H B hB k m j) (prescribedPeriodMap_injective H B hB k m j)
    (prescribedPeriodMap_span H B hB k m j) F α hFP n g u hn hαn hg ?_ hu
  rwa [twistedLattice_rank_int H B hB]

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

end

import RHLean.Geometry.NativeThetaPeriodFreeness

/-!
# Native period freeness from the actual nilpotence index

The finite-order proof needs a bound for the nilpotence index on prime
torsion. A cardinality estimate is one way to obtain that bound, but an
explicit index is stronger and removes the rank-dependent prime threshold.
This file carries the index theorem to the same native period quotient.

If `(alpha - 1)^u` maps the original lattice into `g L`, the sufficient
prime condition is `u + 2 ≤ g`. In particular, full congruence
`alpha = 1 mod g L` has `u = 1`, so every prime `g ≥ 3` works independently
of the lattice rank and the coefficient-field degree. The final declaration
specializes this to the literal auxiliary level `5` on the actual prescribed
periods.

Every divisor, period and lattice is unchanged. The finite-order integral
action and its compatible real-linear lift remain explicit. Full rational
level congruence is stronger than the original Alpöge one-ideal unipotence
hypothesis; an actual geometric level action and its cost must supply it.
No prime ideal of norm `5`, moduli action, or section-separation result is
asserted here.

This is a refinement of the proof reconstructed from
`FiniteOrderUnipotentAutDivisiblePrimaryEqId.lean`, Alpöge source
`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`: the existing `prime_order`
and `coprime_order` arguments apply directly to the given index, while
`nil_index` is needed only for the older cardinality-based theorem.
-/

set_option autoImplicit false

noncomputable section

open NumberField
open scoped Pointwise

namespace RHLean.Geometry.NativeThetaPeriodTorsion

section Primary

variable {L V : Type} [AddCommGroup L] [AddCommGroup V] [Module ℝ V]

/-- Actual ambient division supplies every primary-group hypothesis except
finite order and the stated first-layer nilpotence index. No finite torsion
set or rank bound is required. -/
theorem finite_order_unipotent_primary_eq_id_of_index
    (P : L →+ V) (β : PeriodQuotient P →+ PeriodQuotient P) (n g u : ℕ)
    (hn : 0 < n) (hβ : ∀ x, β^[n] x = x) (hg : g.Prime)
    (hgu : u + 2 ≤ g)
    (hu : ∀ x : PeriodQuotient P, g • x = 0 →
      (fun z => β z - z)^[u] x = 0) :
    ∀ x : PeriodQuotient P, (∃ j : ℕ, g ^ j • x = 0) → β x = x := by
  have hfix := NativeThetaOrbitTorsion.finite_order_unipotent_eq_id_of_index
    (primary P g) (primaryMap P g β) n g u hn
    (fun x => Subtype.ext (by rw [primaryMap_iterate, hβ])) hg hgu
    (primary_divisible P g hg.ne_zero)
    (fun x => by
      obtain ⟨j, hj⟩ := x.2
      exact ⟨j, Subtype.ext hj⟩)
    (fun x hx => Subtype.ext (by
      rw [primaryMap_sub_iterate]
      exact hu x.1 (congrArg Subtype.val hx)))
  intro x hx
  exact congrArg Subtype.val (hfix ⟨x, hx⟩)

/-- Whole-period freeness depends on the actual nilpotence index, with no
integer-rank or coefficient-degree condition on the auxiliary prime. -/
theorem finite_order_unipotent_periodAction_eq_id_of_index [Module.Free ℤ L]
    (P : L →+ V) (hP : Function.Injective P)
    (hspan : Submodule.span ℝ (Set.range P) = ⊤)
    (F : V →ₗ[ℝ] V) (α : L →+ L) (hFP : ∀ l, F (P l) = P (α l))
    (n g u : ℕ) (hn : 0 < n) (hαn : ∀ l, α^[n] l = l)
    (hg : g.Prime) (hgu : u + 2 ≤ g)
    (hu : ∀ l : L, (fun z => α z - z)^[u] l ∈
      (nsmulAddMonoidHom (α := L) g).range) :
    F = LinearMap.id ∧ α = AddMonoidHom.id L ∧
      quotientMap P F α hFP = AddMonoidHom.id (PeriodQuotient P) := by
  have hfix := finite_order_unipotent_primary_eq_id_of_index P (quotientMap P F α hFP)
    n g u hn (quotientMap_finite_order P hspan F α hFP n hαn) hg hgu
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

/-- Full congruence has nilpotence index one. Every odd prime works,
independently of the rank of the actual free integral lattice. -/
theorem finite_order_congruent_periodAction_eq_id [Module.Free ℤ L]
    (P : L →+ V) (hP : Function.Injective P)
    (hspan : Submodule.span ℝ (Set.range P) = ⊤)
    (F : V →ₗ[ℝ] V) (α : L →+ L) (hFP : ∀ l, F (P l) = P (α l))
    (n g : ℕ) (hn : 0 < n) (hαn : ∀ l, α^[n] l = l)
    (hg : g.Prime) (hg3 : 3 ≤ g)
    (hcongr : ∀ l : L, α l - l ∈ (nsmulAddMonoidHom (α := L) g).range) :
    F = LinearMap.id ∧ α = AddMonoidHom.id L ∧
      quotientMap P F α hFP = AddMonoidHom.id (PeriodQuotient P) := by
  apply finite_order_unipotent_periodAction_eq_id_of_index
    P hP hspan F α hFP n g 1 hn hαn hg hg3
  intro l
  simpa only [Function.iterate_one] using hcongr l

end Primary

end RHLean.Geometry.NativeThetaPeriodTorsion

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry.NativeThetaPeriodTorsion

variable {φ : Frame} (H : HostRaw φ)

/-- The actual native period construction inherits the smaller index
threshold with every original lattice and period map retained. -/
theorem prescribedPeriod_finite_order_unipotent_eq_id_of_index
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j : ℕ)
    (F : (Fin ((cmTypeFinset H).card * (k + m - 1)) → ℂ) →ₗ[ℝ]
      (Fin ((cmTypeFinset H).card * (k + m - 1)) → ℂ))
    (α : prescribedLattice H B k m →+ prescribedLattice H B k m)
    (hFP : ∀ l, F (prescribedPeriodMap H B hB k m j l) =
      prescribedPeriodMap H B hB k m j (α l))
    (n g u : ℕ) (hn : 0 < n) (hαn : ∀ l, α^[n] l = l)
    (hg : g.Prime) (hgu : u + 2 ≤ g)
    (hu : ∀ l, (fun z => α z - z)^[u] l ∈
      (nsmulAddMonoidHom (α := prescribedLattice H B k m) g).range) :
    F = LinearMap.id ∧ α = AddMonoidHom.id (prescribedLattice H B k m) ∧
      quotientMap (prescribedPeriodMap H B hB k m j) F α hFP =
        AddMonoidHom.id (PeriodQuotient (prescribedPeriodMap H B hB k m j)) := by
  let := twistedLattice_free_int H B (k + m - 1)
  exact finite_order_unipotent_periodAction_eq_id_of_index
    (prescribedPeriodMap H B hB k m j) (prescribedPeriodMap_injective H B hB k m j)
    (prescribedPeriodMap_span H B hB k m j) F α hFP n g u hn hαn hg hgu hu

/-- Literal fixed auxiliary level five on the same actual native torus.
Only the finite-order lattice action and its full level-five congruence
remain as action premises; no rank-dependent prime choice is needed. -/
theorem prescribedPeriod_finite_order_congruent_five_eq_id
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j : ℕ)
    (F : (Fin ((cmTypeFinset H).card * (k + m - 1)) → ℂ) →ₗ[ℝ]
      (Fin ((cmTypeFinset H).card * (k + m - 1)) → ℂ))
    (α : prescribedLattice H B k m →+ prescribedLattice H B k m)
    (hFP : ∀ l, F (prescribedPeriodMap H B hB k m j l) =
      prescribedPeriodMap H B hB k m j (α l))
    (n : ℕ) (hn : 0 < n) (hαn : ∀ l, α^[n] l = l)
    (hcongr : ∀ l, α l - l ∈
      (nsmulAddMonoidHom (α := prescribedLattice H B k m) 5).range) :
    F = LinearMap.id ∧ α = AddMonoidHom.id (prescribedLattice H B k m) ∧
      quotientMap (prescribedPeriodMap H B hB k m j) F α hFP =
        AddMonoidHom.id (PeriodQuotient (prescribedPeriodMap H B hB k m j)) := by
  let := twistedLattice_free_int H B (k + m - 1)
  exact finite_order_congruent_periodAction_eq_id
    (prescribedPeriodMap H B hB k m j) (prescribedPeriodMap_injective H B hB k m j)
    (prescribedPeriodMap_span H B hB k m j) F α hFP n 5 hn hαn
    (by decide) (by decide) hcongr

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

end

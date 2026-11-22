import Mathlib
import RHLean.Analysis.AlpogeCompletePrimitiveASK
import RHLean.Proof.FinitePartialMoments

/-!
# The ACTUAL Alpöge ASK–MAIN map in native NNS coordinates

This is a direct rewrite of Alpöge's published arithmetic map
  FirstPrimeNeSecondPrime -> StronglyIrreducible.colour_balance
    -> GrowthBoundGivesRiemannHypothesis.topExcess

through already-established RHLean identities:
  alpogeNativeCanonicalHostASK_sub_MAIN_eq_primitiveDe
  alpogeNativeCftGPsi_eq_primitiveGPsi
  alpogeNativePrimVal_eq_primitive.

No new Gz tail, matrix, surrogate cohomology group or assumed
physical ASK/MAIN bound is inserted. We retain the original
additive-character orthogonality, coset means, conductor zeros,
all prime powers, real widths, and the real part of the COMPLETE
complex primitive sum.

A single real NNS atom is the FULL character average at one of
Alpöge's original color fibers g (not the absolute value of each
individual character). Thus the signed cancellation of different
characters within each original g-fiber is performed BEFORE the
upper/lower partial-moment split.

The identity is exact. It does NOT claim the original global
geometric/automorphic estimates needed for a critical Gz bound.
-/

noncomputable section
open Finset
open scoped BigOperators

namespace RHLean.Analysis

/-- Alpöge's *original* non-Phi color fibers from the two-bit host.
Exactly the same sites as in CompletePrimitiveDe, not invented NNS bins. -/
def alpogeOriginalNNSColourSites
    (H : Type*) [AddCommGroup H] [Fintype H] [DecidableEq H] :
    Finset (AlpogeNativeE0 × H) :=
  Finset.univ.filter (fun g => ¬ alpogeNativeInPhi g)

/-- The genuine full-character primitive De at ONE original color
fiber, including principal Gz, every nonprincipal Dirichlet GPsi,
the actual Artin/CFT character evaluations, the a/w scale, the
per-fiber width and the exact 1/|Phi| normalization.

Critical: Fourier cancellation is inside the real atom.
NNS partial moments are applied ONLY AFTER this complete sum. -/
def alpogeOriginalNNSColourAtom
    {N : ℕ} [NeZero N]
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (a : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ)
    (g : AlpogeNativeE0 × H) : ℝ := by
  classical
  exact
    (((1 / ((alpogeNativePhiSet H).card : ℂ)) *
       ∑ ψ : AddChar (AlpogeNativeE0 × H) ℂ,
         starRingEnd ℂ (ψ g) *
           ((w (alpogeNativePartner t g) : ℝ) : ℂ) *
             alpogeNativeRealizedPrimitiveGPsi r ell ψ
               (a / w (alpogeNativePartner t g))).re)

/-- Upper NNS mass on the ORIGINAL g-fibers and the COMPLETE
original character sum; no character has been removed. -/
def alpogeOriginalNNSColourUPM
    {N : ℕ} [NeZero N]
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (a : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ) : ℝ :=
  upperPartialMass (alpogeOriginalNNSColourSites H)
    (alpogeOriginalNNSColourAtom r ell a t w)

/-- Lower NNS mass over exactly the same source. -/
def alpogeOriginalNNSColourLPM
    {N : ℕ} [NeZero N]
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (a : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ) : ℝ :=
  lowerPartialMass (alpogeOriginalNNSColourSites H)
    (alpogeOriginalNNSColourAtom r ell a t w)

/-- The full finite Alpöge De equals its native signed NNS color
mass, EXACTLY, with no loss, normalizing approximation or sign flip. -/
theorem alpogeCompletePrimitiveDe_re_eq_originalNNS
    {N : ℕ} [NeZero N]
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (a : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ) :
    (alpogeNativeCompletePrimitiveDe r ell a t w).re =
      alpogeOriginalNNSColourUPM r ell a t w -
      alpogeOriginalNNSColourLPM r ell a t w := by
  classical
  unfold alpogeOriginalNNSColourUPM alpogeOriginalNNSColourLPM
  rw [upperPartialMass_sub_lowerPartialMass_eq_finiteSignedSum]
  unfold finiteSignedSum alpogeOriginalNNSColourAtom
    alpogeOriginalNNSColourSites alpogeNativeCompletePrimitiveDe
  rw [Finset.mul_sum, Complex.re_sum]

/-- EXACT published physical ASK-MAIN identity, now expressed
directly in NNS coordinates on the genuine Frobenius/inertia host,
not by a renamed abstract source. -/
theorem alpogeActualCftASK_sub_MAIN_re_eq_originalNNS
    {N : ℕ} [NeZero N]
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (q d : ℕ)
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (M : ℕ) (a : ℝ) (t : H)
    (w : AlpogeNativeE0 × H → ℝ)
    (ha : 0 < a)
    (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 < w ρ)
    (hM : ∀ ρ, alpogeNativeInPhi ρ → a / w ρ ≤ (M : ℝ)) :
    (alpogeNativeFullKernelASK
       (alpogeNativeCftData N q d r).inertia
       (alpogeNativeCftData N q d r).frob M a t w -
     alpogeNativeMAIN ell a w).re =
      alpogeOriginalNNSColourUPM r ell a t w -
      alpogeOriginalNNSColourLPM r ell a t w := by
  rw [alpogeNativeCftASK_sub_MAIN_eq_completePrimitiveDe
        q d r ell M a t w ha hw hM]
  exact alpogeCompletePrimitiveDe_re_eq_originalNNS r ell a t w

/-- The SAME map with Alpöge's actual primitive logarithmic
derivative at one, instead of an arbitrary ell parameter. -/
theorem alpogeActualCanonicalASK_MAIN_re_eq_originalNNS
    {N : ℕ} [NeZero N]
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (q d : ℕ)
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (M : ℕ) (a : ℝ) (t : H)
    (w : AlpogeNativeE0 × H → ℝ)
    (ha : 0 < a)
    (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 < w ρ)
    (hM : ∀ ρ, alpogeNativeInPhi ρ → a / w ρ ≤ (M : ℝ)) :
    (alpogeNativeFullKernelASK
       (alpogeNativeCftData N q d r).inertia
       (alpogeNativeCftData N q d r).frob M a t w -
     alpogeNativeMAIN (alpogeNativeCanonicalHostEll r) a w).re =
      alpogeOriginalNNSColourUPM r
        (alpogeNativeCanonicalHostEll r) a t w -
      alpogeOriginalNNSColourLPM r
        (alpogeNativeCanonicalHostEll r) a t w := by
  exact alpogeActualCftASK_sub_MAIN_re_eq_originalNNS
    q d r (alpogeNativeCanonicalHostEll r) M a t w ha hw hM

/-!
## Original topExcess, WITHOUT changing Alpöge's array indices

We keep u0:H, t in TT, j in Fin m and the unaltered widths w(u0,j).
The only change of coordinates is replacing each exact ASK-MAIN gap
with the proved NNS UPM1-LPM1 of its actual colour-character source.
-/

/-- The SAME mean over original u0,t,j used in Alpöge's topExcess
with the actual physical ASK-MAIN expression, not NNS terminology. -/
def alpogeActualCanonicalTopExcess
    {N : ℕ} [NeZero N]
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (q d : ℕ)
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (M : ℕ) {m : ℕ} (TT : Finset H)
    (a : H → ℝ)
    (w : H → Fin m → AlpogeNativeE0 × H → ℝ) : ℝ :=
  (1 / (Fintype.card H : ℝ)) *
    ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m,
      (alpogeNativeFullKernelASK
         (alpogeNativeCftData N q d r).inertia
         (alpogeNativeCftData N q d r).frob
         M (a t) t (w u0 j) -
       alpogeNativeMAIN
         (alpogeNativeCanonicalHostEll r) (a t) (w u0 j)).re

/-- The same topExcess in NNS coordinates with both signs retained,
the SAME actual modular-unit character host and identical weights. -/
def alpogeActualNNSTopExcess
    {N : ℕ} [NeZero N]
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    {m : ℕ} (TT : Finset H)
    (a : H → ℝ)
    (w : H → Fin m → AlpogeNativeE0 × H → ℝ) : ℝ :=
  (1 / (Fintype.card H : ℝ)) *
    ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m,
      (alpogeOriginalNNSColourUPM r
          (alpogeNativeCanonicalHostEll r) (a t) t (w u0 j) -
       alpogeOriginalNNSColourLPM r
          (alpogeNativeCanonicalHostEll r) (a t) t (w u0 j))

/-- FULL original averaged ASK–MAIN equals the identical averaged
NNS physical source. The only hypotheses are ORIGINAL sharp cutoff
and positive width assumptions; no cost or saving is introduced. -/
theorem alpogeActualCanonicalTopExcess_eq_NNS
    {N : ℕ} [NeZero N]
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (q d : ℕ)
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (M : ℕ) {m : ℕ} (TT : Finset H)
    (a : H → ℝ)
    (w : H → Fin m → AlpogeNativeE0 × H → ℝ)
    (ha : ∀ t ∈ TT, 0 < a t)
    (hw : ∀ u0 j ρ, alpogeNativeInPhi ρ → 0 < w u0 j ρ)
    (hM : ∀ u0 j t, t ∈ TT →
      ∀ ρ, alpogeNativeInPhi ρ →
        a t / w u0 j ρ ≤ (M : ℝ)) :
    alpogeActualCanonicalTopExcess q d r M TT a w =
      alpogeActualNNSTopExcess r TT a w := by
  classical
  unfold alpogeActualCanonicalTopExcess alpogeActualNNSTopExcess
  congr 1
  apply Finset.sum_congr rfl
  intro u0 _hu0
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro j _hj
  exact alpogeActualCanonicalASK_MAIN_re_eq_originalNNS
    q d r M (a t) t (w u0 j) (ha t ht)
    (fun ρ hρ => hw u0 j ρ hρ)
    (fun ρ hρ => hM u0 j t ht ρ hρ)

/-- Every upper COST inequality on Alpöge's original physical
topExcess is literally IFF the identical inequality in NNS
coordinates. This is the ACTUAL analytic "one exact bridge point". -/
theorem alpogeActualCanonicalTopExcess_le_iff_NNS
    {N : ℕ} [NeZero N]
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (q d : ℕ)
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (M : ℕ) {m : ℕ} (TT : Finset H)
    (a : H → ℝ)
    (w : H → Fin m → AlpogeNativeE0 × H → ℝ)
    (ha : ∀ t ∈ TT, 0 < a t)
    (hw : ∀ u0 j ρ, alpogeNativeInPhi ρ → 0 < w u0 j ρ)
    (hM : ∀ u0 j t, t ∈ TT →
      ∀ ρ, alpogeNativeInPhi ρ →
        a t / w u0 j ρ ≤ (M : ℝ))
    (Err : ℝ) :
    alpogeActualCanonicalTopExcess q d r M TT a w ≤ Err ↔
      alpogeActualNNSTopExcess r TT a w ≤ Err := by
  rw [alpogeActualCanonicalTopExcess_eq_NNS
    q d r M TT a w ha hw hM]

end RHLean.Analysis

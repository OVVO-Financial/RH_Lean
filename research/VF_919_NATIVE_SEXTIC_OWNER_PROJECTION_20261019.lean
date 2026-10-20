import «research.VF_919_NATIVE_SEXTIC_IDEAL_FIBER_20261019»
import «research.VF_MID_919_OAI_PHASE_ALIGNED_OWNER_COMPENSATION»

/-!
# Exact lift from varying sextic ideal rows to literal RH_Lean owner sites

A rational norm n=p*N(α) is the RECEIVER of several distinct Eisenstein
prime-ideal labels; it is not an adequate phase label by itself.

This module combines (i) the kernel-checked native finite-field sixth-root
rows, (ii) the true integer norm, and (iii) RH_Lean's *actual*
lowOwnerZeroFrequencyMobiusSite weight, without changing or factorizing it.

Theorem 'not_norm_only' is the critical well-typed obstruction to collapsing
the character before the analytic moment. The same integer owner site admits
different true sextic phases. Consequently an independent OAI-style
moment argument MUST sum/tag all corresponding ideal fibers before converting
to a scalar owner. No OAI analytic module is imported.
-/

noncomputable section
namespace RHLean.Proof

open RHLean.Analysis

/-- Projection from actual Eisenstein cofactor α to its physical integer
    owner n=p*N(α). The prime ideal over p and the generator α remain
    separate as phase labels. -/
def vf919SexticOwnerProjection (p : ℕ) (a b : ℤ) : ℕ :=
  p * (vf919EisensteinCoordNorm a b).toNat

/-- The ORIGINAL RH_Lean first-owner signed Möbius site at that integer,
    not a surrogate Hecke coefficient or a constant physical profile. -/
def vf919SexticNativeAMPSite (R p : ℕ) (a b : ℤ) : ℝ :=
  lowOwnerZeroFrequencyMobiusSite R (vf919SexticOwnerProjection p a b)

/-- Moving physical integer weights commute with ideal-to-rational
    projection only AFTER all distinct ideal labels have been retained. -/
theorem vf919SexticSameNorm_samePhysicalSite
    (p : ℕ) {a b c d : ℤ}
    (h : vf919EisensteinCoordNorm a b =
       vf919EisensteinCoordNorm c d) :
    vf919SexticOwnerProjection p a b =
      vf919SexticOwnerProjection p c d := by
  unfold vf919SexticOwnerProjection
  rw [h]

theorem vf919SexticSameNorm_sameArbitraryWeight
    (p : ℕ) (w : ℕ → ℂ) {a b c d : ℤ}
    (h : vf919EisensteinCoordNorm a b =
       vf919EisensteinCoordNorm c d) :
    w (vf919SexticOwnerProjection p a b) =
      w (vf919SexticOwnerProjection p c d) := by
  rw [vf919SexticSameNorm_samePhysicalSite p h]

theorem vf919SexticSameNorm_sameNativeAMP
    (R p : ℕ) {a b c d : ℤ}
    (h : vf919EisensteinCoordNorm a b =
       vf919EisensteinCoordNorm c d) :
    vf919SexticNativeAMPSite R p a b =
      vf919SexticNativeAMPSite R p c d := by
  unfold vf919SexticNativeAMPSite
  rw [vf919SexticSameNorm_samePhysicalSite p h]

/-- All four *actual original integer owner locations* at their correct
    cutoffs, including the strict square-block convention. -/
theorem vf919SexticFourWits_ownerProjections :
    (vf919SexticOwnerProjection 19 (-2) (-3) = 133 ∧
      vf919SexticOwnerProjection 19 1 3 = 133) ∧
    (vf919SexticOwnerProjection 37 (-2) (-3) = 259 ∧
      vf919SexticOwnerProjection 37 1 3 = 259) ∧
    (vf919SexticOwnerProjection 439 (-17) (-12) = 100531 ∧
      vf919SexticOwnerProjection 439 (-5) 12 = 100531) ∧
    (vf919SexticOwnerProjection 3727 13 (-6) = 1054741 ∧
      vf919SexticOwnerProjection 3727 19 6 = 1054741) := by
  -- The defining Eisenstein norm and Int.toNat are fully reducible for
  -- these four exact primary generators: discharge the arithmetic in the
  -- kernel without assuming any prime-ideal source identities.
  decide

/-- Same source n=133, same literal physical AMP weight, but provably
    DIFFERENT canonical sextic Hecke-row phases. -/
theorem vf919Sextic_x317_sameNativeSeat_differentIdealPhase
    (R : ℕ) :
    vf919SexticNativeAMPSite R 19 1 3 =
      vf919SexticNativeAMPSite R 19 (-2) (-3) ∧
    vf919SplitSexticResidue 19 (7 : ZMod 19) 1 3 ≠
      vf919SplitSexticResidue 19 (7 : ZMod 19) (-2) (-3) := by
  constructor
  · apply vf919SexticSameNorm_sameNativeAMP
    exact vf919SexticX_primaryNorms.2.trans
      vf919SexticX_primaryNorms.1.symm
  · decide

/-- An explicit impossibility proof for a scalar owner-only character.
    A norm-first phase projection CANNOT equal the actual Hecke-row value
    even at x=317, where both primary ideals have the same norm. -/
theorem vf919Sextic_x317_noOwnerOnlyCharacter :
    ¬ ∃ f : ℕ → ZMod 19, ∀ a b : ℤ,
        vf919SplitSexticResidue 19 (7 : ZMod 19) a b =
          f (vf919SexticOwnerProjection 19 a b) := by
  rintro ⟨f, hf⟩
  have hs : vf919SexticOwnerProjection 19 1 3 =
      vf919SexticOwnerProjection 19 (-2) (-3) :=
    vf919SexticSameNorm_samePhysicalSite 19
      (vf919SexticX_primaryNorms.2.trans
        vf919SexticX_primaryNorms.1.symm)
  have hdiff :
      vf919SplitSexticResidue 19 (7 : ZMod 19) 1 3 ≠
        vf919SplitSexticResidue 19 (7 : ZMod 19) (-2) (-3) := by
    decide
  apply hdiff
  calc
    vf919SplitSexticResidue 19 (7 : ZMod 19) 1 3 =
      f (vf919SexticOwnerProjection 19 1 3) := hf 1 3
    _ = f (vf919SexticOwnerProjection 19 (-2) (-3)) := by rw [hs]
    _ = vf919SplitSexticResidue 19 (7 : ZMod 19) (-2) (-3) :=
      (hf (-2) (-3)).symm

/-- Exact phase amplitudes expressed in ℤ[ζ₆] = ℤ + ℤζ₆, where
    ζ₆²=ζ₆-1. This preserves the character SIGN, not just its norm. -/
def vf919SexticPhaseBasis (e : ℕ) : ℤ × ℤ :=
  if e % 6 = 0 then (1, 0)
  else if e % 6 = 1 then (0, 1)
  else if e % 6 = 2 then (-1, 1)
  else if e % 6 = 3 then (-1, 0)
  else if e % 6 = 4 then (0, -1)
  else (1, -1)

/-- Add exactly the four prime-ideal phases before any norm taking. -/
def vf919SexticExactFourIdealPhaseTotal (es : List ℕ) : ℤ × ℤ :=
  ((es.map fun e => (vf919SexticPhaseBasis e).1).sum,
   (es.map fun e => (vf919SexticPhaseBasis e).2).sum)

/-- Exact *signed complex* four-ideal sums. The unphased norm-fiber
    coefficient is +4 in ALL FOUR cases (two distinct split primes);
    genuine character-phase totals instead vary 2,-1,1,-1. -/
theorem vf919SexticFourWits_twistedIdealTotals :
    vf919SexticExactFourIdealPhaseTotal [5, 5, 1, 1] = (2, 0) ∧
    vf919SexticExactFourIdealPhaseTotal [1, 3, 3, 5] = (-1, 0) ∧
    vf919SexticExactFourIdealPhaseTotal [0, 4, 2, 0] = (1, 0) ∧
    vf919SexticExactFourIdealPhaseTotal [3, 1, 5, 3] = (-1, 0) := by
  decide

/-- OpenAI's actual marked-minus-rescaled MAIN high-row coefficient is
    -chi_P(u)^{-1}. In the exact Eisenstein sixth-root basis this is
    zeta6^(3-e) when chi_P(u)=zeta6^e. The nonunit / local-error branch is
    deliberately NOT identified with this coefficient. -/
def vf919SexticSelectedMainPhaseBasis (e : ℕ) : ℤ × ℤ :=
  vf919SexticPhaseBasis ((3 + 6 - e % 6) % 6)

def vf919SexticSelectedMainFourIdealTotal (es : List ℕ) : ℤ × ℤ :=
  ((es.map fun e => (vf919SexticSelectedMainPhaseBasis e).1).sum,
   (es.map fun e => (vf919SexticSelectedMainPhaseBasis e).2).sum)

/-- A source-faithful numerical dictionary for the actual selected-prime
    PHASE in all four original owner coordinate systems. The four sums
    are -2,+1,-1,+1 rather than a fixed scalar Euler term. -/
theorem vf919SexticFourWits_markedMinusRescaledMainTotals :
    vf919SexticSelectedMainFourIdealTotal [5, 5, 1, 1] = (-2, 0) ∧
    vf919SexticSelectedMainFourIdealTotal [1, 3, 3, 5] = (1, 0) ∧
    vf919SexticSelectedMainFourIdealTotal [0, 4, 2, 0] = (-1, 0) ∧
    vf919SexticSelectedMainFourIdealTotal [3, 1, 5, 3] = (1, 0) := by
  decide

/-- Existing native Möbius first-prime law applied at the unit
    gives the correct sign of ANY prime, without evaluating a generic
    squarefree/cardFactors expression by computation. -/
private theorem vf919SexticRealMoebius_prime
    (p : ℕ) (hp : p.Prime) : realMoebiusStep p = -1 := by
  have hunit : realMoebiusStep 1 = 1 := by
    norm_num [realMoebiusStep]
  have hnew : ¬ p ∣ 1 := by
    simpa using! hp.ne_one
  have hflip := realMoebiusStep_mul_prime_eq_neg
    (p := p) (n := 1) hp hnew
  simpa [hunit] using! hflip

/-- Fresh multiplication by a second prime flips -1 back to +1.
    This supplies the actual Möbius signs at every one of our four
    semiprime witnesses, using RH_Lean's general theorem. -/
private theorem vf919SexticRealMoebius_distinctPrimePair
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hnew : ¬ p ∣ q) :
    realMoebiusStep (p * q) = 1 := by
  rw [realMoebiusStep_mul_prime_eq_neg hp hnew,
    vf919SexticRealMoebius_prime q hq]
  norm_num

/-- Four original actual integer Möbius sites have sign +1, as proved
    by the native fresh-prime multiplication law. -/
theorem vf919SexticFourWits_originalIntegerMobius :
    realMoebiusStep 133 = 1 ∧
    realMoebiusStep 259 = 1 ∧
    realMoebiusStep 100531 = 1 ∧
    realMoebiusStep 1054741 = 1 := by
  constructor
  · simpa only [show 19 * 7 = 133 by norm_num] using!
      (vf919SexticRealMoebius_distinctPrimePair 19 7
        (by norm_num) (by norm_num) (by norm_num))
  constructor
  · simpa only [show 37 * 7 = 259 by norm_num] using!
      (vf919SexticRealMoebius_distinctPrimePair 37 7
        (by norm_num) (by norm_num) (by norm_num))
  constructor
  · simpa only [show 439 * 229 = 100531 by norm_num] using!
      (vf919SexticRealMoebius_distinctPrimePair 439 229
        (by norm_num) (by norm_num) (by norm_num))
  · simpa only [show 3727 * 283 = 1054741 by norm_num] using!
      (vf919SexticRealMoebius_distinctPrimePair 3727 283
        (by norm_num) (by norm_num) (by norm_num))

#print axioms vf919SexticSameNorm_samePhysicalSite
#print axioms vf919SexticFourWits_ownerProjections
#print axioms vf919Sextic_x317_sameNativeSeat_differentIdealPhase
#print axioms vf919Sextic_x317_noOwnerOnlyCharacter
#print axioms vf919SexticFourWits_twistedIdealTotals
#print axioms vf919SexticFourWits_markedMinusRescaledMainTotals
#print axioms vf919SexticFourWits_originalIntegerMobius

end RHLean.Proof

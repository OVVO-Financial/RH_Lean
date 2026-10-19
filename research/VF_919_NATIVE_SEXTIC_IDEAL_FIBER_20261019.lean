import Mathlib

/-!
# Genuine varying sextic phases over split Eisenstein ideals:
  x=317, x=1027, R=317, R=1027

INDEPENDENT NATIVE COMPUTATION. No OAI module/theorem is imported.

Coordinate map O = ℤ[ω], ω²+ω+1=0, ζ₆=1+ω.
For a rational split prime p≡1(mod 3), the two distinct prime ideals
above p correspond to the two roots r,r' of r²+r+1=0 in ZMod p.
The residue of α=a+bω at the prime ideal indexed by r is a+b*r.

The canonical sextic residue equation is
    (ζ₆ mod P_r)^e = (α mod P_r)^((p-1)/6).
This is the finite-field reduction property of the actual sextic
character proved independently in OAI's
GaussSum/FiniteFourier.lean, sexticChar_reduce_unit.

Here we DEFINE and PROVE that reduction directly on ZMod p and
literal RH_Lean integer owner sites. The computations below are
exact arithmetic; no norm-only character is postulated.

The finite witnesses produce genuinely differing sextic phases at
DIFFERENT ideals of the SAME rational norm. The final analytic
inverse/plain moment inequalities, zero detector and 7/8 bound do
NOT follow merely from these finite theorems.
-/

noncomputable section
namespace RHLean.Analysis

/-- Integer norm in the original Eisenstein cofactor coordinates. -/
def vf919EisensteinCoordNorm (a b : ℤ) : ℤ :=
  a * a - a * b + b * b

/-- The prime-ideal residue of a+bω, with ω↦r in ZMod p. -/
def vf919SplitIdealResidue (p : ℕ) (r : ZMod p) (a b : ℤ) : ZMod p :=
  (a : ZMod p) + (b : ZMod p) * r

/-- The sixth-power residue of a *genuine* Eisenstein cofactor, not
    of its rational norm or its integer-owner scalar label. -/
def vf919SplitSexticResidue
    (p : ℕ) (r : ZMod p) (a b : ℤ) : ZMod p :=
  (vf919SplitIdealResidue p r a b) ^ ((p - 1) / 6)

/-- The Eisenstein product (a+bω)(c+dω) in native coordinate pairs. -/
def vf919EisensteinCoordMul (a b c d : ℤ) : ℤ × ℤ :=
  (a * c - b * d, a * d + b * c - b * d)

/-- Exact algebraic prime-ideal evaluation, *before* sextic exponentiation. -/
theorem vf919SplitIdealResidue_mul
    (p : ℕ) (r : ZMod p) (hr : r ^ 2 + r + 1 = 0)
    (a b c d : ℤ) :
    vf919SplitIdealResidue p r (a * c - b * d)
        (a * d + b * c - b * d) =
      vf919SplitIdealResidue p r a b *
        vf919SplitIdealResidue p r c d := by
  unfold vf919SplitIdealResidue
  push_cast
  linear_combination - (b : ZMod p) * (d : ZMod p) * hr

/-- The norm-to-rational-integer projection is the PRODUCT of conjugate
    prime-ideal evaluations. It is not either one of their sextic phases. -/
theorem vf919SplitIdealResidue_norm
    (p : ℕ) (r : ZMod p) (hr : r ^ 2 + r + 1 = 0)
    (a b : ℤ) :
    vf919SplitIdealResidue p r a b *
      vf919SplitIdealResidue p (-1 - r) a b =
        (vf919EisensteinCoordNorm a b : ZMod p) := by
  unfold vf919SplitIdealResidue vf919EisensteinCoordNorm
  push_cast
  linear_combination - ((b : ZMod p) ^ 2) * hr

/-- The canonical residue of the complex sixth root ζ₆=1+ω has sixth
    power one at every genuine split prime. -/
theorem vf919SplitIdealSixthRoot_pow_six
    (p : ℕ) (r : ZMod p) (hr : r ^ 2 + r + 1 = 0) :
    (1 + r) ^ 6 = 1 := by
  have h2 : (1 + r) ^ 2 = r := by
    linear_combination hr
  have h3 : (1 + r) ^ 3 = -1 := by
    calc
      (1 + r) ^ 3 = (1 + r) * (1 + r) ^ 2 := by ring
      _ = (1 + r) * r := by rw [h2]
      _ = -1 := by linear_combination hr
  calc
    (1 + r) ^ 6 = ((1 + r) ^ 3) ^ 2 := by ring
    _ = 1 := by rw [h3]; ring

/-- The *actual* sixth-residue map is multiplicative in Eisenstein
    cofactor pairs. This is the native replacement for a placeholder
    multiplicative phase hypothesis. -/
theorem vf919SplitSexticResidue_mul
    (p : ℕ) (r : ZMod p) (hr : r ^ 2 + r + 1 = 0)
    (a b c d : ℤ) :
    vf919SplitSexticResidue p r (a * c - b * d)
        (a * d + b * c - b * d) =
      vf919SplitSexticResidue p r a b *
        vf919SplitSexticResidue p r c d := by
  unfold vf919SplitSexticResidue
  rw [vf919SplitIdealResidue_mul p r hr]
  exact mul_pow _ _ _

/-- Primary α≡1 mod 3 and the ordinary integer Möbius squarefree seats
    share the following FOUR source coordinates. All four high primes and
    all four low norm cofactors are distinct, split rational primes. -/
theorem vf919SexticFourWits_actualIntegerCutoffs :
    (17 < 19 ∧ 19 * 7 ≤ 317 ∧ (19 : ℕ).Prime ∧ (7 : ℕ).Prime) ∧
    (32 < 37 ∧ 37 * 7 ≤ 1027 ∧ (37 : ℕ).Prime) ∧
    (317 < 439 ∧ 317 ^ 2 < 439 * 229 ∧
      439 * 229 < 318 ^ 2 ∧
      (439 : ℕ).Prime ∧ (229 : ℕ).Prime) ∧
    (1027 < 3727 ∧ 1027 ^ 2 < 3727 * 283 ∧
      3727 * 283 < 1028 ^ 2 ∧
      (3727 : ℕ).Prime ∧ (283 : ℕ).Prime) := by
  norm_num

/-- The TWO prime-ideal roots above each of the high split primes.
    Different roots are not identified by taking their rational norm. -/
theorem vf919SexticFourWits_splitRoots :
    ((7 : ZMod 19) ^ 2 + 7 + 1 = 0 ∧
      (11 : ZMod 19) ^ 2 + 11 + 1 = 0) ∧
    ((10 : ZMod 37) ^ 2 + 10 + 1 = 0 ∧
      (26 : ZMod 37) ^ 2 + 26 + 1 = 0) ∧
    ((171 : ZMod 439) ^ 2 + 171 + 1 = 0 ∧
      (267 : ZMod 439) ^ 2 + 267 + 1 = 0) ∧
    ((1188 : ZMod 3727) ^ 2 + 1188 + 1 = 0 ∧
      (2538 : ZMod 3727) ^ 2 + 2538 + 1 = 0) := by
  decide

/-- TWO different primary ideal generators above k=7, at x=317 and 1027. -/
theorem vf919SexticX_primaryNorms :
    vf919EisensteinCoordNorm (-2) (-3) = 7 ∧
      vf919EisensteinCoordNorm 1 3 = 7 := by
  norm_num [vf919EisensteinCoordNorm]

/-- x=317: p=19, k=7, n=133. The two ideal generators have phases
    ζ₆⁵ and ζ₆¹ at BOTH conjugate high prime ideals. -/
theorem vf919Sextic_x317_exactFourIdealPhases :
    vf919SplitSexticResidue 19 (7 : ZMod 19) (-2) (-3) =
      (1 + (7 : ZMod 19)) ^ 5 ∧
    vf919SplitSexticResidue 19 (11 : ZMod 19) (-2) (-3) =
      (1 + (11 : ZMod 19)) ^ 5 ∧
    vf919SplitSexticResidue 19 (7 : ZMod 19) 1 3 =
      (1 + (7 : ZMod 19)) ^ 1 ∧
    vf919SplitSexticResidue 19 (11 : ZMod 19) 1 3 =
      (1 + (11 : ZMod 19)) ^ 1 := by
  decide

/-- x=1027: p=37, k=7, n=259. Exact split ideal phases differ
    from both rational norm-only signs and from x=317. -/
theorem vf919Sextic_x1027_exactFourIdealPhases :
    vf919SplitSexticResidue 37 (10 : ZMod 37) (-2) (-3) =
      (1 + (10 : ZMod 37)) ^ 1 ∧
    vf919SplitSexticResidue 37 (26 : ZMod 37) (-2) (-3) =
      (1 + (26 : ZMod 37)) ^ 3 ∧
    vf919SplitSexticResidue 37 (10 : ZMod 37) 1 3 =
      (1 + (10 : ZMod 37)) ^ 3 ∧
    vf919SplitSexticResidue 37 (26 : ZMod 37) 1 3 =
      (1 + (26 : ZMod 37)) ^ 5 := by
  decide

/-- R=317 square shell: p=439, k=229, n=100531. Two primary
    ideal generators over 229 are distinct Eisenstein coordinates. -/
theorem vf919Sextic_R317_primaryNorms :
    vf919EisensteinCoordNorm (-17) (-12) = 229 ∧
      vf919EisensteinCoordNorm (-5) 12 = 229 := by
  norm_num [vf919EisensteinCoordNorm]

theorem vf919Sextic_R317_exactFourIdealPhases :
    vf919SplitSexticResidue 439 (171 : ZMod 439) (-17) (-12) =
      (1 + (171 : ZMod 439)) ^ 0 ∧
    vf919SplitSexticResidue 439 (267 : ZMod 439) (-17) (-12) =
      (1 + (267 : ZMod 439)) ^ 4 ∧
    vf919SplitSexticResidue 439 (171 : ZMod 439) (-5) 12 =
      (1 + (171 : ZMod 439)) ^ 2 ∧
    vf919SplitSexticResidue 439 (267 : ZMod 439) (-5) 12 =
      (1 + (267 : ZMod 439)) ^ 0 := by
  decide

/-- R=1027 square shell: p=3727, k=283, n=1054741. -/
theorem vf919Sextic_R1027_primaryNorms :
    vf919EisensteinCoordNorm 13 (-6) = 283 ∧
      vf919EisensteinCoordNorm 19 6 = 283 := by
  norm_num [vf919EisensteinCoordNorm]

set_option maxRecDepth 16384 in
theorem vf919Sextic_R1027_exactFourIdealPhases :
    vf919SplitSexticResidue 3727 (1188 : ZMod 3727) 13 (-6) =
      (1 + (1188 : ZMod 3727)) ^ 3 ∧
    vf919SplitSexticResidue 3727 (2538 : ZMod 3727) 13 (-6) =
      (1 + (2538 : ZMod 3727)) ^ 1 ∧
    vf919SplitSexticResidue 3727 (1188 : ZMod 3727) 19 6 =
      (1 + (1188 : ZMod 3727)) ^ 5 ∧
    vf919SplitSexticResidue 3727 (2538 : ZMod 3727) 19 6 =
      (1 + (2538 : ZMod 3727)) ^ 3 := by
  decide

/-- A concrete theorem that the varying sextic phase CANNOT factor
    through rational norm at x=317. This is the exact interface problem
    between ideal-labeled source rows and integer owner coordinates. -/
theorem vf919Sextic_x317_not_only_rationalNorm :
    ¬ ∃ f : ℤ → ZMod 19, ∀ a b : ℤ,
        vf919SplitSexticResidue 19 (7 : ZMod 19) a b =
          f (vf919EisensteinCoordNorm a b) := by
  rintro ⟨f, hf⟩
  have hnorm := vf919SexticX_primaryNorms
  have hdiff :
      vf919SplitSexticResidue 19 (7 : ZMod 19) 1 3 ≠
        vf919SplitSexticResidue 19 (7 : ZMod 19) (-2) (-3) := by
    decide
  apply hdiff
  rw [hf 1 3, hf (-2) (-3), hnorm.1, hnorm.2]

#print axioms vf919SplitIdealResidue_mul
#print axioms vf919SplitIdealResidue_norm
#print axioms vf919SplitIdealSixthRoot_pow_six
#print axioms vf919SplitSexticResidue_mul
#print axioms vf919Sextic_x317_exactFourIdealPhases
#print axioms vf919Sextic_x1027_exactFourIdealPhases
#print axioms vf919Sextic_R317_exactFourIdealPhases
#print axioms vf919Sextic_R1027_exactFourIdealPhases
#print axioms vf919Sextic_x317_not_only_rationalNorm

end RHLean.Analysis

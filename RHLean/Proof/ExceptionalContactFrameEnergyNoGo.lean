import RHLean.Analysis.PhysicalDegreeOneHigherSquareRecurrences
import RHLean.Analysis.PhysicalSquareCRTPeriodNoGo
import RHLean.Proof.ExceptionalOwnerEnergyClosure
import RHLean.Proof.SquareRootAncestryRoot

/-!
# The six-contact frame constant is counting, not Mobius cancellation

A recurring proposal is to close the exceptional owner schedule `{3,5,7}` by
computing a frame constant `alpha_q` for the six-contact `q^2` pullback on the
finite super-orbit `Z/q^2 x Z/11^2`, proving `alpha_q <= 3`, and feeding that
into `ExceptionalOwnerEnergyStep` through the budget
`3*(1/9+1/25+1/49) = 1891/3675 < 1`.

This module records why that route supplies no arithmetic content.  Three exact
finite facts are certified.

1. **The contact classes are pullbacks of the offsets, not the offsets.**
   `physicalTransitionActiveOffsets = {1,2,3,5,6,7}` are offsets `a` inside the
   physical site `4*k+a`.  The cell classes carrying a forced `q^2` hit are
   their images under `a` mapsto `-a/4 mod q^2`: `{1,...,6}` mod `9`,
   `{5,6,11,12,17,18}` mod `25`, `{11,12,23,24,35,36}` mod `49`.  Those six
   element sets are not the offset set, and the identifications below prevent a
   repeat of that conflation.

2. **The frame constant is two, for every field.**  Since `q` is odd,
   `q^2*d` and `d` agree modulo four, and the six offsets split into the three
   mod-four pairs `{1,5}`, `{2,6}`, `{3,7}`.  A daughter therefore has exactly
   two tagged contact preimages off the zero class and none on it.
   `contact_frame_two` is stated for an arbitrary field `w : ℕ → ℤ`, so the
   proposed `alpha_q <= 3` estimate is a corollary of fibre counting
   (`contact_frame_three`) with no Mobius input at all.  Two is attained on the
   all-ones field, so no field-independent constant is smaller.  A least-owner
   restriction can only delete preimages, so `<= 2` persists and the route is
   not helped there either.

3. **Assembled coefficient norm and recursive Mertens energy are different
   objects.**  `contactDaughterCoefficientNorm q Y` is the squared mass of the
   assembled `q^2` children over the daughter range, which is what a frame
   estimate bounds.  The induction instead consumes `E (X / q^2)`.  With the
   recursive Mertens energy `E Y = mertensSummatoryInt Y ^ 2` the two are
   separated by an exact finite witness: `mertensSummatoryInt 2 = 0` while the
   assembled coefficient norm is already positive at `Y = 2` for all three
   exceptional owners.  So no constant compares them, at any scale.  This is a
   type mismatch, not a bad constant.

What is *not* claimed.  The finite mask operator exists and is perfectly well
defined; its norm is just the fibre-counting constant above.  What does not
exist is a fixed finite Mobius vector on the residue torus whose spectral data
could be computed once and reused at every physical period: the masks are
periodic, the Mobius observable is not, and the repository's transported field
reconstructs its value by pulling back to the physical source cell
(`selectedDegreeOneOffsetDaughterField`) instead of assigning a value to a
residue class.  Nothing here refutes the coefficient-level compensation
identities, the `q^2` transport, or RH.  The operative consequence is narrow:
the `q^2` children must be reassembled with their signs before any norm is
taken, never squared first.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof

open RHLean.Analysis

/-! ## 1. The contact classes are the pullbacks of the active offsets -/

/-- The nine-channel classes are the active offsets pulled back by `4` mod `9`. -/
theorem physicalNineChannelResidues_eq_image_activeOffsets :
    physicalNineChannelResidues =
      physicalTransitionActiveOffsets.image (fun a => 2 * a % 9) := by
  decide

/-- The twenty-five hit classes are the offsets pulled back by `4` mod `25`. -/
theorem physicalTwentyFiveHitResidues_eq_image_activeOffsets :
    physicalTwentyFiveHitResidues =
      physicalTransitionActiveOffsets.image (fun a => 6 * a % 25) := by
  decide

/-- The forty-nine hit classes are the offsets pulled back by `4` mod `49`. -/
theorem physicalFortyNineHitResidues_eq_image_activeOffsets :
    physicalFortyNineHitResidues =
      physicalTransitionActiveOffsets.image (fun a => 12 * a % 49) := by
  decide

/-- The contact classes are never the offset set itself. -/
theorem physicalNineChannelResidues_ne_activeOffsets :
    physicalNineChannelResidues ≠ physicalTransitionActiveOffsets := by
  decide

theorem physicalTwentyFiveHitResidues_ne_activeOffsets :
    physicalTwentyFiveHitResidues ≠ physicalTransitionActiveOffsets := by
  decide

theorem physicalFortyNineHitResidues_ne_activeOffsets :
    physicalFortyNineHitResidues ≠ physicalTransitionActiveOffsets := by
  decide

/-! ## 2. The six-contact fibre and its field-independent frame constant -/

/-- The active offsets compatible with a physical site in the class `r` modulo
four.  Because `4*k+a` determines `a` modulo four, this is the exact fibre of
the tagged contact map over one daughter. -/
def activeOffsetsOfResidue (r : ℕ) : Finset ℕ :=
  physicalTransitionActiveOffsets.filter fun a => a % 4 = r

theorem activeOffsetsOfResidue_zero : activeOffsetsOfResidue 0 = ∅ := by decide

theorem activeOffsetsOfResidue_one :
    activeOffsetsOfResidue 1 = ({1, 5} : Finset ℕ) := by decide

theorem activeOffsetsOfResidue_two :
    activeOffsetsOfResidue 2 = ({2, 6} : Finset ℕ) := by decide

theorem activeOffsetsOfResidue_three :
    activeOffsetsOfResidue 3 = ({3, 7} : Finset ℕ) := by decide

/-- Exact fibre sizes: three mod-four pairs, nothing over the zero class. -/
theorem card_activeOffsetsOfResidue (r : ℕ) (hr : r < 4) :
    (activeOffsetsOfResidue r).card = if r = 0 then 0 else 2 := by
  interval_cases r <;> decide

private theorem sum_pair_int (a b : ℕ) (hab : a ≠ b) (f : ℕ → ℤ) :
    ∑ x ∈ ({a, b} : Finset ℕ), f x = f a + f b := by
  rw [Finset.sum_insert (by simpa using hab), Finset.sum_singleton]

/-- Two-term Cauchy-Schwarz: the entire content of the frame bound. -/
private theorem sq_add_le_two_mul_sq_add_sq (x y : ℤ) :
    (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg (x - y)]

private theorem sq_sum_activeOffsetsOfResidue_le_two_mul
    (r : ℕ) (hr : r < 4) (w : ℕ → ℤ) :
    (∑ a ∈ activeOffsetsOfResidue r, w a) ^ 2 ≤
      2 * ∑ a ∈ activeOffsetsOfResidue r, (w a) ^ 2 := by
  interval_cases r
  · rw [activeOffsetsOfResidue_zero]
    simp
  · rw [activeOffsetsOfResidue_one, sum_pair_int 1 5 (by norm_num),
      sum_pair_int 1 5 (by norm_num)]
    exact sq_add_le_two_mul_sq_add_sq _ _
  · rw [activeOffsetsOfResidue_two, sum_pair_int 2 6 (by norm_num),
      sum_pair_int 2 6 (by norm_num)]
    exact sq_add_le_two_mul_sq_add_sq _ _
  · rw [activeOffsetsOfResidue_three, sum_pair_int 3 7 (by norm_num),
      sum_pair_int 3 7 (by norm_num)]
    exact sq_add_le_two_mul_sq_add_sq _ _

/-- The tagged contact fibre over the daughter `d` of owner `q`. -/
def contactFibre (q d : ℕ) : Finset ℕ :=
  activeOffsetsOfResidue (q * q * d % 4)

/-- Exact fibre size: two tagged preimages off the zero class, none on it. -/
theorem card_contactFibre (q d : ℕ) :
    (contactFibre q d).card = if q * q * d % 4 = 0 then 0 else 2 := by
  unfold contactFibre
  exact card_activeOffsetsOfResidue _ (Nat.mod_lt _ (by norm_num))

/-- Every actual tagged `q^2` contact of a physical cell lies in the fibre of
its own daughter: the fibre is the literal contact set, not a model of it. -/
theorem mem_contactFibre_of_contact {q a k : ℕ}
    (ha : a ∈ physicalTransitionActiveOffsets) (hdiv : q * q ∣ 4 * k + a) :
    a ∈ contactFibre q (qSquareOffsetDaughter q a k) := by
  have hx : q * q * qSquareOffsetDaughter q a k = 4 * k + a :=
    qSquareOffsetDaughter_exact hdiv
  unfold contactFibre activeOffsetsOfResidue
  refine Finset.mem_filter.mpr ⟨ha, ?_⟩
  rw [hx]
  omega

/-- Conversely each fibre element reconstructs its physical source cell. -/
theorem contactFibre_sourceCell_spec {q a d : ℕ}
    (ha : a ∈ contactFibre q d) (hle : a ≤ q * q * d) :
    4 * qSquareOffsetSourceCell q a d + a = q * q * d := by
  unfold contactFibre activeOffsetsOfResidue at ha
  have hmod : a % 4 = q * q * d % 4 := (Finset.mem_filter.mp ha).2
  unfold qSquareOffsetSourceCell
  omega

/-- **Field-independent frame constant two.**  The bound holds for an arbitrary
field `w`, so it uses no property of Mobius whatsoever. -/
theorem contact_frame_two (q d : ℕ) (w : ℕ → ℤ) :
    (∑ a ∈ contactFibre q d, w a) ^ 2 ≤
      2 * ∑ a ∈ contactFibre q d, (w a) ^ 2 := by
  unfold contactFibre
  exact sq_sum_activeOffsetsOfResidue_le_two_mul _ (Nat.mod_lt _ (by norm_num)) w

/-- **The proposed `alpha_q <= 3` estimate is a corollary of fibre counting.**
It is therefore not a cancellation theorem, and cannot carry arithmetic content
into the exceptional induction. -/
theorem contact_frame_three (q d : ℕ) (w : ℕ → ℤ) :
    (∑ a ∈ contactFibre q d, w a) ^ 2 ≤
      3 * ∑ a ∈ contactFibre q d, (w a) ^ 2 := by
  have h := contact_frame_two q d w
  have hnn : (0 : ℤ) ≤ ∑ a ∈ contactFibre q d, (w a) ^ 2 :=
    Finset.sum_nonneg fun a _ => sq_nonneg _
  linarith

/-- Two is attained on the all-ones field, so no field-independent constant is
smaller.  The gap between the proposed three and the observed value near one is
not arithmetic content; it is an assumption about Mobius signs. -/
theorem contact_frame_two_sharp :
    (∑ a ∈ activeOffsetsOfResidue 1, (1 : ℤ)) ^ 2 =
      2 * ∑ a ∈ activeOffsetsOfResidue 1, (1 : ℤ) ^ 2 := by
  rw [activeOffsetsOfResidue_one, sum_pair_int 1 5 (by norm_num),
    sum_pair_int 1 5 (by norm_num)]
  norm_num

/-! ## 3. Assembled coefficient norm versus recursive Mertens energy -/

/-- Computable form of the true physical degree-one source observable. -/
def physicalSourceCellValue (k : ℕ) : ℤ :=
  μ (4 * k + 1) + μ (4 * k + 2) + μ (4 * k + 3)

/-- It is exactly the repository's degree-one source observable. -/
theorem physicalSourceCellValue_eq_threeSlotDegreeOneValue (k : ℕ) :
    physicalSourceCellValue k = threeSlotDegreeOneValue (threeSlotState k) :=
  (threeSlotDegreeOneValue_threeSlotState k).symm

/-- The assembled `q^2` child of one daughter: the signed sum over the tagged
contact fibre, taken *before* any norm. -/
def contactDaughterCoefficient (q d : ℕ) : ℤ :=
  ∑ a ∈ contactFibre q d, physicalSourceCellValue (qSquareOffsetSourceCell q a d)

/-- The squared mass of the assembled children over the daughter range.  This
is the quantity a frame estimate bounds. -/
def contactDaughterCoefficientNorm (q Y : ℕ) : ℤ :=
  ∑ d ∈ Finset.Icc 1 Y, (contactDaughterCoefficient q d) ^ 2

/-- The recursive energy profile the exceptional induction actually consumes. -/
def mertensEnergy (Y : ℕ) : ℚ := ((mertensSummatoryInt Y : ℚ)) ^ 2

/-- The daughter terms of the exceptional step are that recursive energy at the
smaller cutoff, never an assembled coefficient norm. -/
theorem exceptionalOwnerEnergyStep_mertensEnergy (C alpha3 alpha5 alpha7 : ℚ) :
    ExceptionalOwnerEnergyStep mertensEnergy C alpha3 alpha5 alpha7 ↔
      ∀ X : ℕ, mertensEnergy X ≤ C * (X : ℚ) +
        alpha3 * mertensEnergy (X / 9) + alpha5 * mertensEnergy (X / 25) +
        alpha7 * mertensEnergy (X / 49) :=
  Iff.rfl

/-- Computable evaluator for the daughter Mertens value. -/
def mertensEval (Y : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (Y + 1), μ n

theorem mertensEval_eq_mertensSummatoryInt (Y : ℕ) :
    mertensEval Y = mertensSummatoryInt Y := rfl

/-- Finite certificate: the daughter Mertens value vanishes at the cutoff two. -/
theorem mertensEval_two : mertensEval 2 = 0 := by
  native_decide

theorem mertensSummatoryInt_two : mertensSummatoryInt 2 = 0 := by
  rw [← mertensEval_eq_mertensSummatoryInt]
  exact mertensEval_two

/-- Finite certificates: the assembled coefficient norm is already positive at
the same cutoff, for every exceptional owner. -/
theorem contactDaughterCoefficientNorm_three_two :
    contactDaughterCoefficientNorm 3 2 = 2 := by
  native_decide

theorem contactDaughterCoefficientNorm_five_two :
    contactDaughterCoefficientNorm 5 2 = 5 := by
  native_decide

theorem contactDaughterCoefficientNorm_seven_two :
    contactDaughterCoefficientNorm 7 2 = 5 := by
  native_decide

/-- **Type mismatch between the two energies.**  No constant compares the
assembled `q^2` coefficient norm with the recursive Mertens energy at the same
daughter cutoff: the latter vanishes at `Y = 2` while the former does not.  The
frame route therefore cannot produce the `alpha_q * E (X / q^2)` term of
`ExceptionalOwnerEnergyStep`, whatever frame constant is proved. -/
theorem no_contactDaughterCoefficientNorm_mertensEnergy_constant
    {q : ℕ} (hq : q = 3 ∨ q = 5 ∨ q = 7) :
    ¬ ∃ alpha : ℚ, ∀ Y : ℕ,
      (contactDaughterCoefficientNorm q Y : ℚ) ≤ alpha * mertensEnergy Y := by
  rintro ⟨alpha, halpha⟩
  have hpos : 0 < contactDaughterCoefficientNorm q 2 := by
    rcases hq with rfl | rfl | rfl
    · rw [contactDaughterCoefficientNorm_three_two]; norm_num
    · rw [contactDaughterCoefficientNorm_five_two]; norm_num
    · rw [contactDaughterCoefficientNorm_seven_two]; norm_num
  have hzero : mertensEnergy 2 = 0 := by
    unfold mertensEnergy
    rw [mertensSummatoryInt_two]
    norm_num
  have h := halpha 2
  rw [hzero, mul_zero] at h
  have hposQ : (0 : ℚ) < (contactDaughterCoefficientNorm q 2 : ℚ) := by
    exact_mod_cast hpos
  linarith

/-- The same separation against an arbitrary dominating profile: no energy
profile dominating the assembled coefficient norm is the recursive Mertens
energy. -/
theorem dominating_profile_ne_mertensEnergy
    {q : ℕ} (hq : q = 3 ∨ q = 5 ∨ q = 7) {E : ℕ → ℚ}
    (hdom : ∀ Y : ℕ, (contactDaughterCoefficientNorm q Y : ℚ) ≤ E Y) :
    E ≠ mertensEnergy := by
  intro hE
  refine no_contactDaughterCoefficientNorm_mertensEnergy_constant hq ⟨1, fun Y => ?_⟩
  have := hdom Y
  rw [hE] at this
  linarith

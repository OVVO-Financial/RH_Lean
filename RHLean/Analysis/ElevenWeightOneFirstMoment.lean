import Mathlib
import RHLean.Analysis.FinitePrimeTMixing
import RHLean.Arithmetic.PrimeCombFiniteDifferenceFreshPrime
import RHLean.Arithmetic.PrimeCombFiniteDifferenceRecovery

/-!
# Exact first-moment action of the 11-layer on the T sector

The finite-prime spectral file records the abstract Walsh factor and the exact
cardinalities of the `11^2` zero-free/no-flip/singleton-flip classes.  Here we
package the same finite arithmetic law directly as an operator on first moments.

For each of the six source/destination sign coordinates, multiplication by the
prime-11 Euler sign has average `19/23` on the `115` zero-free residue classes.
Consequently *every* weight-one linear combination is multiplied by `19/23`,
and its square is multiplied by `(19/23)^2`.

The CRT section upgrades that finite average to a deterministic tensor theorem:
any complementary weight field on a modulus coprime to `11^2` may vary
arbitrarily, and the complete product orbit still sees exactly the same
`19/23` first-moment scalar.  No independence assumption is used.

The complete-contact section proves the missing least-square local mechanism:
for an odd prime owner `q`, each fixed physical affine offset has exactly one
`q^2` root.  Therefore, on a complete coprime super-orbit, restricting to that
`q^2` contact is exactly one copy of the complementary first moment.  This is a
finite equivalence, not a density estimate; the complementary field is arbitrary
and can carry all earlier-square masks, selected-prime signs, and Schur weights.
The combined theorem then shows that this exact q-square transport commutes with
the selected-11 layer, so the transported weight-one energy receives precisely
the same `(19/23)^2` factor.

The final section proves the exact operator-level intertwining with the
square-dilated Go scale on the actual recovered prime-wheel field `raw-2*smooth`.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Sign multiplier contributed by prime `11` to one of the six transition
coordinates.  On the zero-free residue set the coordinate is never divisible by
`11^2`, so divisibility by `11` is exactly the one-prime sign flip. -/
def elevenCoordinateMultiplier (i : Fin 6) (k : Fin 121) : ℚ :=
  if 11 ∣ tTransitionForm i k.1 then -1 else 1

/-- Unnormalized signed multiplier mass on the exact `115`-point zero-free
prime-11 residue population. -/
def elevenCoordinateMultiplierSum (i : Fin 6) : ℚ :=
  ∑ k ∈ elevenZeroFreeResidues, elevenCoordinateMultiplier i k

/-- Every coordinate has signed mass `105 - 10 = 95`: ten zero-free residues
flip that coordinate and the other 105 do not. -/
theorem elevenCoordinateMultiplierSum_eq_ninety_five (i : Fin 6) :
    elevenCoordinateMultiplierSum i = 95 := by
  fin_cases i <;>
    native_decide

/-- Normalized first-moment multiplier on one coordinate. -/
def elevenCoordinateMeanMultiplier (i : Fin 6) : ℚ :=
  elevenCoordinateMultiplierSum i / 115

/-- The direct residue average is the same `19/23` weight-one Walsh factor
already exposed abstractly by `FinitePrimeTMixing`. -/
theorem elevenCoordinateMeanMultiplier_eq_walsh_one (i : Fin 6) :
    elevenCoordinateMeanMultiplier i = onePrimeWalshFactor 11 1 := by
  rw [elevenCoordinateMeanMultiplier,
    elevenCoordinateMultiplierSum_eq_ninety_five,
    onePrimeWalshFactor_eleven_one]
  norm_num

/-- Coordinatewise first-moment action of the exact selected-11 zero-free law. -/
def elevenWeightOneFirstMomentAction (z : Fin 6 → ℚ) : Fin 6 → ℚ :=
  fun i => elevenCoordinateMeanMultiplier i * z i

/-- **Exact scalar action on the whole weight-one sector.** -/
theorem elevenWeightOneFirstMomentAction_apply
    (z : Fin 6 → ℚ) (i : Fin 6) :
    elevenWeightOneFirstMomentAction z i =
      onePrimeWalshFactor 11 1 * z i := by
  rw [elevenWeightOneFirstMomentAction,
    elevenCoordinateMeanMultiplier_eq_walsh_one]

/-- Therefore every linear functional of the six weight-one coordinates is
multiplied by exactly the same scalar. -/
theorem elevenWeightOneFirstMomentAction_linearFunctional
    (a z : Fin 6 → ℚ) :
    (∑ i : Fin 6, a i * elevenWeightOneFirstMomentAction z i) =
      onePrimeWalshFactor 11 1 * (∑ i : Fin 6, a i * z i) := by
  simp only [elevenWeightOneFirstMomentAction_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- **Exact rank-one energy contraction.** -/
theorem elevenWeightOneFirstMomentAction_linearFunctional_sq
    (a z : Fin 6 → ℚ) :
    (∑ i : Fin 6, a i * elevenWeightOneFirstMomentAction z i) ^ 2 =
      (onePrimeWalshFactor 11 1) ^ 2 *
        (∑ i : Fin 6, a i * z i) ^ 2 := by
  rw [elevenWeightOneFirstMomentAction_linearFunctional]
  ring

/-- The exact square multiplier is strictly subunit. -/
theorem elevenWeightOneFirstMoment_squareFactor_lt_one :
    (onePrimeWalshFactor 11 1) ^ 2 < (1 : ℚ) := by
  rw [onePrimeWalshFactor_eleven_one]
  norm_num

/-! ## Deterministic CRT tensorization of the 11 first moment -/

/-- A finite sum of a pure tensor on coprime residue coordinates factors
exactly.  This is just the Chinese remainder equivalence followed by Fubini. -/
theorem coprimeZMod_sum_tensor
    (m n : ℕ) [NeZero m] [NeZero n]
    (hcop : Nat.Coprime m n)
    (f : ZMod m → ℚ) (g : ZMod n → ℚ) :
    (∑ z : ZMod (m * n),
      f ((ZMod.chineseRemainder hcop) z).1 *
        g ((ZMod.chineseRemainder hcop) z).2) =
      (∑ a : ZMod m, f a) * (∑ b : ZMod n, g b) := by
  calc
    (∑ z : ZMod (m * n),
        f ((ZMod.chineseRemainder hcop) z).1 *
          g ((ZMod.chineseRemainder hcop) z).2) =
      ∑ ab : ZMod m × ZMod n, f ab.1 * g ab.2 := by
        exact Fintype.sum_equiv
          (ZMod.chineseRemainder hcop).toEquiv
          (fun z : ZMod (m * n) =>
            f ((ZMod.chineseRemainder hcop) z).1 *
              g ((ZMod.chineseRemainder hcop) z).2)
          (fun ab : ZMod m × ZMod n => f ab.1 * g ab.2)
          (by intro z; rfl)
    _ = (∑ a : ZMod m, f a) * (∑ b : ZMod n, g b) := by
      rw [Fintype.sum_prod_type]
      calc
        (∑ a : ZMod m, ∑ b : ZMod n, f a * g b) =
            ∑ a : ZMod m, f a * (∑ b : ZMod n, g b) := by
          apply Fintype.sum_congr
          intro a
          rw [Finset.mul_sum]
        _ = (∑ a : ZMod m, f a) * (∑ b : ZMod n, g b) := by
          rw [Finset.sum_mul]

/-- Zero-free indicator of the local prime-11 transition residue. -/
def elevenZeroFreeIndicatorZMod (z : ZMod 121) : ℚ :=
  if tSquareZeroFreeAt 11 z.val then 1 else 0

/-- Signed prime-11 multiplier, with square-zero residues killed. -/
def elevenZeroFreeCoordinateMultiplierZMod
    (i : Fin 6) (z : ZMod 121) : ℚ :=
  if tSquareZeroFreeAt 11 z.val then
    if 11 ∣ tTransitionForm i z.val then -1 else 1
  else 0

/-- The local zero-free indicator has total mass `115`. -/
theorem sum_elevenZeroFreeIndicatorZMod :
    (∑ z : ZMod 121, elevenZeroFreeIndicatorZMod z) = 115 := by
  native_decide

/-- Every weight-one coordinate has local signed mass `95`. -/
theorem sum_elevenZeroFreeCoordinateMultiplierZMod (i : Fin 6) :
    (∑ z : ZMod 121, elevenZeroFreeCoordinateMultiplierZMod i z) = 95 := by
  fin_cases i <;> native_decide

/-- **Deterministic complete-fibre 11 intertwining.**  Let `g` be an arbitrary
complementary arithmetic field on any modulus `M` coprime to `121`.  On the
complete product orbit, the selected-11 coordinate acts by exactly `19/23` on
the first moment.  No constancy, randomness, or decorrelation of `g` is assumed;
CRT makes the two finite coordinates a literal product. -/
theorem eleven_coprimeTensor_firstMoment
    (M : ℕ) [NeZero M] (hcop : Nat.Coprime 121 M)
    (i : Fin 6) (g : ZMod M → ℚ) :
    (∑ z : ZMod (121 * M),
      elevenZeroFreeCoordinateMultiplierZMod i
          ((ZMod.chineseRemainder hcop) z).1 *
        g ((ZMod.chineseRemainder hcop) z).2) =
      onePrimeWalshFactor 11 1 *
        (∑ z : ZMod (121 * M),
          elevenZeroFreeIndicatorZMod
              ((ZMod.chineseRemainder hcop) z).1 *
            g ((ZMod.chineseRemainder hcop) z).2) := by
  have hsigned := coprimeZMod_sum_tensor 121 M hcop
    (elevenZeroFreeCoordinateMultiplierZMod i) g
  have hzero := coprimeZMod_sum_tensor 121 M hcop
    elevenZeroFreeIndicatorZMod g
  rw [sum_elevenZeroFreeCoordinateMultiplierZMod] at hsigned
  rw [sum_elevenZeroFreeIndicatorZMod] at hzero
  rw [hsigned, hzero, onePrimeWalshFactor_eleven_one]
  ring

/-- Squaring the exact complete-fibre identity gives the same energy factor
used in the `ElevenQ2EnergyStep` engine. -/
theorem eleven_coprimeTensor_firstMoment_sq
    (M : ℕ) [NeZero M] (hcop : Nat.Coprime 121 M)
    (i : Fin 6) (g : ZMod M → ℚ) :
    (∑ z : ZMod (121 * M),
      elevenZeroFreeCoordinateMultiplierZMod i
          ((ZMod.chineseRemainder hcop) z).1 *
        g ((ZMod.chineseRemainder hcop) z).2) ^ 2 =
      (onePrimeWalshFactor 11 1) ^ 2 *
        (∑ z : ZMod (121 * M),
          elevenZeroFreeIndicatorZMod
              ((ZMod.chineseRemainder hcop) z).1 *
            g ((ZMod.chineseRemainder hcop) z).2) ^ 2 := by
  rw [eleven_coprimeTensor_firstMoment M hcop i g]
  ring

/-! ## Complete q-square contact fibres are exact daughters -/

/-- Multiplication by a residue coprime to the modulus, followed by translation,
is a permutation of the complete residue population. -/
def zmodAffineEquivOfCoprime
    (m a : ℕ) [NeZero m] (hcop : Nat.Coprime a m) (b : ZMod m) :
    ZMod m ≃ ZMod m where
  toFun z := (a : ZMod m) * z + b
  invFun y := (a : ZMod m)⁻¹ * (y - b)
  left_inv := by
    intro z
    have hu : IsUnit (a : ZMod m) :=
      (ZMod.isUnit_iff_coprime a m).2 hcop
    dsimp
    calc
      (a : ZMod m)⁻¹ * ((a : ZMod m) * z + b - b) =
          ((a : ZMod m)⁻¹ * (a : ZMod m)) * z := by ring
      _ = z := by rw [ZMod.inv_mul_of_unit _ hu, one_mul]
  right_inv := by
    intro y
    have hu : IsUnit (a : ZMod m) :=
      (ZMod.isUnit_iff_coprime a m).2 hcop
    dsimp
    calc
      (a : ZMod m) * ((a : ZMod m)⁻¹ * (y - b)) + b =
          ((a : ZMod m) * (a : ZMod m)⁻¹) * (y - b) + b := by ring
      _ = y := by
        rw [ZMod.mul_inv_of_unit _ hu]
        ring

/-- Local indicator that the physical affine site `4*k+a` is hit by `q^2`.
Writing the condition in `ZMod (q^2)` makes the one-root geometry explicit. -/
def qSquareOffsetHitIndicator (q a : ℕ) (z : ZMod (q ^ 2)) : ℚ :=
  if (4 : ZMod (q ^ 2)) * z + (a : ZMod (q ^ 2)) = 0 then 1 else 0

/-- For every odd prime owner and every fixed physical offset, the `q^2` contact
has exactly one residue in a complete local period. -/
theorem sum_qSquareOffsetHitIndicator_eq_one
    {q a : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    (∑ z : ZMod (q ^ 2), qSquareOffsetHitIndicator q a z) = 1 := by
  letI : NeZero (q ^ 2) := ⟨pow_ne_zero 2 hq.ne_zero⟩
  have hcop : Nat.Coprime (q ^ 2) 4 := by
    simpa using
      (Nat.coprime_pow_primes (p := q) (q := 2) 2 2
        hq Nat.prime_two hq2)
  let e : ZMod (q ^ 2) ≃ ZMod (q ^ 2) :=
    zmodAffineEquivOfCoprime (q ^ 2) 4 hcop.symm (a : ZMod (q ^ 2))
  calc
    (∑ z : ZMod (q ^ 2), qSquareOffsetHitIndicator q a z) =
        ∑ y : ZMod (q ^ 2), if y = 0 then (1 : ℚ) else 0 := by
      exact Fintype.sum_equiv e
        (fun z : ZMod (q ^ 2) => qSquareOffsetHitIndicator q a z)
        (fun y : ZMod (q ^ 2) => if y = 0 then (1 : ℚ) else 0)
        (by
          intro z
          simp [e, qSquareOffsetHitIndicator, zmodAffineEquivOfCoprime])
    _ = 1 := by simp

/-- The modular contact indicator is literally the natural divisibility
condition used by the physical least-square carrier. -/
theorem qSquareOffsetHitIndicator_natCast
    {q a k : ℕ} (hq : q.Prime) :
    qSquareOffsetHitIndicator q a (k : ZMod (q ^ 2)) =
      (if q ^ 2 ∣ 4 * k + a then 1 else 0) := by
  letI : NeZero (q ^ 2) := ⟨pow_ne_zero 2 hq.ne_zero⟩
  unfold qSquareOffsetHitIndicator
  have hcast :
      (4 : ZMod (q ^ 2)) * (k : ZMod (q ^ 2)) +
          (a : ZMod (q ^ 2)) =
        ((4 * k + a : ℕ) : ZMod (q ^ 2)) := by
    push_cast
    rfl
  rw [hcast, ZMod.natCast_eq_zero_iff]

/-- **Complete least-square contact / daughter equivalence.**  Let `g` be any
complementary arithmetic first-moment field on a modulus coprime to `q^2`.
Restricting a complete product orbit to one physical `q^2` contact leaves
*exactly one copy* of the complementary first moment.  Thus every earlier-square
mask, selected-prime sign, or rank-one Schur weight may be carried inside `g`
without loss: the q-square coordinate is removed by a finite bijection, not by
an estimate or an independence assumption. -/
theorem qSquareOffset_coprimeTensor_firstMoment
    (q M a : ℕ) [NeZero M]
    (hq : q.Prime) (hq2 : q ≠ 2)
    (hcop : Nat.Coprime (q ^ 2) M)
    (g : ZMod M → ℚ) :
    (∑ z : ZMod ((q ^ 2) * M),
      qSquareOffsetHitIndicator q a
          ((ZMod.chineseRemainder hcop) z).1 *
        g ((ZMod.chineseRemainder hcop) z).2) =
      ∑ b : ZMod M, g b := by
  letI : NeZero (q ^ 2) := ⟨pow_ne_zero 2 hq.ne_zero⟩
  have htensor := coprimeZMod_sum_tensor (q ^ 2) M hcop
    (qSquareOffsetHitIndicator q a) g
  rw [sum_qSquareOffsetHitIndicator_eq_one hq hq2] at htensor
  simpa using htensor

/-- The rank-one energy carried by a complete q-square contact is therefore
identical to the daughter rank-one energy before the independent 11-layer is
applied. -/
theorem qSquareOffset_coprimeTensor_firstMoment_sq
    (q M a : ℕ) [NeZero M]
    (hq : q.Prime) (hq2 : q ≠ 2)
    (hcop : Nat.Coprime (q ^ 2) M)
    (g : ZMod M → ℚ) :
    (∑ z : ZMod ((q ^ 2) * M),
      qSquareOffsetHitIndicator q a
          ((ZMod.chineseRemainder hcop) z).1 *
        g ((ZMod.chineseRemainder hcop) z).2) ^ 2 =
      (∑ b : ZMod M, g b) ^ 2 := by
  rw [qSquareOffset_coprimeTensor_firstMoment q M a hq hq2 hcop g]

/-- **Full complete-fibre intertwining of q² contact and the 11 layer.**  The
q-square coordinate may be removed first, or the selected-11 weight-one action
may be applied first: the resulting first moment is identical.  The field on all
remaining prime coordinates is arbitrary.  Hence least-owner masks, selected
signs, and the rank-one Schur first moment survive the q² descent without an
independence hypothesis. -/
theorem qSquareOffset_eleven_coprimeTensor_firstMoment
    (q M a : ℕ) [NeZero M]
    (hq : q.Prime) (hq2 : q ≠ 2)
    (hqcop : Nat.Coprime (q ^ 2) (121 * M))
    (h11cop : Nat.Coprime 121 M)
    (i : Fin 6) (g : ZMod M → ℚ) :
    (∑ z : ZMod ((q ^ 2) * (121 * M)),
      qSquareOffsetHitIndicator q a
          ((ZMod.chineseRemainder hqcop) z).1 *
        (elevenZeroFreeCoordinateMultiplierZMod i
            ((ZMod.chineseRemainder h11cop)
              ((ZMod.chineseRemainder hqcop) z).2).1 *
          g ((ZMod.chineseRemainder h11cop)
              ((ZMod.chineseRemainder hqcop) z).2).2)) =
      onePrimeWalshFactor 11 1 *
        (∑ z : ZMod ((q ^ 2) * (121 * M)),
          qSquareOffsetHitIndicator q a
              ((ZMod.chineseRemainder hqcop) z).1 *
            (elevenZeroFreeIndicatorZMod
                ((ZMod.chineseRemainder h11cop)
                  ((ZMod.chineseRemainder hqcop) z).2).1 *
              g ((ZMod.chineseRemainder h11cop)
                  ((ZMod.chineseRemainder hqcop) z).2).2)) := by
  let Gsigned : ZMod (121 * M) → ℚ := fun w =>
    elevenZeroFreeCoordinateMultiplierZMod i
        ((ZMod.chineseRemainder h11cop) w).1 *
      g ((ZMod.chineseRemainder h11cop) w).2
  let Gzero : ZMod (121 * M) → ℚ := fun w =>
    elevenZeroFreeIndicatorZMod
        ((ZMod.chineseRemainder h11cop) w).1 *
      g ((ZMod.chineseRemainder h11cop) w).2
  have hqSigned := qSquareOffset_coprimeTensor_firstMoment
    q (121 * M) a hq hq2 hqcop Gsigned
  have hqZero := qSquareOffset_coprimeTensor_firstMoment
    q (121 * M) a hq hq2 hqcop Gzero
  have h11 := eleven_coprimeTensor_firstMoment M h11cop i g
  have h11' :
      (∑ w : ZMod (121 * M), Gsigned w) =
        onePrimeWalshFactor 11 1 *
          (∑ w : ZMod (121 * M), Gzero w) := by
    simpa [Gsigned, Gzero] using h11
  calc
    (∑ z : ZMod ((q ^ 2) * (121 * M)),
        qSquareOffsetHitIndicator q a
            ((ZMod.chineseRemainder hqcop) z).1 *
          (elevenZeroFreeCoordinateMultiplierZMod i
              ((ZMod.chineseRemainder h11cop)
                ((ZMod.chineseRemainder hqcop) z).2).1 *
            g ((ZMod.chineseRemainder h11cop)
                ((ZMod.chineseRemainder hqcop) z).2).2)) =
      ∑ w : ZMod (121 * M), Gsigned w := by
        simpa [Gsigned] using hqSigned
    _ = onePrimeWalshFactor 11 1 *
        (∑ w : ZMod (121 * M), Gzero w) := h11'
    _ = onePrimeWalshFactor 11 1 *
        (∑ z : ZMod ((q ^ 2) * (121 * M)),
          qSquareOffsetHitIndicator q a
              ((ZMod.chineseRemainder hqcop) z).1 *
            (elevenZeroFreeIndicatorZMod
                ((ZMod.chineseRemainder h11cop)
                  ((ZMod.chineseRemainder hqcop) z).2).1 *
              g ((ZMod.chineseRemainder h11cop)
                  ((ZMod.chineseRemainder hqcop) z).2).2)) := by
        rw [hqZero]

/-- Squaring the commuting first-moment diagram gives the exact `(19/23)^2`
energy multiplier on every complete q-square contact fibre. -/
theorem qSquareOffset_eleven_coprimeTensor_firstMoment_sq
    (q M a : ℕ) [NeZero M]
    (hq : q.Prime) (hq2 : q ≠ 2)
    (hqcop : Nat.Coprime (q ^ 2) (121 * M))
    (h11cop : Nat.Coprime 121 M)
    (i : Fin 6) (g : ZMod M → ℚ) :
    (∑ z : ZMod ((q ^ 2) * (121 * M)),
      qSquareOffsetHitIndicator q a
          ((ZMod.chineseRemainder hqcop) z).1 *
        (elevenZeroFreeCoordinateMultiplierZMod i
            ((ZMod.chineseRemainder h11cop)
              ((ZMod.chineseRemainder hqcop) z).2).1 *
          g ((ZMod.chineseRemainder h11cop)
              ((ZMod.chineseRemainder hqcop) z).2).2)) ^ 2 =
      (onePrimeWalshFactor 11 1) ^ 2 *
        (∑ z : ZMod ((q ^ 2) * (121 * M)),
          qSquareOffsetHitIndicator q a
              ((ZMod.chineseRemainder hqcop) z).1 *
            (elevenZeroFreeIndicatorZMod
                ((ZMod.chineseRemainder h11cop)
                  ((ZMod.chineseRemainder hqcop) z).2).1 *
              g ((ZMod.chineseRemainder h11cop)
                  ((ZMod.chineseRemainder hqcop) z).2).2)) ^ 2 := by
  rw [qSquareOffset_eleven_coprimeTensor_firstMoment
    q M a hq hq2 hqcop h11cop i g]
  ring

/-! ## Exact all-prime Euler / q-square intertwining -/

/-- Square-root prime-wheel recovery is respected by an arbitrary independent
finite Möbius difference operator `D_T`. -/
theorem finiteDifferenceOperator_primeWheelRecovery_general
    (P T : Finset ℕ) (upper x : ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage P upper)
    (hx : x ≤ upper) :
    finiteDifferenceOperator T
        (fun y =>
          primeWheelRawPositivePrefix P y -
            2 * primeWheelSmoothPositivePrefix P upper y) x =
      finiteDifferenceOperator T moebiusPositivePrefix x := by
  classical
  unfold finiteDifferenceOperator
  apply Finset.sum_congr rfl
  intro d hd
  have hdx : x / d ≤ upper :=
    (Nat.div_le_self x d).trans hx
  have hprefix :=
    primeWheelRaw_sub_two_smooth_eq_moebiusPositivePrefix
      P upper (x / d) hprime hcover hdx
  rw [show
    shift d
        (fun y =>
          primeWheelRawPositivePrefix P y -
            2 * primeWheelSmoothPositivePrefix P upper y) x =
      shift d moebiusPositivePrefix x by
        simpa [shift] using hprefix]

/-- The same all-prime recovery after a multiplicative daughter shift. -/
theorem finiteDifferenceOperator_primeWheelRecovery_squareShift
    (P T : Finset ℕ) (upper x q : ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage P upper)
    (hx : x ≤ upper) :
    finiteDifferenceOperator T
        (shift (q * q) (fun y =>
          primeWheelRawPositivePrefix P y -
            2 * primeWheelSmoothPositivePrefix P upper y)) x =
      finiteDifferenceOperator T
        (shift (q * q) moebiusPositivePrefix) x := by
  rw [finiteDifferenceOperator_shift_comm,
    finiteDifferenceOperator_shift_comm]
  have hchild : x / (q * q) ≤ upper :=
    (Nat.div_le_self x (q * q)).trans hx
  simpa [shift] using
    finiteDifferenceOperator_primeWheelRecovery_general
      P T upper (x / (q * q)) hprime hcover hchild

/-- Recovery is preserved after one arbitrary fresh-prime difference. -/
theorem finiteDifferenceOperator_primeWheelRecovery_freshDifference
    (P T : Finset ℕ) (upper x p : ℕ)
    (hprime : ∀ r ∈ P, Nat.Prime r)
    (hcover : PrimeWheelSqrtCoverage P upper)
    (hx : x ≤ upper) :
    finiteDifferenceOperator T
        (freshPrimeDifference p (fun y =>
          primeWheelRawPositivePrefix P y -
            2 * primeWheelSmoothPositivePrefix P upper y)) x =
      finiteDifferenceOperator T
        (freshPrimeDifference p moebiusPositivePrefix) x := by
  unfold freshPrimeDifference
  rw [finiteDifferenceOperator_sub, finiteDifferenceOperator_sub,
    finiteDifferenceOperator_shift_comm,
    finiteDifferenceOperator_shift_comm]
  have hbase :=
    finiteDifferenceOperator_primeWheelRecovery_general
      P T upper x hprime hcover hx
  have hpchild : x / p ≤ upper :=
    (Nat.div_le_self x p).trans hx
  have hchild :=
    finiteDifferenceOperator_primeWheelRecovery_general
      P T upper (x / p) hprime hcover hpchild
  simp only [Pi.sub_apply, shift]
  rw [hbase, hchild]

/-- **Actual Möbius prime-11 / q² intertwining.** -/
theorem finiteDifferenceOperator_recoveredMobius_eleven_q2_intertwining
    (P T : Finset ℕ) (upper x q : ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage P upper)
    (hx : x ≤ upper) :
    finiteDifferenceOperator T
        (freshPrimeDifference 11
          (shift (q * q) (fun y =>
            primeWheelRawPositivePrefix P y -
              2 * primeWheelSmoothPositivePrefix P upper y))) x =
      finiteDifferenceOperator T
        (freshPrimeDifference 11
          (shift (q * q) moebiusPositivePrefix)) x := by
  rw [finiteDifferenceOperator_eleven_squareShift_intertwining,
    finiteDifferenceOperator_eleven_squareShift_intertwining]
  have hchild : x / (q * q) ≤ upper :=
    (Nat.div_le_self x (q * q)).trans hx
  simpa [shift] using
    finiteDifferenceOperator_primeWheelRecovery_freshDifference
      P T upper (x / (q * q)) 11 hprime hcover hchild

end RHLean.Analysis

import Mathlib
import «research.LOW_OWNER_Q2_ENDPOINT_FREQUENCY_DISTANCE»

/-!
# Exact endpoint-arc Fubini for finite wheel frequencies

The physical information "distance from a known endpoint" has an exact Fourier
form.  For the finite Dirichlet response at one wheel frequency,

  D_{A+d}(r) - D_A(r) = chi(r)^A D_d(r).

Thus the difference of two pinned prefixes is not a new global object: it is a
finite sum of endpoint-phased short arcs.  For a nonzero frequency the short arc
then depends only on `d mod c_r`, where `c_r` is the reduced additive conductor.

This file is deliberately prior to any identification with a particular
Mertens shell.  It proves the exact finite harmonic dictionary, with no norm or
nonconcentration estimate.
-/

noncomputable section
open scoped BigOperators
open AddChar

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- Finite Dirichlet kernels split exactly at an intermediate distance. -/
theorem primeWheelDirichletKernel_add
    (W : PrimeWheelFiniteSystem) (A d : ℕ)
    (r : ZMod W.modulus) :
    primeWheelDirichletKernel W (A + d) r =
      primeWheelDirichletKernel W A r +
        ZMod.stdAddChar r ^ A * primeWheelDirichletKernel W d r := by
  by_cases hr : r = 0
  · subst r
    simp [primeWheelDirichletKernel_zero]
  · rw [primeWheelDirichletKernel_eq_geom_of_ne_zero W (A + d) r hr,
      primeWheelDirichletKernel_eq_geom_of_ne_zero W A r hr,
      primeWheelDirichletKernel_eq_geom_of_ne_zero W d r hr,
      pow_add]
    ring

/-- One frequency contribution to the forward arc of length `d` starting after
prefix length `A`. -/
def primeWheelForwardArcFrequencyAtom
    (W : PrimeWheelFiniteSystem) (A d : ℕ)
    (r : ZMod W.modulus) : ℂ :=
  primeWheelPinnedCoefficient W r *
    ZMod.stdAddChar r ^ A * primeWheelDirichletKernel W d r

/-- **Exact endpoint-arc Fubini.**  A difference of two finite pinned prefixes
is the sum of the endpoint-phased short frequency arcs. -/
theorem primeWheelDirichletPrefix_add_sub_eq_sum_forwardArc
    (W : PrimeWheelFiniteSystem) (A d : ℕ) :
    primeWheelDirichletPrefix W (A + d) -
        primeWheelDirichletPrefix W A =
      ∑ r : ZMod W.modulus,
        primeWheelForwardArcFrequencyAtom W A d r := by
  unfold primeWheelDirichletPrefix primeWheelForwardArcFrequencyAtom
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [primeWheelDirichletKernel_add W A d r]
  ring

/-- At a nonzero frequency, the short endpoint arc depends only on the physical
distance modulo the reduced additive conductor. -/
theorem primeWheelForwardArcFrequencyAtom_eq_reducedDistance
    (W : PrimeWheelFiniteSystem) (A d : ℕ)
    (r : ZMod W.modulus) (hr : r ≠ 0) :
    primeWheelForwardArcFrequencyAtom W A d r =
      primeWheelPinnedCoefficient W r *
        ZMod.stdAddChar r ^ A *
          primeWheelDirichletKernel W
            (d % reducedAdditiveConductor r) r := by
  unfold primeWheelForwardArcFrequencyAtom
  rw [primeWheelDirichletKernel_eq_mod_reducedAdditiveConductor W d r hr]

/-- The complete forward prefix difference can be partitioned into the zero
frequency plus nonzero residual-distance atoms without changing the sum. -/
theorem primeWheelDirichletPrefix_add_sub_eq_zero_add_reducedNonzero
    (W : PrimeWheelFiniteSystem) (A d : ℕ) :
    primeWheelDirichletPrefix W (A + d) -
        primeWheelDirichletPrefix W A =
      primeWheelForwardArcFrequencyAtom W A d 0 +
        ∑ r : ZMod W.modulus,
          if r = 0 then 0 else
            primeWheelPinnedCoefficient W r *
              ZMod.stdAddChar r ^ A *
                primeWheelDirichletKernel W
                  (d % reducedAdditiveConductor r) r := by
  rw [primeWheelDirichletPrefix_add_sub_eq_sum_forwardArc W A d]
  classical
  let f : ZMod W.modulus → ℂ :=
    fun r => primeWheelForwardArcFrequencyAtom W A d r
  have hsplitPointwise : ∀ r : ZMod W.modulus,
      f r =
        (if r = 0 then f 0 else 0) +
        (if r = 0 then 0 else f r) := by
    intro r
    by_cases hr : r = 0
    · subst r
      simp
    · simp [hr]
  calc
    (∑ r : ZMod W.modulus, primeWheelForwardArcFrequencyAtom W A d r) =
        ∑ r : ZMod W.modulus,
          ((if r = 0 then f 0 else 0) +
            (if r = 0 then 0 else f r)) := by
      apply Finset.sum_congr rfl
      intro r _hrmem
      simpa [f] using hsplitPointwise r
    _ = (∑ r : ZMod W.modulus, if r = 0 then f 0 else 0) +
        ∑ r : ZMod W.modulus, if r = 0 then 0 else f r := by
      rw [Finset.sum_add_distrib]
    _ = f 0 +
        ∑ r : ZMod W.modulus, if r = 0 then 0 else f r := by
      simp
    _ = primeWheelForwardArcFrequencyAtom W A d 0 +
        ∑ r : ZMod W.modulus,
          if r = 0 then 0 else
            primeWheelPinnedCoefficient W r *
              ZMod.stdAddChar r ^ A *
                primeWheelDirichletKernel W
                  (d % reducedAdditiveConductor r) r := by
      dsimp [f]
      congr 1
      apply Finset.sum_congr rfl
      intro r _hrmem
      by_cases hr : r = 0
      · simp [hr]
      · simp only [hr, if_false]
        exact primeWheelForwardArcFrequencyAtom_eq_reducedDistance W A d r hr


/-!
## Shifted-arc Gram = physical overlap

The start phase is not disposable.  For an arc of prefix-coordinate length
\`d\` beginning after prefix coordinate \`A\`, define the pure window kernel

  K_{A,d}(r) = chi(r)^A D_d(r).

The normalized bilinear Fourier Gram of two such kernels is exactly the
physical overlap of the two shifted windows.  This is the deterministic
nonalignment identity needed before any prime-spacing estimate: offset windows
can interact spectrally only to the extent that they overlap physically.
-/

/-- Physical forward-arc indicator in prefix coordinates.  The arc represented
by the prefix difference at lengths \`A+d\` and \`A\` is
\`(lower+A, lower+A+d]\`. -/
def primeWheelForwardArcWindow
    (W : PrimeWheelFiniteSystem) (A d : ℕ) : ZMod W.modulus → ℂ :=
  fun z =>
    if W.lower + A < z.val ∧ z.val ≤ W.lower + (A + d) then 1 else 0

/-- The pure shifted Dirichlet kernel of one physical forward arc.  Unlike an
absolute Dirichlet bound, this retains the starting offset \`A\`. -/
def primeWheelShiftedArcKernel
    (W : PrimeWheelFiniteSystem) (A d : ℕ)
    (r : ZMod W.modulus) : ℂ :=
  ZMod.stdAddChar r ^ A * primeWheelDirichletKernel W d r

/-- A forward-arc indicator is exactly the difference of the two pinned prefix
windows that bound it. -/
theorem primeWheelForwardArcWindow_eq_prefix_sub
    (W : PrimeWheelFiniteSystem) (A d : ℕ) :
    primeWheelForwardArcWindow W A d =
      W.torusPrefixWindow (W.lower + (A + d)) -
        W.torusPrefixWindow (W.lower + A) := by
  funext z
  unfold primeWheelForwardArcWindow
    PrimeWheelFiniteSystem.torusPrefixWindow
  by_cases hzlow : z.val ≤ W.lower
  · have hlow : ¬ W.lower < z.val := by omega
    have hstart : ¬ W.lower + A < z.val := by omega
    simp [hlow, hstart]
  · have hlow : W.lower < z.val := by omega
    by_cases hzA : z.val ≤ W.lower + A
    · have hstart : ¬ W.lower + A < z.val := by omega
      have hzEnd : z.val ≤ W.lower + (A + d) := by omega
      simp [hlow, hzA, hstart, hzEnd]
    · have hstart : W.lower + A < z.val := by omega
      by_cases hzEnd : z.val ≤ W.lower + (A + d)
      · simp [hlow, hzA, hstart, hzEnd]
      · simp [hlow, hzA, hstart, hzEnd]

/-- Exact DFT of a shifted physical arc.  The pinned arithmetic phase is common
to every arc; the extra factor \`chi(r)^A\` is the physically different starting
offset that must be retained in the Gram. -/
theorem dft_primeWheelForwardArcWindow_neg_eq
    (W : PrimeWheelFiniteSystem) (A d : ℕ)
    (r : ZMod W.modulus)
    (hupper : W.lower + (A + d) ≤ W.upper) :
    ZMod.dft (primeWheelForwardArcWindow W A d) (-r) =
      primeWheelPinnedPhase W r * primeWheelShiftedArcKernel W A d r := by
  have hshort : W.lower + A ≤ W.upper := by omega
  have hlong :=
    prefixWindowSpectrum_neg_eq_phase_mul_dirichlet W (A + d) r hupper
  have hbase :=
    prefixWindowSpectrum_neg_eq_phase_mul_dirichlet W A r hshort
  rw [primeWheelForwardArcWindow_eq_prefix_sub]
  rw [map_sub]
  change
    W.prefixWindowSpectrum (W.lower + (A + d)) (-r) -
        W.prefixWindowSpectrum (W.lower + A) (-r) =
      primeWheelPinnedPhase W r * primeWheelShiftedArcKernel W A d r
  rw [hlong, hbase, primeWheelDirichletKernel_add W A d r]
  unfold primeWheelShiftedArcKernel
  ring

/-- Opposite pinned phases cancel exactly. -/
theorem primeWheelPinnedPhase_neg_mul_self
    (W : PrimeWheelFiniteSystem) (r : ZMod W.modulus) :
    primeWheelPinnedPhase W (-r) * primeWheelPinnedPhase W r = 1 := by
  unfold primeWheelPinnedPhase
  rw [← map_add_eq_mul]
  have hzero :
      (((W.lower + 1 : ℕ) : ZMod W.modulus) * (-r)) +
          (((W.lower + 1 : ℕ) : ZMod W.modulus) * r) = 0 := by
    ring
  rw [hzero]
  exact AddChar.map_zero_eq_one
    (ZMod.stdAddChar : AddChar (ZMod W.modulus) ℂ)

/-- Physical pairing of two shifted arc windows is literally their overlap
indicator count. -/
theorem finiteTorusPairing_forwardArcWindow_eq_overlap
    (W : PrimeWheelFiniteSystem) (A d B e : ℕ) :
    finiteTorusPairing
        (primeWheelForwardArcWindow W A d)
        (primeWheelForwardArcWindow W B e) =
      ∑ z : ZMod W.modulus,
        if (W.lower + A < z.val ∧ z.val ≤ W.lower + (A + d)) ∧
            (W.lower + B < z.val ∧ z.val ≤ W.lower + (B + e))
        then 1 else 0 := by
  unfold finiteTorusPairing primeWheelForwardArcWindow
  apply Finset.sum_congr rfl
  intro z _hz
  by_cases hA :
      W.lower + A < z.val ∧ z.val ≤ W.lower + (A + d)
  · by_cases hB :
        W.lower + B < z.val ∧ z.val ≤ W.lower + (B + e)
    · simp [hA, hB]
    · simp [hA, hB]
  · simp [hA]

/-- **Shifted-arc Gram = physical overlap.**

After normalizing by the torus cardinality, the complete frequency Gram of the
two offset Dirichlet arcs is exactly the number of torus sites lying in both
physical windows.  In particular, replacing the phases by absolute values
throws away an exact geometric restriction: disjoint shifted windows have zero
complete Gram coupling. -/
theorem primeWheelShiftedArcGram_eq_physicalOverlap
    (W : PrimeWheelFiniteSystem) (A d B e : ℕ)
    (hAupper : W.lower + (A + d) ≤ W.upper)
    (hBupper : W.lower + (B + e) ≤ W.upper) :
    ((W.modulus : ℂ)⁻¹) *
        ∑ r : ZMod W.modulus,
          primeWheelShiftedArcKernel W A d (-r) *
            primeWheelShiftedArcKernel W B e r =
      ∑ z : ZMod W.modulus,
        if (W.lower + A < z.val ∧ z.val ≤ W.lower + (A + d)) ∧
            (W.lower + B < z.val ∧ z.val ≤ W.lower + (B + e))
        then 1 else 0 := by
  let f : ZMod W.modulus → ℂ := primeWheelForwardArcWindow W A d
  let g : ZMod W.modulus → ℂ := primeWheelForwardArcWindow W B e
  have hpair := finiteTorusPairing_eq_spectral f g
  have hspec :
      finiteTorusPairing f g =
        ((W.modulus : ℂ)⁻¹) *
          ∑ r : ZMod W.modulus,
            primeWheelShiftedArcKernel W A d (-r) *
              primeWheelShiftedArcKernel W B e r := by
    rw [hpair]
    unfold finiteTorusSpectralPairing
    congr 1
    apply Finset.sum_congr rfl
    intro r _hr
    have hAf :=
      dft_primeWheelForwardArcWindow_neg_eq W A d (-r) hAupper
    have hBg :=
      dft_primeWheelForwardArcWindow_neg_eq W B e r hBupper
    have hAf' :
        ZMod.dft (primeWheelForwardArcWindow W A d) r =
          primeWheelPinnedPhase W (-r) *
            primeWheelShiftedArcKernel W A d (-r) := by
      simpa only [neg_neg] using hAf
    have hphase := primeWheelPinnedPhase_neg_mul_self W r
    change
      ZMod.dft f r * ZMod.dft g (-r) =
        primeWheelShiftedArcKernel W A d (-r) *
          primeWheelShiftedArcKernel W B e r
    dsimp [f, g]
    rw [hAf', hBg]
    exact
      (show
        (primeWheelPinnedPhase W (-r) *
            primeWheelShiftedArcKernel W A d (-r)) *
          (primeWheelPinnedPhase W r *
            primeWheelShiftedArcKernel W B e r) =
          primeWheelShiftedArcKernel W A d (-r) *
            primeWheelShiftedArcKernel W B e r by
        calc
          _ = (primeWheelPinnedPhase W (-r) *
                primeWheelPinnedPhase W r) *
              (primeWheelShiftedArcKernel W A d (-r) *
                primeWheelShiftedArcKernel W B e r) := by ring
          _ = _ := by rw [hphase]; simp)
  calc
    ((W.modulus : ℂ)⁻¹) *
        ∑ r : ZMod W.modulus,
          primeWheelShiftedArcKernel W A d (-r) *
            primeWheelShiftedArcKernel W B e r =
      finiteTorusPairing f g := hspec.symm
    _ = finiteTorusPairing
          (primeWheelForwardArcWindow W A d)
          (primeWheelForwardArcWindow W B e) := by rfl
    _ = _ := finiteTorusPairing_forwardArcWindow_eq_overlap W A d B e


/-!
## Weighted owner Fubini

The pairwise overlap identity can be summed over an arbitrary finite owner set
without changing coefficients.  This is the exact form needed by the reciprocal
q² daughter column: the physical coefficient \`1/q\` remains inside both sides
of the Gram.
-/

/-- Weighted shifted-arc synthesis over a finite owner set. -/
def primeWheelWeightedShiftedArcSynthesis
    (W : PrimeWheelFiniteSystem) (S : Finset ℕ)
    (w : ℕ → ℂ) (A d : ℕ → ℕ)
    (r : ZMod W.modulus) : ℂ :=
  ∑ q ∈ S, w q * primeWheelShiftedArcKernel W (A q) (d q) r

/-- Weighted physical overlap census with the exact owner coefficients kept. -/
def primeWheelWeightedArcOverlapCensus
    (W : PrimeWheelFiniteSystem) (S : Finset ℕ)
    (w : ℕ → ℂ) (A d : ℕ → ℕ) : ℂ :=
  ∑ q ∈ S, ∑ q' ∈ S,
    w q * w q' *
      (∑ z : ZMod W.modulus,
        if (W.lower + A q < z.val ∧
              z.val ≤ W.lower + (A q + d q)) ∧
            (W.lower + A q' < z.val ∧
              z.val ≤ W.lower + (A q' + d q'))
        then 1 else 0)

/-- **Weighted shifted-arc Gram = weighted physical overlap census.**

No coefficient is replaced by its norm and no ownerwise triangle inequality is
used.  This is just finite Fubini plus the pairwise offset identity. -/
theorem primeWheelWeightedShiftedArcGram_eq_overlapCensus
    (W : PrimeWheelFiniteSystem) (S : Finset ℕ)
    (w : ℕ → ℂ) (A d : ℕ → ℕ)
    (hupper : ∀ q ∈ S, W.lower + (A q + d q) ≤ W.upper) :
    ((W.modulus : ℂ)⁻¹) *
        ∑ r : ZMod W.modulus,
          primeWheelWeightedShiftedArcSynthesis W S w A d (-r) *
            primeWheelWeightedShiftedArcSynthesis W S w A d r =
      primeWheelWeightedArcOverlapCensus W S w A d := by
  unfold primeWheelWeightedShiftedArcSynthesis
    primeWheelWeightedArcOverlapCensus
  rw [Finset.mul_sum]
  calc
    ((W.modulus : ℂ)⁻¹) *
        ∑ r : ZMod W.modulus,
          (∑ q ∈ S,
              w q * primeWheelShiftedArcKernel W (A q) (d q) (-r)) *
            (∑ q' ∈ S,
              w q' * primeWheelShiftedArcKernel W (A q') (d q') r) =
      ∑ q ∈ S, ∑ q' ∈ S,
        w q * w q' *
          (((W.modulus : ℂ)⁻¹) *
            ∑ r : ZMod W.modulus,
              primeWheelShiftedArcKernel W (A q) (d q) (-r) *
                primeWheelShiftedArcKernel W (A q') (d q') r) := by
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _hq
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q' _hq'
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring
    _ = ∑ q ∈ S, ∑ q' ∈ S,
        w q * w q' *
          (∑ z : ZMod W.modulus,
            if (W.lower + A q < z.val ∧
                  z.val ≤ W.lower + (A q + d q)) ∧
                (W.lower + A q' < z.val ∧
                  z.val ≤ W.lower + (A q' + d q'))
            then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro q' hq'
      rw [primeWheelShiftedArcGram_eq_physicalOverlap
        W (A q) (d q) (A q') (d q') (hupper q hq) (hupper q' hq')]

end RHLean.Analysis

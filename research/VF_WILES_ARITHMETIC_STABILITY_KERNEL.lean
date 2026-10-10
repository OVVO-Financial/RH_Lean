import Mathlib

/-!
# Wiles-style arithmetic owner stability: independent finite kernel

This Mathlib-only module proves a genuinely universal finite statement about
occurrence-preserving signed transport. Its class is defined by a local,
weight-preserving involution on individual occurrences, *not* by a global
prime-count error bound, a first-bad inequality, or an assumption of RH.

The local sector law is f(z) = 4*z - 2*|z|. A return involution preserves the
finite source carrier and reverses the exact signed, masked amplitude.
Consequently the FULL signed sum is nonpositive. Additional dissipative
sinks contribute negative squares. This is the elementary generic theorem,
not an assertion that the ACTUAL VF owner packet admits such a completion.

The open arithmetic problem is a term-by-term identification of the original
VF first-bad source plus its SIX genuinely clipped boundary sectors with a
packet of this kind. In particular, a fitted scalar sum-of-squares equality,
a future owner return, a repeated historical parent charge, or an arbitrary
new sink is NOT an acceptable arithmetic realization.

See VF_WILES_ARITHMETIC_STABILITY_PROOF_CONTRACT.md.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- The original signed local sign-reversal law, before summing over sites. -/
def vfWilesLocalSector (z : ℝ) : ℝ :=
  4 * z - 2 * |z|

theorem vfWilesLocalSector_mirror (z : ℝ) :
    vfWilesLocalSector z + vfWilesLocalSector (-z) = -4 * |z| := by
  unfold vfWilesLocalSector
  rw [abs_neg]
  ring

/-- A purely finite, independently specified arithmetic-combinatorial class.

The data consist of actual *occurrences* (not distinct owner values), an
involutive return on the SAME finite carrier, and antisymmetry of the signed
amplitude. Multiplicities, masks, and physical weights must be encoded in
the occurrence index and amplitude BEFORE a packet is constructed.

This is deliberately restrictive. The actual six-sector source has not
been proved to lie in this class; its raw boundary cells may demand a more
general Gram or spectral completion rather than literal involutive pairing.
-/
structure VFWilesReversibleCells (α : Type*) [DecidableEq α] where
  sites : Finset α
  mirror : α → α
  mirror_mem : ∀ i ∈ sites, mirror i ∈ sites
  mirror_involutive : ∀ i ∈ sites, mirror (mirror i) = i
  amplitude : α → ℝ
  amplitude_neg : ∀ i ∈ sites, amplitude (mirror i) = -amplitude i

/-- Exact occurrence-preserving reindexing under the involution. This is a
genuine finite Fubini/permutation identity, not a cancellation estimate. -/
theorem vfWilesReversibleCells_sum_mirror
    {α : Type*} [DecidableEq α] (c : VFWilesReversibleCells α) :
    (∑ i ∈ c.sites, c.amplitude (c.mirror i)) =
      ∑ i ∈ c.sites, c.amplitude i := by
  classical
  refine Finset.sum_bij (fun i _hi => c.mirror i) ?_ ?_ ?_ ?_
  · intro i hi
    exact c.mirror_mem i hi
  · intro i hi j hj h
    have h' := congrArg c.mirror h
    simpa [c.mirror_involutive i hi,
      c.mirror_involutive j hj] using h'
  · intro j hj
    exact ⟨c.mirror j, c.mirror_mem j hj,
      c.mirror_involutive j hj⟩
  · intro i _hi
    rfl

/-- The signed amplitude cancels on a closed, anti-phase finite orbit
system. There is no pointwise absolute-value bound here. -/
theorem vfWilesReversibleCells_amplitude_sum_zero
    {α : Type*} [DecidableEq α] (c : VFWilesReversibleCells α) :
    (∑ i ∈ c.sites, c.amplitude i) = 0 := by
  have hperm := vfWilesReversibleCells_sum_mirror c
  have hsign :
      (∑ i ∈ c.sites, c.amplitude (c.mirror i)) =
        -(∑ i ∈ c.sites, c.amplitude i) := by
    calc
      (∑ i ∈ c.sites, c.amplitude (c.mirror i)) =
          ∑ i ∈ c.sites, -(c.amplitude i) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact c.amplitude_neg i hi
      _ = -(∑ i ∈ c.sites, c.amplitude i) := by
        simp
  linarith

/-- The genuine signed packet, not its unsigned or squared replacement. -/
def vfWilesReversibleSector
    {α : Type*} [DecidableEq α] (c : VFWilesReversibleCells α) : ℝ :=
  ∑ i ∈ c.sites, vfWilesLocalSector (c.amplitude i)

/-- Universal cancellation for ANY closed weighted anti-phase occurrence
system. The direction is forced by the local formula plus reindexing. -/
theorem vfWilesReversibleSector_eq_negative_absolute
    {α : Type*} [DecidableEq α] (c : VFWilesReversibleCells α) :
    vfWilesReversibleSector c =
      -2 * (∑ i ∈ c.sites, |c.amplitude i|) := by
  unfold vfWilesReversibleSector vfWilesLocalSector
  calc
    (∑ i ∈ c.sites, (4 * c.amplitude i - 2 * |c.amplitude i|)) =
        4 * (∑ i ∈ c.sites, c.amplitude i) -
          2 * (∑ i ∈ c.sites, |c.amplitude i|) := by
            simp only [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = -2 * (∑ i ∈ c.sites, |c.amplitude i|) := by
          rw [vfWilesReversibleCells_amplitude_sum_zero c]
          ring

theorem vfWilesReversibleSector_nonpos
    {α : Type*} [DecidableEq α] (c : VFWilesReversibleCells α) :
    vfWilesReversibleSector c ≤ 0 := by
  rw [vfWilesReversibleSector_eq_negative_absolute]
  have hsum : 0 ≤ ∑ i ∈ c.sites, |c.amplitude i| := by
    apply Finset.sum_nonneg
    intro i _hi
    exact abs_nonneg _
  linarith

/-- The exact condition under which a physical zero mask is allowed to
commute with the return map. It is NOT automatic for OAI/Hecke tuple masks;
that compatibility is part of the open actual-arithmetic bridge. -/
def vfWilesSymmetricMask
    {α : Type*} [DecidableEq α]
    (c : VFWilesReversibleCells α)
    (keep : α → Prop) [DecidablePred keep]
    (hkeep : ∀ i ∈ c.sites, keep (c.mirror i) ↔ keep i) :
    VFWilesReversibleCells α where
  sites := c.sites
  mirror := c.mirror
  mirror_mem := c.mirror_mem
  mirror_involutive := c.mirror_involutive
  amplitude := fun i => if keep i then c.amplitude i else 0
  amplitude_neg := by
    intro i hi
    by_cases hk : keep i
    · have hm : keep (c.mirror i) := (hkeep i hi).mpr hk
      simp [hk, hm, c.amplitude_neg i hi]
    · have hm : ¬keep (c.mirror i) := by
        intro him
        exact hk ((hkeep i hi).mp him)
      simp [hk, hm]

/-- A mirror-invariant zero mask preserves finite signed packet stability,
with all physical coefficients kept on their original occurrences. -/
theorem vfWilesSymmetricMask_stable
    {α : Type*} [DecidableEq α]
    (c : VFWilesReversibleCells α)
    (keep : α → Prop) [DecidablePred keep]
    (hkeep : ∀ i ∈ c.sites, keep (c.mirror i) ↔ keep i) :
    vfWilesReversibleSector (vfWilesSymmetricMask c keep hkeep) ≤ 0 :=
  vfWilesReversibleSector_nonpos _

/-- A zero mask alone never increases the ordinary finite quadratic norm.
Unlike the signed sector theorem, this fact does not require mask symmetry;
it also does not give a SIGNED mixed owner-child estimate. -/
theorem vfWilesZeroMaskEnergy_le_original
    {α : Type*} (s : Finset α)
    (keep : α → Prop) [DecidablePred keep]
    (u : α → ℝ) :
    (∑ i ∈ s, (if keep i then u i else 0) ^ 2) ≤
      ∑ i ∈ s, (u i) ^ 2 := by
  apply Finset.sum_le_sum
  intro i _hi
  by_cases hk : keep i
  · simp [hk]
  · simp [hk]
    positivity

/-- Independent negative-square sinks: their membership and signed weights
must also be established from real historical arithmetic, without fitting a
new square root to the aggregate first-bad excess. -/
def vfWilesDissipation
    {β : Type*} (sinks : Finset β) (amplitude : β → ℝ) : ℝ :=
  ∑ j ∈ sinks, (amplitude j) ^ 2

theorem vfWilesDissipation_nonneg
    {β : Type*} (sinks : Finset β) (amplitude : β → ℝ) :
    0 ≤ vfWilesDissipation sinks amplitude := by
  unfold vfWilesDissipation
  apply Finset.sum_nonneg
  intro j _hj
  positivity

/-- The universal signed stability theorem for the independent finite class.

This theorem makes NO reference to pi, Li, VF, a first-bad premise, or RH.
It follows from an occurrence pairing and nonnegative square energies.
-/
theorem vfWilesUniversalArithmeticPacketStability
    {α β : Type*} [DecidableEq α]
    (c : VFWilesReversibleCells α)
    (sinks : Finset β) (dissipationAmplitude : β → ℝ) :
    vfWilesReversibleSector c -
      vfWilesDissipation sinks dissipationAmplitude ≤ 0 := by
  have hpair := vfWilesReversibleSector_nonpos c
  have hsink := vfWilesDissipation_nonneg sinks dissipationAmplitude
  linarith

/-- Abstract Ribet-style trap: a POSITIVE physical first-bad ledger cannot
simultaneously have an occurrence-level representation by the class above.

The hypothesis hrepresentation is the major OPEN source-to-boundary arithmetic
identification. It must be established from real owner incidence, NOT by
postulating the inequality to be proved. -/
theorem vfWilesFirstBadContradiction_of_arithmeticRepresentation
    {α β : Type*} [DecidableEq α]
    (c : VFWilesReversibleCells α)
    (sinks : Finset β) (dissipationAmplitude : β → ℝ)
    (nativeSixSectorBudget : ℝ)
    (hfirstBadObstruction : 0 < nativeSixSectorBudget)
    (hrepresentation :
      nativeSixSectorBudget =
        vfWilesReversibleSector c -
          vfWilesDissipation sinks dissipationAmplitude) :
    False := by
  have hstable :=
    vfWilesUniversalArithmeticPacketStability c sinks dissipationAmplitude
  linarith

/-- Countercheck: unsigned or unpaired source atoms are NOT automatically
dissipative. This excludes an illicit universal all-state stability claim. -/
theorem vfWilesUnpairedCell_canBePositive :
    0 < vfWilesLocalSector (1 : ℝ) := by
  norm_num [vfWilesLocalSector]

/-- Countercheck against treating the OAI difference-of-rows polarization
as a sign estimate: opposed rows have POSITIVE signed interaction. -/
theorem vfWilesOpposedRows_canHavePositiveGram :
    0 < ((1 : ℝ) - (-1)) ^ 2 - (1 : ℝ) ^ 2 - (-1 : ℝ) ^ 2 := by
  norm_num


/-! ## Exact obstruction to pairing UNALTERED physical odd-seat charges

The genuine native VF site charge in square block R is
  w_R - 1_Prime(n), where 0 < w_R < 1/2 for R >= 8.
Consequently each ORIGINAL prime charge is < -1/2 while every
ORIGINAL composite charge is between 0 and +1/2.
An exact sign-reversing mirror cannot map any one of these original
atoms to another, even when the source/destination roots differ.

This is an algebraic no-go result, NOT a bound on prime distribution:
the antiphase class above can represent actual prime history only via
independently derived compensated or composite cells (such as a masked
higher-rank Gram with its honest boundary and historical terms). It cannot
obtain membership by simply naming the original physical sites as cells.
-/

/-- Literal original VF odd-site charge. In the physical application,
isPrime is the true Nat.Prime decision at that occurrence. -/
def vfWilesOriginalOddSeatCharge (w : ℝ) (isPrime : Bool) : ℝ :=
  if isPrime then w - 1 else w

/-- No two unsplit original physical charges (possibly in DIFFERENT
square blocks) can be exact negatives when their native weights lie
strictly between 0 and 1/2. This excludes any direct antiphase return
between literal odd-seat occurrences. -/
theorem vfWilesOriginalOddSeatCharge_no_exact_antiphase
    (w v : ℝ)
    (hwpos : 0 < w) (hwhalf : w < 1 / 2)
    (hvpos : 0 < v) (hvhalf : v < 1 / 2)
    (p q : Bool) :
    vfWilesOriginalOddSeatCharge w p ≠
      -vfWilesOriginalOddSeatCharge v q := by
  intro heq
  cases p <;> cases q <;>
    dsimp [vfWilesOriginalOddSeatCharge] at heq <;>
    linarith

/-- An anti-phase reversible packet whose amplitudes are EXACTLY the
unaltered raw odd-seat physical charges must have EMPTY support. This
gives a formal red-team acceptance failure for the naive proposed
actual-prime membership of the original reversible class. -/
theorem vfWilesReversibleRawPhysicalCarrier_empty
    {α : Type*} [DecidableEq α]
    (c : VFWilesReversibleCells α)
    (weight : α → ℝ) (isPrime : α → Bool)
    (hpos : ∀ i ∈ c.sites, 0 < weight i)
    (hhalf : ∀ i ∈ c.sites, weight i < (1 / 2 : ℝ))
    (hraw : ∀ i ∈ c.sites,
      c.amplitude i =
        vfWilesOriginalOddSeatCharge (weight i) (isPrime i)) :
    c.sites = ∅ := by
  classical
  by_contra hne
  have hs : c.sites.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨i, hi⟩ := hs
  have hmi : c.mirror i ∈ c.sites := c.mirror_mem i hi
  have hanti := c.amplitude_neg i hi
  rw [hraw (c.mirror i) hmi, hraw i hi] at hanti
  exact (vfWilesOriginalOddSeatCharge_no_exact_antiphase
    (weight (c.mirror i)) (weight i)
    (hpos (c.mirror i) hmi) (hhalf (c.mirror i) hmi)
    (hpos i hi) (hhalf i hi)
    (isPrime (c.mirror i)) (isPrime i)) hanti

/-- A general exact identity retaining the unmatched physical boundary.
Closed anti-phase cells cancel in their LINEAR signed amplitude. Any
unmatched sites remain explicitly in the 4*boundary flux, so their
signed contribution cannot be silently converted into dissipation. -/
theorem vfWilesIncompleteReturn_exact_boundary
    {α β : Type*} [DecidableEq α]
    (paired : VFWilesReversibleCells α)
    (boundary : Finset β) (boundaryAmplitude : β → ℝ) :
    vfWilesReversibleSector paired +
      (∑ i ∈ boundary, vfWilesLocalSector (boundaryAmplitude i)) =
    4 * (∑ i ∈ boundary, boundaryAmplitude i) -
      2 * ((∑ i ∈ paired.sites, |paired.amplitude i|) +
        (∑ i ∈ boundary, |boundaryAmplitude i|)) := by
  have hboundary :
      (∑ i ∈ boundary, vfWilesLocalSector (boundaryAmplitude i)) =
        4 * (∑ i ∈ boundary, boundaryAmplitude i) -
          2 * (∑ i ∈ boundary, |boundaryAmplitude i|) := by
    unfold vfWilesLocalSector
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [vfWilesReversibleSector_eq_negative_absolute, hboundary]
  ring


/-! ## Exact original Co/Div prime-wheel owner-event influence

On the actual anchored original odd-seat carrier each composite is
initially an unclassified parity survivor with virtual prime charge
w - 1, and is reclassified exactly once, by its LEAST prime factor,
into its actual composite charge w. The intermediate classification
is a finite enumeration state, never a claim about extra actual primes.

The resulting Co/Div slack change has a precise three-term
decomposition: (a) the site's diagonal, (b) positive interaction
with as-yet-unclassified negative seats, and (c) negative interaction
with the already-positive anchor/composite seats. The owner index
determines WHICH integer is removed and WHEN. After t removals,
the local effect depends only on t, so the exact identity cannot
by itself establish a distributional or first-bad contraction.
-/

/-- Original native anchored Co/Div slack, equivalently M^2-2S^2. -/
def vfWilesCoDivSlack (U L : ℝ) : ℝ :=
  6 * U * L - U ^ 2 - L ^ 2

/-- The exact signed change produced when a *genuine composite* is
first removed by its least prime owner: one as-yet unclassified
negative seat of magnitude 1-w becomes a positive seat of mass w.
The original historical anchor appears ONLY in U and L. -/
theorem vfWilesOwnerReclassification_event_delta
    (U L w : ℝ) :
    vfWilesCoDivSlack (U + w) (L - (1 - w)) -
      vfWilesCoDivSlack U L =
      (1 - 2 * w) +
        (2 + 4 * w) * (L - (1 - w)) -
          (6 - 4 * w) * U := by
  unfold vfWilesCoDivSlack
  ring

/-- Across an actual owner-ordered integer census, once t composite
sites have been *reclassified* the increment at the next genuinely
composite site decreases by a precise positive coefficient
2+8*w*(1-w) when 0<w<1. The effect is algebraic and
independent of that next site's factorization identity. -/
theorem vfWilesOwnerReclassification_event_affine
    (U0 L0 w t : ℝ) :
    vfWilesCoDivSlack (U0 + w * (t + 1))
        (L0 - (1 - w) * (t + 1)) -
      vfWilesCoDivSlack (U0 + w * t)
        (L0 - (1 - w) * t) =
    (vfWilesCoDivSlack (U0 + w) (L0 - (1 - w)) -
      vfWilesCoDivSlack U0 L0) -
      (2 + 8 * w * (1 - w)) * t := by
  unfold vfWilesCoDivSlack
  ring

/-- The one-event slope is strictly positive for the physical
0<w<1 weights. Therefore the event contribution ultimately
changes from restoring to adverse as composite removals progress.
No positivity of the *terminal* Co/Div slack follows. -/
theorem vfWilesOwnerReclassification_slope_pos
    (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1) :
    0 < 2 + 8 * w * (1 - w) := by
  have hpos : 0 < w * (1 - w) :=
    mul_pos hw0 (sub_pos.mpr hw1)
  nlinarith

/-- Final slack after removing t composite seats depends on the
one preserved historical anchor and the total number of removed
seats. This deliberately exposes why ownerwise finite arithmetic
identities alone do not give a first-bad inequality. -/
theorem vfWilesOwnerReclassification_final_from_population
    (U0 L0 w t : ℝ) :
    vfWilesCoDivSlack (U0 + w * t) (L0 - (1 - w) * t) =
      (6 * (U0 + w * t) * (L0 - (1 - w) * t) -
        (U0 + w * t) ^ 2 - (L0 - (1 - w) * t) ^ 2) := by
  rfl



/-! ## Original-site frozen-wheel signed return (not a fantasy pi definition)

For a genuine odd nonsquare integer in a subdoubling frozen A-wheel,
survival either means a true prime, or one late product p*q of
distinct genuine primes >A. The native arithmetic modules already
provide that exact factorization classifier. This independent
Mathlib-only lemma is the POINTWISE weighted transport, where rho
is an explicit independent odd-wheel density and w is the original
VF seat weight. None of the three terms is fitted to a pi error.

The native actual-prime specialization must use the existing
finite prime/survivor/late-factor classifier, not assert that a
floor-Li fantasy has real prime factors. The equality is LINEAR
and cannot be substituted for the still-open quadratic Sector Six
uniform bound.
-/

/-- One Boolean sieve site: a late composite survivor must actually
survive the frozen low-prime wheel. -/
theorem vfWilesFrozenWheelOddSeat_pointwise
    (survives late : Bool)
    (hLate : late = true → survives = true)
    (rho w : ℝ) :
    (if survives && !late then (1 : ℝ) else 0) - w =
      (rho - w) +
        ((if survives then (1 : ℝ) else 0) - rho) -
          (if late then (1 : ℝ) else 0) := by
  cases survives <;> cases late <;>
    simp_all; ring

/-- Every original physical odd seat retains its OWN w_r; the bias,
signed survivor phase, and late composite term are summed without
absolute values, proxy prime events, or changed denominators. -/
theorem vfWilesFrozenWheelOddSeat_sum
    {α : Type*}
    (sites : Finset α) (survives late : α → Bool)
    (rho : ℝ) (w : α → ℝ)
    (hLate : ∀ i ∈ sites, late i = true → survives i = true) :
    (∑ i ∈ sites,
      ((if survives i && !late i then (1 : ℝ) else 0) - w i)) =
      (∑ i ∈ sites, (rho - w i)) +
        (∑ i ∈ sites,
          ((if survives i then (1 : ℝ) else 0) - rho)) -
          (∑ i ∈ sites, (if late i then (1 : ℝ) else 0)) := by
  classical
  calc
    _ = ∑ i ∈ sites,
        ((rho - w i) +
          ((if survives i then (1 : ℝ) else 0) - rho) -
            (if late i then (1 : ℝ) else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact vfWilesFrozenWheelOddSeat_pointwise
            (survives i) (late i) (hLate i hi) rho (w i)
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]


/-! ## A genuine all-integer no-migration lemma for the raw next-right clip

The x=289..324 and larger-block sweeps suggest that no surviving
odd physical pair changes its first/next/returned clipping orientation
after the two physical sites are present. The underlying next-right
geometry is independent of primality estimates.

Let a=r*h and c=p*b be two odd sites above R^2, with p<r odd.
If the *prospective* r*b corner exceeds both sites, then its
overhang cannot be smaller than the completed square-band width:
it is at least (R+1)^2. This derives solely from (i) odd factors
separated by >=2 and (ii) narrow square bands.

This lemma does not prove the native six-sector inclusion by itself:
the original first-owner and returned-owner source selectors must
still be imported when constructing the actual-prime specialization.
-/

/-- A next-right raw-parent corner cannot newly cross the clock
in the interior of a completed square band, once both physical
odd source sites have entered. -/
theorem vfWilesOddBandNextRightClip_noIntermediate
    (R p r h b : ℕ)
    (hpOdd : p % 2 = 1) (hrOdd : r % 2 = 1)
    (hhOdd : h % 2 = 1) (hbOdd : b % 2 = 1)
    (hpr : p < r)
    (ha : R ^ 2 < r * h)
    (hc : R ^ 2 < p * b)
    (hafter : max (r * h) (p * b) < r * b) :
    (R + 1) ^ 2 ≤ r * b := by
  have hgap : p + 2 ≤ r := by omega
  by_cases hrR : r ≤ R
  · have hpR : p ≤ R := by omega
    have hbR : R < b := by
      by_contra h
      have hbLe : b ≤ R := by omega
      have h1 : p * b ≤ R * b := Nat.mul_le_mul_right b hpR
      have h2 : R * b ≤ R * R := Nat.mul_le_mul_left R hbLe
      have hcl : R * R < p * b := by simpa only [pow_two] using hc
      omega
    have hmul : (p + 2) * b ≤ r * b :=
      Nat.mul_le_mul_right b hgap
    nlinarith
  · have hrgt : R < r := by omega
    have hrh : r * h < r * b :=
      lt_of_le_of_lt (Nat.le_max_left (r * h) (p * b)) hafter
    have hbh : h < b := by
      by_contra hnot
      have hble : b ≤ h := by omega
      have hmul : r * b ≤ r * h := Nat.mul_le_mul_left r hble
      omega
    have hgapb : h + 2 ≤ b := by omega
    have hmul : r * (h + 2) ≤ r * b :=
      Nat.mul_le_mul_left r hgapb
    nlinarith


/-! ## Exact quadratic backbone versus actual arithmetic profile

The square-block fractional-root parameter controls the geometric
two-coordinate pair count. An actual signed next-right sector
additionally contains the independently determined prime/squarefree-
composite incidence P*C and composite/composite clipped count N.

The statement below preserves the ORIGINAL VF sign and weight.
It isolates the *only* correction to a pure t^2 law at every
actual cutoff, without postulating cancellation or identifying
the correction with a positive Gram payment. The physical
specialization must use P, C, and N from the true integer carrier.
-/

/-- Exact signed next-right departure from the purely geometric
quadratic profile: deltaP, deltaC, deltaN are discrepancies in
the actual prime, squarefree-composite, and native next-right
composite-pair incidence counts, respectively. -/
theorem vfWilesSignedNextRight_quadraticDeviation
    (w t P C N deltaP deltaC deltaN : ℝ) :
    (w ^ 2 * (t ^ 2 * N + deltaN) -
       w * (1 - w) * (t * P + deltaP) * (t * C + deltaC)) -
       t ^ 2 * (w ^ 2 * N - w * (1 - w) * P * C) =
    w ^ 2 * deltaN -
      w * (1 - w) *
        (t * (P * deltaC + C * deltaP) + deltaP * deltaC) := by
  ring

/-- Unfiltered two-site pair formation is exactly quadratic in
site occupancy with an explicit finite-population correction.
This is a UNIVERSAL algebraic law, not a short-interval PNT
for the signed and owner-filtered actual packet. -/
theorem vfWilesUnfilteredPairQuadratic_ratio
    (m R : ℕ) (hR : 2 ≤ R) :
    ((m : ℝ) * ((m : ℝ) - 1)) /
        ((R : ℝ) * ((R : ℝ) - 1)) =
      ((m : ℝ) / (R : ℝ)) ^ 2 -
        ((m : ℝ) / (R : ℝ)) *
          (1 - (m : ℝ) / (R : ℝ)) / ((R : ℝ) - 1) := by
  have hRpos : (0 : ℝ) < (R : ℝ) := by
    exact_mod_cast (show 0 < R by omega)
  have hRone : (1 : ℝ) < (R : ℝ) := by
    exact_mod_cast (show 1 < R by omega)
  have hn0 : (R : ℝ) ≠ 0 := ne_of_gt hRpos
  have hn1 : (R : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hRone)
  field_simp
  ring

end RHLean.Analysis

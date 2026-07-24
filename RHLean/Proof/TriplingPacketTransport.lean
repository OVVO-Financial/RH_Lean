import Mathlib
import RHLean.Proof.ConcreteSquarePrefixHighResidual
import RHLean.Proof.NormalizedCofactorTripling

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Complex coefficient compatibility with the `ActualResidualData` convention:
the lower Möbius factor is applied by `actualResidualEntry`, while the remaining
normalized channel amplitude carries the dyadic weight and upper Möbius factor. -/
theorem lowerMoebius_mul_normalizedChannelAmplitude
    (c q : ℕ) :
    (((μ c : ℤ) : ℂ)) *
        normalizedChannelAmplitude
          { lowerCofactor := c, upperFactor := q } =
      normalizedCofactorWeight c q := by
  simpa [normalizedChannelAmplitude, normalizedCofactorWeight] using
    congrArg (fun x : ℚ => (x : ℂ))
      (lowerMoebius_mul_normalizedChannelAmplitudeRat c q)

/-- The full normalized Farey transport entry before finite packet summation. It
keeps the arithmetic coefficient, exact channel phase, and packet-index phase
as three visible factors. -/
def normalizedFareyTransportEntry
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel)
    (packetIndex : ℕ) : ℂ :=
  normalizedCofactorWeight channel.lowerCofactor channel.upperFactor *
    fareyChannelPhase mode channel *
      RHLean.Analysis.resonantQuadraticMode mode (packetIndex : ℤ)

/-- The exact contiguous transport packet on `[⌊√(cq)⌋,q-1)`. -/
def normalizedFareyTransportPacket
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel) : ℂ :=
  RHLean.Kernel.packet
    (normalizedFareyTransportEntry mode channel)
    (orderedChannelEntryShell channel)
    (orderedChannelTransitionIndex channel - orderedChannelEntryShell channel)

/-- Interval-sum form of the exact normalized transport packet. -/
theorem normalizedFareyTransportPacket_eq_intervalSum
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel) :
    normalizedFareyTransportPacket mode channel =
      ∑ packetIndex ∈ Finset.Ico (orderedChannelEntryShell channel)
          (orderedChannelTransitionIndex channel),
        normalizedFareyTransportEntry mode channel packetIndex := by
  unfold normalizedFareyTransportPacket
  simpa [orderedTransportPacketStart, orderedTransportPacketLength] using
    orderedTransportPacket_eq_intervalSum
      (normalizedFareyTransportEntry mode channel) 0 channel 0

/-- Transport amplitude for the concrete high-height dynamical packet data. The
exact normalized coefficient remains separated from the lower Möbius factor,
and the complete channel phase is inserted before the packet-index phase applied
by `actualResidualEntry`. -/
def squarePrefixHighTransportAmplitude
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (shell : ℕ) (channel : RHLean.Analysis.ActualCofactorChannel)
    (modeLabel _packetIndex : ℕ) : ℂ :=
  if shell = squarePrefixHighShell channel then
    normalizedChannelAmplitude channel *
      fareyChannelPhase
        (fareyResonantMode cutoff M hcutoff modeLabel) channel
  else
    0

/-- Concrete high-height transport data. This is distinct from the singleton
source-entry realization used for exact high-sector signal recombination: it uses
the compiled contiguous transport windows and all retained Farey modes. -/
noncomputable def squarePrefixHighTransportData
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ) : RHLean.Analysis.ActualResidualData cutoff M where
  shellCount := squarePrefixEntryShellCount n
  cofactorChannels := squarePrefixHighHeightChannels Λ n
  denominatorModes := fareyModeLabels (cutoff M)
  mode := fareyResonantMode cutoff M hcutoff
  packetStart := orderedTransportPacketStart
  packetLength := orderedTransportPacketLength
  amplitude := squarePrefixHighTransportAmplitude cutoff M hcutoff

/-- At its assigned source shell, the concrete transport entry is exactly the
normalized arithmetic/Farey/packet-index entry. -/
theorem actualResidualEntry_squarePrefixHighTransportData_ownShell
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ)
    (channel : RHLean.Analysis.ActualCofactorChannel)
    (modeLabel packetIndex : ℕ) :
    RHLean.Analysis.actualResidualEntry
        (squarePrefixHighTransportData cutoff M hcutoff Λ n)
        (squarePrefixHighShell channel) channel modeLabel packetIndex =
      normalizedFareyTransportEntry
        (fareyResonantMode cutoff M hcutoff modeLabel)
        channel packetIndex := by
  unfold RHLean.Analysis.actualResidualEntry
    squarePrefixHighTransportData
    squarePrefixHighTransportAmplitude
    normalizedFareyTransportEntry
  simp only [if_pos rfl]
  rw [lowerMoebius_mul_normalizedChannelAmplitude]
  ring

/-- At its own source shell, an actual transport packet is exactly the normalized
contiguous Farey transport packet. -/
theorem actualResidualPacket_squarePrefixHighTransportData_ownShell
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ)
    (channel : RHLean.Analysis.ActualCofactorChannel)
    (modeLabel : ℕ) :
    RHLean.Analysis.actualResidualPacket
        (squarePrefixHighTransportData cutoff M hcutoff Λ n)
        (squarePrefixHighShell channel) channel modeLabel =
      normalizedFareyTransportPacket
        (fareyResonantMode cutoff M hcutoff modeLabel) channel := by
  unfold RHLean.Analysis.actualResidualPacket normalizedFareyTransportPacket
  change RHLean.Kernel.packet
      (RHLean.Analysis.actualResidualEntry
        (squarePrefixHighTransportData cutoff M hcutoff Λ n)
        (squarePrefixHighShell channel) channel modeLabel)
      (orderedChannelEntryShell channel)
      (orderedChannelTransitionIndex channel - orderedChannelEntryShell channel) = _
  unfold RHLean.Kernel.packet
  apply Finset.sum_congr rfl
  intro packetIndex _
  exact actualResidualEntry_squarePrefixHighTransportData_ownShell
    cutoff M hcutoff Λ n channel modeLabel packetIndex

/-- The explicit phase multiplier relating `(3c,q)` to `(c,q)`. It contains no
Möbius sign; the arithmetic sign is already carried by the normalized coefficient. -/
def triplingPhaseTransport
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel) : ℂ :=
  RHLean.QuadraticPrimePhase.quadraticPhase
    (-8 * mode.numerator) (mode.denominator : ℤ)
    (channel.lowerCofactor : ℤ)

/-- The compiled channel-phase transport law in named transport-factor form. -/
theorem fareyChannelPhase_tripled_eq_transport_mul
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel) :
    fareyChannelPhase mode (tripledCofactorChannel channel) =
      triplingPhaseTransport mode channel * fareyChannelPhase mode channel := by
  exact fareyChannelPhase_tripled mode channel

/-- Tripling cannot move an ordered channel to an earlier source-entry shell. -/
theorem orderedChannelEntryShell_le_tripled
    (channel : RHLean.Analysis.ActualCofactorChannel) :
    orderedChannelEntryShell channel ≤
      orderedChannelEntryShell (tripledCofactorChannel channel) := by
  unfold orderedChannelEntryShell tripledCofactorChannel
  apply Nat.sqrt_le_sqrt
  calc
    channel.lowerCofactor * channel.upperFactor ≤
        3 * (channel.lowerCofactor * channel.upperFactor) := by omega
    _ = (3 * channel.lowerCofactor) * channel.upperFactor := by
      simp [Nat.mul_assoc]

/-- Tripling the lower cofactor leaves the smoothness-transition index unchanged. -/
@[simp] theorem orderedChannelTransitionIndex_tripled
    (channel : RHLean.Analysis.ActualCofactorChannel) :
    orderedChannelTransitionIndex (tripledCofactorChannel channel) =
      orderedChannelTransitionIndex channel := by
  rfl

/-- The finite base-channel prefix removed when transport begins only at the
tripled entry shell. The `min` handles the case in which the tripled channel enters
after the transition, leaving the common transport window empty. -/
def triplingBoundaryPacket
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel) : ℂ :=
  ∑ packetIndex ∈ Finset.Ico (orderedChannelEntryShell channel)
      (min (orderedChannelEntryShell (tripledCofactorChannel channel))
        (orderedChannelTransitionIndex channel)),
    normalizedFareyTransportEntry mode channel packetIndex

/-- The base profile restricted to the exact packet window shared with its
tripled channel. -/
def triplingTransportedBasePacket
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel) : ℂ :=
  ∑ packetIndex ∈
      Finset.Ico (orderedChannelEntryShell (tripledCofactorChannel channel))
        (orderedChannelTransitionIndex channel),
    normalizedFareyTransportEntry mode channel packetIndex

/-- The exact full packet splits into the boundary prefix and the common
tripling-transport window. -/
theorem normalizedFareyTransportPacket_eq_boundary_add_common
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel) :
    normalizedFareyTransportPacket mode channel =
      triplingBoundaryPacket mode channel +
        triplingTransportedBasePacket mode channel := by
  rw [normalizedFareyTransportPacket_eq_intervalSum]
  unfold triplingBoundaryPacket triplingTransportedBasePacket
  have hstart := orderedChannelEntryShell_le_tripled channel
  rw [← Finset.sum_union]
  · congr 1
    ext packetIndex
    simp
    omega
  · rw [Finset.disjoint_left]
    intro packetIndex hboundary hcommon
    simp only [Finset.mem_Ico] at hboundary hcommon
    omega

/-- Pointwise phase-aligned child-plus-twice-parent cancellation on the common
packet window. -/
theorem normalizedFareyTransportEntry_phaseAligned_cancel
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel)
    (packetIndex : ℕ)
    (h3 : ¬ 3 ∣ channel.lowerCofactor * channel.upperFactor) :
    triplingPhaseTransport mode channel *
        normalizedFareyTransportEntry mode channel packetIndex +
      2 * normalizedFareyTransportEntry mode
        (tripledCofactorChannel channel) packetIndex = 0 := by
  change
    triplingPhaseTransport mode channel *
        (normalizedCofactorWeight channel.lowerCofactor channel.upperFactor *
          fareyChannelPhase mode channel *
          RHLean.Analysis.resonantQuadraticMode mode (packetIndex : ℤ)) +
      2 *
        (normalizedCofactorWeight (3 * channel.lowerCofactor) channel.upperFactor *
          fareyChannelPhase mode (tripledCofactorChannel channel) *
          RHLean.Analysis.resonantQuadraticMode mode (packetIndex : ℤ)) = 0
  rw [normalized_tripling_scaling
      channel.lowerCofactor channel.upperFactor h3,
    fareyChannelPhase_tripled_eq_transport_mul]
  ring

/-- Unaligned pointwise cancellation leaves exactly the explicit phase defect. -/
theorem normalizedFareyTransportEntry_add_two_tripled_eq_phaseDefect
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel)
    (packetIndex : ℕ)
    (h3 : ¬ 3 ∣ channel.lowerCofactor * channel.upperFactor) :
    normalizedFareyTransportEntry mode channel packetIndex +
      2 * normalizedFareyTransportEntry mode
        (tripledCofactorChannel channel) packetIndex =
      (1 - triplingPhaseTransport mode channel) *
        normalizedFareyTransportEntry mode channel packetIndex := by
  have hcancel := normalizedFareyTransportEntry_phaseAligned_cancel
    mode channel packetIndex h3
  linear_combination hcancel

/-- Summed phase-aligned cancellation on the entire common packet window. -/
theorem triplingTransportedBasePacket_phaseAligned_cancel
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel)
    (h3 : ¬ 3 ∣ channel.lowerCofactor * channel.upperFactor) :
    triplingPhaseTransport mode channel *
        triplingTransportedBasePacket mode channel +
      2 * normalizedFareyTransportPacket mode
        (tripledCofactorChannel channel) = 0 := by
  rw [normalizedFareyTransportPacket_eq_intervalSum]
  unfold triplingTransportedBasePacket
  simp only [orderedChannelTransitionIndex_tripled]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro packetIndex _
  exact normalizedFareyTransportEntry_phaseAligned_cancel
    mode channel packetIndex h3

/-- Summed unaligned common-window identity with the exact phase defect retained. -/
theorem triplingTransportedBasePacket_add_two_tripled_eq_phaseDefect
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel)
    (h3 : ¬ 3 ∣ channel.lowerCofactor * channel.upperFactor) :
    triplingTransportedBasePacket mode channel +
      2 * normalizedFareyTransportPacket mode
        (tripledCofactorChannel channel) =
      (1 - triplingPhaseTransport mode channel) *
        triplingTransportedBasePacket mode channel := by
  rw [normalizedFareyTransportPacket_eq_intervalSum]
  unfold triplingTransportedBasePacket
  simp only [orderedChannelTransitionIndex_tripled]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro packetIndex _
  exact normalizedFareyTransportEntry_add_two_tripled_eq_phaseDefect
    mode channel packetIndex h3

/-- Boundary plus phase mismatch: the complete exact signed defect left by
tripling one normalized Farey transport packet. -/
def triplingSignedDefect
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel) : ℂ :=
  triplingBoundaryPacket mode channel +
    (1 - triplingPhaseTransport mode channel) *
      triplingTransportedBasePacket mode channel

/-- Full signed packet identity. No shell, mode, endpoint, or boundary term is
discarded: tripling leaves exactly the finite boundary prefix plus the explicit
phase defect on the common transport window. -/
theorem normalizedFareyTransportPacket_add_two_tripled_eq_signedDefect
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel)
    (h3 : ¬ 3 ∣ channel.lowerCofactor * channel.upperFactor) :
    normalizedFareyTransportPacket mode channel +
      2 * normalizedFareyTransportPacket mode
        (tripledCofactorChannel channel) =
      triplingSignedDefect mode channel := by
  rw [normalizedFareyTransportPacket_eq_boundary_add_common]
  calc
    (triplingBoundaryPacket mode channel +
        triplingTransportedBasePacket mode channel) +
        2 * normalizedFareyTransportPacket mode
          (tripledCofactorChannel channel) =
      triplingBoundaryPacket mode channel +
        (triplingTransportedBasePacket mode channel +
          2 * normalizedFareyTransportPacket mode
            (tripledCofactorChannel channel)) := by ring
    _ = triplingSignedDefect mode channel := by
      rw [triplingTransportedBasePacket_add_two_tripled_eq_phaseDefect
        mode channel h3]
      rfl

/-- A retained concrete tripling pair. Both ordered channels remain explicit in
the high-height support, and the new-prime hypothesis is recorded separately. -/
structure SquarePrefixHighTriplingPair (Λ : ℝ) (n : ℕ) where
  base : RHLean.Analysis.ActualCofactorChannel
  newPrime : ¬ 3 ∣ base.lowerCofactor * base.upperFactor
  base_mem : base ∈ squarePrefixHighHeightChannels Λ n
  tripled_mem : tripledCofactorChannel base ∈
    squarePrefixHighHeightChannels Λ n

/-- The base source shell of a retained tripling pair is inside the concrete
finite shell range. -/
theorem SquarePrefixHighTriplingPair.baseShell_lt
    {Λ : ℝ} {n : ℕ} (pair : SquarePrefixHighTriplingPair Λ n) :
    squarePrefixHighShell pair.base < squarePrefixEntryShellCount n :=
  squarePrefixHighShell_lt_shellCount pair.base_mem

/-- The tripled source shell of a retained tripling pair is inside the concrete
finite shell range. -/
theorem SquarePrefixHighTriplingPair.tripledShell_lt
    {Λ : ℝ} {n : ℕ} (pair : SquarePrefixHighTriplingPair Λ n) :
    squarePrefixHighShell (tripledCofactorChannel pair.base) <
      squarePrefixEntryShellCount n :=
  squarePrefixHighShell_lt_shellCount pair.tripled_mem

/-- Full signed defect identity expressed through the actual transport-data
packet interface at the two exact source shells. -/
theorem actualResidualPacket_squarePrefixHighTransportData_tripling_signedDefect
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ) (pair : SquarePrefixHighTriplingPair Λ n)
    (modeLabel : ℕ) :
    RHLean.Analysis.actualResidualPacket
        (squarePrefixHighTransportData cutoff M hcutoff Λ n)
        (squarePrefixHighShell pair.base) pair.base modeLabel +
      2 * RHLean.Analysis.actualResidualPacket
        (squarePrefixHighTransportData cutoff M hcutoff Λ n)
        (squarePrefixHighShell (tripledCofactorChannel pair.base))
        (tripledCofactorChannel pair.base) modeLabel =
      triplingSignedDefect
        (fareyResonantMode cutoff M hcutoff modeLabel) pair.base := by
  rw [actualResidualPacket_squarePrefixHighTransportData_ownShell,
    actualResidualPacket_squarePrefixHighTransportData_ownShell]
  exact normalizedFareyTransportPacket_add_two_tripled_eq_signedDefect
    (fareyResonantMode cutoff M hcutoff modeLabel)
    pair.base pair.newPrime

/-- Complete signed child-plus-twice-parent contribution with all retained Farey
modes summed jointly. -/
def squarePrefixHighTriplingModeContribution
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ) (pair : SquarePrefixHighTriplingPair Λ n) : ℂ :=
  ∑ modeLabel ∈ fareyModeLabels (cutoff M),
    (RHLean.Analysis.actualResidualPacket
        (squarePrefixHighTransportData cutoff M hcutoff Λ n)
        (squarePrefixHighShell pair.base) pair.base modeLabel +
      2 * RHLean.Analysis.actualResidualPacket
        (squarePrefixHighTransportData cutoff M hcutoff Λ n)
        (squarePrefixHighShell (tripledCofactorChannel pair.base))
        (tripledCofactorChannel pair.base) modeLabel)

/-- Complete retained-mode defect sum for one tripling pair. -/
def squarePrefixHighTriplingModeDefect
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    {Λ : ℝ} {n : ℕ} (pair : SquarePrefixHighTriplingPair Λ n) : ℂ :=
  ∑ modeLabel ∈ fareyModeLabels (cutoff M),
    triplingSignedDefect
      (fareyResonantMode cutoff M hcutoff modeLabel) pair.base

/-- Exact all-mode signed defect identity. Cross-mode cancellation remains inside
the single finite sum and is not replaced by separate positive mode estimates. -/
theorem squarePrefixHighTriplingModeContribution_eq_defect
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ) (pair : SquarePrefixHighTriplingPair Λ n) :
    squarePrefixHighTriplingModeContribution
        cutoff M hcutoff Λ n pair =
      squarePrefixHighTriplingModeDefect cutoff M hcutoff pair := by
  unfold squarePrefixHighTriplingModeContribution
    squarePrefixHighTriplingModeDefect
  apply Finset.sum_congr rfl
  intro modeLabel _
  exact actualResidualPacket_squarePrefixHighTransportData_tripling_signedDefect
    cutoff M hcutoff Λ n pair modeLabel

/-- Energy form of the exact all-mode defect identity. The norm is taken only
after the signed denominator-mode recombination. -/
theorem squarePrefixHighTriplingModeContribution_energy_eq_defect
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ) (pair : SquarePrefixHighTriplingPair Λ n) :
    ‖squarePrefixHighTriplingModeContribution
        cutoff M hcutoff Λ n pair‖ ^ 2 =
      ‖squarePrefixHighTriplingModeDefect cutoff M hcutoff pair‖ ^ 2 := by
  rw [squarePrefixHighTriplingModeContribution_eq_defect]

end RHLean.Proof

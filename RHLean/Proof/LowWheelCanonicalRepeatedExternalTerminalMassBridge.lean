import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedTerminalHighPrimeBridge
import RHLean.Proof.LowWheelExternalTerminalEightRootBound
import RHLean.Proof.LowWheelCanonicalDowncrossSignedParentSplit

/-!
# Repeated external terminal mass is the existing ERrep transport mass

The repeated frozen terminal state has literal shape `(t,(1,p))`.  On the
external side `R < p`, this is not merely analogous to the existing high-prime
transport grid: the map

`(t,(1,p)) -> (t,p)`

is a bijection from the repeated external-terminal downcross carrier onto
`squareRootExternalTerminalRepeatedFaceCarrier R`.  The tagged downcross weight
is exactly the Boolean-face weight used by `squareRootERrep`.

Thus the repeated external endpoint created by the bottom-up downcross
coordinate is *identically the same signed mass* already present in the top-down
high-prime coordinate.  This is the exact dictionary needed to invoke the
existing `ERrep + FarSurvivor - Near = -ERuniq` recoupling before taking norms.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Forget the forced cofactor `1` and retain the Boolean face/high prime. -/
def lowWheelRepeatedExternalTerminalToFacePrime
    (y : LowWheelTaggedDowncrossState) : LowWheelExternalTerminalFacePrime :=
  (y.1, lowWheelTaggedDowncrossPivot y)

/-- Every repeated external terminal downcross is literally a repeated point of
the external high-prime face grid. -/
theorem lowWheelRepeatedExternalTerminalToFacePrime_mem
    {R : ℕ} (hR : 2 ≤ R)
    {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedExternalTerminalPart R) :
    lowWheelRepeatedExternalTerminalToFacePrime y ∈
      squareRootExternalTerminalRepeatedFaceCarrier R := by
  have hterminal := (Finset.mem_filter.mp hy).1
  have hfrozen := (Finset.mem_filter.mp hterminal).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := lowWheelCanonicalRepeatedExternalTerminal_mem_taggedCarrier hy
  have htagData := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hhighData := lowWheelCanonicalRepeatedExternalTerminal_highPrime_data hy
  have hPRange := hhighData.1
  have hhigh := hhighData.2.1
  have hPltR := (Finset.mem_Ico.mp hPRange).2
  have htAdm : y.1 ∈ admissiblePrimeFaces (R - 1) := by
    rw [admissiblePrimeFaces_pred_eq_lowCube_filter_product_lt R (by omega)]
    exact Finset.mem_filter.mpr ⟨htagData.1, hPltR⟩
  rcases Finset.mem_filter.mp hhigh with ⟨hpRange, hpPrime, htop⟩
  have hzBase :
      lowWheelRepeatedExternalTerminalToFacePrime y ∈
        squareRootExternalTerminalFaceCarrier R := by
    apply mem_squareRootExternalTerminalFaceCarrier.mpr
    exact ⟨htAdm, hpRange, hpPrime, htop⟩
  apply Finset.mem_filter.mpr
  refine ⟨hzBase, ?_⟩
  rcases lowWheelCanonicalRepeatedTerminalBoundary_geometry hterminal with
    ⟨hc, hk, _hp, _hface, _hdown, _hup⟩
  simpa [lowWheelRepeatedExternalTerminalToFacePrime,
    squareRootExternalTerminalTag, hc, hk] using hrepeated

/-- The external face-grid tag lands back in the complete external terminal
carrier. -/
theorem squareRootExternalTerminalRepeatedTag_mem_externalTerminal
    {R : ℕ} (hR : 2 ≤ R)
    {z : LowWheelExternalTerminalFacePrime}
    (hz : z ∈ squareRootExternalTerminalRepeatedFaceCarrier R) :
    squareRootExternalTerminalTag z ∈
      lowWheelCanonicalExternalTerminalRepeatedPart R := by
  have hzBase := (Finset.mem_filter.mp hz).1
  have hzRepeated := (Finset.mem_filter.mp hz).2
  have htag := squareRootExternalTerminalTag_mem_downcross hR hzBase
  rcases z with ⟨t, p⟩
  rcases mem_squareRootExternalTerminalFaceCarrier.mp hzBase with
    ⟨_htAdm, hpRange, hp, _htop⟩
  have hpivot :
      lowWheelTaggedDowncrossPivot
        (squareRootExternalTerminalTag (t, p)) = p := by
    simp [lowWheelTaggedDowncrossPivot,
      squareRootExternalTerminalTag,
      lowWheelCanonicalCofactorQuotientPivot, hp.minFac_eq]
  have htagData := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htag
  have hface :
      ∀ q ∈ t,
        q < lowWheelTaggedDowncrossPivot
          (squareRootExternalTerminalTag (t, p)) := by
    intro q hqt
    have hqGlobal := (Finset.mem_powerset.mp htagData.1) hqt
    have hqR := (mem_primesUpTo.mp hqGlobal).2
    rw [hpivot]
    omega
  have hext :
      squareRootExternalTerminalTag (t, p) ∈
        lowWheelCanonicalExternalTerminalPart R := by
    apply Finset.mem_filter.mpr
    refine ⟨htag, ?_⟩
    refine ⟨rfl, ?_, hface, ?_⟩
    · simpa [squareRootExternalTerminalTag] using hpivot.symm
    · rw [hpivot]
      exact (Finset.mem_Ioc.mp hpRange).1
  exact Finset.mem_filter.mpr ⟨hext, hzRepeated⟩

/-- The external repeated tag is therefore in the repeated terminal carrier of
#496. -/
theorem squareRootExternalTerminalRepeatedTag_mem_repeatedExternal
    {R : ℕ} (hR : 2 ≤ R)
    {z : LowWheelExternalTerminalFacePrime}
    (hz : z ∈ squareRootExternalTerminalRepeatedFaceCarrier R) :
    squareRootExternalTerminalTag z ∈
      lowWheelCanonicalRepeatedExternalTerminalPart R := by
  rw [← lowWheelCanonicalExternalTerminalRepeated_eq_repeatedExternalTerminal R]
  exact squareRootExternalTerminalRepeatedTag_mem_externalTerminal hR hz

/-- Tagging and then forgetting the forced cofactor is the identity. -/
theorem lowWheelRepeatedExternalTerminalToFacePrime_tag
    {R : ℕ} (hR : 2 ≤ R)
    {z : LowWheelExternalTerminalFacePrime}
    (hz : z ∈ squareRootExternalTerminalRepeatedFaceCarrier R) :
    lowWheelRepeatedExternalTerminalToFacePrime
        (squareRootExternalTerminalTag z) = z := by
  rcases z with ⟨t, p⟩
  have hzBase := (Finset.mem_filter.mp hz).1
  rcases mem_squareRootExternalTerminalFaceCarrier.mp hzBase with
    ⟨_htAdm, _hpRange, hp, _htop⟩
  apply Prod.ext
  · rfl
  · simp [lowWheelRepeatedExternalTerminalToFacePrime,
      lowWheelTaggedDowncrossPivot, squareRootExternalTerminalTag,
      lowWheelCanonicalCofactorQuotientPivot, hp.minFac_eq]

/-- The forgetting map is injective on the repeated external terminal carrier. -/
theorem lowWheelRepeatedExternalTerminalToFacePrime_injOn
    (R : ℕ) :
    Set.InjOn lowWheelRepeatedExternalTerminalToFacePrime
      (lowWheelCanonicalRepeatedExternalTerminalPart R) := by
  intro a ha b hb hab
  have hface : a.1 = b.1 := congrArg Prod.fst hab
  have hpivot :
      lowWheelTaggedDowncrossPivot a = lowWheelTaggedDowncrossPivot b :=
    congrArg Prod.snd hab
  have hta := (Finset.mem_filter.mp ha).1
  have htb := (Finset.mem_filter.mp hb).1
  rcases lowWheelCanonicalRepeatedTerminalBoundary_geometry hta with
    ⟨hca, hka, _hpa, _hfa, _hda, _hua⟩
  rcases lowWheelCanonicalRepeatedTerminalBoundary_geometry htb with
    ⟨hcb, hkb, _hpb, _hfb, _hdb, _hub⟩
  have hc : a.2.1 = b.2.1 := hca.trans hcb.symm
  have hk : a.2.2 = b.2.2 := by
    calc
      a.2.2 = lowWheelTaggedDowncrossPivot a := hka
      _ = lowWheelTaggedDowncrossPivot b := hpivot
      _ = b.2.2 := hkb.symm
  exact Prod.ext hface (Prod.ext hc hk)

/-- Exact image identity: there is no extra or missing occurrence on either
side of the coordinate change. -/
theorem lowWheelRepeatedExternalTerminalToFacePrime_image
    (R : ℕ) (hR : 2 ≤ R) :
    (lowWheelCanonicalRepeatedExternalTerminalPart R).image
        lowWheelRepeatedExternalTerminalToFacePrime =
      squareRootExternalTerminalRepeatedFaceCarrier R := by
  ext z
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
    exact lowWheelRepeatedExternalTerminalToFacePrime_mem hR hy
  · intro hz
    have htag := squareRootExternalTerminalRepeatedTag_mem_repeatedExternal hR hz
    apply Finset.mem_image.mpr
    exact ⟨squareRootExternalTerminalTag z, htag,
      lowWheelRepeatedExternalTerminalToFacePrime_tag hR hz⟩

/-- Signed mass of the repeated external terminal downcross population. -/
def lowWheelCanonicalRepeatedExternalTerminalMass (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelCanonicalRepeatedExternalTerminalPart R,
    lowWheelTaggedDowncrossWeight y

/-- A terminal state's downcross weight is just its Boolean-face sign. -/
theorem lowWheelRepeatedExternalTerminal_weight_eq_faceSign
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedExternalTerminalPart R) :
    lowWheelTaggedDowncrossWeight y = (booleanCubeSign y.1 : ℂ) := by
  have hterminal := (Finset.mem_filter.mp hy).1
  have hc := (lowWheelCanonicalRepeatedTerminalBoundary_geometry hterminal).1
  unfold lowWheelTaggedDowncrossWeight
  rw [hc]
  simp [canonicalMoebiusWeight]

/-- **Exact top/bottom coordinate identification.**  The repeated external
terminal mass of the canonical downcross frontier is exactly `squareRootERrep`. -/
theorem lowWheelCanonicalRepeatedExternalTerminalMass_eq_ERrep
    (R : ℕ) (hR : 2 ≤ R) :
    lowWheelCanonicalRepeatedExternalTerminalMass R = squareRootERrep R := by
  unfold lowWheelCanonicalRepeatedExternalTerminalMass squareRootERrep
  calc
    (∑ y ∈ lowWheelCanonicalRepeatedExternalTerminalPart R,
        lowWheelTaggedDowncrossWeight y) =
      ∑ y ∈ lowWheelCanonicalRepeatedExternalTerminalPart R,
        (booleanCubeSign y.1 : ℂ) := by
          apply Finset.sum_congr rfl
          intro y hy
          exact lowWheelRepeatedExternalTerminal_weight_eq_faceSign hy
    _ =
      ∑ z ∈
        (lowWheelCanonicalRepeatedExternalTerminalPart R).image
          lowWheelRepeatedExternalTerminalToFacePrime,
        (booleanCubeSign z.1 : ℂ) := by
          symm
          apply Finset.sum_image
          intro a ha b hb hab
          exact lowWheelRepeatedExternalTerminalToFacePrime_injOn R ha hb hab
    _ = ∑ z ∈ squareRootExternalTerminalRepeatedFaceCarrier R,
        (booleanCubeSign z.1 : ℂ) := by
          rw [lowWheelRepeatedExternalTerminalToFacePrime_image R hR]

end RHLean.Proof

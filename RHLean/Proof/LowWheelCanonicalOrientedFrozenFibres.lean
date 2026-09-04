import Mathlib
import RHLean.Proof.SquareRootCanonicalOrientedEpsilonBound
import RHLean.Proof.SquareRootLowPrimeFirstOwnerWallRecurrence

/-!
# Canonically oriented downcross fibres are frozen predecessor windows

After exact late-parent cancellation, the remaining root-downcross population
is the genuinely oriented Euler first-crossing carrier.  On one fixed physical
state `x = (c,k)`, orientation forces `k` to equal its canonical pivot `p` and
every face prime to lie strictly below `p`.

This file makes the resulting predecessor cube literal.  The Boolean faces that
charge one fixed oriented state are exactly the frozen faces of the old prime
universe `primesUpTo (p-1)` whose products lie in the state's physical
ownership window.  Consequently the signed face mass of one oriented state is
one `frozenPrimeUniverseWindowMass` with owner `p`.

No norm, prime count, PNT input, Mertens estimate, or asymptotic statement is
used.  This is the common-owner representation needed before taking the square
of a forward run difference.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis
open LowWheelCanonicalDowncrossOwnership
open SignedOwnershipInterval

attribute [local instance] Classical.propDecidable

/-- Boolean faces which charge one fixed state *and* survive the exact
late-parent cancellation, i.e. belong to the canonically oriented population. -/
def lowWheelCanonicalDowncrossOrientedChargingFaces
    (R : ℕ) (x : LowWheelCofactorQuotientState) : Finset (Finset ℕ) :=
  (primesUpTo R).powerset.filter fun t =>
    x ∈ lowWheelCanonicalDowncrossOrientedPart R t

@[simp] theorem mem_lowWheelCanonicalDowncrossOrientedChargingFaces
    {R : ℕ} {x : LowWheelCofactorQuotientState} {t : Finset ℕ} :
    t ∈ lowWheelCanonicalDowncrossOrientedChargingFaces R x ↔
      t ∈ (primesUpTo R).powerset ∧
        x ∈ lowWheelCanonicalDowncrossOrientedPart R t := by
  simp [lowWheelCanonicalDowncrossOrientedChargingFaces]

/-- One oriented charging face already forces the quotient coordinate to be the
canonical fresh owner. -/
theorem lowWheelCanonicalDowncrossOrientedChargingFaces_quotient_eq_pivot
    {R c k : ℕ}
    (hne : (lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k)).Nonempty) :
    k = lowWheelCanonicalDowncrossPivot (c, k) := by
  rcases hne with ⟨t, ht⟩
  have hx :=
    (mem_lowWheelCanonicalDowncrossOrientedChargingFaces.mp ht).2
  exact lowWheelCanonicalDowncrossOriented_quotient_eq_pivot hx

/-- An oriented charging family is in particular a nonempty ordinary charging
family, so the exact state-dependent ownership interval is available. -/
theorem lowWheelCanonicalDowncrossChargingFaces_nonempty_of_oriented
    {R c k : ℕ}
    (hne : (lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k)).Nonempty) :
    (lowWheelCanonicalDowncrossChargingFaces R (c, k)).Nonempty := by
  rcases hne with ⟨t, ht⟩
  rcases mem_lowWheelCanonicalDowncrossOrientedChargingFaces.mp ht with
    ⟨htPow, hx⟩
  exact ⟨t, mem_lowWheelCanonicalDowncrossChargingFaces.mpr
    ⟨htPow, (mem_lowWheelCanonicalDowncrossOrientedPart.mp hx).1⟩⟩

/-- **One oriented state is exactly one frozen predecessor window.**

If `(c,k)` is charged by at least one oriented face and `p` is its canonical
pivot, the complete set of oriented charging faces is precisely the old Boolean
cube through `p-1`, restricted to the exact physical ownership interval.
The reverse inclusion uses the already-proved exact ownership image, so no
support enlargement occurs. -/
theorem lowWheelCanonicalDowncrossOrientedChargingFaces_eq_frozenWindow
    {R c k : ℕ}
    (hne : (lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k)).Nonempty) :
    lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k) =
      frozenPrimeUniverseWindowFaces
        (primesUpTo (lowWheelCanonicalDowncrossPivot (c, k) - 1))
        (R / k)
        (lowWheelCanonicalDowncrossOwnershipUpper R c k) := by
  classical
  let p := lowWheelCanonicalDowncrossPivot (c, k)
  have hk : k = p := by
    simpa [p] using
      lowWheelCanonicalDowncrossOrientedChargingFaces_quotient_eq_pivot hne
  have hcharging :
      (lowWheelCanonicalDowncrossChargingFaces R (c, k)).Nonempty :=
    lowWheelCanonicalDowncrossChargingFaces_nonempty_of_oriented hne
  rcases hne with ⟨t0, ht0⟩
  rcases mem_lowWheelCanonicalDowncrossOrientedChargingFaces.mp ht0 with
    ⟨ht0Pow, hx0⟩
  have hdown0 := (mem_lowWheelCanonicalDowncrossOrientedPart.mp hx0).1
  have hgeom0 := lowWheelCanonicalDowncross_firstFailure_geometry hdown0
  dsimp only at hgeom0
  have hp : p.Prime := by simpa [p] using hgeom0.1
  ext t
  constructor
  · intro ht
    rcases mem_lowWheelCanonicalDowncrossOrientedChargingFaces.mp ht with
      ⟨htPow, hx⟩
    have htCharging :
        t ∈ lowWheelCanonicalDowncrossChargingFaces R (c, k) :=
      mem_lowWheelCanonicalDowncrossChargingFaces.mpr
        ⟨htPow, (mem_lowWheelCanonicalDowncrossOrientedPart.mp hx).1⟩
    have hwindow := primeFaceProduct_mem_exactOwnershipInterval htCharging
    apply mem_frozenPrimeUniverseWindowFaces.mpr
    refine ⟨?_, (Finset.mem_Ioc.mp hwindow).1,
      (Finset.mem_Ioc.mp hwindow).2⟩
    apply Finset.mem_powerset.mpr
    intro q hqt
    have hqPrime : q.Prime :=
      prime_of_mem_primesUpTo ((Finset.mem_powerset.mp htPow) hqt)
    have hqLt : q < p := by
      simpa [p] using
        lowWheelCanonicalDowncrossOriented_facePrime_lt_pivot htPow hx hqt
    exact mem_primesUpTo.mpr ⟨hqPrime, by omega⟩
  · intro ht
    rcases mem_frozenPrimeUniverseWindowFaces.mp ht with
      ⟨htPred, hlo, hup⟩
    have hpredSub := Finset.mem_powerset.mp htPred
    have hprodPos : 0 < primeFaceProduct t :=
      primeFaceProduct_pos_of_mem_powerset htPred
    have hupperLeR :
        lowWheelCanonicalDowncrossOwnershipUpper R c k ≤ R := by
      unfold lowWheelCanonicalDowncrossOwnershipUpper
      have hpPos : 0 < p := hp.pos
      have hdiv : k / lowWheelCanonicalDowncrossPivot (c, k) = 1 := by
        rw [hk]
        simpa [p] using Nat.div_self hpPos
      rw [hdiv]
      simpa using (min_le_left R (squareRootEndpoint R / (c * k)))
    have htSubR : t ⊆ primesUpTo R := by
      intro q hqt
      have hqPred := hpredSub hqt
      have hqPrime := prime_of_mem_primesUpTo hqPred
      have hqDvd : q ∣ primeFaceProduct t := by
        change q ∣ t.prod id
        exact Finset.dvd_prod_of_mem id hqt
      have hqProd : q ≤ primeFaceProduct t := Nat.le_of_dvd hprodPos hqDvd
      exact mem_primesUpTo.mpr ⟨hqPrime, hqProd.trans (hup.trans hupperLeR)⟩
    have htPowR : t ∈ (primesUpTo R).powerset :=
      Finset.mem_powerset.mpr htSubR
    have hmu : μ (primeFaceProduct t) = booleanCubeSign t :=
      moebius_primeFaceProduct_eq_booleanCubeSign t (by
        intro q hqt
        exact prime_of_mem_primesUpTo (hpredSub hqt))
    have hmuNe : μ (primeFaceProduct t) ≠ 0 := by
      rw [hmu]
      unfold booleanCubeSign
      exact pow_ne_zero _ (by norm_num)
    have hsq : Squarefree (primeFaceProduct t) :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuNe
    have hOwn :
        primeFaceProduct t ∈
          lowWheelCanonicalDowncrossOwnershipProducts R c k :=
      mem_lowWheelCanonicalDowncrossOwnershipProducts.mpr ⟨hlo, hup, hsq⟩
    have himage :=
      image_primeFaceProduct_chargingFaces_eq_ownershipProducts hcharging
    have hImageMem :
        primeFaceProduct t ∈
          (lowWheelCanonicalDowncrossChargingFaces R (c, k)).image
            primeFaceProduct := by
      rw [himage]
      exact hOwn
    rcases Finset.mem_image.mp hImageMem with ⟨u, huCharging, hprod⟩
    have huData := mem_lowWheelCanonicalDowncrossChargingFaces.mp huCharging
    have huSub := Finset.mem_powerset.mp huData.1
    have hut : u = t :=
      (primeFaceProduct_eq_iff
        (fun q hqu => prime_of_mem_primesUpTo (huSub hqu))
        (fun q hqt => prime_of_mem_primesUpTo (htSubR hqt))).mp hprod
    subst u
    apply mem_lowWheelCanonicalDowncrossOrientedChargingFaces.mpr
    refine ⟨htPowR, mem_lowWheelCanonicalDowncrossOrientedPart.mpr
      ⟨huData.2, ?_⟩⟩
    intro q hqParent
    have hparentEq :
        lowWheelCanonicalDowncrossParent t (c, k) = primeFaceProduct t := by
      unfold lowWheelCanonicalDowncrossParent
      have hpPos : 0 < p := hp.pos
      rw [hk]
      change primeFaceProduct t *
          (p / lowWheelCanonicalDowncrossPivot (c, p)) = primeFaceProduct t
      have hpivot : lowWheelCanonicalDowncrossPivot (c, p) = p := by
        simpa [hk, p] using congrArg lowWheelCanonicalDowncrossPivot (Prod.ext rfl hk)
      rw [hpivot, Nat.div_self hpPos, Nat.mul_one]
    rw [hparentEq] at hqParent
    have hqData := Nat.mem_primeFactors.mp hqParent
    rcases hqData with ⟨hqPrime, hqDvd, _hprodNe⟩
    change q ∣ t.prod id at hqDvd
    rcases (Prime.dvd_finset_prod_iff hqPrime.prime id).mp hqDvd with
      ⟨r, hrt, hqr⟩
    have hrPrime : r.Prime :=
      prime_of_mem_primesUpTo (hpredSub hrt)
    have hqrEq : q = r :=
      (Nat.prime_dvd_prime_iff_eq hqPrime hrPrime).mp hqr
    subst q
    have hrPred := mem_primesUpTo.mp (hpredSub hrt)
    omega

/-- **Signed oriented fibre = signed frozen predecessor strip.**  The equality
holds before any absolute value and retains the full Boolean/Möbius sign. -/
theorem sum_booleanCubeSign_orientedChargingFaces_eq_frozenWindowMass
    {R c k : ℕ}
    (hne : (lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k)).Nonempty) :
    (∑ t ∈ lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k),
        booleanCubeSign t) =
      frozenPrimeUniverseWindowMass
        (primesUpTo (lowWheelCanonicalDowncrossPivot (c, k) - 1))
        (R / k)
        (lowWheelCanonicalDowncrossOwnershipUpper R c k) := by
  rw [lowWheelCanonicalDowncrossOrientedChargingFaces_eq_frozenWindow hne]
  rfl

end RHLean.Proof

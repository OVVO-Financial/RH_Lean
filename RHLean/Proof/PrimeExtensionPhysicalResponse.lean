import Mathlib
import RHLean.Analysis.PrimeExtensionEnergyTelescope
import RHLean.Analysis.RoughWheelFiniteCounting
import RHLean.Proof.PrimeWheelFrozenRoughSeatBridge
import RHLean.Proof.SquareRootAncestryRoot

/-!
# Physical response form of the exact prime-extension energy telescope

The chronological state in `PrimeExtensionEnergyTelescope` contains the child
amplitude

```text
B = T_(pW)(floor(x/p)).
```

This file opens that finite rough prefix on its literal rough-seat / frozen-cube
carrier before any inequality is taken.

For a squarefree wheel `V`, scales `z` and `y`, define the signed response

```text
R_V(z,y)
  = sum_{z < n <= y, (n,V)=1} mu(n)
    + sum_{n <= z, (n,V)=1} mu(n) * (1 - F_V(floor(z/n))),
```

where `F_V` is the frozen Boolean cube on the prime factors of `V`.

The exact finite identity is

```text
T_V(y) = M(z) + R_V(z,y).
```

At one prime-extension step take

```text
V = pW,  y = floor(x/p),  z = floor(x/p^2).
```

Thus the #789 defect splits exactly into a true `p^2` Mertens daughter plus
one signed physical response/covariance packet.  Iterating gives the requested
ordered-chain energy telescope with every lower-scale Mertens square exposed
and all response terms kept assembled.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The exact signed physical response between two scales on a squarefree wheel.

The first term is the newly opened rough-seat interval.  The second term is the
frozen-cube response on rough seats already present at the lower scale. -/
def roughWheelPhysicalResponse (V z y : ℕ) : ℤ :=
  roughInterval V z y +
    ∑ n ∈ roughWheelInterval V 0 z,
      (μ n : ℤ) *
        (1 - frozenPrimeUniverseMass V.primeFactors (z / n))

/-- On an ordered pair of scales the first summand is literally the physical
rough-seat carrier, not merely an algebraic difference of prefixes. -/
theorem roughWheelPhysicalResponse_eq_carrierSums
    {V z y : ℕ} (hzy : z ≤ y) :
    roughWheelPhysicalResponse V z y =
      (∑ n ∈ roughWheelInterval V z y, (μ n : ℤ)) +
        ∑ n ∈ roughWheelInterval V 0 z,
          (μ n : ℤ) *
            (1 - frozenPrimeUniverseMass V.primeFactors (z / n)) := by
  unfold roughWheelPhysicalResponse
  rw [roughInterval_eq_sum_roughWheelInterval V z y hzy]

/-- **Finite rough-seat / frozen-cube amplitude decomposition.**

For every squarefree wheel, the upper rough prefix is exactly the ordinary
Mertens prefix at the lower scale plus the physical response above.  No
triangle inequality or asymptotic input is used. -/
theorem roughMertens_eq_mertensSummatoryInt_add_physicalResponse
    {V z y : ℕ} (hV : Squarefree V) :
    roughMertens V y =
      mertensSummatoryInt z + roughWheelPhysicalResponse V z y := by
  have hprime : ∀ q ∈ V.primeFactors, q.Prime := by
    intro q hq
    exact (Nat.mem_primeFactors.mp hq).1
  have hprod :
      RHLean.Arithmetic.primorial V.primeFactors = V := by
    simpa [RHLean.Arithmetic.primorial] using
      Nat.prod_primeFactors_of_squarefree hV
  have hMertens :
      roughMertens 1 z = mertensSummatoryInt z := by
    unfold roughMertens mertensSummatoryInt
    simp [roughMoebius]
  have hfrozen :=
    roughMertens_one_eq_primeWheel_frozenFullRoughSeatCorrelation
      V.primeFactors hprime z
  rw [hMertens] at hfrozen
  unfold primeWheelFrozenFullRoughSeatCorrelation at hfrozen
  rw [hprod] at hfrozen
  have hzero : roughMertens V 0 = 0 := by
    simp [roughMertens, roughMoebius]
  have hrough :=
    roughInterval_eq_sum_roughWheelInterval V 0 z (Nat.zero_le z)
  unfold roughInterval at hrough
  rw [hzero, sub_zero] at hrough
  have hresponse :
      (∑ n ∈ roughWheelInterval V 0 z,
          (μ n : ℤ) *
            (1 - frozenPrimeUniverseMass V.primeFactors (z / n))) =
        roughMertens V z - mertensSummatoryInt z := by
    calc
      (∑ n ∈ roughWheelInterval V 0 z,
          (μ n : ℤ) *
            (1 - frozenPrimeUniverseMass V.primeFactors (z / n))) =
          (∑ n ∈ roughWheelInterval V 0 z, (μ n : ℤ)) -
            ∑ n ∈ roughWheelInterval V 0 z,
              (μ n : ℤ) *
                frozenPrimeUniverseMass V.primeFactors (z / n) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro n _hn
            ring
      _ = roughMertens V z - mertensSummatoryInt z := by
            rw [← hrough, ← hfrozen]
  unfold roughWheelPhysicalResponse
  rw [hresponse]
  unfold roughInterval
  ring

/-- Physical response attached to the child amplitude in one prime-extension
step.  Its two scales are exactly `x/p` and `x/p^2`. -/
def roughPrimeExtensionPhysicalResponse (W p x : ℕ) : ℤ :=
  roughWheelPhysicalResponse (p * W) (x / (p * p)) (x / p)

/-- The response can always be displayed on its literal two physical carriers;
the square-dilated cutoff is automatically below the once-dilated cutoff. -/
theorem roughPrimeExtensionPhysicalResponse_eq_carrierSums
    (W p x : ℕ) :
    roughPrimeExtensionPhysicalResponse W p x =
      (∑ n ∈ roughWheelInterval (p * W) (x / (p * p)) (x / p),
          (μ n : ℤ)) +
        ∑ n ∈ roughWheelInterval (p * W) 0 (x / (p * p)),
          (μ n : ℤ) *
            (1 - frozenPrimeUniverseMass (p * W).primeFactors
              ((x / (p * p)) / n)) := by
  unfold roughPrimeExtensionPhysicalResponse
  apply roughWheelPhysicalResponse_eq_carrierSums
  rw [← Nat.div_div_eq_div_mul]
  exact Nat.div_le_self (x / p) p

/-- **The missing scale conversion in #789.**

The child rough amplitude is an actual `p^2` Mertens daughter plus a response
defined on the rough-seat/frozen-cube physical ledger. -/
theorem roughMertens_primeExtensionChild_eq_mertensSquare_add_physicalResponse
    {W p : ℕ} (hpW : Squarefree (p * W)) (x : ℕ) :
    roughMertens (p * W) (x / p) =
      mertensSummatoryInt (x / (p * p)) +
        roughPrimeExtensionPhysicalResponse W p x := by
  exact
    roughMertens_eq_mertensSummatoryInt_add_physicalResponse
      (V := p * W) (z := x / (p * p)) (y := x / p) hpW

/-- Signed quadratic response left after the true `p^2` daughter square is
exposed inside the exact #789 one-prime defect. -/
def roughPrimeExtensionPhysicalGamma (W p x : ℕ) : ℤ :=
  let A := roughMertens (p * W) x
  let M := mertensSummatoryInt (x / (p * p))
  let R := roughPrimeExtensionPhysicalResponse W p x
  R ^ 2 + 2 * M * R - 2 * A * M - 2 * A * R

/-- The #789 one-prime defect is exactly a true `p^2` Mertens energy plus the
assembled signed physical response/covariance term. -/
theorem roughPrimeExtensionEnergyDefect_eq_mertensSquare_add_physicalGamma
    {W p : ℕ} (hpW : Squarefree (p * W)) (x : ℕ) :
    roughPrimeExtensionEnergyDefect W p x =
      mertensSummatoryInt (x / (p * p)) ^ 2 +
        roughPrimeExtensionPhysicalGamma W p x := by
  have hchild :=
    roughMertens_primeExtensionChild_eq_mertensSquare_add_physicalResponse
      (W := W) (p := p) hpW x
  unfold roughPrimeExtensionEnergyDefect roughPrimeExtensionPhysicalGamma
  rw [hchild]
  ring

/-- Exact one-prime energy law with the genuine `p^2` Mertens daughter
displayed and the full signed physical response left intact. -/
theorem roughMertens_sq_prime_extension_physical
    {W p : ℕ} (hp : p.Prime) (hpW : Squarefree (p * W)) (x : ℕ) :
    roughMertens W x ^ 2 =
      roughMertens (p * W) x ^ 2 +
        mertensSummatoryInt (x / (p * p)) ^ 2 +
        roughPrimeExtensionPhysicalGamma W p x := by
  rw [roughMertens_sq_prime_extension hp hpW x,
    roughPrimeExtensionEnergyDefect_eq_mertensSquare_add_physicalGamma hpW x]
  ring

/-- Sum of the genuine lower-scale Mertens daughter energies along an ordered
prime-extension chain. -/
def primeExtensionMertensSquareSum (x : ℕ) : List ℕ → ℤ
  | [] => 0
  | p :: ps =>
      mertensSummatoryInt (x / (p * p)) ^ 2 +
        primeExtensionMertensSquareSum x ps

/-- Sum of the assembled physical response/covariance packets along the same
ordered chain.  The wheel is advanced after every prime exactly as in #789. -/
def roughPrimeExtensionPhysicalGammaSum (W x : ℕ) : List ℕ → ℤ
  | [] => 0
  | p :: ps =>
      roughPrimeExtensionPhysicalGamma W p x +
        roughPrimeExtensionPhysicalGammaSum (p * W) x ps

/-- **Physical ordered-chain energy telescope.**

This is the corrected #789 telescope: every chronological step exposes a true
`p_j^2` Mertens daughter, while every remaining cross term stays inside one
signed physical response packet. -/
theorem roughMertens_sq_primeExtensionChain_physical
    {W x : ℕ} {ps : List ℕ}
    (hchain : PrimeExtensionChainAdmissible W ps) :
    roughMertens W x ^ 2 =
      roughMertens (primeExtensionWheel W ps) x ^ 2 +
        primeExtensionMertensSquareSum x ps +
        roughPrimeExtensionPhysicalGammaSum W x ps := by
  induction ps generalizing W with
  | nil =>
      simp [primeExtensionWheel, primeExtensionMertensSquareSum,
        roughPrimeExtensionPhysicalGammaSum]
  | cons p ps ih =>
      simp only [PrimeExtensionChainAdmissible] at hchain
      rcases hchain with ⟨hp, hpW, htail⟩
      calc
        roughMertens W x ^ 2 =
            roughMertens (p * W) x ^ 2 +
              mertensSummatoryInt (x / (p * p)) ^ 2 +
              roughPrimeExtensionPhysicalGamma W p x :=
          roughMertens_sq_prime_extension_physical hp hpW x
        _ =
            (roughMertens (primeExtensionWheel (p * W) ps) x ^ 2 +
              primeExtensionMertensSquareSum x ps +
              roughPrimeExtensionPhysicalGammaSum (p * W) x ps) +
              mertensSummatoryInt (x / (p * p)) ^ 2 +
              roughPrimeExtensionPhysicalGamma W p x := by
          rw [ih htail]
        _ =
            roughMertens (primeExtensionWheel W (p :: ps)) x ^ 2 +
              primeExtensionMertensSquareSum x (p :: ps) +
              roughPrimeExtensionPhysicalGammaSum W x (p :: ps) := by
          simp [primeExtensionWheel, primeExtensionMertensSquareSum,
            roughPrimeExtensionPhysicalGammaSum]
          ring


/-! ## Global finite covariance reassembly

The one-step physical response above is an amplitude object.  When the #789
energy defects are summed over a chain, the passage from the diagonal daughter
energy to the square of the assembled daughter column necessarily creates the
off-diagonal owner covariance.  The following identities expose that finite
bookkeeping exactly. -/

/-- Sum of the once-dilated child amplitudes encountered along an ordered
prime-extension chain. -/
def roughPrimeExtensionChildAmplitudeSum (W x : ℕ) : List ℕ → ℤ
  | [] => 0
  | p :: ps =>
      roughMertens (p * W) (x / p) +
        roughPrimeExtensionChildAmplitudeSum (p * W) x ps

/-- Exact amplitude telescope underlying the #789 energy telescope. -/
theorem roughMertens_primeExtensionChain_amplitude
    {W x : ℕ} {ps : List ℕ}
    (hchain : PrimeExtensionChainAdmissible W ps) :
    roughMertens W x =
      roughMertens (primeExtensionWheel W ps) x -
        roughPrimeExtensionChildAmplitudeSum W x ps := by
  induction ps generalizing W with
  | nil =>
      simp [primeExtensionWheel, roughPrimeExtensionChildAmplitudeSum]
  | cons p ps ih =>
      simp only [PrimeExtensionChainAdmissible] at hchain
      rcases hchain with ⟨hp, hpW, htail⟩
      have hstep := roughMertens_prime_extension (W := W) hp hpW x
      have htailAmp := ih (W := p * W) htail
      calc
        roughMertens W x =
            roughMertens (p * W) x -
              roughMertens (p * W) (x / p) := by
          linarith
        _ =
            (roughMertens (primeExtensionWheel (p * W) ps) x -
              roughPrimeExtensionChildAmplitudeSum (p * W) x ps) -
              roughMertens (p * W) (x / p) := by
          rw [htailAmp]
        _ =
            roughMertens (primeExtensionWheel W (p :: ps)) x -
              roughPrimeExtensionChildAmplitudeSum W x (p :: ps) := by
          simp [primeExtensionWheel, roughPrimeExtensionChildAmplitudeSum]
          ring

/-- Sum of the genuine lower-scale Mertens amplitudes exposed along a chain. -/
def primeExtensionMertensSum (x : ℕ) : List ℕ → ℤ
  | [] => 0
  | p :: ps =>
      mertensSummatoryInt (x / (p * p)) +
        primeExtensionMertensSum x ps

/-- Sum of the physically defined rough-seat/frozen-cube responses along the
same chain. -/
def roughPrimeExtensionPhysicalResponseSum (W x : ℕ) : List ℕ → ℤ
  | [] => 0
  | p :: ps =>
      roughPrimeExtensionPhysicalResponse W p x +
        roughPrimeExtensionPhysicalResponseSum (p * W) x ps

/-- The complete child-amplitude column splits exactly into the true q² Mertens
column plus the assembled physical response column. -/
theorem roughPrimeExtensionChildAmplitudeSum_eq_mertensSum_add_physicalResponseSum
    {W x : ℕ} {ps : List ℕ}
    (hchain : PrimeExtensionChainAdmissible W ps) :
    roughPrimeExtensionChildAmplitudeSum W x ps =
      primeExtensionMertensSum x ps +
        roughPrimeExtensionPhysicalResponseSum W x ps := by
  induction ps generalizing W with
  | nil =>
      simp [roughPrimeExtensionChildAmplitudeSum, primeExtensionMertensSum,
        roughPrimeExtensionPhysicalResponseSum]
  | cons p ps ih =>
      simp only [PrimeExtensionChainAdmissible] at hchain
      rcases hchain with ⟨_hp, hpW, htail⟩
      have hchild :=
        roughMertens_primeExtensionChild_eq_mertensSquare_add_physicalResponse
          (W := W) (p := p) hpW x
      have htailSplit := ih (W := p * W) htail
      simp only [roughPrimeExtensionChildAmplitudeSum, primeExtensionMertensSum,
        roughPrimeExtensionPhysicalResponseSum]
      rw [hchild, htailSplit]
      ring

/-- Corrected chain-level amplitude normal form: terminal rough amplitude minus
the genuine q² Mertens column minus one assembled physical-response column. -/
theorem roughMertens_primeExtensionChain_physical_amplitude
    {W x : ℕ} {ps : List ℕ}
    (hchain : PrimeExtensionChainAdmissible W ps) :
    roughMertens W x =
      roughMertens (primeExtensionWheel W ps) x -
        primeExtensionMertensSum x ps -
        roughPrimeExtensionPhysicalResponseSum W x ps := by
  rw [roughMertens_primeExtensionChain_amplitude hchain,
    roughPrimeExtensionChildAmplitudeSum_eq_mertensSum_add_physicalResponseSum
      hchain]
  ring

/-- Off-diagonal covariance created when the true q² daughter amplitudes are
assembled before squaring.  This is exactly the difference between the square
of the daughter column and its diagonal energy. -/
def primeExtensionMertensCrossCovariance (x : ℕ) (ps : List ℕ) : ℤ :=
  primeExtensionMertensSum x ps ^ 2 -
    primeExtensionMertensSquareSum x ps

/-- **Exact global form of the signed Gamma response.**

The summed #789 response is not a linear boundary population.  It consists of
the off-diagonal q²-owner covariance, its cross coupling with the assembled
physical response, the response self-energy, and the two terminal-wheel cross
terms.  This is the finite bookkeeping obstruction that disappears if the
physical amplitudes are squared owner-by-owner. -/
theorem roughPrimeExtensionPhysicalGammaSum_eq_crossCovariance_reassembly
    {W x : ℕ} {ps : List ℕ}
    (hchain : PrimeExtensionChainAdmissible W ps) :
    roughPrimeExtensionPhysicalGammaSum W x ps =
      primeExtensionMertensCrossCovariance x ps +
        2 * primeExtensionMertensSum x ps *
          roughPrimeExtensionPhysicalResponseSum W x ps +
        roughPrimeExtensionPhysicalResponseSum W x ps ^ 2 -
        2 * roughMertens (primeExtensionWheel W ps) x *
          primeExtensionMertensSum x ps -
        2 * roughMertens (primeExtensionWheel W ps) x *
          roughPrimeExtensionPhysicalResponseSum W x ps := by
  have henergy :=
    roughMertens_sq_primeExtensionChain_physical
      (W := W) (x := x) (ps := ps) hchain
  have hamp :=
    roughMertens_primeExtensionChain_physical_amplitude
      (W := W) (x := x) (ps := ps) hchain
  calc
    roughPrimeExtensionPhysicalGammaSum W x ps =
        roughMertens W x ^ 2 -
          roughMertens (primeExtensionWheel W ps) x ^ 2 -
          primeExtensionMertensSquareSum x ps := by
      linarith
    _ =
        primeExtensionMertensCrossCovariance x ps +
          2 * primeExtensionMertensSum x ps *
            roughPrimeExtensionPhysicalResponseSum W x ps +
          roughPrimeExtensionPhysicalResponseSum W x ps ^ 2 -
          2 * roughMertens (primeExtensionWheel W ps) x *
            primeExtensionMertensSum x ps -
          2 * roughMertens (primeExtensionWheel W ps) x *
            roughPrimeExtensionPhysicalResponseSum W x ps := by
      rw [hamp]
      unfold primeExtensionMertensCrossCovariance
      ring

end RHLean.Proof

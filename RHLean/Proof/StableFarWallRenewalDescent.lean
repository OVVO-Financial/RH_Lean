import RHLean.Proof.StableFarWallCrossingRenewal

/-!
# Well-founded descent of the stable-far crossing renewal

The post-#672 crossing renewal is not merely a return to the same physical wall.
It is a strict arithmetic descent.

A crossing product is indexed by `(q, d*p)`, where `q` is the canonical largest
prime stripped from the old low cofactor `c=q*d`, and the returned stable-wall
state has low cofactor `d`.  Thus one renewal step replaces `q*d` by `d`.

The first theorem below records the resulting strict decrease of the low
cofactor.  More importantly, if a returned state is itself the parent of a
second crossing, then the second stripped owner is the canonical largest prime
of `d`, hence is strictly smaller than the previous owner `q`.

Consequently a chain of strict crossing renewals has strictly decreasing prime
owners and cannot cycle.  This is the well-foundedness needed to iterate the
exact signed renewal before taking a norm: every path must terminate either in
a literal q^2-descended child or at a terminal low-cofactor state.

No estimate, norm, Mertens hypothesis, or asymptotic input is used.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

/-- Low cofactor before the crossing owner is stripped.  For an actual crossing
product `(q,d*p)` this is `q*d`. -/
def lowWheelFarPrimeCrossingParentLowCofactor (x : ℕ × ℕ) : ℕ :=
  x.1 * canonicalCofactor x.2

/-- Low cofactor after the crossing owner is stripped.  For an actual crossing
product `(q,d*p)` this is `d`. -/
def lowWheelFarPrimeCrossingRenewalLowCofactor (x : ℕ × ℕ) : ℕ :=
  canonicalCofactor x.2

/-- **One renewal step strictly decreases the low cofactor.** -/
theorem lowWheelFarPrimeCrossingRenewalLowCofactor_lt_parent
    {R : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ lowWheelFarPrimeCrossingProductCarrier R) :
    lowWheelFarPrimeCrossingRenewalLowCofactor x <
      lowWheelFarPrimeCrossingParentLowCofactor x := by
  rcases Finset.mem_image.mp hx with ⟨t, htCross, rfl⟩
  have ht : t ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp htCross).1
  rcases lowWheelFarPrimeLowCofactorTriple_data ht with
    ⟨hq, _hqR, hd1, _hp, _hpR, _hdsq, _hdq, _hcut⟩
  have hcoords := lowWheelFarPrimeProduct_coordinates ht
  unfold lowWheelFarPrimeCrossingRenewalLowCofactor
    lowWheelFarPrimeCrossingParentLowCofactor
    lowWheelFarPrimeProductKey
  rw [hcoords.2]
  have hq2 : 2 ≤ t.1 := hq.two_le
  nlinarith

/-- If a returned crossing state is used as the parent of another crossing,
then the next stripped owner is strictly smaller than the previous owner.

The equality hypothesis is exactly the low-cofactor compatibility of two
successive renewal steps: the second parent `q' * d'` is the first returned
cofactor `d`. -/
theorem lowWheelFarPrimeCrossing_nested_owner_lt
    {R : ℕ} {x y : ℕ × ℕ}
    (hx : x ∈ lowWheelFarPrimeCrossingProductCarrier R)
    (hy : y ∈ lowWheelFarPrimeCrossingProductCarrier R)
    (hchain : lowWheelFarPrimeCrossingParentLowCofactor y =
      lowWheelFarPrimeCrossingRenewalLowCofactor x) :
    y.1 < x.1 := by
  rcases Finset.mem_image.mp hx with ⟨tx, htxCross, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨ty, htyCross, rfl⟩
  have htx : tx ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp htxCross).1
  have hty : ty ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp htyCross).1
  rcases lowWheelFarPrimeLowCofactorTriple_data htx with
    ⟨_hqx, _hqxR, _hdx1, _hpx, _hpxR, _hdxsq, hdxq, _hcutx⟩
  rcases lowWheelFarPrimeLowCofactorTriple_data hty with
    ⟨hqy, _hqyR, hdy1, _hpy, _hpyR, _hdysq, hdyq, _hcuty⟩
  have hcoordsX := lowWheelFarPrimeProduct_coordinates htx
  have hcoordsY := lowWheelFarPrimeProduct_coordinates hty
  have hchain' : ty.1 * ty.2.1 = tx.2.1 := by
    simpa [lowWheelFarPrimeCrossingParentLowCofactor,
      lowWheelFarPrimeCrossingRenewalLowCofactor,
      lowWheelFarPrimeProductKey, hcoordsX.2, hcoordsY.2] using hchain
  have hdyPos : 0 < ty.2.1 := by omega
  have hlpfY :
      canonicalLargestPrimeFactor (ty.1 * ty.2.1) = ty.1 := by
    have h := canonicalLargestPrimeFactor_mul_prime_eq_of_rough
      hdyPos hqy hdyq
    simpa [Nat.mul_comm] using h
  have hownerEq :
      ty.1 = canonicalLargestPrimeFactor tx.2.1 := by
    have h := congrArg canonicalLargestPrimeFactor hchain'
    rw [hlpfY] at h
    exact h
  rw [hownerEq]
  exact hdxq

/-- In particular, two strict crossing renewals cannot form a two-cycle. -/
theorem lowWheelFarPrimeCrossing_no_twoCycle
    {R : ℕ} {x y : ℕ × ℕ}
    (hx : x ∈ lowWheelFarPrimeCrossingProductCarrier R)
    (hy : y ∈ lowWheelFarPrimeCrossingProductCarrier R) :
    ¬ (lowWheelFarPrimeCrossingParentLowCofactor y =
          lowWheelFarPrimeCrossingRenewalLowCofactor x ∧
        lowWheelFarPrimeCrossingParentLowCofactor x =
          lowWheelFarPrimeCrossingRenewalLowCofactor y) := by
  rintro ⟨hyx, hxy⟩
  have h1 := lowWheelFarPrimeCrossing_nested_owner_lt hx hy hyx
  have h2 := lowWheelFarPrimeCrossing_nested_owner_lt hy hx hxy
  omega

end RHLean.Proof

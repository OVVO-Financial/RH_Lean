import Mathlib
import RHLean.Proof.SquareRootLowPrimeGoSecondContactSources
import RHLean.Proof.SquareRootLowPrimeSignedResponseMatching

/-!
# Interface flux register for the second-contact seam

The #632 recombination is currently an identity between two *totals*: the summed
Go square residuals and the signed Möbius mass of their arithmetic children.  A
total identity is fragile under regrouping, because a later reorganisation of
the carrier can only reuse it wholesale.

This module replaces the total by its coefficient function.  A finite signed
ledger is written as an occurrence set `S`, a map `φ` sending each occurrence to
the arithmetic state it acts on, and an integer weight `w`.  Its
`ledgerCoefficient` at a state `n` is the signed total of the occurrences that
land on `n`, multiplicities retained.  The `interfaceFluxRegister` of two
ledgers is their coefficientwise difference: the exact algebraic analogue of the
flux register used to restore conservation across a refinement interface, where
a coarse face and the fine faces covering it must be assigned the same total
flux.

Two structural facts make the register worth carrying:

* summing a ledger's coefficients over any finite set of states returns exactly
  the ledger mass carried by the occurrences landing in that set
  (`sum_ledgerCoefficient_eq_restrictedMass`);
* a register that vanishes at *every* state forces the two ledgers to agree on
  *every* finite selection of states
  (`restrictedMass_eq_of_interfaceFluxRegister_eq_zero`).

So a vanishing register is a cancellation that survives any later regrouping,
which the equality of totals is not.

The second half instantiates this on the concrete carrier compiled in
`SquareRootLowPrimeGoSecondContactSources`.  The proposed rough-prefix ledger is
the owner-tagged occurrence set `(q,c)` — the second-contact owner `q` together
with its rough prefix `c`, `P⁺(c) < q`, `c ≤ X/q²` — mapped to the arithmetic
state `q*c` with weight `μ(c)`.  The existing low-transport ledger is the
disjoint arithmetic child population with weight `-μ(m)`.
`goSecondContactInterfaceFluxRegister_eq_zero` proves the register between them
vanishes at every arithmetic state; the owner tag is kept until the coefficient
has been summed, and is then recovered from the state itself as `P⁺(m)`.

The last section isolates the boundary term this identification exposes.  The
rough prefixes include the unit `c = 1`, which is not a second contact at all:
it contributes the bare owner `m = q`, and only when `q² ≤ X`.  Splitting it off
gives

`Σ_{q∈Q} F_{q⁻}(X/q²) = #{q ∈ Q : q² ≤ X} + Σ_{q∈Q} Σ_{c>1} μ(c)`,

an exact identity whose first term is a genuine root-scale anchor
(`goRoughPrefixUnitAnchor_card_le_sqrt`).  Removing it also sharpens the support
of the remaining cascade: a strict rough prefix `c > 1` forces its owner to
satisfy `q ≥ 3`, because the only prefix rough below `2` is the unit itself.
Hence the anchor-free population lives at `m ≤ X/3` rather than `m ≤ X/2`, and

`|Σ_{q∈Q} F_{q⁻}(X/q²)| ≤ √X + X/3`.

This is an exact split plus an elementary support count.  It is strictly smaller
than the `X/2` bound of #632 once `X > 36`, but it is still linear in `X`: no
power saving, no Mertens input, and no asymptotic estimate is claimed here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-! ## Ledger coefficients on a common arithmetic carrier -/

/-- Coefficient of a finite signed ledger at one arithmetic state: the total
weight of the occurrences that land on `n`, with multiplicities retained. -/
def ledgerCoefficient {ι : Type*} (S : Finset ι) (φ : ι → ℕ) (w : ι → ℤ)
    (n : ℕ) : ℤ :=
  ∑ z ∈ S.filter (fun z => φ z = n), w z

/-- Discarding the occurrences that land outside `N` does not change any
coefficient inside `N`. -/
theorem ledgerCoefficient_restrict {ι : Type*}
    (S : Finset ι) (φ : ι → ℕ) (w : ι → ℤ) {N : Finset ℕ} {n : ℕ}
    (hn : n ∈ N) :
    ledgerCoefficient (S.filter (fun z => φ z ∈ N)) φ w n =
      ledgerCoefficient S φ w n := by
  have hset :
      (S.filter (fun z => φ z ∈ N)).filter (fun z => φ z = n) =
        S.filter (fun z => φ z = n) := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1.1, h.2⟩
    · intro h
      refine ⟨⟨h.1, ?_⟩, h.2⟩
      rw [h.2]
      exact hn
  unfold ledgerCoefficient
  rw [hset]

/-- **Fibrewise resummation.**  Summing a ledger's coefficients over any finite
set of arithmetic states recovers exactly the mass carried by the occurrences
landing in that set.  This is the conservation bookkeeping: a coarse selection
of states and the fine occurrences covering it carry the same total. -/
theorem sum_ledgerCoefficient_eq_restrictedMass {ι : Type*}
    (S : Finset ι) (φ : ι → ℕ) (w : ι → ℤ) (N : Finset ℕ) :
    (∑ n ∈ N, ledgerCoefficient S φ w n) =
      ∑ z ∈ S.filter (fun z => φ z ∈ N), w z := by
  have hmaps : ∀ z ∈ S.filter (fun z => φ z ∈ N), φ z ∈ N := by
    intro z hz
    exact (Finset.mem_filter.mp hz).2
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps w
  calc
    (∑ n ∈ N, ledgerCoefficient S φ w n) =
        ∑ n ∈ N, ledgerCoefficient (S.filter (fun z => φ z ∈ N)) φ w n := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      exact (ledgerCoefficient_restrict S φ w hn).symm
    _ = ∑ z ∈ S.filter (fun z => φ z ∈ N), w z := by
      unfold ledgerCoefficient
      exact hfib

/-- **Total conservation.**  If every occurrence lands inside `N`, the ledger's
coefficients over `N` sum to its total signed mass. -/
theorem sum_ledgerCoefficient_eq_total {ι : Type*}
    (S : Finset ι) (φ : ι → ℕ) (w : ι → ℤ) {N : Finset ℕ}
    (hmaps : ∀ z ∈ S, φ z ∈ N) :
    (∑ n ∈ N, ledgerCoefficient S φ w n) = ∑ z ∈ S, w z := by
  rw [sum_ledgerCoefficient_eq_restrictedMass]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext z
  simp only [Finset.mem_filter]
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, hmaps z h⟩

/-- Reindexing a ledger along a map that is injective on its occurrence set
leaves every coefficient unchanged. -/
theorem ledgerCoefficient_image_of_injOn {ι : Type*}
    (S : Finset ι) (φ : ι → ℕ) (v : ℕ → ℤ)
    (hinj : Set.InjOn φ (S : Set ι)) (n : ℕ) :
    ledgerCoefficient (S.image φ) (fun m => m) v n =
      ledgerCoefficient S φ (fun z => v (φ z)) n := by
  have hset :
      (S.image φ).filter (fun m => m = n) =
        (S.filter (fun z => φ z = n)).image φ := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨z, hzS, hzm⟩, hmn⟩
      refine ⟨z, Finset.mem_filter.mpr ⟨hzS, ?_⟩, hzm⟩
      rw [hzm]
      exact hmn
    · rintro ⟨z, hz, hzm⟩
      rcases Finset.mem_filter.mp hz with ⟨hzS, hzn⟩
      refine ⟨⟨z, hzS, hzm⟩, ?_⟩
      rw [← hzm]
      exact hzn
  show (∑ m ∈ (S.image φ).filter (fun m => m = n), v m) =
    ∑ z ∈ S.filter (fun z => φ z = n), v (φ z)
  rw [hset]
  apply Finset.sum_image
  intro a ha b hb hab
  exact hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab

/-- Coefficient of a ledger already indexed by the arithmetic state itself. -/
theorem ledgerCoefficient_state (T : Finset ℕ) (v : ℕ → ℤ) (n : ℕ) :
    ledgerCoefficient T (fun m => m) v n = if n ∈ T then v n else 0 := by
  show (∑ m ∈ T.filter (fun m => m = n), v m) = if n ∈ T then v n else 0
  by_cases hn : n ∈ T
  · have hset : T.filter (fun m => m = n) = {n} := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro h
        exact h.2
      · intro h
        subst h
        exact ⟨hn, rfl⟩
    rw [hset, Finset.sum_singleton, if_pos hn]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hmT, hmn⟩
    subst hmn
    exact absurd hmT hn

/-- **Interface flux register.**  The signed coefficientwise difference of two
ledgers written on the same arithmetic carrier. -/
def interfaceFluxRegister {ι κ : Type*}
    (S : Finset ι) (φP : ι → ℕ) (wP : ι → ℤ)
    (T : Finset κ) (φL : κ → ℕ) (wL : κ → ℤ) (n : ℕ) : ℤ :=
  ledgerCoefficient S φP wP n - ledgerCoefficient T φL wL n

/-- The register's own total is exactly the difference of the two ledger
totals, so nothing is lost by carrying it instead of the totals. -/
theorem sum_interfaceFluxRegister_eq_totalDifference {ι κ : Type*}
    (S : Finset ι) (φP : ι → ℕ) (wP : ι → ℤ)
    (T : Finset κ) (φL : κ → ℕ) (wL : κ → ℤ) {N : Finset ℕ}
    (hP : ∀ z ∈ S, φP z ∈ N) (hL : ∀ z ∈ T, φL z ∈ N) :
    (∑ n ∈ N, interfaceFluxRegister S φP wP T φL wL n) =
      (∑ z ∈ S, wP z) - ∑ z ∈ T, wL z := by
  unfold interfaceFluxRegister
  rw [Finset.sum_sub_distrib, sum_ledgerCoefficient_eq_total S φP wP hP,
    sum_ledgerCoefficient_eq_total T φL wL hL]

/-- **Regrouping invariance.**  A register that vanishes at every arithmetic
state forces the two ledgers to agree on *every* finite selection of states.
This is the property an equality of totals does not have. -/
theorem restrictedMass_eq_of_interfaceFluxRegister_eq_zero {ι κ : Type*}
    {S : Finset ι} {φP : ι → ℕ} {wP : ι → ℤ}
    {T : Finset κ} {φL : κ → ℕ} {wL : κ → ℤ}
    (hzero : ∀ n, interfaceFluxRegister S φP wP T φL wL n = 0)
    (N : Finset ℕ) :
    (∑ z ∈ S.filter (fun z => φP z ∈ N), wP z) =
      ∑ z ∈ T.filter (fun z => φL z ∈ N), wL z := by
  rw [← sum_ledgerCoefficient_eq_restrictedMass S φP wP N,
    ← sum_ledgerCoefficient_eq_restrictedMass T φL wL N]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  have h := hzero n
  unfold interfaceFluxRegister at h
  omega

/-! ## The Go second-contact interface -/

/-- Integer form of the fresh-prime sign flip on a rough prefix. -/
theorem moebius_mul_prime_eq_neg_of_rough
    {c q : ℕ} (hc : 0 < c) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor c < q) :
    μ (c * q) = -μ c := by
  have h := canonicalMoebiusWeight_mul_prime_eq_neg_of_rough hc hq hrough
  unfold canonicalMoebiusWeight at h
  exact_mod_cast h

/-- Owner-tagged rough-prefix occurrences at cutoff `X`.  The pair `(q,c)`
records both the second-contact owner `q` and its rough prefix `c`; the tag is
kept until its contribution to each coefficient has been summed. -/
def goRoughPrefixOccurrences (Q : Finset ℕ) (X : ℕ) : Finset (ℕ × ℕ) :=
  Q.biUnion fun q =>
    (squareRootLowPrimeGoSmoothCofactors q (X / (q * q))).image fun c => (q, c)

theorem mem_goRoughPrefixOccurrences {Q : Finset ℕ} {X : ℕ} {z : ℕ × ℕ} :
    z ∈ goRoughPrefixOccurrences Q X ↔
      z.1 ∈ Q ∧
        z.2 ∈ squareRootLowPrimeGoSmoothCofactors z.1 (X / (z.1 * z.1)) := by
  constructor
  · intro hz
    unfold goRoughPrefixOccurrences at hz
    rcases Finset.mem_biUnion.mp hz with ⟨q, hqQ, hzq⟩
    rcases Finset.mem_image.mp hzq with ⟨c, hc, hzc⟩
    subst hzc
    exact ⟨hqQ, hc⟩
  · intro hz
    unfold goRoughPrefixOccurrences
    refine Finset.mem_biUnion.mpr ⟨z.1, hz.1, ?_⟩
    exact Finset.mem_image.mpr ⟨z.2, hz.2, rfl⟩

/-- The arithmetic state acted on by one owner-tagged occurrence. -/
def goRoughPrefixState (z : ℕ × ℕ) : ℕ := z.1 * z.2

/-- Every owner-tagged occurrence lands on an existing second-contact source. -/
theorem goRoughPrefixState_mem_sources
    {Q : Finset ℕ} {X : ℕ} (hprime : ∀ q ∈ Q, q.Prime)
    {z : ℕ × ℕ} (hz : z ∈ goRoughPrefixOccurrences Q X) :
    goRoughPrefixState z ∈ squareRootLowPrimeGoSecondContactSources Q X := by
  rcases mem_goRoughPrefixOccurrences.mp hz with ⟨hqQ, hc⟩
  have hq := hprime _ hqQ
  unfold squareRootLowPrimeGoSecondContactSources
  refine Finset.mem_biUnion.mpr ⟨z.1, hqQ, ?_⟩
  rw [squareRootLowPrimeGoWallSquareResidualChildren_eq_smoothCofactorImage hq]
  exact Finset.mem_image.mpr ⟨z.2, hc, rfl⟩

/-- The owner tag is recovered from the arithmetic state: no prime multiplicity
is carried externally. -/
theorem goRoughPrefixState_owner
    {Q : Finset ℕ} {X : ℕ} (hprime : ∀ q ∈ Q, q.Prime)
    {z : ℕ × ℕ} (hz : z ∈ goRoughPrefixOccurrences Q X) :
    canonicalLargestPrimeFactor (goRoughPrefixState z) = z.1 := by
  rcases mem_goRoughPrefixOccurrences.mp hz with ⟨hqQ, hc⟩
  have hq := hprime _ hqQ
  rcases mem_squareRootLowPrimeGoSmoothCofactors.mp hc with
    ⟨hc1, _hcB, _hcsq, hrough⟩
  have hcPos : 0 < z.2 := by omega
  have hcomm : z.1 * z.2 = z.2 * z.1 := Nat.mul_comm z.1 z.2
  unfold goRoughPrefixState
  rw [hcomm]
  exact canonicalLargestPrimeFactor_mul_prime_eq_of_rough hcPos hq hrough

/-- Distinct owner-tagged occurrences land on distinct arithmetic states. -/
theorem goRoughPrefixState_injOn
    {Q : Finset ℕ} {X : ℕ} (hprime : ∀ q ∈ Q, q.Prime) :
    Set.InjOn goRoughPrefixState
      (goRoughPrefixOccurrences Q X : Set (ℕ × ℕ)) := by
  intro y hy z hz heq
  have hyOwner := goRoughPrefixState_owner hprime hy
  have hzOwner := goRoughPrefixState_owner hprime hz
  have hq : y.1 = z.1 := by
    rw [← hyOwner, ← hzOwner, heq]
  have hyPrime := hprime _ (mem_goRoughPrefixOccurrences.mp hy).1
  have hstate : y.1 * y.2 = z.1 * z.2 := heq
  have hc : y.2 = z.2 := by
    have h2 : y.1 * y.2 = y.1 * z.2 := by rw [hstate, hq]
    exact Nat.eq_of_mul_eq_mul_left hyPrime.pos h2
  have hpair : (y.1, y.2) = (z.1, z.2) := by rw [hq, hc]
  exact hpair

/-- The owner-tagged occurrences cover exactly the existing arithmetic
second-contact source population. -/
theorem goRoughPrefixOccurrences_image_state
    {Q : Finset ℕ} {X : ℕ} (hprime : ∀ q ∈ Q, q.Prime) :
    (goRoughPrefixOccurrences Q X).image goRoughPrefixState =
      squareRootLowPrimeGoSecondContactSources Q X := by
  ext m
  constructor
  · intro hm
    rcases Finset.mem_image.mp hm with ⟨z, hz, hzm⟩
    rw [← hzm]
    exact goRoughPrefixState_mem_sources hprime hz
  · intro hm
    unfold squareRootLowPrimeGoSecondContactSources at hm
    rcases Finset.mem_biUnion.mp hm with ⟨q, hqQ, hmq⟩
    have hq := hprime q hqQ
    rw [squareRootLowPrimeGoWallSquareResidualChildren_eq_smoothCofactorImage
      hq] at hmq
    rcases Finset.mem_image.mp hmq with ⟨c, hc, hcm⟩
    refine Finset.mem_image.mpr ⟨(q, c), ?_, hcm⟩
    exact mem_goRoughPrefixOccurrences.mpr ⟨hqQ, hc⟩

/-- The rough-prefix weight is exactly the negated Möbius weight of the state it
acts on. -/
theorem goRoughPrefix_weight_eq_neg_stateMoebius
    {Q : Finset ℕ} {X : ℕ} (hprime : ∀ q ∈ Q, q.Prime)
    {z : ℕ × ℕ} (hz : z ∈ goRoughPrefixOccurrences Q X) :
    μ z.2 = -μ (goRoughPrefixState z) := by
  rcases mem_goRoughPrefixOccurrences.mp hz with ⟨hqQ, hc⟩
  have hq := hprime _ hqQ
  rcases mem_squareRootLowPrimeGoSmoothCofactors.mp hc with
    ⟨hc1, _hcB, _hcsq, hrough⟩
  have hcPos : 0 < z.2 := by omega
  have hflip : μ (z.2 * z.1) = -μ z.2 :=
    moebius_mul_prime_eq_neg_of_rough hcPos hq hrough
  have hcomm : z.1 * z.2 = z.2 * z.1 := Nat.mul_comm z.1 z.2
  unfold goRoughPrefixState
  rw [hcomm, hflip]
  ring

/-- **Coefficientwise identification of the two ledgers.**  At every arithmetic
state the owner-tagged rough-prefix ledger and the existing low-transport ledger
carry the same signed coefficient. -/
theorem goRoughPrefix_ledgerCoefficient_eq_sourceCoefficient
    {Q : Finset ℕ} {X : ℕ} (hprime : ∀ q ∈ Q, q.Prime) (n : ℕ) :
    ledgerCoefficient (goRoughPrefixOccurrences Q X) goRoughPrefixState
        (fun z => μ z.2) n =
      ledgerCoefficient (squareRootLowPrimeGoSecondContactSources Q X)
        (fun m => m) (fun m => -μ m) n := by
  have hstep :
      ledgerCoefficient (squareRootLowPrimeGoSecondContactSources Q X)
          (fun m => m) (fun m => -μ m) n =
        ledgerCoefficient (goRoughPrefixOccurrences Q X) goRoughPrefixState
          (fun z => -μ (goRoughPrefixState z)) n := by
    rw [← goRoughPrefixOccurrences_image_state hprime]
    exact ledgerCoefficient_image_of_injOn (goRoughPrefixOccurrences Q X)
      goRoughPrefixState (fun m => -μ m) (goRoughPrefixState_injOn hprime) n
  rw [hstep]
  unfold ledgerCoefficient
  refine Finset.sum_congr rfl ?_
  intro z hz
  exact goRoughPrefix_weight_eq_neg_stateMoebius hprime
    (Finset.mem_filter.mp hz).1

/-- **The interface flux register of the Go second-contact seam vanishes.**
Owner multiplicities and inherited roughness are preserved: the owner tag is
summed into the coefficient, and recovered from the state as `P⁺(m)`. -/
theorem goSecondContactInterfaceFluxRegister_eq_zero
    {Q : Finset ℕ} {X : ℕ} (hprime : ∀ q ∈ Q, q.Prime) (n : ℕ) :
    interfaceFluxRegister (goRoughPrefixOccurrences Q X) goRoughPrefixState
        (fun z => μ z.2)
        (squareRootLowPrimeGoSecondContactSources Q X) (fun m => m)
        (fun m => -μ m) n = 0 := by
  unfold interfaceFluxRegister
  rw [goRoughPrefix_ledgerCoefficient_eq_sourceCoefficient hprime n]
  ring

/-- Explicit value of the rough-prefix coefficient at each arithmetic state. -/
theorem goRoughPrefix_ledgerCoefficient_eq_ite
    {Q : Finset ℕ} {X : ℕ} (hprime : ∀ q ∈ Q, q.Prime) (n : ℕ) :
    ledgerCoefficient (goRoughPrefixOccurrences Q X) goRoughPrefixState
        (fun z => μ z.2) n =
      if n ∈ squareRootLowPrimeGoSecondContactSources Q X then -μ n else 0 := by
  rw [goRoughPrefix_ledgerCoefficient_eq_sourceCoefficient hprime n]
  exact ledgerCoefficient_state _ _ n

/-- **Regrouping-invariant cancellation on the Go seam.**  The two ledgers agree
on every finite selection of arithmetic states, not merely in total. -/
theorem goSecondContact_restrictedMass_eq
    {Q : Finset ℕ} {X : ℕ} (hprime : ∀ q ∈ Q, q.Prime) (N : Finset ℕ) :
    (∑ z ∈ (goRoughPrefixOccurrences Q X).filter
        (fun z => goRoughPrefixState z ∈ N), μ z.2) =
      ∑ m ∈ (squareRootLowPrimeGoSecondContactSources Q X).filter
        (fun m => m ∈ N), -μ m :=
  restrictedMass_eq_of_interfaceFluxRegister_eq_zero
    (goSecondContactInterfaceFluxRegister_eq_zero hprime) N

/-! ## The rough-prefix unit and its root-scale anchor -/

/-- Owners whose rough-prefix unit `c=1` is actually represented at cutoff `X`. -/
def goRoughPrefixUnitAnchor (Q : Finset ℕ) (X : ℕ) : Finset ℕ :=
  Q.filter fun q => q * q ≤ X

theorem mem_goRoughPrefixUnitAnchor {Q : Finset ℕ} {X q : ℕ} :
    q ∈ goRoughPrefixUnitAnchor Q X ↔ q ∈ Q ∧ q * q ≤ X := by
  unfold goRoughPrefixUnitAnchor
  exact Finset.mem_filter

/-- The rough-prefix unit is represented at owner `q` exactly when `q² ≤ X`. -/
theorem one_mem_squareRootLowPrimeGoSmoothCofactors_iff
    {q X : ℕ} (hq : q.Prime) :
    (1 ∈ squareRootLowPrimeGoSmoothCofactors q (X / (q * q))) ↔ q * q ≤ X := by
  have hqq : 0 < q * q := Nat.mul_pos hq.pos hq.pos
  constructor
  · intro h
    have hB := (mem_squareRootLowPrimeGoSmoothCofactors.mp h).2.1
    have hmul := (Nat.le_div_iff_mul_le hqq).1 hB
    simpa using hmul
  · intro h
    refine mem_squareRootLowPrimeGoSmoothCofactors.mpr
      ⟨le_refl 1, ?_, squarefree_one, ?_⟩
    · refine (Nat.le_div_iff_mul_le hqq).2 ?_
      simpa using h
    · simp [canonicalLargestPrimeFactor, hq.one_lt]

/-- Strict rough prefixes at one owner: the honest second contacts, with the
unit removed. -/
def goStrictRoughPrefixes (q X : ℕ) : Finset ℕ :=
  (squareRootLowPrimeGoSmoothCofactors q (X / (q * q))).filter fun c => 1 < c

theorem mem_goStrictRoughPrefixes {q X c : ℕ} :
    c ∈ goStrictRoughPrefixes q X ↔
      c ∈ squareRootLowPrimeGoSmoothCofactors q (X / (q * q)) ∧ 1 < c := by
  unfold goStrictRoughPrefixes
  exact Finset.mem_filter

/-- **Unit/endpoint split of one Go square residual.**  The rough-prefix unit is
not a second contact; it contributes its own anchor term. -/
theorem squareRootLowPrimeGoWallSquareResidual_eq_unitAnchor_add_strict
    {q X : ℕ} (hq : q.Prime) :
    squareRootLowPrimeGoWallSquareResidual q X =
      (if q * q ≤ X then (1 : ℤ) else 0) +
        ∑ c ∈ goStrictRoughPrefixes q X, μ c := by
  have hsplit :
      (∑ c ∈ (squareRootLowPrimeGoSmoothCofactors q (X / (q * q))).filter
          (fun c => 1 < c), μ c) +
        (∑ c ∈ (squareRootLowPrimeGoSmoothCofactors q (X / (q * q))).filter
          (fun c => ¬ 1 < c), μ c) =
        ∑ c ∈ squareRootLowPrimeGoSmoothCofactors q (X / (q * q)), μ c :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hunit :
      (∑ c ∈ (squareRootLowPrimeGoSmoothCofactors q (X / (q * q))).filter
          (fun c => ¬ 1 < c), μ c) = if q * q ≤ X then (1 : ℤ) else 0 := by
    have hfilterEq :
        (squareRootLowPrimeGoSmoothCofactors q (X / (q * q))).filter
            (fun c => ¬ 1 < c) =
          (squareRootLowPrimeGoSmoothCofactors q (X / (q * q))).filter
            (fun c => c = 1) := by
      ext c
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hcS, hc⟩
        have hc1 := (mem_squareRootLowPrimeGoSmoothCofactors.mp hcS).1
        exact ⟨hcS, by omega⟩
      · rintro ⟨hcS, hc⟩
        exact ⟨hcS, by omega⟩
    rw [hfilterEq]
    by_cases h : q * q ≤ X
    · have h1S : (1 : ℕ) ∈ squareRootLowPrimeGoSmoothCofactors q (X / (q * q)) :=
        (one_mem_squareRootLowPrimeGoSmoothCofactors_iff hq).2 h
      have hset :
          (squareRootLowPrimeGoSmoothCofactors q (X / (q * q))).filter
              (fun c => c = 1) = {1} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · intro hc
          exact hc.2
        · intro hc
          subst hc
          exact ⟨h1S, rfl⟩
      rw [hset, Finset.sum_singleton, if_pos h]
      simp
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro c hc
      rcases Finset.mem_filter.mp hc with ⟨hcS, hc1⟩
      subst hc1
      exact absurd ((one_mem_squareRootLowPrimeGoSmoothCofactors_iff hq).1 hcS) h
  rw [squareRootLowPrimeGoWallSquareResidual_eq_smoothCofactorSum hq, ← hsplit,
    hunit]
  unfold goStrictRoughPrefixes
  ring

/-- **Global unit/endpoint split.**  Over any finite prime owner schedule the
rough-prefix units contribute exactly the anchor count. -/
theorem squareRootLowPrimeGoWallSquareResidualTotal_eq_unitAnchor_add_strict
    {Q : Finset ℕ} {X : ℕ} (hprime : ∀ q ∈ Q, q.Prime) :
    squareRootLowPrimeGoWallSquareResidualTotal Q X =
      ((goRoughPrefixUnitAnchor Q X).card : ℤ) +
        ∑ q ∈ Q, ∑ c ∈ goStrictRoughPrefixes q X, μ c := by
  have hpoint : ∀ q ∈ Q,
      squareRootLowPrimeGoWallSquareResidual q X =
        (if q * q ≤ X then (1 : ℤ) else 0) +
          ∑ c ∈ goStrictRoughPrefixes q X, μ c := by
    intro q hq
    exact squareRootLowPrimeGoWallSquareResidual_eq_unitAnchor_add_strict
      (hprime q hq)
  have hanchorSum :
      (∑ q ∈ Q, (if q * q ≤ X then (1 : ℤ) else 0)) =
        ((goRoughPrefixUnitAnchor Q X).card : ℤ) := by
    unfold goRoughPrefixUnitAnchor
    first
      | rw [Finset.sum_boole]
      | (rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero]; simp)
      | simp [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero]
  unfold squareRootLowPrimeGoWallSquareResidualTotal
  rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib, hanchorSum]

/-- The rough-prefix unit anchor is a genuine root-scale boundary term. -/
theorem goRoughPrefixUnitAnchor_card_le_sqrt
    {Q : Finset ℕ} {X : ℕ} (hprime : ∀ q ∈ Q, q.Prime) :
    (goRoughPrefixUnitAnchor Q X).card ≤ Nat.sqrt X := by
  have hsub : goRoughPrefixUnitAnchor Q X ⊆ Finset.Icc 1 (Nat.sqrt X) := by
    intro q hq
    rcases mem_goRoughPrefixUnitAnchor.mp hq with ⟨hqQ, hqX⟩
    have hqPrime := hprime q hqQ
    exact Finset.mem_Icc.mpr ⟨hqPrime.one_lt.le, Nat.le_sqrt.mpr hqX⟩
  calc
    (goRoughPrefixUnitAnchor Q X).card ≤ (Finset.Icc 1 (Nat.sqrt X)).card :=
      Finset.card_le_card hsub
    _ = Nat.sqrt X := by simp

/-! ## The anchor-free cascade lives at third scale -/

/-- Strict second-contact children at one owner. -/
def goStrictSecondContactChildren (q X : ℕ) : Finset ℕ :=
  (goStrictRoughPrefixes q X).image fun c => q * c

/-- Global strict second-contact source population. -/
def goStrictSecondContactSources (Q : Finset ℕ) (X : ℕ) : Finset ℕ :=
  Q.biUnion fun q => goStrictSecondContactChildren q X

theorem goStrictSecondContactChildren_subset
    {q X : ℕ} (hq : q.Prime) :
    goStrictSecondContactChildren q X ⊆
      squareRootLowPrimeGoWallSquareResidualChildren q X := by
  rw [squareRootLowPrimeGoWallSquareResidualChildren_eq_smoothCofactorImage hq]
  unfold goStrictSecondContactChildren goStrictRoughPrefixes
  exact Finset.image_subset_image (Finset.filter_subset _ _)

theorem goStrictSecondContactChildren_pairwiseDisjoint
    (Q : Finset ℕ) (X : ℕ) (hprime : ∀ q ∈ Q, q.Prime) :
    Set.PairwiseDisjoint (↑Q)
      (fun q => goStrictSecondContactChildren q X) := by
  intro q hq r hr hqr
  have hfull := squareRootLowPrimeGoWallSquareResidualChildren_disjoint
    (hprime q hq) (hprime r hr) hqr
  exact Finset.disjoint_of_subset_left
    (goStrictSecondContactChildren_subset (hprime q hq))
    (Finset.disjoint_of_subset_right
      (goStrictSecondContactChildren_subset (hprime r hr)) hfull)

/-- One-owner strict signed recombination. -/
theorem goStrictRoughPrefixSum_eq_neg_strictChildMass
    {q X : ℕ} (hq : q.Prime) :
    (∑ c ∈ goStrictRoughPrefixes q X, μ c) =
      -∑ m ∈ goStrictSecondContactChildren q X, μ m := by
  have himage :
      (∑ m ∈ goStrictSecondContactChildren q X, μ m) =
        ∑ c ∈ goStrictRoughPrefixes q X, μ (q * c) := by
    unfold goStrictSecondContactChildren
    apply Finset.sum_image
    intro a _ha b _hb hab
    exact Nat.eq_of_mul_eq_mul_left hq.pos hab
  rw [himage, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro c hc
  rcases mem_goStrictRoughPrefixes.mp hc with ⟨hcCof, hc1⟩
  have hrough := (mem_squareRootLowPrimeGoSmoothCofactors.mp hcCof).2.2.2
  have hcPos : 0 < c := by omega
  have hflip : μ (c * q) = -μ c :=
    moebius_mul_prime_eq_neg_of_rough hcPos hq hrough
  have hcomm : q * c = c * q := Nat.mul_comm q c
  rw [hcomm, hflip]
  ring

/-- **Anchor-free global recombination.**  The Go square-residual total is the
root-scale unit anchor minus the signed mass of the strict second contacts. -/
theorem squareRootLowPrimeGoWallSquareResidualTotal_eq_anchor_sub_strictMass
    {Q : Finset ℕ} {X : ℕ} (hprime : ∀ q ∈ Q, q.Prime) :
    squareRootLowPrimeGoWallSquareResidualTotal Q X =
      ((goRoughPrefixUnitAnchor Q X).card : ℤ) -
        ∑ m ∈ goStrictSecondContactSources Q X, μ m := by
  have hunion :
      (∑ m ∈ goStrictSecondContactSources Q X, μ m) =
        ∑ q ∈ Q, ∑ m ∈ goStrictSecondContactChildren q X, μ m := by
    unfold goStrictSecondContactSources
    exact Finset.sum_biUnion
      (goStrictSecondContactChildren_pairwiseDisjoint Q X hprime)
  have hstrict :
      (∑ q ∈ Q, ∑ c ∈ goStrictRoughPrefixes q X, μ c) =
        -∑ m ∈ goStrictSecondContactSources Q X, μ m := by
    calc
      (∑ q ∈ Q, ∑ c ∈ goStrictRoughPrefixes q X, μ c) =
          ∑ q ∈ Q, -∑ m ∈ goStrictSecondContactChildren q X, μ m := by
        refine Finset.sum_congr rfl ?_
        intro q hqQ
        exact goStrictRoughPrefixSum_eq_neg_strictChildMass (hprime q hqQ)
      _ = -∑ q ∈ Q, ∑ m ∈ goStrictSecondContactChildren q X, μ m := by
        rw [Finset.sum_neg_distrib]
      _ = -∑ m ∈ goStrictSecondContactSources Q X, μ m := by
        rw [hunion]
  rw [squareRootLowPrimeGoWallSquareResidualTotal_eq_unitAnchor_add_strict hprime,
    hstrict]
  ring

/-- **Strict second contacts force `q ≥ 3`.**  The only prefix rough below `2`
is the unit itself, so the anchor-free cascade never has owner `2`. -/
theorem goStrictSecondContactSources_subset_thirdScale
    {Q : Finset ℕ} {X : ℕ} (hprime : ∀ q ∈ Q, q.Prime) :
    goStrictSecondContactSources Q X ⊆ Finset.Icc 1 (X / 3) := by
  intro m hm
  unfold goStrictSecondContactSources at hm
  rcases Finset.mem_biUnion.mp hm with ⟨q, hqQ, hmq⟩
  have hqPrime := hprime q hqQ
  have hmFull : m ∈ squareRootLowPrimeGoWallSquareResidualChildren q X :=
    goStrictSecondContactChildren_subset hqPrime hmq
  have hcontact :=
    squareRootLowPrimeGoWallSquareResidualChild_owner_mul_le hqPrime hmFull
  have hmq' : m ∈ (goStrictRoughPrefixes q X).image (fun c => q * c) := hmq
  rcases Finset.mem_image.mp hmq' with ⟨c, hc, hcm⟩
  rcases mem_goStrictRoughPrefixes.mp hc with ⟨hcCof, hc1⟩
  have hrough := (mem_squareRootLowPrimeGoSmoothCofactors.mp hcCof).2.2.2
  have hcPrime : (canonicalLargestPrimeFactor c).Prime :=
    canonicalLargestPrimeFactor_prime hc1
  have hcTwo := hcPrime.two_le
  have hq2 : 2 < q := lt_of_le_of_lt hcTwo hrough
  have hq3 : 3 ≤ q := by omega
  have hmPos : 0 < m := by
    rw [← hcm]
    exact Nat.mul_pos hqPrime.pos (by omega)
  have h3m : 3 * m ≤ X := le_trans (Nat.mul_le_mul_right m hq3) hcontact
  have hthird : m ≤ X / 3 := by
    refine (Nat.le_div_iff_mul_le (by norm_num : 0 < (3 : ℕ))).2 ?_
    omega
  exact Finset.mem_Icc.mpr ⟨hmPos, hthird⟩

theorem goStrictSecondContactSources_card_le_thirdScale
    {Q : Finset ℕ} {X : ℕ} (hprime : ∀ q ∈ Q, q.Prime) :
    (goStrictSecondContactSources Q X).card ≤ X / 3 := by
  calc
    (goStrictSecondContactSources Q X).card ≤ (Finset.Icc 1 (X / 3)).card :=
      Finset.card_le_card (goStrictSecondContactSources_subset_thirdScale hprime)
    _ = X / 3 := by simp

/-- **Anchor-separated flux bound.**  Splitting the rough-prefix unit off before
counting replaces the `X/2` support bound by a root-scale anchor plus a third
scale cascade.  This is an exact split and an elementary support count: it is
smaller than `X/2` once `X > 36`, but it remains linear in `X`. -/
theorem abs_squareRootLowPrimeGoWallSquareResidualTotal_le_anchor_add_thirdScale
    {Q : Finset ℕ} {X : ℕ} (hprime : ∀ q ∈ Q, q.Prime) :
    |squareRootLowPrimeGoWallSquareResidualTotal Q X| ≤
      (Nat.sqrt X : ℤ) + ((X / 3 : ℕ) : ℤ) := by
  have hanchor : ((goRoughPrefixUnitAnchor Q X).card : ℤ) ≤ (Nat.sqrt X : ℤ) := by
    exact_mod_cast goRoughPrefixUnitAnchor_card_le_sqrt hprime
  have hanchor0 : (0 : ℤ) ≤ ((goRoughPrefixUnitAnchor Q X).card : ℤ) := by
    exact_mod_cast Nat.zero_le (goRoughPrefixUnitAnchor Q X).card
  have hsqrt0 : (0 : ℤ) ≤ (Nat.sqrt X : ℤ) := by
    exact_mod_cast Nat.zero_le (Nat.sqrt X)
  have hmass : |∑ m ∈ goStrictSecondContactSources Q X, μ m| ≤ ((X / 3 : ℕ) : ℤ) := by
    calc
      |∑ m ∈ goStrictSecondContactSources Q X, μ m| ≤
          ((goStrictSecondContactSources Q X).card : ℤ) :=
        abs_moebiusSum_le_card (goStrictSecondContactSources Q X)
      _ ≤ ((X / 3 : ℕ) : ℤ) := by
        exact_mod_cast goStrictSecondContactSources_card_le_thirdScale hprime
  rcases abs_le.mp hmass with ⟨hlow, hhigh⟩
  rw [squareRootLowPrimeGoWallSquareResidualTotal_eq_anchor_sub_strictMass hprime]
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith
  · linarith

end RHLean.Proof

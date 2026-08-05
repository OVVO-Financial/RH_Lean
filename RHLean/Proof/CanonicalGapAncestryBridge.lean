import Mathlib
import RHLean.Proof.CanonicalGapAncestryFlow
import RHLean.Proof.CanonicalGapPrefixGram

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

namespace CanonicalGapAncestryBridge

open CanonicalGapAncestryFlow
open CanonicalGapAncestryFlow.ParentFlow
open CanonicalGapPrefixGram

/-!
# Concrete realization and termination of the canonical ancestry flow

For a fixed distinguished prime `q`, a canonical core is a positive squarefree
integer `c`, coprime to `q`, all of whose prime divisors are strictly below `q`.
The source represented by the core is `q*c`.

A core with `c ≤ q` is transport-oriented and is a root.  A core with `q < c`
is smooth-oriented.  Its parent is obtained by stripping the largest prime divisor
of `c`.  This module proves, without assumptions or axioms, that:

* every smooth-oriented core has exactly one such largest-prime parent;
* the parent is again an admissible core and has strictly smaller rank;
* the Möbius weight reverses sign along the parent edge;
* on a bounded core universe the successor operator is nilpotent;
* the renewal equation therefore has a genuinely finite alternating expansion;
* the expansion survives the integer-square-root clock pushforward;
* the resulting square-block increment sequence telescopes exactly to that
  pushed-forward canonical source field.

No analytic prefix-energy estimate is asserted here.
-/

/-- Arithmetic admissibility of a core below the distinguished prime `q`. -/
def CoreAdmissible (q c : ℕ) : Prop :=
  1 ≤ c ∧ Squarefree c ∧ Nat.Coprime q c ∧
    ∀ p : ℕ, p.Prime → p ∣ c → p < q

/-- A bounded finite universe of admissible canonical cores. -/
def CoreIndex (q B : ℕ) :=
  {c : Fin (B + 1) // CoreAdmissible q c.1}

noncomputable instance coreIndexFintype (q B : ℕ) : Fintype (CoreIndex q B) :=
  Fintype.ofFinite _

/-- The natural-number core represented by an index. -/
def coreValue {q B : ℕ} (s : CoreIndex q B) : ℕ := s.1.1

@[simp] theorem coreValue_lt_succ {q B : ℕ} (s : CoreIndex q B) :
    coreValue s < B + 1 := s.1.2

@[simp] theorem coreValue_pos {q B : ℕ} (s : CoreIndex q B) :
    1 ≤ coreValue s := s.2.1

/-- The largest prime divisor of `c`, with value `1` in the irrelevant range
`c ≤ 1`. -/
noncomputable def largestPrimeFactor (c : ℕ) : ℕ :=
  if h : 1 < c then
    c.primeFactors.max' ((Nat.nonempty_primeFactors).2 h)
  else 1

/-- The largest prime factor belongs to the prime-factor finset. -/
theorem largestPrimeFactor_mem {c : ℕ} (hc : 1 < c) :
    largestPrimeFactor c ∈ c.primeFactors := by
  rw [largestPrimeFactor, dif_pos hc]
  exact Finset.max'_mem c.primeFactors ((Nat.nonempty_primeFactors).2 hc)

/-- The largest prime factor is prime. -/
theorem largestPrimeFactor_prime {c : ℕ} (hc : 1 < c) :
    (largestPrimeFactor c).Prime :=
  Nat.prime_of_mem_primeFactors (largestPrimeFactor_mem hc)

/-- The largest prime factor divides the number. -/
theorem largestPrimeFactor_dvd {c : ℕ} (hc : 1 < c) :
    largestPrimeFactor c ∣ c :=
  Nat.dvd_of_mem_primeFactors (largestPrimeFactor_mem hc)

/-- Every prime divisor is bounded by the selected largest prime factor. -/
theorem prime_dvd_le_largestPrimeFactor {c r : ℕ} (hc : 1 < c)
    (hr : r.Prime) (hrc : r ∣ c) : r ≤ largestPrimeFactor c := by
  have hc0 : c ≠ 0 := by omega
  have hrmem : r ∈ c.primeFactors :=
    (Nat.mem_primeFactors_of_ne_zero hc0).2 ⟨hr, hrc⟩
  rw [largestPrimeFactor, dif_pos hc]
  exact Finset.le_max' c.primeFactors r hrmem

/-- Core obtained by stripping the largest prime factor. -/
def strippedCore (c : ℕ) : ℕ := c / largestPrimeFactor c

/-- Exact factor reconstruction after stripping. -/
theorem strippedCore_mul_largestPrimeFactor {c : ℕ} (hc : 1 < c) :
    strippedCore c * largestPrimeFactor c = c := by
  exact Nat.div_mul_cancel (largestPrimeFactor_dvd hc)

/-- The stripped core is positive. -/
theorem strippedCore_pos {c : ℕ} (hc : 1 < c) : 1 ≤ strippedCore c := by
  have hp := (largestPrimeFactor_prime hc).two_le
  have hfac := strippedCore_mul_largestPrimeFactor hc
  by_contra h
  have ha : strippedCore c = 0 := by omega
  rw [ha, zero_mul] at hfac
  omega

/-- Stripping strictly decreases the core. -/
theorem strippedCore_lt {c : ℕ} (hc : 1 < c) : strippedCore c < c := by
  have ha := strippedCore_pos hc
  have hp := (largestPrimeFactor_prime hc).two_le
  have hfac := strippedCore_mul_largestPrimeFactor hc
  nlinarith

/-- The stripped core divides the original core. -/
theorem strippedCore_dvd {c : ℕ} (hc : 1 < c) : strippedCore c ∣ c := by
  exact ⟨largestPrimeFactor c, (strippedCore_mul_largestPrimeFactor hc).symm⟩

/-- Squarefreeness makes the stripped core coprime to the removed prime. -/
theorem largestPrimeFactor_coprime_strippedCore {c : ℕ}
    (hc : 1 < c) (hsq : Squarefree c) :
    Nat.Coprime (largestPrimeFactor c) (strippedCore c) := by
  have hsqprod : Squarefree (strippedCore c * largestPrimeFactor c) := by
    simpa [strippedCore_mul_largestPrimeFactor hc] using hsq
  exact (Nat.coprime_of_squarefree_mul hsqprod).symm

/-- The stripped factorization has the removed prime as its unique maximal prime. -/
theorem largestPrimeFactor_coreMaxPrime {c : ℕ}
    (hc : 1 < c) (hsq : Squarefree c) :
    CoreMaxPrime (largestPrimeFactor c) (strippedCore c) := by
  refine ⟨largestPrimeFactor_prime hc,
    largestPrimeFactor_coprime_strippedCore hc hsq, ?_⟩
  intro r hr hra
  have hrdivc : r ∣ c := hra.trans (strippedCore_dvd hc)
  have hrle := prime_dvd_le_largestPrimeFactor hc hr hrdivc
  have hrne : r ≠ largestPrimeFactor c := by
    intro heq
    subst r
    exact (largestPrimeFactor_coprime_strippedCore hc hsq).not_dvd_of_dvd_right hra
  omega

/-- Stripping preserves canonical core admissibility. -/
theorem strippedCore_admissible {q c : ℕ}
    (hcgt : 1 < c) (hc : CoreAdmissible q c) :
    CoreAdmissible q (strippedCore c) := by
  rcases hc with ⟨hcpos, hsq, hcop, hdom⟩
  have hadvd : strippedCore c ∣ c := strippedCore_dvd hcgt
  refine ⟨strippedCore_pos hcgt,
    Squarefree.squarefree_of_dvd hadvd hsq,
    hcop.coprime_dvd_right hadvd, ?_⟩
  intro r hr hra
  exact hdom r hr (hra.trans hadvd)

/-- The concrete stripped parent inside the same bounded universe. -/
noncomputable def strippedIndex {q B : ℕ} (s : CoreIndex q B)
    (hsmooth : q < coreValue s) : CoreIndex q B := by
  have hq1 : 1 < q := by
    have hp : ∃ p : ℕ, p.Prime ∧ p ∣ coreValue s :=
      Nat.exists_prime_and_dvd (by omega : coreValue s ≠ 1)
    rcases hp with ⟨p, hp, _⟩
    have := s.2.2.2.2 p hp (by assumption)
    omega
  have hcgt : 1 < coreValue s := lt_trans hq1 hsmooth
  exact ⟨⟨strippedCore (coreValue s),
      lt_trans (strippedCore_lt hcgt) (coreValue_lt_succ s)⟩,
    strippedCore_admissible hcgt s.2⟩

/-- Concrete parent map: transport-oriented cores are roots; smooth-oriented
cores strip their largest prime factor. -/
noncomputable def coreParent {q B : ℕ} (s : CoreIndex q B) :
    Option (CoreIndex q B) :=
  if h : q < coreValue s then some (strippedIndex s h) else none

/-- Smooth orientation is exactly the existence of a parent. -/
theorem coreParent_isSome_iff {q B : ℕ} (s : CoreIndex q B) :
    (coreParent s).isSome ↔ q < coreValue s := by
  by_cases h : q < coreValue s <;> simp [coreParent, h]

/-- Transport orientation is exactly roothood. -/
theorem coreParent_eq_none_iff {q B : ℕ} (s : CoreIndex q B) :
    coreParent s = none ↔ coreValue s ≤ q := by
  by_cases h : q < coreValue s
  · simp [coreParent, h]
  · have hle : coreValue s ≤ q := by omega
    simp [coreParent, h, hle]

/-- Every smooth-oriented source has a concrete parent. -/
theorem smoothSource_has_parent {q B : ℕ} (s : CoreIndex q B)
    (hsmooth : q < coreValue s) :
    coreParent s = some (strippedIndex s hsmooth) := by
  simp [coreParent, hsmooth]

/-- Every smooth-oriented source has exactly one parent index. -/
theorem smoothSource_parent_unique {q B : ℕ} (s : CoreIndex q B)
    (hsmooth : q < coreValue s) :
    ∃! t : CoreIndex q B, coreParent s = some t := by
  refine ⟨strippedIndex s hsmooth, smoothSource_has_parent s hsmooth, ?_⟩
  intro t ht
  rw [smoothSource_has_parent s hsmooth] at ht
  exact Option.some.inj ht.symm

/-- Arithmetic witness for a canonical largest-prime parent. -/
def IsLargestPrimeParent (q c a p : ℕ) : Prop :=
  c = a * p ∧ CoreMaxPrime p a ∧ p < q ∧ Nat.Coprime p (q * a)

/-- The selected largest-prime factor is below `q` and coprime to the full parent. -/
theorem stripped_isLargestPrimeParent {q c : ℕ} (hq : q.Prime)
    (hsmooth : q < c) (hc : CoreAdmissible q c) :
    IsLargestPrimeParent q c (strippedCore c) (largestPrimeFactor c) := by
  have hcgt : 1 < c := lt_trans hq.one_lt hsmooth
  have hpprime := largestPrimeFactor_prime hcgt
  have hpdvd := largestPrimeFactor_dvd hcgt
  have hpltq := hc.2.2.2.2 _ hpprime hpdvd
  have hpq : Nat.Coprime (largestPrimeFactor c) q :=
    (Nat.coprime_of_lt_prime hpprime.ne_zero hpltq hq).symm
  have hpa := largestPrimeFactor_coprime_strippedCore hcgt hc.2.1
  refine ⟨(strippedCore_mul_largestPrimeFactor hcgt).symm,
    largestPrimeFactor_coreMaxPrime hcgt hc.2.1, hpltq, ?_⟩
  exact (Nat.coprime_mul_iff_right).2 ⟨hpq, hpa⟩

/-- The arithmetic largest-prime parent witness is unique. -/
theorem largestPrimeParent_unique {q c a a' p p' : ℕ}
    (h : IsLargestPrimeParent q c a p)
    (h' : IsLargestPrimeParent q c a' p') : a = a' ∧ p = p' := by
  have hp : p = p' :=
    coreMaxPrime_unique_factor h.2.1 h'.2.1 (h.1.symm.trans h'.1)
  have ha_mul : a * p = a' * p := by
    calc
      a * p = c := h.1.symm
      _ = a' * p' := h'.1
      _ = a' * p := by rw [hp]
  have ha : a = a' := Nat.mul_right_cancel h.2.1.prime.pos ha_mul
  exact ⟨ha, hp⟩

/-- Every actual smooth-oriented canonical core admits a unique arithmetic
largest-prime parent witness. -/
theorem smoothSource_exists_unique_largestPrimeParent {q c : ℕ}
    (hq : q.Prime) (hsmooth : q < c) (hc : CoreAdmissible q c) :
    ∃! ap : ℕ × ℕ, IsLargestPrimeParent q c ap.1 ap.2 := by
  refine ⟨(strippedCore c, largestPrimeFactor c),
    stripped_isLargestPrimeParent hq hsmooth hc, ?_⟩
  rintro ⟨a, p⟩ hap
  exact Prod.ext (largestPrimeParent_unique
    (stripped_isLargestPrimeParent hq hsmooth hc) hap).1
    (largestPrimeParent_unique
      (stripped_isLargestPrimeParent hq hsmooth hc) hap).2

/-- Möbius weight of a bounded canonical source. -/
def coreWeight (q : ℕ) {B : ℕ} (s : CoreIndex q B) : ℤ :=
  (μ (q * coreValue s) : ℤ)

/-- Exact sign reversal under the concrete largest-prime parent map. -/
theorem coreWeight_stripped_eq_neg {q B : ℕ} (hq : q.Prime)
    (s : CoreIndex q B) (hsmooth : q < coreValue s) :
    coreWeight q s = -coreWeight q (strippedIndex s hsmooth) := by
  have hcgt : 1 < coreValue s := lt_trans hq.one_lt hsmooth
  have hparent := stripped_isLargestPrimeParent hq hsmooth s.2
  have hfactor := hparent.1
  have hcop := hparent.2.2.2
  unfold coreWeight coreValue
  change (μ (q * coreValue s) : ℤ) =
    -(μ (q * strippedCore (coreValue s)) : ℤ)
  calc
    (μ (q * coreValue s) : ℤ) =
        μ ((q * strippedCore (coreValue s)) * largestPrimeFactor (coreValue s)) := by
      congr 1
      rw [hfactor]
      ring
    _ = (μ (q * strippedCore (coreValue s)) : ℤ) *
          μ (largestPrimeFactor (coreValue s)) :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop.symm
    _ = -(μ (q * strippedCore (coreValue s)) : ℤ) := by
      rw [ArithmeticFunction.moebius_apply_prime
        (largestPrimeFactor_prime hcgt)]
      ring

/-- Pointwise sign reversal for the concrete parent map. -/
theorem coreWeight_signReversal {q B : ℕ} (hq : q.Prime)
    (s t : CoreIndex q B) (hparent : coreParent s = some t) :
    coreWeight q s = -coreWeight q t := by
  by_cases hsmooth : q < coreValue s
  · have ht : t = strippedIndex s hsmooth := by
      simpa [coreParent, hsmooth] using hparent
    subst t
    exact coreWeight_stripped_eq_neg hq s hsmooth
  · simp [coreParent, hsmooth] at hparent

/-- The concrete finite parent flow on all bounded admissible cores. -/
noncomputable def boundedCoreFlow {q B : ℕ} (hq : q.Prime) :
    ParentFlow (CoreIndex q B) where
  parent := coreParent
  weight := coreWeight q
  signReversal := coreWeight_signReversal hq

/-! ## Ranked termination -/

/-- A finite parent flow equipped with a strict parent rank and a global height. -/
structure RankedParentFlow (ι : Type*) [Fintype ι] where
  flow : ParentFlow ι
  rank : ι → ℕ
  height : ℕ
  rank_lt_height : ∀ i, rank i < height
  parent_rank_lt : ∀ i p, flow.parent i = some p → rank p < rank i

namespace RankedParentFlow

/-- The signed alternating tail vanishes pointwise once its depth exceeds the
rank of the node. -/
theorem alternatingTail_apply_eq_zero_of_rank_lt
    {ι : Type*} [Fintype ι] (F : RankedParentFlow ι)
    (f : ι → ℤ) {depth : ℕ} :
    ∀ i, F.rank i < depth →
      alternatingTail F.flow.successorOperator f depth i = 0 := by
  induction depth with
  | zero =>
      intro i hi
      omega
  | succ d ih =>
      intro i hi
      simp only [alternatingTail]
      cases hparent : F.flow.parent i with
      | none => simp [ParentFlow.successorOperator, hparent]
      | some p =>
          have hrank := F.parent_rank_lt i p hparent
          have hpdepth : F.rank p < d := by omega
          have hzero := ih p hpdepth
          simp [ParentFlow.successorOperator, hparent, hzero]

/-- The full alternating tail is zero at the declared finite height. -/
theorem alternatingTail_eq_zero
    {ι : Type*} [Fintype ι] (F : RankedParentFlow ι) (f : ι → ℤ) :
    alternatingTail F.flow.successorOperator f F.height = 0 := by
  funext i
  exact alternatingTail_apply_eq_zero_of_rank_lt F f i
    (F.rank_lt_height i)

/-- A ranked finite flow has an exact tail-free alternating renewal expansion. -/
theorem finite_alternating_expansion
    {ι : Type*} [Fintype ι] (F : RankedParentFlow ι) :
    F.flow.weight =
      alternatingPrefix F.flow.successorOperator F.flow.rootField F.height := by
  exact finite_renewal_identity
    (F.flow.weight_eq_root_sub_successor)
    (alternatingTail_eq_zero F F.flow.weight)

end RankedParentFlow

/-- The concrete core flow is ranked by the core itself and terminates before
`B+1` generations. -/
noncomputable def boundedCoreRankedFlow {q B : ℕ} (hq : q.Prime) :
    RankedParentFlow (CoreIndex q B) where
  flow := boundedCoreFlow hq
  rank := coreValue
  height := B + 1
  rank_lt_height := coreValue_lt_succ
  parent_rank_lt := by
    intro s t hparent
    by_cases hsmooth : q < coreValue s
    · have ht : t = strippedIndex s hsmooth := by
        simpa [boundedCoreFlow, coreParent, hsmooth] using hparent
      subst t
      exact strippedCore_lt (lt_trans hq.one_lt hsmooth)
    · simp [boundedCoreFlow, coreParent, hsmooth] at hparent

/-- Explicit transport-oriented root field. -/
theorem boundedCore_rootField_apply {q B : ℕ} (hq : q.Prime)
    (s : CoreIndex q B) :
    (boundedCoreFlow hq).rootField s =
      if coreValue s ≤ q then coreWeight q s else 0 := by
  by_cases hroot : coreValue s ≤ q
  · have hpnone : coreParent s = none :=
      (coreParent_eq_none_iff s).2 hroot
    simp [ParentFlow.rootField, boundedCoreFlow, hpnone, hroot]
  · have hsmooth : q < coreValue s := by omega
    have hpsome := smoothSource_has_parent s hsmooth
    simp [ParentFlow.rootField, boundedCoreFlow, hpsome, hroot]

/-- Exact finite alternating expansion of the full bounded canonical source field
from the transport-oriented root field. -/
theorem boundedCore_weight_eq_finite_alternating {q B : ℕ} (hq : q.Prime) :
    (boundedCoreFlow hq).weight =
      alternatingPrefix (boundedCoreFlow hq).successorOperator
        (boundedCoreFlow hq).rootField (B + 1) := by
  exact RankedParentFlow.finite_alternating_expansion
    (boundedCoreRankedFlow hq)

/-! ## Integer-square-root clock realization -/

/-- Entry clock of a bounded canonical source. -/
def coreClock (q : ℕ) {B : ℕ} (s : CoreIndex q B) : ℕ :=
  Nat.sqrt (q * coreValue s)

/-- Full bounded canonical source prefix after integer-square-root clock pushforward. -/
def coreSourcePrefix {q B : ℕ} (hq : q.Prime) (x : ℕ) : ℤ :=
  clockPushforward (coreClock q) x (boundedCoreFlow hq).weight

/-- The prefix is literally the finite sum of all admitted source weights whose
integer-square-root clocks have fired. -/
theorem coreSourcePrefix_eq_sum {q B : ℕ} (hq : q.Prime) (x : ℕ) :
    coreSourcePrefix hq x =
      ∑ s : CoreIndex q B,
        if Nat.sqrt (q * coreValue s) ≤ x then (μ (q * coreValue s) : ℤ) else 0 := by
  rfl

/-- The concrete renewal identity survives the actual integer-square-root clock. -/
theorem coreSourcePrefix_renewal {q B : ℕ} (hq : q.Prime) (x : ℕ) :
    coreSourcePrefix hq x =
      clockPushforward (coreClock q) x (boundedCoreFlow hq).rootField -
      clockPushforward (coreClock q) x
        ((boundedCoreFlow hq).successorOperator (boundedCoreFlow hq).weight) := by
  exact (boundedCoreFlow hq).clockPushforward_renewal (coreClock q) x

/-- The clock-pushed source field is exactly the clock pushforward of the finite
alternating successor expansion; there is no terminal tail. -/
theorem coreSourcePrefix_eq_finite_alternating {q B : ℕ}
    (hq : q.Prime) (x : ℕ) :
    coreSourcePrefix hq x =
      clockPushforward (coreClock q) x
        (alternatingPrefix (boundedCoreFlow hq).successorOperator
          (boundedCoreFlow hq).rootField (B + 1)) := by
  unfold coreSourcePrefix
  rw [boundedCore_weight_eq_finite_alternating hq]

/-- Square-block increment induced by the exact clock-pushed source field. -/
def coreBlockIncrement {q B : ℕ} (hq : q.Prime) : ℕ → ℤ
  | 0 => coreSourcePrefix hq 0
  | n + 1 => coreSourcePrefix hq (n + 1) - coreSourcePrefix hq n

/-- The block increments telescope exactly back to the canonical source prefix. -/
theorem sum_coreBlockIncrement_eq_prefix {q B : ℕ} (hq : q.Prime) (x : ℕ) :
    ∑ n ∈ Finset.range (x + 1), coreBlockIncrement hq n =
      coreSourcePrefix hq x := by
  induction x with
  | zero => simp [coreBlockIncrement]
  | succ x ih =>
      rw [Finset.sum_range_succ, ih]
      simp [coreBlockIncrement]

/-- The cumulative square-block field is therefore exactly the finite alternating
successor flow under the integer-square-root clock. -/
theorem sum_coreBlockIncrement_eq_finite_alternating {q B : ℕ}
    (hq : q.Prime) (x : ℕ) :
    ∑ n ∈ Finset.range (x + 1), coreBlockIncrement hq n =
      clockPushforward (coreClock q) x
        (alternatingPrefix (boundedCoreFlow hq).successorOperator
          (boundedCoreFlow hq).rootField (B + 1)) := by
  rw [sum_coreBlockIncrement_eq_prefix hq x,
    coreSourcePrefix_eq_finite_alternating hq x]

end CanonicalGapAncestryBridge

end RHLean.Proof

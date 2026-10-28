import Mathlib
import «research.EULER_RANK_ONE_FRACTIONAL_ROWS_20261027»
import RHLean.Proof.SquareRootAncestryRoot

/-!
# Quotient-bucket historical carry staircase

On X = R^2-1, N=R-1, L=R+1:
  I_q = (floor(N/(q+1)), floor(N/q)]
  c_(q,b)(a) = floor(floor(X/b)/a) - floor(L*q/b).

The complete carry is a monotone integer staircase. Its kth level is
a <= floor(floor(X/b)/(floor(L*q/b)+k)), with no post-root argument.

The carry VANISHES on divisor rows a|N. No signed cancellation or finite-C
hypothesis is assumed in these structural theorems.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof
open RHLean.Analysis

/-- Historical quotient-bucket lower endpoint. -/
def eulerBucketLow (R q : ℕ) : ℕ := (R - 1) / (q + 1)

/-- Historical quotient-bucket upper endpoint. -/
def eulerBucketHigh (R q : ℕ) : ℕ := (R - 1) / q

/-- All genuine historical a with the fixed reciprocal quotient q. -/
def eulerBucketIndices (R q : ℕ) : Finset ℕ :=
  Finset.Ioc (eulerBucketLow R q) (eulerBucketHigh R q)

/-- Upper hyperbola quotient, computed once for each b. -/
def eulerBucketY (R b : ℕ) : ℕ := squareRootEndpoint R / b

/-- The phase's integer quotient, constant across the entire a-bucket. -/
def eulerBucketPhaseQuot (R q b : ℕ) : ℕ := (R + 1) * q / b

/-- Genuine nonnegative carry, before combining with the modular residue. -/
def eulerBucketCarry (R q b a : ℕ) : ℕ :=
  eulerBucketY R b / a - eulerBucketPhaseQuot R q b

/-- The exact kth integer jump threshold. -/
def eulerBucketJumpEnd (R q b k : ℕ) : ℕ :=
  eulerBucketY R b / (eulerBucketPhaseQuot R q b + k)

/-- Every a in the original interval I_q has its exact quotient q. -/
theorem eulerBucketIndices_quotient (R q a : ℕ) (hq : 0 < q)
    (ha : a ∈ eulerBucketIndices R q) :
    (R - 1) / a = q := by
  have hlo : (R - 1) / (q + 1) < a :=
    (Finset.mem_Ioc.mp ha).1
  have hhi : a ≤ (R - 1) / q :=
    (Finset.mem_Ioc.mp ha).2
  have hloNonneg : 0 ≤ (R - 1) / (q + 1) := Nat.zero_le _
  have ha0 : 0 < a := by omega
  have hqle : q ≤ (R - 1) / a := by
    apply (Nat.le_div_iff_mul_le ha0).2
    have hmul := (Nat.le_div_iff_mul_le hq).1 hhi
    simpa [Nat.mul_comm] using hmul
  have hlt : (R - 1) / a < q + 1 := by
    apply (Nat.div_lt_iff_lt_mul ha0).2
    have hraw := (Nat.div_lt_iff_lt_mul (by omega : 0 < q + 1)).1 hlo
    simpa [Nat.mul_comm] using hraw
  omega

/-- Carry is pointwise non-increasing along each historical a-bucket. -/
theorem eulerBucketCarry_antitone
    (R q b a a' : ℕ) (ha : 0 < a) (haa' : a ≤ a') :
    eulerBucketCarry R q b a' ≤ eulerBucketCarry R q b a := by
  have ha' : 0 < a' := lt_of_lt_of_le ha haa'
  have hmul := Nat.div_mul_le_self (eulerBucketY R b) a'
  have hmul' :
      (eulerBucketY R b / a') * a ≤
        (eulerBucketY R b / a') * a' := Nat.mul_le_mul_left _ haa'
  have hdiv :
      eulerBucketY R b / a' ≤ eulerBucketY R b / a :=
    (Nat.le_div_iff_mul_le ha).2 (hmul'.trans hmul)
  unfold eulerBucketCarry
  omega

/-- An integer carry reaches level k iff the historical index stays below
the corresponding exact, clipped quotient endpoint. -/
theorem eulerBucketCarry_ge_iff_le_jumpEnd
    (R q b a k : ℕ) (ha : 0 < a) (hk : 0 < k) :
    k ≤ eulerBucketCarry R q b a ↔
      a ≤ eulerBucketJumpEnd R q b k := by
  let Y := eulerBucketY R b
  let m := eulerBucketPhaseQuot R q b
  have hmk : 0 < m + k := by omega
  change k ≤ Y / a - m ↔ a ≤ Y / (m + k)
  constructor
  · intro h
    have hquot : m + k ≤ Y / a := by omega
    have hmul := (Nat.le_div_iff_mul_le ha).1 hquot
    apply (Nat.le_div_iff_mul_le hmk).2
    simpa [Nat.mul_comm] using hmul
  · intro h
    have hmul := (Nat.le_div_iff_mul_le hmk).1 h
    have hquot : m + k ≤ Y / a :=
      (Nat.le_div_iff_mul_le ha).2 (by simpa [Nat.mul_comm] using hmul)
    omega

/-- For divisor rows, the FULL original carry vanishes: no terms must be
excised from the signed carry sum when passing to complete buckets. -/
theorem eulerBucketCarry_zero_of_dvd
    (R q b a : ℕ) (hR : 2 ≤ R) (ha : 0 < a)
    (hadiv : a ∣ R - 1) (hq : (R - 1) / a = q) :
    eulerBucketCarry R q b a = 0 := by
  have hmod : (R - 1) % a = 0 := Nat.mod_eq_zero_of_dvd hadiv
  have hdivmod := Nat.div_add_mod (R - 1) a
  rw [hq, hmod, add_zero] at hdivmod
  have hN : R - 1 = a * q := hdivmod.symm
  have hX : squareRootEndpoint R = a * ((R + 1) * q) := by
    rw [eulerRootEndpoint_factor R hR, hN]
    ring
  have hfloor :
      squareRootEndpoint R / (a * b) = ((R + 1) * q) / b := by
    rw [hX]
    exact Nat.mul_div_mul_left (m := a) ((R + 1) * q) b ha
  have hnested :
      eulerBucketY R b / a = squareRootEndpoint R / (a * b) := by
    unfold eulerBucketY
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
  unfold eulerBucketCarry eulerBucketPhaseQuot
  rw [hnested, hfloor]
  omega

/-- The preceding vanishing holds for EVERY divisor row in the
corresponding actual quotient bucket. -/
theorem eulerBucketCarry_zero_on_divisor_member
    (R q b a : ℕ) (hR : 2 ≤ R) (hq : 0 < q)
    (ha : a ∈ eulerBucketIndices R q) (hadiv : a ∣ R - 1) :
    eulerBucketCarry R q b a = 0 := by
  have ha0 : 0 < a := by
    have h := (Finset.mem_Ioc.mp ha).1
    unfold eulerBucketLow at h
    have hz : 0 ≤ (R - 1) / (q + 1) := Nat.zero_le _
    omega
  exact eulerBucketCarry_zero_of_dvd R q b a hR ha0 hadiv
    (eulerBucketIndices_quotient R q a hq ha)


/-- Empty quotient buckets have ZERO levels; otherwise the maximum carry is
at the first admitted integer. This convention prevents ghost levels. -/
def eulerBucketLevelCount (R q b : ℕ) : ℕ :=
  if eulerBucketLow R q < eulerBucketHigh R q then
    eulerBucketCarry R q b (eulerBucketLow R q + 1)
  else 0

/-- Every genuine bucket index is bounded by the first carry staircase step. -/
theorem eulerBucketCarry_le_levelCount (R q b a : ℕ)
    (ha : a ∈ eulerBucketIndices R q) :
    eulerBucketCarry R q b a ≤ eulerBucketLevelCount R q b := by
  have hlo := (Finset.mem_Ioc.mp ha).1
  have hhi := (Finset.mem_Ioc.mp ha).2
  have hne : eulerBucketLow R q < eulerBucketHigh R q :=
    lt_of_lt_of_le hlo hhi
  have haPos : 0 < eulerBucketLow R q + 1 := Nat.succ_pos _
  have haLe : eulerBucketLow R q + 1 ≤ a := by omega
  have hmono := eulerBucketCarry_antitone R q b
    (eulerBucketLow R q + 1) a haPos haLe
  simpa [eulerBucketLevelCount, hne] using hmono

/-- No spurious quotient steps are introduced when a bucket is empty. -/
theorem eulerBucketLevelCount_eq_zero_of_empty
    (R q b : ℕ) (h : ¬ eulerBucketLow R q < eulerBucketHigh R q) :
    eulerBucketLevelCount R q b = 0 := by
  simp [eulerBucketLevelCount, h]

/-- Every admitted positive level hits a historical index ABOVE the bucket
lower bound. Therefore the corresponding Mertens increment is legitimate. -/
theorem eulerBucketLow_le_min_jumpEnd
    (R q b k : ℕ)
    (hk : k ∈ Finset.Icc 1 (eulerBucketLevelCount R q b)) :
    eulerBucketLow R q ≤
      min (eulerBucketHigh R q) (eulerBucketJumpEnd R q b k) := by
  have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
  have hkupper : k ≤ eulerBucketLevelCount R q b :=
    (Finset.mem_Icc.mp hk).2
  by_cases hne : eulerBucketLow R q < eulerBucketHigh R q
  · have hc :
        k ≤ eulerBucketCarry R q b (eulerBucketLow R q + 1) := by
      simpa [eulerBucketLevelCount, hne] using hkupper
    have hEnd :
        eulerBucketLow R q + 1 ≤ eulerBucketJumpEnd R q b k :=
      (eulerBucketCarry_ge_iff_le_jumpEnd R q b
          (eulerBucketLow R q + 1) k (Nat.succ_pos _) hkpos).mp hc
    exact le_min (le_of_lt hne) (by omega)
  · have hz := eulerBucketLevelCount_eq_zero_of_empty R q b hne
    omega

/-- The original discrete carry is EXACTLY its sum of integer-level masks. -/
theorem eulerBucketCarry_eq_levelIndicatorSum
    (R q b a : ℕ) (ha : a ∈ eulerBucketIndices R q) :
    (eulerBucketCarry R q b a : ℤ) =
      ∑ k ∈ Finset.Icc 1 (eulerBucketLevelCount R q b),
        if a ≤ eulerBucketJumpEnd R q b k then (1 : ℤ) else 0 := by
  have habound := eulerBucketCarry_le_levelCount R q b a ha
  have haPos : 0 < a := by
    have hlo := (Finset.mem_Ioc.mp ha).1
    have hz : 0 ≤ eulerBucketLow R q := Nat.zero_le _
    omega
  have hfilter :
      (Finset.Icc 1 (eulerBucketLevelCount R q b)).filter
        (fun k => a ≤ eulerBucketJumpEnd R q b k) =
        Finset.Icc 1 (eulerBucketCarry R q b a) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    by_cases hk : 0 < k
    · have hEquiv :=
        eulerBucketCarry_ge_iff_le_jumpEnd R q b a k haPos hk
      constructor
      · rintro ⟨⟨hOne, _hK⟩, hCut⟩
        exact ⟨hOne, hEquiv.mpr hCut⟩
      · rintro ⟨hOne, hCarry⟩
        exact ⟨⟨hOne, hCarry.trans habound⟩, hEquiv.mp hCarry⟩
    · omega
  symm
  calc
    (∑ k ∈ Finset.Icc 1 (eulerBucketLevelCount R q b),
      if a ≤ eulerBucketJumpEnd R q b k then (1 : ℤ) else 0) =
      ∑ k ∈ (Finset.Icc 1 (eulerBucketLevelCount R q b)).filter
        (fun k => a ≤ eulerBucketJumpEnd R q b k), (1 : ℤ) := by
          rw [Finset.sum_filter]
    _ = ∑ k ∈ Finset.Icc 1 (eulerBucketCarry R q b a), (1 : ℤ) := by
          rw [hfilter]
    _ = (eulerBucketCarry R q b a : ℤ) := by
          simp

/-- Signed Möbius mass of a clipped historical interval is a difference
of the ORIGINAL Mertens function, not a substitute counting sequence. -/
theorem eulerMobius_Ioc_eq_historicalMertens
    (lo hi : ℕ) (h : lo ≤ hi) :
    (∑ a ∈ Finset.Ioc lo hi, (μ a : ℤ)) =
      mertensSummatoryInt hi - mertensSummatoryInt lo := by
  have hs := Finset.sum_Ioc_consecutive
    (f := fun a : ℕ => (μ a : ℤ)) (Nat.zero_le lo) h
  have hIoc (x : ℕ) : Finset.Ioc 0 x = Finset.Icc 1 x := by
    ext a
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hIoc lo, hIoc hi,
      ← mertensSummatoryInt_eq_Icc,
      ← mertensSummatoryInt_eq_Icc] at hs
  omega

/-- THE COMPLETE CARRY-LEVEL COLLAPSE.
All Möbius weights are genuine; every Mertens endpoint is <R.
The min is an exact finite clipping operator and is harmless when the
k-th level automatically ends at or below the bucket high endpoint.
Empty buckets contribute zero on BOTH sides. -/
theorem eulerBucketCarry_sum_eq_historicalMertens
    (R q b : ℕ) :
    (∑ a ∈ eulerBucketIndices R q,
        (μ a : ℤ) * (eulerBucketCarry R q b a : ℤ)) =
      ∑ k ∈ Finset.Icc 1 (eulerBucketLevelCount R q b),
        (mertensSummatoryInt
            (min (eulerBucketHigh R q) (eulerBucketJumpEnd R q b k)) -
          mertensSummatoryInt (eulerBucketLow R q)) := by
  let S := eulerBucketIndices R q
  let K := eulerBucketLevelCount R q b
  let lo := eulerBucketLow R q
  let hi := eulerBucketHigh R q
  let U := fun k => eulerBucketJumpEnd R q b k
  have hCut (k : ℕ) (hk : k ∈ Finset.Icc 1 K) :
      lo ≤ min hi (U k) := by
    exact eulerBucketLow_le_min_jumpEnd R q b k hk
  calc
    (∑ a ∈ S, (μ a : ℤ) * (eulerBucketCarry R q b a : ℤ)) =
      ∑ a ∈ S,
        ∑ k ∈ Finset.Icc 1 K,
          if a ≤ U k then (μ a : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        have hc := eulerBucketCarry_eq_levelIndicatorSum R q b a ha
        calc
          (μ a : ℤ) * (eulerBucketCarry R q b a : ℤ) =
            (μ a : ℤ) *
              (∑ k ∈ Finset.Icc 1 K,
                if a ≤ U k then (1 : ℤ) else 0) := by
              rw [hc]
          _ = ∑ k ∈ Finset.Icc 1 K,
              if a ≤ U k then (μ a : ℤ) else 0 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _hk
              split_ifs <;> ring
    _ = ∑ k ∈ Finset.Icc 1 K,
          ∑ a ∈ S, if a ≤ U k then (μ a : ℤ) else 0 :=
        Finset.sum_comm
    _ = ∑ k ∈ Finset.Icc 1 K,
          (mertensSummatoryInt (min hi (U k)) -
            mertensSummatoryInt lo) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hset :
            S.filter (fun a => a ≤ U k) =
              Finset.Ioc lo (min hi (U k)) := by
          ext a
          simp only [S, eulerBucketIndices, Finset.mem_filter,
            Finset.mem_Ioc, le_min_iff]
          tauto
        calc
          (∑ a ∈ S, if a ≤ U k then (μ a : ℤ) else 0) =
            ∑ a ∈ S.filter (fun a => a ≤ U k), (μ a : ℤ) := by
              rw [Finset.sum_filter]
          _ = ∑ a ∈ Finset.Ioc lo (min hi (U k)), (μ a : ℤ) := by
              rw [hset]
          _ = mertensSummatoryInt (min hi (U k)) -
                mertensSummatoryInt lo :=
              eulerMobius_Ioc_eq_historicalMertens lo
                (min hi (U k)) (hCut k hk)

/-- Every Mertens evaluation on the right of the carry collapse occurs
below the original historical root R. -/
theorem eulerBucketMertens_endpoint_lt_root
    (R q b k : ℕ) (hR : 2 ≤ R) :
    min (eulerBucketHigh R q) (eulerBucketJumpEnd R q b k) < R := by
  calc
    _ ≤ eulerBucketHigh R q := min_le_left _ _
    _ ≤ R - 1 := Nat.div_le_self _ _
    _ < R := by omega


/-- Exact integer Euclidean carry: both original arithmetic remainders
are retained, with no smooth approximation. -/
theorem eulerBucketCarry_eq_euclidean
    (R q b a : ℕ) (hR : 2 ≤ R) (ha : 0 < a) (hb : 0 < b)
    (hq : (R - 1) / a = q) :
    eulerBucketCarry R q b a =
      (a * (((R + 1) * q) % b) +
         (R + 1) * ((R - 1) % a)) / (a * b) := by
  let N := R - 1
  let L := R + 1
  let m := L * q / b
  let rho := (L * q) % b
  let t := N % a
  have hN : a * q + t = N := by
    change a * q + (R - 1) % a = R - 1
    rw [← hq]
    exact Nat.div_add_mod (R - 1) a
  have hQ : b * m + rho = L * q := Nat.div_add_mod (L * q) b
  have hX :
      squareRootEndpoint R =
        (a * b) * m + (a * rho + L * t) := by
    calc
      squareRootEndpoint R = L * N := by
        simpa [L, N] using eulerRootEndpoint_factor R hR
      _ = L * (a * q + t) := by rw [hN]
      _ = a * (L * q) + L * t := by ring
      _ = a * (b * m + rho) + L * t := by rw [hQ]
      _ = (a * b) * m + (a * rho + L * t) := by ring
  have hquot :
      squareRootEndpoint R / (a * b) =
        m + (a * rho + L * t) / (a * b) := by
    rw [hX, Nat.mul_add_div (Nat.mul_pos ha hb)]
  have hnest :
      eulerBucketY R b / a = squareRootEndpoint R / (a * b) := by
    unfold eulerBucketY
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm b a]
  unfold eulerBucketCarry eulerBucketPhaseQuot
  rw [hnest, hquot]
  change m + (a * rho + L * t) / (a * b) - m =
    (a * rho + L * t) / (a * b)
  have hnonneg : 0 ≤ (a * rho + L * t) / (a * b) := Nat.zero_le _
  omega

/-- True pointwise sharp carry range. The small power-saving lemma uses
BOTH a<=N and the original Euclidean residues, not a generic floor matrix. -/
theorem eulerBucketCarry_le_div_add_one
    (R q b a : ℕ) (hR : 2 ≤ R) (ha : 0 < a) (hb : 0 < b)
    (haN : a ≤ R - 1) (hq : (R - 1) / a = q) :
    eulerBucketCarry R q b a ≤ (R - 1) / b + 1 := by
  let N := R - 1
  let L := R + 1
  let rho := (L * q) % b
  let t := N % a
  have hr : rho ≤ b - 1 := by
    have hlt : rho < b := Nat.mod_lt (L * q) hb
    omega
  have ht : t ≤ a - 1 := by
    have hlt : t < a := Nat.mod_lt N ha
    omega
  have haR : a ≤ R := by omega
  have haa : a - 1 + 1 = a := by omega
  have hLbound : L * (a - 1) ≤ a * R := by
    have hm : L * (a - 1) + L = L * a := by
      calc
        _ = L * ((a - 1) + 1) := by ring
        _ = L * a := by rw [haa]
    dsimp [L] at *
    nlinarith
  have hnum : a * rho + L * t ≤ a * (N + b) := by
    calc
      _ ≤ a * (b - 1) + L * (a - 1) :=
        Nat.add_le_add (Nat.mul_le_mul_left a hr)
          (Nat.mul_le_mul_left L ht)
      _ ≤ a * (b - 1) + a * R :=
        Nat.add_le_add_left hLbound _
      _ = a * (N + b) := by
        have heq : (b - 1) + R = N + b := by
          dsimp [N]
          omega
        calc
          _ = a * ((b - 1) + R) := by ring
          _ = a * (N + b) := by rw [heq]
  have hrat :
      (a * rho + L * t) / (a * b) ≤ (N + b) / b := by
    calc
      _ ≤ (a * (N + b)) / (a * b) := Nat.div_le_div_right hnum
      _ = (N + b) / b := Nat.mul_div_mul_left (m := a) (N + b) b ha
  have hadd : (N + b) / b = N / b + 1 := by
    calc
      _ = (b * 1 + N) / b := by ring
      _ = 1 + N / b := Nat.mul_add_div hb 1 N
      _ = N / b + 1 := by omega
  rw [eulerBucketCarry_eq_euclidean R q b a hR ha hb hq]
  exact le_of_le_of_eq hrat hadd

/-- Certified complexity bound for the COMPLETE genuine historical bucket.
In particular b>N/2 forces at most TWO integer carry levels. -/
theorem eulerBucketLevelCount_le_div_add_one
    (R q b : ℕ) (hR : 2 ≤ R) (hq : 0 < q) (hb : 0 < b) :
    eulerBucketLevelCount R q b ≤ (R - 1) / b + 1 := by
  by_cases hne : eulerBucketLow R q < eulerBucketHigh R q
  · have haMem :
        eulerBucketLow R q + 1 ∈ eulerBucketIndices R q :=
      Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
    have haN : eulerBucketLow R q + 1 ≤ R - 1 := by
      have hhigh : eulerBucketHigh R q ≤ R - 1 :=
        Nat.div_le_self _ _
      have hhi := (Finset.mem_Ioc.mp haMem).2
      omega
    have hqexact := eulerBucketIndices_quotient R q
      (eulerBucketLow R q + 1) hq haMem
    have hbound := eulerBucketCarry_le_div_add_one R q b
      (eulerBucketLow R q + 1) hR (Nat.succ_pos _) hb haN hqexact
    simpa [eulerBucketLevelCount, hne] using hbound
  · simp [eulerBucketLevelCount, hne]


/-- The full original signed carry sum is UNCHANGED when divisor rows are
removed: each omitted divisor has zero integer carry. -/
theorem eulerBucketCarry_sum_unpunctured
    (R q b : ℕ) (hR : 2 ≤ R) (hq : 0 < q) :
    (∑ a ∈ (eulerBucketIndices R q).filter (fun a => ¬ a ∣ R - 1),
        (μ a : ℤ) * (eulerBucketCarry R q b a : ℤ)) =
      ∑ a ∈ eulerBucketIndices R q,
        (μ a : ℤ) * (eulerBucketCarry R q b a : ℤ) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hd : a ∣ R - 1
  · have hc := eulerBucketCarry_zero_on_divisor_member R q b a hR hq ha hd
    simp [hd, hc]
  · simp [hd]

/-- On b>N/2, EVERY real quotient bucket has at most two integer carry levels.
This is a derived numerical *complexity* bound, not a covariance bound. -/
theorem eulerBucketLevelCount_le_two_of_upper_half
    (R q b : ℕ) (hR : 2 ≤ R) (hq : 0 < q) (hb : 0 < b)
    (hhalf : (R - 1) / 2 < b) :
    eulerBucketLevelCount R q b ≤ 2 := by
  have hc := eulerBucketLevelCount_le_div_add_one R q b hR hq hb
  have hNlt : R - 1 < b * 2 :=
    (Nat.div_lt_iff_lt_mul (by norm_num : 0 < (2 : ℕ))).mp hhalf
  have hquot : (R - 1) / b < 2 :=
    (Nat.div_lt_iff_lt_mul hb).2 (by simpa [Nat.mul_comm] using hNlt)
  omega

#print axioms eulerBucketIndices_quotient
#print axioms eulerBucketCarry_antitone
#print axioms eulerBucketCarry_ge_iff_le_jumpEnd
#print axioms eulerBucketCarry_zero_on_divisor_member
#print axioms eulerBucketCarry_sum_eq_historicalMertens
#print axioms eulerBucketMertens_endpoint_lt_root
#print axioms eulerBucketCarry_eq_euclidean
#print axioms eulerBucketLevelCount_le_div_add_one
#print axioms eulerBucketCarry_sum_unpunctured
#print axioms eulerBucketLevelCount_le_two_of_upper_half

end RHLean.Proof

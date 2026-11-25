import RHLean.Arithmetic.SignedBuchstabRecursion

/-!
# One-prime Euler extension: physical removal and signed defect

Every quantity below is computed from the actual finite integer population.
No bound, recovery witness, or desired signed inequality is built into a definition.
The algebra is valid even for signed weights; disjoint least-prime ownership
requires inserting distinct primes in increasing order.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Research.SinglePrimeEuler

def survives (S : Finset ℕ) (n : ℕ) : Prop :=
  ∀ q ∈ S, ¬ q ∣ n

def indicator (S : Finset ℕ) (n : ℕ) : ℝ := by
  classical
  exact if survives S n then 1 else 0

def capacity (I S : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ I, w n * indicator S n

def removal (I S : Finset ℕ) (p : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ I.filter (fun n => p ∣ n), w n * indicator S n

theorem survives_insert (S : Finset ℕ) (p n : ℕ) :
    survives (insert p S) n ↔ ¬ p ∣ n ∧ survives S n := by
  constructor
  · intro h
    exact ⟨h p (Finset.mem_insert_self p S),
      fun q hq => h q (Finset.mem_insert_of_mem hq)⟩
  · rintro ⟨hp, hS⟩ q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact hS q hq

theorem indicator_insert (S : Finset ℕ) (p n : ℕ) :
    indicator (insert p S) n = if p ∣ n then 0 else indicator S n := by
  classical
  by_cases hp : p ∣ n <;> simp [indicator, survives_insert, hp]

/-- The actual one-prime subtraction; no approximation by density. -/
theorem capacity_insert (I S : Finset ℕ) (p : ℕ) (w : ℕ → ℝ) :
    capacity I (insert p S) w = capacity I S w - removal I S p w := by
  classical
  unfold capacity removal
  rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [indicator_insert]
  by_cases h : p ∣ n <;> simp [h]

/-- Coprimality makes the owner cofactor inherit exactly the previous wheel. -/
theorem indicator_mul (S : Finset ℕ) {p : ℕ} (hp : p.Prime)
    (hS : ∀ q ∈ S, q.Prime) (fresh : p ∉ S) (m : ℕ) :
    indicator S (p * m) = indicator S m := by
  classical
  have hh : survives S (p * m) ↔ survives S m := by
    constructor
    · intro h q hq hd
      exact h q hq (dvd_mul_of_dvd_right hd p)
    · intro h q hq hd
      rcases (hS q hq).dvd_mul.mp hd with hqp | hqm
      · have heq : q = p := (Nat.prime_dvd_prime_iff_eq (hS q hq) hp).mp hqp
        exact fresh (heq ▸ hq)
      · exact h q hq hqm
  simp [indicator, hh]

/-- The removed physical sites are reindexed by their actual cofactors,
with the original weight pulled back, not replaced by a density. -/
theorem removal_reindex (I S : Finset ℕ) {p : ℕ} (hp : p.Prime)
    (hS : ∀ q ∈ S, q.Prime) (fresh : p ∉ S) (w : ℕ → ℝ) :
    removal I S p w =
      ∑ m ∈ ((I.filter (fun n => p ∣ n)).image (fun n => n / p)),
        w (p * m) * indicator S m := by
  classical
  rw [Finset.sum_image]
  · unfold removal
    apply Finset.sum_congr rfl
    intro n hn
    have hd := (Finset.mem_filter.mp hn).2
    have hm := indicator_mul S hp hS fresh (n / p)
    rw [Nat.mul_div_cancel' hd] at hm
    rw [Nat.mul_div_cancel' hd, ← hm]
  · intro a ha b hb hab
    change a / p = b / p at hab
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    calc
      a = p * (a / p) := (Nat.mul_div_cancel' ha').symm
      _ = p * (b / p) := by rw [hab]
      _ = b := Nat.mul_div_cancel' hb'

def eulerFactor (p : ℕ) : ℝ := 1 - 1 / (p : ℝ)

def defect (I S : Finset ℕ) (p : ℕ) (w : ℕ → ℝ) : ℝ :=
  removal I S p w - capacity I S w / (p : ℝ)

/-- Exact signed defect: the sole local source of deviation from Euler density. -/
theorem one_step (I S : Finset ℕ) (p : ℕ) (w : ℕ → ℝ) :
    capacity I (insert p S) w =
      eulerFactor p * capacity I S w - defect I S p w := by
  rw [capacity_insert]
  unfold eulerFactor defect
  ring

def attenuation : List ℕ → ℝ
  | [] => 1
  | p :: ps => eulerFactor p * attenuation ps

def runCapacity (I : Finset ℕ) (w : ℕ → ℝ) :
    List ℕ → Finset ℕ → ℝ
  | [], S => capacity I S w
  | p :: ps, S => runCapacity I w ps (insert p S)

def accumulatedDefect (I : Finset ℕ) (w : ℕ → ℝ) :
    List ℕ → Finset ℕ → ℝ
  | [], _ => 0
  | p :: ps, S => attenuation ps * defect I S p w +
      accumulatedDefect I w ps (insert p S)

/-- All later Euler factors attenuate each original signed marginal defect. -/
theorem telescoping (I : Finset ℕ) (w : ℕ → ℝ) (ps : List ℕ) (S : Finset ℕ) :
    runCapacity I w ps S =
      attenuation ps * capacity I S w - accumulatedDefect I w ps S := by
  induction ps generalizing S with
  | nil => simp [runCapacity, attenuation, accumulatedDefect]
  | cons p ps ih =>
    simp only [runCapacity, attenuation, accumulatedDefect]
    rw [ih (insert p S), one_step]
    ring

/-- Centering is a scalar identity, not an estimate. A proof of the lower
bound on the actual accumulated defect must be supplied independently. -/
theorem centered_iff (I : Finset ℕ) (w : ℕ → ℝ) (ps : List ℕ)
    (S : Finset ℕ) (main budget : ℝ) :
    runCapacity I w ps S - main ≤ budget ↔
      attenuation ps * capacity I S w - main - budget ≤
        accumulatedDefect I w ps S := by
  rw [telescoping]
  constructor <;> intro h <;> linarith

#print axioms one_step
#print axioms removal_reindex
#print axioms telescoping
#print axioms centered_iff


/-- Concrete old-wheel population vector for the finite source obstruction. -/
def oldWheelVector30 (lo hi : ℕ) (a : Fin 30) : ℕ :=
  ((Finset.Icc lo hi).filter
    (fun n => Nat.Coprime n 30 ∧ n % 30 = a.val)).card

/-- Actual removal at the fresh prime 7, not a predicted Euler proportion. -/
def actualRemoval7 (lo hi : ℕ) : ℕ :=
  ((Finset.Icc lo hi).filter
    (fun n => Nat.Coprime n 30 ∧ n % 7 = 0)).card

set_option maxRecDepth 4096 in
/-- Two subintervals of the same square block have identical old residue counts. -/
theorem oldWheelVector30_collision_pointwise :
    ∀ a : Fin 30, oldWheelVector30 900 929 a = oldWheelVector30 930 959 a := by
  decide

theorem oldWheelVector30_collision :
    oldWheelVector30 900 929 = oldWheelVector30 930 959 := by
  funext a
  exact oldWheelVector30_collision_pointwise a

/-- But the actual new-prime removal differs on those two physical intervals. -/
theorem actualRemoval7_collision :
    actualRemoval7 900 929 = 1 ∧ actualRemoval7 930 959 = 2 := by
  decide

/-- No function of the old-wheel count vector alone can recover both removals. -/
theorem noBareWheelRecovery30 :
    ¬ ∃ f : (Fin 30 → ℕ) → ℕ,
      f (oldWheelVector30 900 929) = actualRemoval7 900 929 ∧
      f (oldWheelVector30 930 959) = actualRemoval7 930 959 := by
  rintro ⟨f, hI, hJ⟩
  rw [actualRemoval7_collision.1] at hI
  rw [actualRemoval7_collision.2] at hJ
  have h := (congrArg f oldWheelVector30_collision).symm.trans hI
  exact (by decide : (1 : ℕ) ≠ 2) (h.symm.trans hJ)

#print axioms oldWheelVector30_collision
#print axioms actualRemoval7_collision
#print axioms noBareWheelRecovery30

end RHLean.Research.SinglePrimeEuler

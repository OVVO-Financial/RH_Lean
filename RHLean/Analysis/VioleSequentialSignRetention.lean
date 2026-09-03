import Mathlib
import RHLean.Analysis.OriginalVioleFunction
import RHLean.Analysis.VioleSequentialEulerClosure

/-!
# Viole sequential sign retention

This module isolates the exact signed cancellation mechanism on the protected
Viole square-block carrier.

For the reciprocal protected-block summand

`v(m) = mu(m) * Resp(m) / m`,

adjoining a fresh prime `p` gives

`v(mp) = -(1/p) * v(m) + defect_p(m)`.

Thus the child is an opposite-sign `1/p` copy of the parent, up to the explicit
physical response defect.  Pairing parent and child cancels that `1/p` copy and
retains

`(1 - 1/p) * v(m)`.

The Euler factor is strictly positive, so the inherited component keeps the
parent sign.  A sign change is therefore possible only if the physical defect
is large enough to overwhelm that retained Euler mass.

The same mechanism iterates.  Two fresh primes produce the product
`(1 - 1/q) * (1 - 1/p)` on the ancestral summand, while all failure of pure
sign retention is carried by explicitly transported physical defects.  The
defects themselves obey the same Euler compression: their new remainder is a
second mixed finite difference of the physical response.  This is the exact
finite cancellation mechanism behind chronological prime-by-prime descent.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- Positive Euler factor retained after pairing a parent with its fresh-prime
child. -/
def nativePNTSignedSquareBlockEulerFactor (p : Nat) : Real :=
  1 - 1 / (p : Real)

/-- Every genuine prime leaves a strictly positive inherited Euler factor. -/
theorem nativePNTSignedSquareBlockEulerFactor_pos
    {p : Nat} (hp : p.Prime) :
    0 < nativePNTSignedSquareBlockEulerFactor p := by
  have hpR : (1 : Real) < (p : Real) := by
    exact_mod_cast hp.one_lt
  have hpRpos : (0 : Real) < (p : Real) := lt_trans zero_lt_one hpR
  unfold nativePNTSignedSquareBlockEulerFactor
  apply sub_pos.mpr
  apply (div_lt_iff₀ hpRpos).2
  simpa using hpR

/-- Weak form used for signed products. -/
theorem nativePNTSignedSquareBlockEulerFactor_nonneg
    {p : Nat} (hp : p.Prime) :
    0 <= nativePNTSignedSquareBlockEulerFactor p :=
  (nativePNTSignedSquareBlockEulerFactor_pos hp).le

/-- **Child = opposite `1/p` copy + physical defect.**
This is the literal sign-cancellation law before parent and child are added. -/
theorem nativePNTSignedSquareBlockCorrelationReciprocalChild_eq_neg_inv_parent_add_defect
    (N M L : Nat) {m p : Nat}
    (hm : 0 < m) (hp : p.Prime) (hcop : Nat.Coprime m p) :
    nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L (m * p) =
      -(1 / (p : Real)) *
          nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m +
        nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L m p := by
  have hpair :=
    nativePNTSignedSquareBlockCorrelationReciprocalSummand_add_mul_freshPrime
      N M L hm hp hcop
  calc
    nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L (m * p) =
        (nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m +
          nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L (m * p)) -
          nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m := by ring
    _ = ((1 - 1 / (p : Real)) *
          nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m +
        nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L m p) -
          nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m := by
      rw [hpair]
    _ = -(1 / (p : Real)) *
          nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m +
        nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L m p := by ring

/-- If the physical response is invariant across one fresh-prime edge, the
child is exactly the opposite-sign `1/p` copy of its parent. -/
theorem nativePNTSignedSquareBlockCorrelationReciprocalChild_eq_neg_inv_parent_of_response_eq
    (N M L : Nat) {m p : Nat}
    (hm : 0 < m) (hp : p.Prime) (hcop : Nat.Coprime m p)
    (hresp :
      nativePNTSignedSquareBlockCofactorResponse N M L m =
        nativePNTSignedSquareBlockCofactorResponse N M L (m * p)) :
    nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L (m * p) =
      -(1 / (p : Real)) *
        nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m := by
  rw [nativePNTSignedSquareBlockCorrelationReciprocalChild_eq_neg_inv_parent_add_defect
    N M L hm hp hcop]
  unfold nativePNTSignedSquareBlockFreshPrimePhysicalDefect
  rw [hresp]
  ring

/-- In the defect-free case the child really opposes the parent. -/
theorem nativePNTSignedSquareBlockCorrelationReciprocal_child_opposes_parent_of_response_eq
    (N M L : Nat) {m p : Nat}
    (hm : 0 < m) (hp : p.Prime) (hcop : Nat.Coprime m p)
    (hresp :
      nativePNTSignedSquareBlockCofactorResponse N M L m =
        nativePNTSignedSquareBlockCofactorResponse N M L (m * p)) :
    nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m *
        nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L (m * p) <= 0 := by
  rw [nativePNTSignedSquareBlockCorrelationReciprocalChild_eq_neg_inv_parent_of_response_eq
    N M L hm hp hcop hresp]
  have hpRpos : (0 : Real) < (p : Real) := by exact_mod_cast hp.pos
  have hinv : 0 <= (1 : Real) / (p : Real) := (div_nonneg zero_le_one hpRpos.le)
  have hs :
      0 <= (1 / (p : Real)) *
        (nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m) ^ 2 :=
    mul_nonneg hinv (sq_nonneg _)
  nlinarith

/-- The inherited component after one fresh-prime pairing has the same weak
sign as the parent because `1 - 1/p` is positive. -/
theorem nativePNTSignedSquareBlockCorrelationReciprocal_inherited_sign_retained
    (N M L : Nat) {m p : Nat} (hp : p.Prime) :
    0 <=
      nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m *
        (nativePNTSignedSquareBlockEulerFactor p *
          nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m) := by
  have hf := nativePNTSignedSquareBlockEulerFactor_nonneg hp
  calc
    nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m *
        (nativePNTSignedSquareBlockEulerFactor p *
          nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m) =
      nativePNTSignedSquareBlockEulerFactor p *
        (nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m) ^ 2 := by
          ring
    _ >= 0 := mul_nonneg hf (sq_nonneg _)

private theorem mul_add_same_sign_of_abs_le
    (x f d : Real) (hf : 0 <= f) (hd : |d| <= f * |x|) :
    0 <= x * (f * x + d) := by
  by_cases hx : 0 <= x
  · have hdlo := (abs_le.mp hd).1
    rw [abs_of_nonneg hx] at hdlo
    have hsum : 0 <= f * x + d := by linarith
    exact mul_nonneg hx hsum
  · have hx' : x <= 0 := le_of_not_ge hx
    have hdhi := (abs_le.mp hd).2
    rw [abs_of_nonpos hx'] at hdhi
    have hsum : f * x + d <= 0 := by linarith
    exact mul_nonneg_of_nonpos_of_nonpos hx' hsum

/-- **Quantitative sign-retention criterion.**
A fresh-prime pair cannot flip the parent sign unless the physical defect is
larger than the retained Euler mass `(1 - 1/p)|v(m)|`. -/
theorem nativePNTSignedSquareBlockCorrelationReciprocal_pair_sign_retained_of_defect_le
    (N M L : Nat) {m p : Nat}
    (hm : 0 < m) (hp : p.Prime) (hcop : Nat.Coprime m p)
    (hdefect :
      |nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L m p| <=
        nativePNTSignedSquareBlockEulerFactor p *
          |nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m|) :
    0 <=
      nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m *
        (nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m +
          nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L (m * p)) := by
  rw [nativePNTSignedSquareBlockCorrelationReciprocalSummand_add_mul_freshPrime
    N M L hm hp hcop]
  exact mul_add_same_sign_of_abs_le
    (nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m)
    (nativePNTSignedSquareBlockEulerFactor p)
    (nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L m p)
    (nativePNTSignedSquareBlockEulerFactor_nonneg hp) hdefect

/-- In particular, exact response invariance forces sign retention after the
opposite-sign child has canceled its `1/p` share. -/
theorem nativePNTSignedSquareBlockCorrelationReciprocal_pair_sign_retained_of_response_eq
    (N M L : Nat) {m p : Nat}
    (hm : 0 < m) (hp : p.Prime) (hcop : Nat.Coprime m p)
    (hresp :
      nativePNTSignedSquareBlockCofactorResponse N M L m =
        nativePNTSignedSquareBlockCofactorResponse N M L (m * p)) :
    0 <=
      nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m *
        (nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m +
          nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L (m * p)) := by
  have hdef : nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L m p = 0 := by
    unfold nativePNTSignedSquareBlockFreshPrimePhysicalDefect
    rw [hresp]
    ring
  apply nativePNTSignedSquareBlockCorrelationReciprocal_pair_sign_retained_of_defect_le
    N M L hm hp hcop
  rw [hdef, abs_zero]
  exact mul_nonneg
    (nativePNTSignedSquareBlockEulerFactor_nonneg hp) (abs_nonneg _)

/-- **Two-prime chronological Euler compression on the protected Viole block.**
Compress the two `q` edges first and then the remaining `p` edge.  The ancestral
summand receives the positive product of Euler factors.  Every departure from
pure cancellation is an explicit physical defect. -/
theorem nativePNTSignedSquareBlockCorrelationReciprocal_twoPrime_compression
    (N M L : Nat) {m p q : Nat}
    (hm : 0 < m) (hp : p.Prime) (hq : q.Prime)
    (hcopMP : Nat.Coprime m p)
    (hcopMQ : Nat.Coprime m q)
    (hcopMPQ : Nat.Coprime (m * p) q) :
    (nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m +
        nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L (m * q)) +
      (nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L (m * p) +
        nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L ((m * p) * q)) =
      nativePNTSignedSquareBlockEulerFactor q *
          nativePNTSignedSquareBlockEulerFactor p *
          nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m +
        nativePNTSignedSquareBlockEulerFactor q *
          nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L m p +
        nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L m q +
        nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L (m * p) q := by
  have hmq :=
    nativePNTSignedSquareBlockCorrelationReciprocalSummand_add_mul_freshPrime
      N M L hm hq hcopMQ
  have hmpq :=
    nativePNTSignedSquareBlockCorrelationReciprocalSummand_add_mul_freshPrime
      N M L (Nat.mul_pos hm hp.pos) hq hcopMPQ
  have hmp :=
    nativePNTSignedSquareBlockCorrelationReciprocalSummand_add_mul_freshPrime
      N M L hm hp hcopMP
  calc
    (nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m +
        nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L (m * q)) +
      (nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L (m * p) +
        nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L ((m * p) * q)) =
      nativePNTSignedSquareBlockEulerFactor q *
          (nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m +
            nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L (m * p)) +
        nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L m q +
        nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L (m * p) q := by
      rw [hmq, hmpq]
      unfold nativePNTSignedSquareBlockEulerFactor
      ring
    _ = nativePNTSignedSquareBlockEulerFactor q *
          nativePNTSignedSquareBlockEulerFactor p *
          nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m +
        nativePNTSignedSquareBlockEulerFactor q *
          nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L m p +
        nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L m q +
        nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L (m * p) q := by
      rw [hmp]
      ring

/-- The two-prime inherited component still has the ancestral sign: Euler
contraction reduces magnitude but cannot reverse orientation. -/
theorem nativePNTSignedSquareBlockCorrelationReciprocal_twoPrime_inherited_sign_retained
    (N M L : Nat) {m p q : Nat} (hp : p.Prime) (hq : q.Prime) :
    0 <=
      nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m *
        (nativePNTSignedSquareBlockEulerFactor q *
          nativePNTSignedSquareBlockEulerFactor p *
          nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m) := by
  have hp0 := nativePNTSignedSquareBlockEulerFactor_nonneg hp
  have hq0 := nativePNTSignedSquareBlockEulerFactor_nonneg hq
  calc
    nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m *
        (nativePNTSignedSquareBlockEulerFactor q *
          nativePNTSignedSquareBlockEulerFactor p *
          nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m) =
      (nativePNTSignedSquareBlockEulerFactor q *
        nativePNTSignedSquareBlockEulerFactor p) *
        (nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m) ^ 2 := by ring
    _ >= 0 :=
      mul_nonneg (mul_nonneg hq0 hp0) (sq_nonneg _)

/-- Second mixed physical-response difference created when the `p` defect is
itself compressed across a fresh `q` coordinate. -/
def nativePNTSignedSquareBlockFreshPrimeMixedResponseDifference
    (N M L m p q : Nat) : Real :=
  (nativePNTSignedSquareBlockCofactorResponse N M L m -
      nativePNTSignedSquareBlockCofactorResponse N M L (m * p)) -
    (nativePNTSignedSquareBlockCofactorResponse N M L (m * q) -
      nativePNTSignedSquareBlockCofactorResponse N M L ((m * q) * p))

/-- **Defect-of-defect cancellation.**  Physical defects are not dead error
terms.  Under the next fresh prime they obey the same Euler law; the only new
remainder is the mixed second finite difference of the response.  Repeating
this identity pushes uncanceled mass to successively higher-order boundary
finite differences. -/
theorem nativePNTSignedSquareBlockFreshPrimePhysicalDefect_add_mul_freshPrime
    (N M L : Nat) {m p q : Nat}
    (hm : 0 < m) (hp : p.Prime) (hq : q.Prime)
    (hcopMQ : Nat.Coprime m q) :
    nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L m p +
        nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L (m * q) p =
      nativePNTSignedSquareBlockEulerFactor q *
          nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L m p +
        (((μ m : Int) : Real) *
          nativePNTSignedSquareBlockFreshPrimeMixedResponseDifference N M L m p q) /
          (((m * p) * q : Nat) : Real) := by
  have hm0 : (m : Real) != 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hp0 : (p : Real) != 0 := by exact_mod_cast hp.ne_zero
  have hq0 : (q : Real) != 0 := by exact_mod_cast hq.ne_zero
  unfold nativePNTSignedSquareBlockFreshPrimePhysicalDefect
    nativePNTSignedSquareBlockFreshPrimeMixedResponseDifference
    nativePNTSignedSquareBlockEulerFactor
  rw [nativeMobius_adjoin_prime m q hq hcopMQ]
  push_cast
  field_simp [hm0, hp0, hq0]
  ring

/-- If the mixed response difference vanishes, even the first physical defect
retains its sign under the next Euler compression. -/
theorem nativePNTSignedSquareBlockFreshPrimePhysicalDefect_sign_retained_of_mixed_eq_zero
    (N M L : Nat) {m p q : Nat}
    (hm : 0 < m) (hp : p.Prime) (hq : q.Prime)
    (hcopMQ : Nat.Coprime m q)
    (hmixed :
      nativePNTSignedSquareBlockFreshPrimeMixedResponseDifference N M L m p q = 0) :
    0 <=
      nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L m p *
        (nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L m p +
          nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L (m * q) p) := by
  rw [nativePNTSignedSquareBlockFreshPrimePhysicalDefect_add_mul_freshPrime
    N M L hm hp hq hcopMQ, hmixed]
  simp only [mul_zero, zero_div, add_zero]
  have hf := nativePNTSignedSquareBlockEulerFactor_nonneg hq
  calc
    nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L m p *
        (nativePNTSignedSquareBlockEulerFactor q *
          nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L m p) =
      nativePNTSignedSquareBlockEulerFactor q *
        (nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L m p) ^ 2 := by ring
    _ >= 0 := mul_nonneg hf (sq_nonneg _)

end RHLean.Analysis

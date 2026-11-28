import «research.NativeSignLift»
import «research.NativeTrueZeroSchurFit»

/-! The actual four-channel lift of the two physical Euler profiles.
The common unsigned sector cancels; the true-zero Schur correction
to the original star covolume is independently bounded. This is a
transport theorem, not a proof of the signed quantitative estimate. -/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace RHLean.Analysis.AlpogeThin.SlotProjector
namespace SignSchurHandoff

open TrueZeroSchur

/-- A rectangular four-channel observation map. Its positive-path
quotient is M, its signed primitive kernel is X. -/
def observations {J I : Type*} (M X : Matrix J I ℝ) :
    Matrix (J ⊕ J) (I ⊕ I) ℝ :=
  let A := (1/2:ℝ) • (M+X)
  let B := (1/2:ℝ) • (M-X)
  Matrix.fromBlocks A B B A

/-- The determinant factorization is on the actual doubled observation
matrix, rather than two formally assigned determinants. -/
theorem observations_det {J I : Type*} [Fintype J] [Fintype I] [DecidableEq I]
    (M X : Matrix J I ℝ) :
    (WheelNNS.coDiv (observations M X)).det =
      (WheelNNS.coDiv M).det * (WheelNNS.coDiv X).det := by
  let A := (1/2:ℝ) • (M+X)
  let B := (1/2:ℝ) • (M-X)
  have hp : A+B=M := by ext i j; simp [A,B]; ring
  have hm : A-B=X := by ext i j; simp [A,B]; ring
  let C := A.transpose*A+B.transpose*B
  let D := A.transpose*B+B.transpose*A
  have hC : (observations M X).transpose*observations M X =
      NativeSignLift.lift C D := by
    change (Matrix.fromBlocks A B B A).transpose*Matrix.fromBlocks A B B A = _
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
    simp only [NativeSignLift.lift,C,D]
    rw [add_comm (B.transpose*A) (A.transpose*B),
      add_comm (B.transpose*B) (A.transpose*A)]
  have hsum : C+D=M.transpose*M := by
    rw [← hp, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    dsimp only [C,D]
    abel
  have hsub : C-D=X.transpose*X := by
    rw [← hm, Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    dsimp only [C,D]
    abel
  rw [WheelNNS.coDiv_eq, hC, NativeSignLift.lift_det, hsum, hsub,
    WheelNNS.coDiv_eq, WheelNNS.coDiv_eq]

/-- On two profiles with a common measured unsigned reference, its
log volume cancels exactly. The signs of the remaining ratio are kept. -/
theorem relative_log {J I : Type*} [Fintype J] [Fintype I] [DecidableEq I]
    (M X Y : Matrix J I ℝ)
    (hM : (WheelNNS.coDiv M).det ≠ 0)
    (hX : (WheelNNS.coDiv X).det ≠ 0)
    (hY : (WheelNNS.coDiv Y).det ≠ 0) :
    (Real.log (WheelNNS.coDiv (observations M X)).det -
      Real.log (WheelNNS.coDiv (observations M Y)).det)/2 =
    (Real.log (WheelNNS.coDiv X).det - Real.log (WheelNNS.coDiv Y).det)/2 := by
  rw [observations_det, observations_det, Real.log_mul hM hX, Real.log_mul hM hY]
  ring

/-- The ratio of the Schur determinant to the bare star determinant
is independently paid by the measured normal angle. -/
theorem normal_angle_bounds {r : ℕ} (S : Fin (r+1) → Finset ℕ)
    (D : Fin (r+1) → ℕ) (hS : ∀ i, (S i).Nonempty)
    (hD : ∀ i, 0 < D i) (m : ℝ) (_hm : 0 < m)
    (hmin : ∀ i, m ≤ ((S i).card:ℝ)) :
    let W := ∑ i, ((S i).card:ℝ)
    let Q := ∑ i, (wheelNormal D i:ℝ)
    m*dualEnergy S D ≤ Q^2 ∧ Q^2 ≤ W*dualEnergy S D := by
  intro W Q
  let q := fun i => (wheelNormal D i:ℝ)
  let n := fun i => ((S i).card:ℝ)
  have qpos (i : Fin (r+1)) : 0 < q i := by
    dsimp [q,wheelNormal]
    exact_mod_cast (Finset.prod_pos fun j _ => hD j)
  have npos i : 0 < n i := by
    change (0 : ℝ) < ((S i).card : ℝ)
    exact_mod_cast (hS i).card_pos
  have qle i : q i ≤ Q := Finset.single_le_sum
    (s := Finset.univ) (f := q) (fun j _ => (qpos j).le) (Finset.mem_univ i)
  constructor
  · change m*(∑ i, q i^2/n i) ≤ Q^2
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ i, q i*Q := by
        apply Finset.sum_le_sum
        intro i _
        calc
          m*(q i^2/n i) ≤ n i*(q i^2/n i) :=
            mul_le_mul_of_nonneg_right (hmin i) (by positivity)
          _ = q i^2 := by field_simp [(npos i).ne']
          _ ≤ q i*Q := by rw [pow_two]; exact mul_le_mul_of_nonneg_left (qle i) (qpos i).le
      _ = Q^2 := by rw [← Finset.sum_mul]; change Q*Q=Q^2; ring
  · change (∑ i, q i)^2 ≤ (∑ i, n i)*(∑ i, q i^2/n i)
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    · intro i _; exact (npos i).le
    · intro i _; positivity
    · intro i _
      apply le_of_eq
      field_simp [(npos i).ne']

/-- Raw log determinant of the literal anchor plus the original star. -/
def anchorVolume {r : ℕ} (S : Fin (r+1) → Finset ℕ)
    (D : Fin (r+1) → ℕ) : ℝ :=
  Real.log (WheelNNS.coDiv (anchoredColumns S D (fun _ => 1))).det / 2

/-- The independently bounded angular correction for a single profile.
The normal ratio Q²/dualEnergy is between m and W. -/
def angleLog {r : ℕ} (S : Fin (r+1) → Finset ℕ)
    (D : Fin (r+1) → ℕ) : ℝ :=
  Real.log ((∑ i, (wheelNormal D i:ℝ))^2/dualEnergy S D)/2

theorem angleLog_bounds {r : ℕ} (S : Fin (r+1) → Finset ℕ)
    (D : Fin (r+1) → ℕ) (hS : ∀ i, (S i).Nonempty)
    (hD : ∀ i, 0 < D i) (m : ℝ) (hm : 0 < m)
    (hmin : ∀ i, m ≤ ((S i).card:ℝ)) :
    angleLog S D ∈ Set.Icc (Real.log m/2)
      (Real.log (∑ i, ((S i).card:ℝ))/2) := by
  obtain ⟨hl,hu⟩ := normal_angle_bounds S D hS hD m hm hmin
  have hE := dualEnergy_pos S D hS hD
  have lo := (le_div_iff₀ hE).2 hl
  have hi := (div_le_iff₀ hE).2 hu
  exact ⟨div_le_div_of_nonneg_right (Real.log_le_log hm lo) (by norm_num),
    div_le_div_of_nonneg_right (Real.log_le_log (hm.trans_le lo) hi) (by norm_num)⟩

/-- Anchor log volumes differ from the existing relative star log
volumes by exactly the difference of the two angular corrections. -/
theorem anchor_relative {r : ℕ} (S : Fin (r+1) → Finset ℕ)
    (D E : Fin (r+1) → ℕ) (hS : ∀ i, (S i).Nonempty)
    (hD : ∀ i, 0 < D i) (hE : ∀ i, 0 < E i) :
    anchorVolume S D-anchorVolume S E =
      logVolume S D-logVolume S E+angleLog S D-angleLog S E := by
  let Q (d : Fin (r+1) → ℕ) := ∑ i, (wheelNormal d i:ℝ)
  let L := ∏ i, ((S i).card:ℝ)
  have hL : 0 < L := Finset.prod_pos fun i _ => by exact_mod_cast (hS i).card_pos
  have hQ (d : Fin (r+1) → ℕ) (hd : ∀ i, 0 < d i) : 0 < Q d := by
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro i _
    exact_mod_cast (Finset.prod_pos fun j _ => hd j)
  have v (d : Fin (r+1) → ℕ) (hd : ∀ i, 0 < d i) :
      anchorVolume S d = Real.log L/2+Real.log (Q d) := by
    unfold anchorVolume
    rw [augmented_det S d hd]
    simp only [mul_one]
    change Real.log (L*(Q d)^2)/2=_
    rw [Real.log_mul hL.ne' (pow_ne_zero _ (hQ d hd).ne'),Real.log_pow]
    ring
  have a (d : Fin (r+1) → ℕ) (hd : ∀ i, 0 < d i) :
      angleLog S d = Real.log (Q d)-Real.log (dualEnergy S d)/2 := by
    unfold angleLog
    change Real.log ((Q d)^2/dualEnergy S d)/2=_
    rw [Real.log_div (pow_ne_zero _ (hQ d hd).ne') (dualEnergy_pos S d hS hd).ne',Real.log_pow]
    ring
  have cD := complementaryLog_eq S D hS hD
  have cE := complementaryLog_eq S E hS hE
  simp only [complementaryLog,one_div,Real.log_inv] at cD cE
  rw [v D hD,v E hE,a D hD,a E hE]
  linarith only [cD,cE]

/-- On the actual same physical rows, the new comparison differs
from G_x's original summand by at most half the log aspect ratio.
This price is independent of all Euler depths. -/
theorem anchor_relative_price {r : ℕ} (S : Fin (r+1) → Finset ℕ)
    (D E : Fin (r+1) → ℕ) (hS : ∀ i, (S i).Nonempty)
    (hD : ∀ i, 0 < D i) (hE : ∀ i, 0 < E i) (m : ℝ) (hm : 0 < m)
    (hmin : ∀ i, m ≤ ((S i).card:ℝ)) :
    |(anchorVolume S D-anchorVolume S E)-
      (logVolume S D-logVolume S E)| ≤
        (Real.log (∑ i, ((S i).card:ℝ))-Real.log m)/2 := by
  have h1 := angleLog_bounds S D hS hD m hm hmin
  have h2 := angleLog_bounds S E hS hE m hm hmin
  rw [anchor_relative S D E hS hD hE]
  apply abs_le.mpr
  exact ⟨by linarith only [h1.1,h2.2],by linarith only [h1.2,h2.1]⟩

/-- The unsigned profile is the coordinatewise maximum of the actual
two profiles, not a free reference whose determinant is assumed to be one. -/
def commonProfile {r : ℕ} (D E : Fin (r+1) → ℕ) : Fin (r+1) → ℕ :=
  fun i => max (D i) (E i)

def liftedVolume {r : ℕ} (S : Fin (r+1) → Finset ℕ)
    (M D : Fin (r+1) → ℕ) : ℝ :=
  Real.log (WheelNNS.coDiv (observations
    (anchoredColumns S M (fun _ => 1))
    (anchoredColumns S D (fun _ => 1)))).det/2

private theorem anchor_det_ne {r : ℕ} (S : Fin (r+1) → Finset ℕ)
    (D : Fin (r+1) → ℕ) (hS : ∀ i, (S i).Nonempty)
    (hD : ∀ i, 0 < D i) :
    (WheelNNS.coDiv (anchoredColumns S D (fun _ => 1))).det ≠ 0 := by
  rw [augmented_det S D hD]
  have hq (i : Fin (r+1)) : 0 < (wheelNormal D i:ℝ) := by
    exact_mod_cast (Finset.prod_pos fun j _ => hD j)
  have hQ : 0 < ∑ i, (wheelNormal D i:ℝ)*1 :=
    Finset.sum_pos (fun i _ => by simpa using hq i) Finset.univ_nonempty
  have hL : 0 < ∏ i, ((S i).card:ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast (hS i).card_pos
  exact (mul_pos hL (sq_pos_of_pos hQ)).ne'

theorem lifted_relative {r : ℕ} (S : Fin (r+1) → Finset ℕ)
    (D E : Fin (r+1) → ℕ) (hS : ∀ i, (S i).Nonempty)
    (hD : ∀ i, 0 < D i) (hE : ∀ i, 0 < E i) :
    liftedVolume S (commonProfile D E) D-liftedVolume S (commonProfile D E) E =
      anchorVolume S D-anchorVolume S E := by
  have hM : ∀ i, 0 < commonProfile D E i :=
    fun i => (hD i).trans_le (le_max_left _ _)
  have h := relative_log (anchoredColumns S (commonProfile D E) (fun _ => 1))
    (anchoredColumns S D (fun _ => 1)) (anchoredColumns S E (fun _ => 1))
    (anchor_det_ne S _ hS hM) (anchor_det_ne S _ hS hD) (anchor_det_ne S _ hS hE)
  unfold liftedVolume anchorVolume
  linarith only [h]

/-- Exact local handoff to G_x's original volume difference. -/
theorem lifted_relative_price {r : ℕ} (S : Fin (r+1) → Finset ℕ)
    (D E : Fin (r+1) → ℕ) (hS : ∀ i, (S i).Nonempty)
    (hD : ∀ i, 0 < D i) (hE : ∀ i, 0 < E i) (m : ℝ) (hm : 0 < m)
    (hmin : ∀ i, m ≤ ((S i).card:ℝ)) :
    |(liftedVolume S (commonProfile D E) D-liftedVolume S (commonProfile D E) E)-
      (logVolume S D-logVolume S E)| ≤
        (Real.log (∑ i, ((S i).card:ℝ))-Real.log m)/2 := by
  rw [lifted_relative S D E hS hD hE]
  exact anchor_relative_price S D E hS hD hE m hm hmin

/-- The two actual sums over the original partner sites and translates.
The depth functions are the two integral split-factorial removals in
SIGNED_MOBIUS_SPLIT_COMPENSATION_20261127.md. -/
def originalGx {H : Type*} [AddCommGroup H] [DecidableEq H] [Fintype H]
    (tops T : Finset H) (P : Finset ℕ) (g : ℕ → H) (n : ℕ)
    (a : H → ℝ) (width : H × Fin n → H → ℝ)
    (beta alpha : ℕ → ℕ) (c : ℝ) : ℝ :=
  let V := occupied tops P g
  let p := primeAt tops P g
  let S := fun (s : ↥V) (j : ↥(siteRows T n s.val)) =>
    bands (fun i => a (s.val-g (p s i))/(p s i:ℝ)) (width j.val s.val)
  let k : ℝ := (T.card*n:ℕ)
  6*(∑ s : ↥V, ∑ j : ↥(siteRows T n s.val),
    (logVolume (S s j) (fun i => (p s i)^(beta (p s i))) -
      logVolume (S s j) (fun i => (p s i)^(alpha (p s i)))))/(c*k*tops.card)

def liftedGx {H : Type*} [AddCommGroup H] [DecidableEq H] [Fintype H]
    (tops T : Finset H) (P : Finset ℕ) (g : ℕ → H) (n : ℕ)
    (a : H → ℝ) (width : H × Fin n → H → ℝ)
    (beta alpha : ℕ → ℕ) (c : ℝ) : ℝ :=
  let V := occupied tops P g
  let p := primeAt tops P g
  let S := fun (s : ↥V) (j : ↥(siteRows T n s.val)) =>
    bands (fun i => a (s.val-g (p s i))/(p s i:ℝ)) (width j.val s.val)
  let k : ℝ := (T.card*n:ℕ)
  let D := fun (s : ↥V) i => (p s i)^(beta (p s i))
  let E := fun (s : ↥V) i => (p s i)^(alpha (p s i))
  6*(∑ s : ↥V, ∑ j : ↥(siteRows T n s.val),
    (liftedVolume (S s j) (commonProfile (D s) (E s)) (D s) -
      liftedVolume (S s j) (commonProfile (D s) (E s)) (E s)))/(c*k*tops.card)

/-- Sum the independent correction on the original native incidence
family. The number of translates cancels, and no new tops or signed
rows are inserted into the normalization. -/
theorem originalGx_price {H : Type*} [AddCommGroup H] [DecidableEq H] [Fintype H]
    (tops T : Finset H) (P : Finset ℕ) (g : ℕ → H) (n : ℕ)
    (a : H → ℝ) (width : H × Fin n → H → ℝ)
    (beta alpha : ℕ → ℕ) (c L m : ℝ)
    (hc : 0 < c) (ht : tops.Nonempty) (hT : T.Nonempty) (hn : 0 < n)
    (hm : 0 < m)
    (hp : ∀ s : ↥(occupied tops P g), ∀ i, 0 < primeAt tops P g s i)
    (hS : ∀ s : ↥(occupied tops P g), ∀ j : ↥(siteRows T n s.val), ∀ i,
      (bands (fun i => a (s.val-g (primeAt tops P g s i))/(primeAt tops P g s i:ℝ))
        (width j.val s.val) i).Nonempty)
    (hmin : ∀ s : ↥(occupied tops P g), ∀ j : ↥(siteRows T n s.val), ∀ i,
      m ≤ ((bands (fun i => a (s.val-g (primeAt tops P g s i))/(primeAt tops P g s i:ℝ))
        (width j.val s.val) i).card:ℝ))
    (hL : ∀ s : ↥(occupied tops P g), ∀ j : ↥(siteRows T n s.val),
      (Real.log (∑ i, ((bands (fun i => a (s.val-g (primeAt tops P g s i))/(primeAt tops P g s i:ℝ))
        (width j.val s.val) i).card:ℝ))-Real.log m)/2 ≤ L) :
    |liftedGx tops T P g n a width beta alpha c -
      originalGx tops T P g n a width beta alpha c| ≤
      6*((occupied tops P g).card:ℝ)*L/(c*tops.card) := by
  classical
  let V := occupied tops P g
  let p := primeAt tops P g
  let S := fun (s : ↥V) (j : ↥(siteRows T n s.val)) =>
    bands (fun i => a (s.val-g (p s i))/(p s i:ℝ)) (width j.val s.val)
  let D := fun (s : ↥V) i => (p s i)^(beta (p s i))
  let E := fun (s : ↥V) i => (p s i)^(alpha (p s i))
  let k : ℝ := (T.card*n:ℕ)
  let B := fun (s : ↥V) (j : ↥(siteRows T n s.val)) =>
    liftedVolume (S s j) (commonProfile (D s) (E s)) (D s) -
      liftedVolume (S s j) (commonProfile (D s) (E s)) (E s)
  let A := fun (s : ↥V) (j : ↥(siteRows T n s.val)) =>
    logVolume (S s j) (D s)-logVolume (S s j) (E s)
  have kt : 0 < k := by
    change (0 : ℝ) < ((T.card * n : ℕ) : ℝ)
    exact_mod_cast Nat.mul_pos hT.card_pos hn
  have tt : (0:ℝ) < tops.card := by exact_mod_cast ht.card_pos
  have pos : 0 < c*k*tops.card := mul_pos (mul_pos hc kt) tt
  have bound (s : ↥V) (j : ↥(siteRows T n s.val)) : |B s j-A s j| ≤ L :=
    (lifted_relative_price (S s j) (D s) (E s) (hS s j)
      (fun i => pow_pos (hp s i) _) (fun i => pow_pos (hp s i) _)
      m hm (hmin s j)).trans (hL s j)
  have total : |∑ s : ↥V, ∑ j : ↥(siteRows T n s.val), (B s j-A s j)| ≤
      (V.card:ℝ)*k*L := by
    calc
      _ ≤ ∑ s : ↥V, |∑ j : ↥(siteRows T n s.val), (B s j-A s j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s : ↥V, ∑ j : ↥(siteRows T n s.val), |B s j-A s j| :=
        Finset.sum_le_sum fun s _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s : ↥V, ∑ _j : ↥(siteRows T n s.val), L :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun j _ => bound s j
      _ = _ := by simp [k,siteRows_card,mul_assoc]
  change |6*(∑ s : ↥V, ∑ j : ↥(siteRows T n s.val), B s j)/(c*k*tops.card) -
    6*(∑ s : ↥V, ∑ j : ↥(siteRows T n s.val), A s j)/(c*k*tops.card)| ≤ _
  rw [← sub_div,← mul_sub,abs_div,abs_mul,abs_of_pos pos,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 6),← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ 6*((V.card:ℝ)*k*L)/(c*k*tops.card) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left total (by norm_num)) pos.le
    _ = _ := by field_simp [hc.ne',kt.ne',tt.ne']; ring

end SignSchurHandoff
end RHLean.Analysis.AlpogeThin.SlotProjector

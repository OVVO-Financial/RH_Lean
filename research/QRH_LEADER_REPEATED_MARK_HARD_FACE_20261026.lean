import Mathlib

/-!
# QRH tracker leader: repeated-mark detector has a K-independent HARD face

This is a standalone exact copy of the six rational branch-root formulas
from GTimG/QuasiRiemannTracker, submission
arvi-repeated-marks-on-sil-face-20261025, Gain/Gain.lean.

The actual repeated-mark source proves a per-class gain as the
minimum over these six branches, and finally the infimum over amplitude
classes p in [0,1/2]. In the p=1/2 class, the inverse-cap / affine-plain
branch (i=1,j=2) is independent of both marked-copy count K and slot
width S. Consequently arbitrarily many extra marked copies CANNOT
increase the universal class gain beyond that branch.

The proof below is exact real arithmetic, not a transfer of the
nontrivial fourth-power Hecke moment or a stronger zero-free bound.
The intended *positive* research target is to improve the actual
p=1/2 fourth-power SOURCE FACE or one of the count witnesses that
creates this branch, preserving its labelled ideals and phases.
-/

noncomputable section
namespace RHLean.Analysis

def qrhLeadInvSlope (p : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then 1 else 1 / (1 - p)

def qrhLeadInvOffset (p K S Q : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then -(2 * p * K * S) else -(p * Q / (1 - p))

def qrhLeadPlainSlope (p lam : ℝ) (j : Fin 3) : ℝ :=
  if j = 2 then 1 / (1 - 2 * p / lam) else 1

def qrhLeadPlainOffset (p B lam h S Q : ℝ) (j : Fin 3) : ℝ :=
  if j = 0 then -(2 * p * S)
  else if j = 1 then -(2 * p * h * Q)
  else -(2 * p * B * Q / lam / (1 - 2 * p / lam))

/-- One of the six original source detector roots. -/
def qrhLeadRoot (nu p K B lam h S Q : ℝ) (ij : Fin 2 × Fin 3) : ℝ :=
  (5 * Q - (5 - 6 * nu) *
      (qrhLeadInvOffset p K S Q ij.1 +
       qrhLeadPlainOffset p B lam h S Q ij.2 / 2)) /
    (6 * nu + (5 - 6 * nu) *
      (qrhLeadInvSlope p ij.1 + qrhLeadPlainSlope p lam ij.2 / 2))

/-- The original *per-amplitude-class* repeated-mark detector gain.
This is the infimum of the six rational branch-root faces. -/
def qrhLeadClassGain (nu p K B lam h S Q : ℝ) : ℝ :=
  (1 - 2 * p) * nu * S +
    nu * ((Finset.univ.inf' Finset.univ_nonempty
       (qrhLeadRoot nu p K B lam h S Q)) -
      (10 / (15 - 6 * nu)) * Q)

/-- The p=1/2 inverse-cap/affine-plain face alone. This expression
contains no mark-copy count, slot width, or parent's height. -/
def qrhLeadAffineCap (nu B lam Q : ℝ) : ℝ :=
  nu * (qrhLeadRoot nu (1 / 2) 0 B lam 0 0 Q (1, 2) -
    (10 / (15 - 6 * nu)) * Q)

theorem qrhLead_affine_face_independent_of_copies
    (nu p K K' B lam h h' S S' Q : ℝ) :
    qrhLeadRoot nu p K B lam h S Q (1, 2) =
      qrhLeadRoot nu p K' B lam h' S' Q (1, 2) := by
  simp [qrhLeadRoot, qrhLeadInvOffset, qrhLeadPlainOffset,
    qrhLeadInvSlope, qrhLeadPlainSlope]

/-- The actual six-branch p=1/2 gain cannot exceed the
K-independent affine cap, no matter how many marks are inserted. -/
theorem qrhLead_half_amplitude_gain_le_cap
    (nu K B lam h S Q : ℝ) (hnu : 0 ≤ nu) :
    qrhLeadClassGain nu (1 / 2) K B lam h S Q ≤
      qrhLeadAffineCap nu B lam Q := by
  have hmin :
      (Finset.univ.inf' Finset.univ_nonempty
          (qrhLeadRoot nu (1 / 2) K B lam h S Q)) ≤
        qrhLeadRoot nu (1 / 2) K B lam h S Q (1, 2) :=
    Finset.inf'_le _ (Finset.mem_univ _)
  have hscaled :=
    mul_le_mul_of_nonneg_left
      (sub_le_sub_right hmin ((10 / (15 - 6 * nu)) * Q)) hnu
  calc
    qrhLeadClassGain nu (1 / 2) K B lam h S Q =
      nu * ((Finset.univ.inf' Finset.univ_nonempty
           (qrhLeadRoot nu (1 / 2) K B lam h S Q)) -
        (10 / (15 - 6 * nu)) * Q) := by
          simp [qrhLeadClassGain]
    _ ≤ nu * (qrhLeadRoot nu (1 / 2) K B lam h S Q (1, 2) -
        (10 / (15 - 6 * nu)) * Q) := hscaled
    _ = qrhLeadAffineCap nu B lam Q := by
        rw [qrhLead_affine_face_independent_of_copies nu (1 / 2)
          K 0 B lam h 0 S 0 Q]
        rfl

/-- For *any* global detector gain bounded above by the p=1/2
class, the same cap applies. This is the precise abstract transfer
to the original infimum over amplitude classes. -/
theorem qrhLead_global_gain_le_affine_cap
    (nu K B lam h S Q gain : ℝ)
    (hnu : 0 ≤ nu)
    (hclass : gain ≤ qrhLeadClassGain nu (1 / 2) K B lam h S Q) :
    gain ≤ qrhLeadAffineCap nu B lam Q :=
  hclass.trans (qrhLead_half_amplitude_gain_le_cap nu K B lam h S Q hnu)

/-- The exact parent physical face from the tracker leader, at its
terminal density nu=(149843/200000); the universal cap is <1/290.
The chosen rational 1/290 is a *ceiling*, not an obtained saving. -/
theorem qrhLead_record_parent_affine_cap_lt :
    qrhLeadAffineCap (149843 / 200000)
      (335106151738000623869543064163 / 344806846470553600000000000000)
      (631360617375411063383 / 210453397504000000000) 1 <
        (1 / 290 : ℝ) := by
  norm_num [qrhLeadAffineCap, qrhLeadRoot,
    qrhLeadInvSlope, qrhLeadInvOffset,
    qrhLeadPlainSlope, qrhLeadPlainOffset]

#print axioms qrhLead_affine_face_independent_of_copies
#print axioms qrhLead_half_amplitude_gain_le_cap
#print axioms qrhLead_global_gain_le_affine_cap
#print axioms qrhLead_record_parent_affine_cap_lt

end RHLean.Analysis

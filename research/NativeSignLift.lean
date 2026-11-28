import Mathlib

/-! Native signed lifts in the integral sum/representative coordinates.
The symmetric/antisymmetric eigenbasis is not unimodular at 2. Instead
use the primitive kernel of summation and its integral quotient, with
a triangular rather than a diagonal lift. This avoids a spurious 2^d
index on every repeated step. The signed/unsigned volume factors
remain separate; this is not a signed analytic bound. -/

set_option autoImplicit false
noncomputable section

namespace RHLean.Analysis.NativeSignLift

variable {R ι : Type*} [CommRing R] [Fintype ι]

/-- Four positive/negative channels; A and B need not commute. -/
def lift (A B : Matrix ι ι R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  Matrix.fromBlocks A B B A

def evenPath (A B C D : Matrix ι ι R) : Matrix ι ι R := A*C+B*D

def oddPath (A B C D : Matrix ι ι R) : Matrix ι ι R := A*D+B*C

theorem lift_mul (A B C D : Matrix ι ι R) :
    lift A B * lift C D = lift (evenPath A B C D) (oddPath A B C D) := by
  simp only [lift, evenPath, oddPath, Matrix.fromBlocks_multiply]
  rw [add_comm (B*C) (A*D), add_comm (B*D) (A*C)]

/-- The signed path reading survives composition, including all mixed
channels. -/
theorem signed_mul (A B C D : Matrix ι ι R) :
    evenPath A B C D-oddPath A B C D = (A-B)*(C-D) := by
  simp only [evenPath,oddPath,Matrix.sub_mul,Matrix.mul_sub]
  abel

theorem unsigned_mul (A B C D : Matrix ι ι R) :
    evenPath A B C D+oddPath A B C D = (A+B)*(C+D) := by
  simp only [evenPath,oddPath,Matrix.add_mul,Matrix.mul_add]
  abel

variable [DecidableEq ι]

/-- Coordinates (x+y,x), not the half-integral even/odd eigenbasis. -/
def changeBasis : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  Matrix.fromBlocks 1 1 1 0

def restoreBasis : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  Matrix.fromBlocks 0 1 1 (-1)

theorem change_restore :
    (changeBasis : Matrix (ι ⊕ ι) (ι ⊕ ι) R)*restoreBasis = 1 := by
  simp [changeBasis,restoreBasis,Matrix.fromBlocks_multiply,Matrix.fromBlocks_one]

theorem restore_change :
    (restoreBasis : Matrix (ι ⊕ ι) (ι ⊕ ι) R)*changeBasis = 1 := by
  simp [changeBasis,restoreBasis,Matrix.fromBlocks_multiply,Matrix.fromBlocks_one]

/-- These coordinates are integral at every place, including 2.
The quotient coordinate carries A+B; the primitive kernel carries A-B. -/
def triangular (A B : Matrix ι ι R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  Matrix.fromBlocks (A+B) 0 B (A-B)

theorem triangular_intertwine (A B : Matrix ι ι R) :
    changeBasis*lift A B = triangular A B*changeBasis := by
  simp only [changeBasis,lift,triangular,Matrix.fromBlocks_multiply,
    Matrix.one_mul,Matrix.mul_one,Matrix.zero_mul,Matrix.mul_zero,add_zero]
  rw [add_comm B A, show B+(A-B)=A by abel]

theorem triangular_conjugate (A B : Matrix ι ι R) :
    changeBasis*lift A B*restoreBasis = triangular A B := by
  rw [triangular_intertwine,Matrix.mul_assoc,change_restore,Matrix.mul_one]

/-- No factor of 2 occurs in the determinant factorization. -/
theorem lift_det (A B : Matrix ι ι R) :
    (lift A B).det = (A+B).det*(A-B).det := by
  have hp : (changeBasis : Matrix (ι ⊕ ι) (ι ⊕ ι) R).det *
      (restoreBasis : Matrix (ι ⊕ ι) (ι ⊕ ι) R).det = 1 := by
    rw [← Matrix.det_mul,change_restore,Matrix.det_one]
  calc
    _ = (lift A B).det * ((changeBasis : Matrix (ι ⊕ ι) (ι ⊕ ι) R).det *
        (restoreBasis : Matrix (ι ⊕ ι) (ι ⊕ ι) R).det) := by rw [hp,mul_one]
    _ = (changeBasis*lift A B*restoreBasis).det := by
      rw [Matrix.det_mul,Matrix.det_mul]
      ring
    _ = _ := by rw [triangular_conjugate,triangular,Matrix.det_fromBlocks_zero₁₂]

/-- Repeated primitive Euler steps on the same integral carrier, with
U the transported shift on the retained lattice. -/
theorem euler_lift_det (a c : R) (U : Matrix ι ι R) :
    (lift (a • (1 : Matrix ι ι R)) (c • U)).det =
      (a • (1 : Matrix ι ι R)+c • U).det*
      (a • (1 : Matrix ι ι R)-c • U).det :=
  lift_det _ _

end RHLean.Analysis.NativeSignLift

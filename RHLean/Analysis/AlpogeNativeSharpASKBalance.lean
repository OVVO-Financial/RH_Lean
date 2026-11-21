import Mathlib
import RHLean.Analysis.AlpogeNativeFourCharacterArithmetic

/-!
# Alpoge's ASK sharp cutoff rebuilt from NATIVE RHLean von Mangoldt

This is the actual finite arithmetic step of published
FirstPrimeNeSecondPrime -> StronglyIrreducible -> AskMainBalance,
not an import of their proofs or the terminal RH theorem.

For ANY complex coefficient c(n) and a,W>0, a/W<=N, it proves
  sum_(n<=N) c(n) max(a/n-W,0)
   = W sum_(n<=floor(a/W)) c(n) (a/W/n-1).

For the PHYSICAL c(n)=Lambda(n)*chi(n), this becomes
  ASK_chi = W*Gchi(a/W) - a*ell_chi,
where the explicit ell has the meaning of the logarithmic
L-derivative at one (not claimed to be known here).

All terms are finite; true prime powers and zero characters at
ramified primes are retained. No new uniform analytic bound or RH.
-/

noncomputable section
open scoped ArithmeticFunction.vonMangoldt BigOperators
namespace RHLean.Analysis

/-- Exact scale transport; this is the arithmetic identity behind
the positive-part cutoff in Alpoge's ASK source. -/
theorem alpogeNativeKernel_rescale
    (a W : ℝ) (n : ℕ) (hW : W ≠ 0) :
    a / (n : ℝ) - W =
      W * (a / W / (n : ℝ) - 1) := by
  have hWa : W * (a / W) = a := by field_simp
  rw [mul_sub, mul_one, mul_div_assoc', hWa]

/-- Exact N-to-floor(a/W) cutoff with ANY complex arithmetic
coefficient, including the von Mangoldt character prime-power source. -/
theorem alpogeNativeMaxCut_eq_sharp
    (c : ℕ → ℂ) (N : ℕ) (a W : ℝ)
    (ha : 0 < a) (hW : 0 < W) (hN : a / W ≤ (N : ℝ)) :
    (∑ n ∈ Finset.Icc 1 N,
      c n * ((max (a / (n : ℝ) - W) 0 : ℝ) : ℂ)) =
    ∑ n ∈ Finset.Icc 1 ⌊a / W⌋₊,
      c n * ((a / (n : ℝ) - W : ℝ) : ℂ) := by
  have hMN : ⌊a / W⌋₊ ≤ N := by
    have h1 : ((⌊a / W⌋₊ : ℕ) : ℝ) ≤ N :=
      (Nat.floor_le (by positivity)).trans hN
    exact_mod_cast h1
  have hterm :
      ∀ n ∈ Finset.Icc 1 N,
        c n * ((max (a / (n : ℝ) - W) 0 : ℝ) : ℂ) =
        if n ≤ ⌊a / W⌋₊ then
          c n * ((a / (n : ℝ) - W : ℝ) : ℂ)
        else 0 := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by
      exact_mod_cast (Finset.mem_Icc.1 hn).1
    have hn0 : (0 : ℝ) < n := by linarith
    split_ifs with h
    · have h2 : (n : ℝ) ≤ a / W :=
        (Nat.le_floor_iff (by positivity)).1 h
      rw [le_div_iff₀ hW] at h2
      have h3 : W ≤ a / n := by
        rw [le_div_iff₀ hn0]
        nlinarith [mul_comm W (n : ℝ)]
      rw [max_eq_left (by linarith)]
    · have h2 : a / W < n :=
        (Nat.floor_lt (by positivity)).1 (not_le.1 h)
      rw [div_lt_iff₀ hW] at h2
      have h3 : a / n < W := by
        rw [div_lt_iff₀ hn0]
        nlinarith [mul_comm W (n : ℝ)]
      rw [max_eq_right (by linarith)]
      simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2.trans hMN⟩, h2⟩

/-- An exact finite source transport back to the original Alpoge
triangular kernel x/n-1. Not an asymptotic approximation. -/
theorem alpogeNativeMaxCut_eq_weightedSource
    (c : ℕ → ℂ) (N : ℕ) (a W : ℝ)
    (ha : 0 < a) (hW : 0 < W) (hN : a / W ≤ (N : ℝ)) :
    (∑ n ∈ Finset.Icc 1 N,
      c n * ((max (a / (n : ℝ) - W) 0 : ℝ) : ℂ)) =
      (W : ℂ) * ∑ n ∈ Finset.Icc 1 ⌊a / W⌋₊,
        c n * (((a / W) / (n : ℝ) - 1 : ℝ) : ℂ) := by
  rw [alpogeNativeMaxCut_eq_sharp c N a W ha hW hN,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [alpogeNativeKernel_rescale a W n hW.ne']
  push_cast
  ring

/-- The fully physical selected ASK: the character is genuinely
multiplicative, with all prime powers present. -/
def alpogeNativeSharpASK {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (N : ℕ) (a W : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    ((Λ n : ℝ) : ℂ) * χ n *
      ((max (a / (n : ℝ) - W) 0 : ℝ) : ℂ)

/-- Exact native arithmetic analogue of Alpoge's inner character
identity, with every logarithmic-derivative constant explicit. -/
theorem alpogeNativeSharpASK_eq_weightedGchi
    {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (ell : ℂ)
    (N : ℕ) (a W : ℝ)
    (ha : 0 < a) (hW : 0 < W) (hN : a / W ≤ (N : ℝ)) :
    alpogeNativeSharpASK χ N a W =
      (W : ℂ) * alpogeNativeGchiArithmetic χ ell (a / W) -
        (a : ℂ) * ell := by
  have hwa : W * (a / W) = a := by field_simp
  have hwaC : (W : ℂ) * ((a / W : ℝ) : ℂ) = (a : ℂ) := by
    rw [← Complex.ofReal_mul, hwa]
  have hsource := alpogeNativeMaxCut_eq_weightedSource
    (fun n => ((Λ n : ℝ) : ℂ) * χ n) N a W ha hW hN
  have htwist :
      (∑ n ∈ Finset.Icc 1 ⌊a / W⌋₊,
          ((Λ n : ℝ) : ℂ) * χ n *
            (((a / W) / (n : ℝ) - 1 : ℝ) : ℂ)) =
      alpogeNativeTwistedPrimeSum χ (a / W) := by
    unfold alpogeNativeTwistedPrimeSum
    apply Finset.sum_congr rfl
    intro n _hn
    unfold alpogeNativePrimePowerWeight
    push_cast
    ring
  calc
    alpogeNativeSharpASK χ N a W =
        (W : ℂ) * ∑ n ∈ Finset.Icc 1 ⌊a / W⌋₊,
          ((Λ n : ℝ) : ℂ) * χ n *
            (((a / W) / (n : ℝ) - 1 : ℝ) : ℂ) := by
              simpa only [alpogeNativeSharpASK] using hsource
    _ = (W : ℂ) * alpogeNativeTwistedPrimeSum χ (a / W) := by
      rw [htwist]
    _ = (W : ℂ) * alpogeNativeGchiArithmetic χ ell (a / W) -
          (a : ℂ) * ell := by
      unfold alpogeNativeGchiArithmetic
      rw [mul_add, ← mul_assoc, hwaC]
      ring

/-- ASK averaged over any finite weighted physical owner group,
with no independence, generic geometry or character error assumed. -/
theorem alpogeNativeSharpASK_family_eq_Gchi
    {q : ℕ} [NeZero q] {ι : Type*}
    (S : Finset ι) (χ : DirichletCharacter ℂ q)
    (ell : ℂ) (N : ℕ) (a : ℝ) (w : ι → ℝ)
    (ha : 0 < a)
    (hw : ∀ j ∈ S, 0 < w j)
    (hN : ∀ j ∈ S, a / w j ≤ (N : ℝ)) :
    (∑ j ∈ S, alpogeNativeSharpASK χ N a (w j)) =
      ∑ j ∈ S, ((w j : ℂ) * alpogeNativeGchiArithmetic χ ell (a / w j)
        - (a : ℂ) * ell) := by
  apply Finset.sum_congr rfl
  intro j hj
  exact alpogeNativeSharpASK_eq_weightedGchi
    χ ell N a (w j) ha (hw j hj) (hN j hj)



/-!
## Native complete positive ASK, not an abstract character interface

The exact finite four-character projector is attached to Alpoge's
SHARP ASK physical kernel at every integer. For genuine quadratic
Dirichlet characters the WHOLE trace is proved nonnegative,
including every ramified prime-power return.
-/

/-- Original positive-part ASK, retaining actual Λ on every prime
power, actual multiplicative characters and the sharp a/n-W weight. -/
def alpogeNativeFourSharpASK {q : ℕ} [NeZero q]
    (χA χB : DirichletCharacter ℂ q)
    (N : ℕ) (a W : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    ((Λ n : ℝ) : ℂ) *
      alpogeNativeFourCharacterKernel χA χB n *
        ((max (a / (n : ℝ) - W) 0 : ℝ) : ℂ)

/-- Every integer of the FULL native four-channel ASK is transported
to the original unrounded Gsig prime-power source, with zero dropped
prime powers or threshold endpoints. -/
theorem alpogeNativeFourSharpASK_eq_weightedTrace
    {q : ℕ} [NeZero q]
    (χA χB : DirichletCharacter ℂ q)
    (N : ℕ) (a W : ℝ)
    (ha : 0 < a) (hW : 0 < W) (hN : a / W ≤ (N : ℝ)) :
    alpogeNativeFourSharpASK χA χB N a W =
      (W : ℂ) * alpogeNativeFourCharacterTrace χA χB (a / W) := by
  have hbase := alpogeNativeMaxCut_eq_weightedSource
    (fun n => ((Λ n : ℝ) : ℂ) *
      alpogeNativeFourCharacterKernel χA χB n)
    N a W ha hW hN
  unfold alpogeNativeFourSharpASK
  rw [hbase]
  unfold alpogeNativeFourCharacterTrace
  congr 1
  apply Finset.sum_congr rfl
  intro n _hn
  unfold alpogeNativePrimePowerWeight
  push_cast
  ring

/-- The actual quadratic sharp ASK has an unconditional fixed
nonnegative sign. The proof uses the FULL source and a real positive
physical weight, not a postulated ASK=MAIN or an assumed error bound. -/
theorem alpogeNativeFourSharpASK_re_nonneg
    {q : ℕ} [NeZero q]
    (χA χB : DirichletCharacter ℂ q)
    (hA : χA ^ 2 = 1) (hB : χB ^ 2 = 1)
    (N : ℕ) (a W : ℝ)
    (ha : 0 < a) (hW : 0 < W) (hN : a / W ≤ (N : ℝ)) :
    0 ≤ (alpogeNativeFourSharpASK χA χB N a W).re := by
  rw [alpogeNativeFourSharpASK_eq_weightedTrace χA χB N a W ha hW hN]
  have hpos : 0 ≤
      (alpogeNativeFourCharacterTrace χA χB (a / W)).re :=
    alpogeNativeFourTrace_quadratic_re_nonneg χA χB hA hB (a / W)
      (le_of_lt (div_pos ha hW))
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact mul_nonneg (le_of_lt hW) hpos

/-- The full, source-faithful positive ASK is 4 times its selected
quadratic class plus the SAME paid ramified mass as the character
trace. Nothing is discarded in the weight transport. -/
theorem alpogeNativeFourSharpASK_eq_selected_plus_ramified
    {q : ℕ} [NeZero q]
    (χA χB : DirichletCharacter ℂ q)
    (hA : χA ^ 2 = 1) (hB : χB ^ 2 = 1)
    (N : ℕ) (a W : ℝ)
    (ha : 0 < a) (hW : 0 < W) (hN : a / W ≤ (N : ℝ)) :
    alpogeNativeFourSharpASK χA χB N a W =
      (W : ℂ) * (4 * alpogeNativeFourSelected χA χB (a / W) +
        (alpogeNativeRamifiedPrimePowerMass q (a / W) : ℂ)) := by
  rw [alpogeNativeFourSharpASK_eq_weightedTrace χA χB N a W ha hW hN,
    alpogeNativeFourTrace_quadratic_exact χA χB hA hB]


/-!
## Original Frobenius/inertia character source (no external theorem imported)

Alpoge's primVal is NOT an ordinary DirichletCharacter. It averages an
additive character over the actual inertia subgroup of a finite
Frobenius group, then multiplies these local means over n.primeFactors.
The definitions below reconstruct precisely that arithmetic operation
using the same native Lambda(n) and sharp a/n-W cutoff as above.
-/

/-- Original inertia-coset average, with the entire inertia subgroup
retained even at ramified primes. -/
def alpogeNativeInertiaCosetMean
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (I : AddSubgroup G) (a : G) (ψ : AddChar G ℂ) : ℂ := by
  classical
  exact (∑ u ∈ (Finset.univ.filter (fun u : G => u ∈ I)),
    ψ (a + u)) /
      (((Finset.univ.filter (fun u : G => u ∈ I)).card : ℕ) : ℂ)

/-- Exact Frobenius character times its full inertia projector.
This identity does not assume the prime is unramified, and it does
not silently turn a ramified character value into zero. -/
theorem alpogeNativeInertiaCosetMean_split
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (I : AddSubgroup G) (a : G) (ψ : AddChar G ℂ) :
    alpogeNativeInertiaCosetMean I a ψ =
      ψ a * alpogeNativeInertiaCosetMean I 0 ψ := by
  classical
  unfold alpogeNativeInertiaCosetMean
  simp only [zero_add]
  calc
    (∑ u ∈ (Finset.univ.filter (fun u : G => u ∈ I)),
        ψ (a + u)) /
        (((Finset.univ.filter (fun u : G => u ∈ I)).card : ℕ) : ℂ) =
      (ψ a * (∑ u ∈ (Finset.univ.filter (fun u : G => u ∈ I)),
        ψ u)) /
        (((Finset.univ.filter (fun u : G => u ∈ I)).card : ℕ) : ℂ) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u _hu
          exact AddChar.map_add_eq_mul ψ a u
    _ = _ := by ring

/-- Unramified inertia is the zero subgroup; its character mean is
the actual Frobenius value, not an additional character hypothesis. -/
theorem alpogeNativeInertiaCosetMean_unramified
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (a : G) (ψ : AddChar G ℂ) :
    alpogeNativeInertiaCosetMean (⊥ : AddSubgroup G) a ψ = ψ a := by
  classical
  have hset :
      (Finset.univ.filter (fun u : G => u ∈ (⊥ : AddSubgroup G))) = {0} := by
    ext u
    simp
  unfold alpogeNativeInertiaCosetMean
  rw [hset]
  simp

/-- Reconstructed original primVal(D,ψ,n): the complete product of
inertia-coset means on n's physical prime factors. -/
def alpogeNativeFrobInertiaPrimeValue
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (inertia : ℕ → AddSubgroup G) (frob : ℕ → G)
    (ψ : AddChar G ℂ) (n : ℕ) : ℂ :=
  ∏ p ∈ n.primeFactors,
    alpogeNativeInertiaCosetMean (inertia p)
      (n.factorization p • frob p) ψ

/-- On a genuine prime power, the multiplicative native valuation
is exactly Alpoge's one Frobenius/inertia coset mean. -/
theorem alpogeNativeFrobInertiaPrimeValue_primePower
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (inertia : ℕ → AddSubgroup G) (frob : ℕ → G)
    (ψ : AddChar G ℂ) (p i : ℕ)
    (hp : p.Prime) (hi : 0 < i) :
    alpogeNativeFrobInertiaPrimeValue inertia frob ψ (p ^ i) =
      alpogeNativeInertiaCosetMean (inertia p) (i • frob p) ψ := by
  have hpf : (p ^ i).primeFactors = {p} := by
    rw [Nat.primeFactors_pow p hi.ne']
    simp [hp]
  simp [alpogeNativeFrobInertiaPrimeValue, hpf,
    hp.factorization_self]

/-- Physical prime-power GPsi source, before the L-derivative main
term and before any geometric height or width bound is applied. -/
def alpogeNativeFrobInertiaPrimeSum
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (inertia : ℕ → AddSubgroup G) (frob : ℕ → G)
    (ψ : AddChar G ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
    ((Λ n : ℝ) : ℂ) *
      alpogeNativeFrobInertiaPrimeValue inertia frob ψ n *
        (((x / (n : ℝ) - 1 : ℝ)) : ℂ)

/-- The genuine sharp ASK over native von Mangoldt and Frobenius/
inertia coset coefficients. No replaced Dirichlet projector. -/
def alpogeNativeFrobInertiaASK
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (inertia : ℕ → AddSubgroup G) (frob : ℕ → G)
    (ψ : AddChar G ℂ) (N : ℕ) (a W : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    (((Λ n : ℝ) : ℂ) *
      alpogeNativeFrobInertiaPrimeValue inertia frob ψ n) *
        (((max (a / (n : ℝ) - W) 0 : ℝ)) : ℂ)

/-- Exact original Frobenius/inertia GPsi-to-ASK transport on the
complete physical prime-power population, with no statistical
cancellation, assumed geometry or imported theorem. -/
theorem alpogeNativeFrobInertiaASK_eq_primeSum
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (inertia : ℕ → AddSubgroup G) (frob : ℕ → G)
    (ψ : AddChar G ℂ) (N : ℕ) (a W : ℝ)
    (ha : 0 < a) (hW : 0 < W) (hN : a / W ≤ (N : ℝ)) :
    alpogeNativeFrobInertiaASK inertia frob ψ N a W =
      (W : ℂ) *
        alpogeNativeFrobInertiaPrimeSum inertia frob ψ (a / W) := by
  simpa only [alpogeNativeFrobInertiaASK,
    alpogeNativeFrobInertiaPrimeSum, mul_assoc] using
    (alpogeNativeMaxCut_eq_weightedSource
      (fun n => ((Λ n : ℝ) : ℂ) *
        alpogeNativeFrobInertiaPrimeValue inertia frob ψ n)
      N a W ha hW hN)


/-- Native reconstruction of published GPsi: its principal mode is the
literal native Gz, and its other modes retain the full Frobenius/inertia
prime-power source plus their analytic logarithmic-derivative constant.
No estimate on that constant is asserted. -/
def alpogeNativeFrobInertiaGPsi
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (inertia : ℕ → AddSubgroup G) (frob : ℕ → G)
    (ell : AddChar G ℂ → ℂ) (ψ : AddChar G ℂ) (x : ℝ) : ℂ := by
  classical
  exact if ψ = 0 then (alpogeNativeGzArithmetic x : ℂ)
    else alpogeNativeFrobInertiaPrimeSum inertia frob ψ x +
      (x : ℂ) * ell ψ

theorem alpogeNativeFrobInertiaGPsi_principal
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (inertia : ℕ → AddSubgroup G) (frob : ℕ → G)
    (ell : AddChar G ℂ → ℂ) (x : ℝ) :
    alpogeNativeFrobInertiaGPsi inertia frob ell 0 x =
      (alpogeNativeGzArithmetic x : ℂ) := by
  classical
  simp [alpogeNativeFrobInertiaGPsi]

theorem alpogeNativeFrobInertiaGPsi_nonprincipal
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (inertia : ℕ → AddSubgroup G) (frob : ℕ → G)
    (ell : AddChar G ℂ → ℂ) (ψ : AddChar G ℂ) (x : ℝ)
    (hψ : ψ ≠ 0) :
    alpogeNativeFrobInertiaGPsi inertia frob ell ψ x =
      alpogeNativeFrobInertiaPrimeSum inertia frob ψ x +
        (x : ℂ) * ell ψ := by
  classical
  simp [alpogeNativeFrobInertiaGPsi, hψ]

/-- The original ASK-to-GPsi identity, with the full Frobenius/inertia
prime-power source and the exact ell correction, proved directly. -/
theorem alpogeNativeFrobInertiaASK_eq_GPsi_nonprincipal
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (inertia : ℕ → AddSubgroup G) (frob : ℕ → G)
    (ell : AddChar G ℂ → ℂ) (ψ : AddChar G ℂ)
    (N : ℕ) (a W : ℝ) (hψ : ψ ≠ 0)
    (ha : 0 < a) (hW : 0 < W) (hN : a / W ≤ (N : ℝ)) :
    alpogeNativeFrobInertiaASK inertia frob ψ N a W =
      (W : ℂ) * alpogeNativeFrobInertiaGPsi inertia frob ell ψ (a / W) -
        (a : ℂ) * ell ψ := by
  have hWa : W * (a / W) = a := by field_simp
  have hWaC : (W : ℂ) * ((a / W : ℝ) : ℂ) = (a : ℂ) := by
    rw [← Complex.ofReal_mul, hWa]
  calc
    alpogeNativeFrobInertiaASK inertia frob ψ N a W =
        (W : ℂ) * alpogeNativeFrobInertiaPrimeSum inertia frob ψ (a / W) :=
      alpogeNativeFrobInertiaASK_eq_primeSum inertia frob ψ N a W ha hW hN
    _ = (W : ℂ) * alpogeNativeFrobInertiaGPsi inertia frob ell ψ (a / W) -
          (a : ℂ) * ell ψ := by
      rw [alpogeNativeFrobInertiaGPsi_nonprincipal inertia frob ell ψ (a / W) hψ]
      rw [mul_add, ← mul_assoc, hWaC]
      ring

/-- The exact four-character Gsig used in the published proof, now
using original additive-character Frobenius/inertia values rather than
ordinary Dirichlet characters at exceptional primes. -/
def alpogeNativeFrobInertiaGsig
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (inertia : ℕ → AddSubgroup G) (frob : ℕ → G)
    (ell : AddChar G ℂ → ℂ)
    (ψA ψB : AddChar G ℂ) (x : ℝ) : ℂ :=
  alpogeNativeFrobInertiaGPsi inertia frob ell 0 x +
    alpogeNativeFrobInertiaGPsi inertia frob ell ψB x -
    alpogeNativeFrobInertiaGPsi inertia frob ell ψA x -
    alpogeNativeFrobInertiaGPsi inertia frob ell (ψA + ψB) x

/-- All FOUR actual character channels, including the principal Gz
and every ramified Frobenius/inertia prime power, with the ell constants
retained exactly rather than bounded or discarded. -/
theorem alpogeNativeFrobInertiaGsig_eq_complete
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (inertia : ℕ → AddSubgroup G) (frob : ℕ → G)
    (ell : AddChar G ℂ → ℂ)
    (ψA ψB : AddChar G ℂ) (x : ℝ)
    (hA : ψA ≠ 0) (hB : ψB ≠ 0)
    (hAB : ψA + ψB ≠ 0) :
    alpogeNativeFrobInertiaGsig inertia frob ell ψA ψB x =
      (alpogeNativeGzArithmetic x : ℂ) +
        alpogeNativeFrobInertiaPrimeSum inertia frob ψB x -
        alpogeNativeFrobInertiaPrimeSum inertia frob ψA x -
        alpogeNativeFrobInertiaPrimeSum inertia frob (ψA + ψB) x +
        (x : ℂ) * (ell ψB - ell ψA - ell (ψA + ψB)) := by
  rw [alpogeNativeFrobInertiaGsig,
    alpogeNativeFrobInertiaGPsi_principal,
    alpogeNativeFrobInertiaGPsi_nonprincipal inertia frob ell ψB x hB,
    alpogeNativeFrobInertiaGPsi_nonprincipal inertia frob ell ψA x hA,
    alpogeNativeFrobInertiaGPsi_nonprincipal inertia frob ell (ψA + ψB) x hAB]
  ring


/-!
## Original finite Fourier orthogonality, for the entire inertia coset

This is the source of Alpoge's unramified/ramified dichotomy.
It is a theorem about actual additive characters and the actual
inertia subgroup, not an independent prime-colour hypothesis.
-/

/-- A complete dual-character sum detects equality on the finite
additive Frobenius group, including both exceptional prime classes. -/
theorem alpogeNativeCharacterDetector
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (a g : G) :
    (∑ ψ : AddChar G ℂ, ψ (-g) * ψ a) =
      if a = g then (Fintype.card G : ℂ) else 0 := by
  classical
  calc
    (∑ ψ : AddChar G ℂ, ψ (-g) * ψ a) =
        ∑ ψ : AddChar G ℂ, ψ (a - g) := by
          apply Finset.sum_congr rfl
          intro ψ _h
          rw [← AddChar.map_add_eq_mul]
          congr 1
          abel
    _ = if a = g then (Fintype.card G : ℂ) else 0 := by
          rw [AddChar.sum_apply_eq_ite]
          simp only [sub_eq_zero]

/-- Exact complete-character response of ONE REAL inertia coset.
The distinguished output site survives iff g-a belongs to inertia.
The normalizer is the TRUE cardinality of inertia, never an
independent arbitrary coefficient or a missing bad-prime term. -/
open Classical in theorem alpogeNativeCosetCharacterOrthogonality
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (I : AddSubgroup G) (a g : G) :
    (∑ ψ : AddChar G ℂ,
      ψ (-g) * alpogeNativeInertiaCosetMean I a ψ) =
        if g - a ∈ I then
          (Fintype.card G : ℂ) /
            (((Finset.univ.filter (fun u : G => u ∈ I)).card : ℕ) : ℂ)
        else 0 := by
  classical
  let S : Finset G := Finset.univ.filter (fun u : G => u ∈ I)
  have hcond (u : G) : a + u = g ↔ u = g - a := by
    constructor
    · intro hu
      calc
        u = (a + u) - a := by abel
        _ = g - a := by rw [hu]
    · intro hu
      rw [hu]
      abel
  have hmem : g - a ∈ S ↔ g - a ∈ I := by
    simp [S]
  have hsum :
      (∑ u ∈ S, if a + u = g then (Fintype.card G : ℂ) else 0) =
        if g - a ∈ I then (Fintype.card G : ℂ) else 0 := by
    simp_rw [hcond]
    simp only [Finset.sum_ite_eq', hmem]
  calc
    (∑ ψ : AddChar G ℂ, ψ (-g) * alpogeNativeInertiaCosetMean I a ψ) =
      ∑ ψ : AddChar G ℂ,
        (∑ u ∈ S, ψ (-g) * ψ (a + u)) / (S.card : ℂ) := by
          apply Finset.sum_congr rfl
          intro ψ _hψ
          unfold alpogeNativeInertiaCosetMean
          change ψ (-g) * ((∑ u ∈ S, ψ (a + u)) / (S.card : ℂ)) = _
          rw [mul_div_assoc', Finset.mul_sum]
    _ = (∑ u ∈ S, ∑ ψ : AddChar G ℂ, ψ (-g) * ψ (a + u)) /
          (S.card : ℂ) := by
          rw [← Finset.sum_div, Finset.sum_comm]
    _ = (∑ u ∈ S, if a + u = g then (Fintype.card G : ℂ) else 0) /
          (S.card : ℂ) := by
          congr 1
          apply Finset.sum_congr rfl
          intro u _hu
          exact alpogeNativeCharacterDetector (a + u) g
    _ = _ := by
          rw [hsum]
          by_cases hi : g - a ∈ I <;> simp [hi, S]

/-- Genuine unramified character orthogonality: no ramified
side is postulated or thrown away. -/
theorem alpogeNativeCosetCharacterOrthogonality_unramified
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (a g : G) :
    (∑ ψ : AddChar G ℂ,
      ψ (-g) * alpogeNativeInertiaCosetMean (⊥ : AddSubgroup G) a ψ) =
        if a = g then (Fintype.card G : ℂ) else 0 := by
  classical
  simp only [alpogeNativeInertiaCosetMean_unramified]
  exact alpogeNativeCharacterDetector a g


/-!
## Physical two-bit colour host, partner bijection, and principal channel

These definitions use the SAME group (Z/2)^2 × H, genuine additive
characters, original site mask and translated partner as the published
ASK/MAIN proof. No analytic/geometric estimate is being postulated.
-/

abbrev AlpogeNativeE0 := ZMod 2 × ZMod 2

def alpogeNativeInPhi {H : Type*} (g : AlpogeNativeE0 × H) : Prop :=
  g.1.1 = 0

instance {H : Type*} : DecidablePred (alpogeNativeInPhi (H := H)) :=
  fun g => inferInstanceAs (Decidable (g.1.1 = 0))

def alpogeNativePhiSet (H : Type*) [AddCommGroup H]
    [Fintype H] [DecidableEq H] : Finset (AlpogeNativeE0 × H) := by
  classical
  exact Finset.univ.filter alpogeNativeInPhi

def alpogeNativeCconj (H : Type*) [AddCommGroup H] :
    AlpogeNativeE0 × H := ((1, 1), 0)

def alpogeNativeTopPl {H : Type*} [AddCommGroup H] (t : H) :
    AlpogeNativeE0 × H := ((0, 0), t)

def alpogeNativePartner {H : Type*} [AddCommGroup H]
    (t : H) (g : AlpogeNativeE0 × H) : AlpogeNativeE0 × H :=
  alpogeNativeCconj H + g + alpogeNativeTopPl t

/-- The actual quadratic class character, not an independent sign
label: χC(g)=+1 for first-bit 0 and -1 for first-bit 1. -/
def alpogeNativeChC (H : Type*) [AddCommGroup H]
    [Fintype H] [DecidableEq H] :
    AddChar (AlpogeNativeE0 × H) ℂ where
  toFun g := if g.1.1 = 0 then 1 else -1
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    rcases a with ⟨⟨a1, a2⟩, ah⟩
    rcases b with ⟨⟨b1, b2⟩, bh⟩
    have key : ∀ x y : ZMod 2, (if x + y = 0 then (1 : ℂ) else -1) =
        (if x = 0 then 1 else -1) * (if y = 0 then 1 else -1) := by
      intro x y
      have hc : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      have h11 : (1 : ZMod 2) + 1 = 0 := rfl
      have h10 : (1 : ZMod 2) ≠ 0 := by decide
      rcases hc x with rfl | rfl <;> rcases hc y with rfl | rfl <;>
        simp [h11, h10]
    exact key a1 b1

section NativeColours
variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

omit [AddCommGroup H] [Fintype H] [DecidableEq H] in
private theorem alpogeNativeNotPhi_iff (g : AlpogeNativeE0 × H) :
    ¬ alpogeNativeInPhi g ↔ g.1.1 = 1 := by
  change ¬ g.1.1 = 0 ↔ g.1.1 = 1
  have hcase : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hcase g.1.1 with h | h <;> rw [h] <;> decide

omit [Fintype H] [DecidableEq H] in
private theorem alpogeNativePartner_fst (t : H) (g : AlpogeNativeE0 × H) :
    (alpogeNativePartner t g).1.1 = 1 + g.1.1 := by
  simp [alpogeNativePartner, alpogeNativeCconj, alpogeNativeTopPl]

omit [Fintype H] [DecidableEq H] in
private theorem alpogeNativePartner_inv_fst (t : H) (g : AlpogeNativeE0 × H) :
    (g - alpogeNativeTopPl t - alpogeNativeCconj H).1.1 = g.1.1 - 1 := by
  simp [alpogeNativeTopPl, alpogeNativeCconj]

/-- Exact transport of every geometric width from the non-Phi
character site to Phi. No lost sites, multiplicities, or weights. -/
theorem alpogeNativeSumPartner {β : Type*} [AddCommMonoid β]
    (t : H) (F : AlpogeNativeE0 × H → β) :
    (∑ g ∈ (Finset.univ.filter (fun g : AlpogeNativeE0 × H =>
        ¬ alpogeNativeInPhi g)), F (alpogeNativePartner t g)) =
      ∑ ρ ∈ alpogeNativePhiSet H, F ρ := by
  classical
  refine Finset.sum_nbij'
    (alpogeNativePartner t)
    (fun ρ => ρ - alpogeNativeTopPl t - alpogeNativeCconj H)
    ?_ ?_ ?_ ?_ ?_
  · intro g hg
    have hg' : ¬ alpogeNativeInPhi g := (Finset.mem_filter.mp hg).2
    simp only [alpogeNativePhiSet, Finset.mem_filter, Finset.mem_univ, true_and]
    change (alpogeNativePartner t g).1.1 = 0
    rw [alpogeNativePartner_fst, (alpogeNativeNotPhi_iff g).mp hg']
    decide
  · intro ρ hρ
    simp only [alpogeNativePhiSet, Finset.mem_filter, Finset.mem_univ, true_and] at hρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [alpogeNativeNotPhi_iff, alpogeNativePartner_inv_fst]
    change ρ.1.1 = 0 at hρ
    rw [hρ]
    decide
  · intro a _
    simp only [alpogeNativePartner]
    abel
  · intro a _
    simp only [alpogeNativePartner]
    abel
  · intro a _
    rfl

private theorem alpogeNativeCardNotPhi :
    (Finset.univ.filter (fun g : AlpogeNativeE0 × H =>
      ¬ alpogeNativeInPhi g)).card =
        (alpogeNativePhiSet H).card := by
  have h := alpogeNativeSumPartner (H := H) (β := ℕ) 0 (fun _ => 1)
  simpa using h

omit [DecidableEq H] in
private theorem alpogeNativeCharStarNeg
    (ψ : AddChar (AlpogeNativeE0 × H) ℂ) (g : AlpogeNativeE0 × H) :
    starRingEnd ℂ (ψ g) = ψ (-g) := by
  exact (AddChar.map_neg_eq_conj ψ g).symm

private theorem alpogeNativeChC_apply (g : AlpogeNativeE0 × H) :
    alpogeNativeChC H g = if g.1.1 = 0 then 1 else -1 := rfl

private theorem alpogeNativeChC_sq (g : AlpogeNativeE0 × H) :
    alpogeNativeChC H g * alpogeNativeChC H g = 1 := by
  change (if g.1.1 = 0 then (1 : ℂ) else -1) *
      (if g.1.1 = 0 then 1 else -1) = 1
  split_ifs <;> simp

private theorem alpogeNativeChC_neg (g : AlpogeNativeE0 × H) :
    alpogeNativeChC H (-g) = alpogeNativeChC H g := by
  have h1 : (-g).1.1 = g.1.1 := by
    simp only [Prod.fst_neg]
    generalize g.1.1 = e
    revert e
    decide
  rw [alpogeNativeChC_apply, alpogeNativeChC_apply, h1]

private theorem alpogeNativeChC_mul_self :
    (alpogeNativeChC H) * (alpogeNativeChC H) = 0 := by
  ext g
  rw [AddChar.mul_apply, alpogeNativeChC_sq]
  simp

private theorem alpogeNativeMulChC_zero_iff
    (ψ : AddChar (AlpogeNativeE0 × H) ℂ) :
    ψ * alpogeNativeChC H = 0 ↔ ψ = alpogeNativeChC H := by
  constructor
  · intro h
    ext g
    have hh : ((ψ * alpogeNativeChC H) : AddChar (AlpogeNativeE0 × H) ℂ) g =
        (0 : AddChar (AlpogeNativeE0 × H) ℂ) g := by rw [h]
    rw [AddChar.mul_apply] at hh
    simp only [AddChar.zero_apply] at hh
    calc
      ψ g = ψ g * (alpogeNativeChC H g * alpogeNativeChC H g) := by
        rw [alpogeNativeChC_sq, mul_one]
      _ = (ψ g * alpogeNativeChC H g) * alpogeNativeChC H g := by ring
      _ = alpogeNativeChC H g := by rw [hh, one_mul]
  · intro h
    rw [h]
    exact alpogeNativeChC_mul_self

private theorem alpogeNativeChC_nontrivial :
    alpogeNativeChC H ≠ 0 := by
  intro h
  have hh := congrArg (fun ψ : AddChar (AlpogeNativeE0 × H) ℂ =>
      ψ (((1, 0), 0) : AlpogeNativeE0 × H)) h
  change (-1 : ℂ) = 1 at hh
  norm_num at hh

private theorem alpogeNativePhiCard_ne_zero :
    ((alpogeNativePhiSet H).card : ℂ) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  apply Finset.card_ne_zero.mpr
  exact ⟨0, by simp [alpogeNativePhiSet, alpogeNativeInPhi]⟩

private theorem alpogeNativeCardDoublePhi :
    (Fintype.card (AlpogeNativeE0 × H) : ℂ) =
      2 * ((alpogeNativePhiSet H).card : ℂ) := by
  have hn : Fintype.card (AlpogeNativeE0 × H) =
      2 * (alpogeNativePhiSet H).card := by
    rw [← Finset.card_univ,
      ← Finset.card_filter_add_card_filter_not
        (p := alpogeNativeInPhi)]
    rw [alpogeNativeCardNotPhi]
    simp only [alpogeNativePhiSet]
    ring
  exact_mod_cast hn

/-- EXACT original ColourSum: the two physical first-bit cosets
kill every off-principal additive character except χC. This is
the MAIN correction, not a free cancellation bound. -/
theorem alpogeNativeColourSum
    (ψ : AddChar (AlpogeNativeE0 × H) ℂ) :
    (∑ g ∈ (Finset.univ.filter (fun g : AlpogeNativeE0 × H =>
      ¬ alpogeNativeInPhi g)), starRingEnd ℂ (ψ g)) =
        if ψ = 0 then ((alpogeNativePhiSet H).card : ℂ)
        else if ψ = alpogeNativeChC H then
          -((alpogeNativePhiSet H).card : ℂ) else 0 := by
  classical
  have hneg (F : AlpogeNativeE0 × H → ℂ) :
      (∑ g : AlpogeNativeE0 × H, F (-g)) =
        ∑ g : AlpogeNativeE0 × H, F g :=
    Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl)
  have hindicator (g : AlpogeNativeE0 × H) :
      (if ¬ alpogeNativeInPhi g then (1 : ℂ) else 0) =
        (1 - alpogeNativeChC H g) / 2 := by
    by_cases hg : g.1.1 = 0
    · simp [alpogeNativeInPhi, alpogeNativeChC_apply, hg]
    · simp [alpogeNativeInPhi, alpogeNativeChC_apply, hg]
      ring
  have hterm (g : AlpogeNativeE0 × H) :
      (if ¬ alpogeNativeInPhi g then starRingEnd ℂ (ψ g) else 0) =
        (starRingEnd ℂ (ψ g) -
          alpogeNativeChC H g * starRingEnd ℂ (ψ g)) / 2 := by
    rw [← boole_mul, hindicator]
    ring
  have hA : (∑ g : AlpogeNativeE0 × H, starRingEnd ℂ (ψ g)) =
      if ψ = 0 then (Fintype.card (AlpogeNativeE0 × H) : ℂ) else 0 := by
    simp_rw [alpogeNativeCharStarNeg]
    rw [hneg (⇑ψ), AddChar.sum_eq_ite]
  have hB : (∑ g : AlpogeNativeE0 × H,
      alpogeNativeChC H g * starRingEnd ℂ (ψ g)) =
      if ψ = alpogeNativeChC H then
        (Fintype.card (AlpogeNativeE0 × H) : ℂ) else 0 := by
    have h4 (g : AlpogeNativeE0 × H) :
        alpogeNativeChC H g * starRingEnd ℂ (ψ g) =
          ((ψ * alpogeNativeChC H) : AddChar (AlpogeNativeE0 × H) ℂ) (-g) := by
      rw [AddChar.mul_apply, alpogeNativeCharStarNeg, ← alpogeNativeChC_neg, mul_comm]
    simp_rw [h4]
    rw [hneg (⇑(ψ * alpogeNativeChC H : AddChar (AlpogeNativeE0 × H) ℂ)),
      AddChar.sum_eq_ite]
    simp only [alpogeNativeMulChC_zero_iff]
  rw [Finset.sum_filter]
  simp_rw [hterm]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, hA, hB, alpogeNativeCardDoublePhi]
  by_cases h0 : ψ = 0
  · have h1 : ψ ≠ alpogeNativeChC H := fun h => alpogeNativeChC_nontrivial (h ▸ h0)
    simp only [if_pos h0, if_neg h1]
    ring
  · by_cases h1 : ψ = alpogeNativeChC H
    · simp only [if_neg h0, if_pos h1]
      ring
    · simp only [if_neg h0, if_neg h1]
      ring

end NativeColours


/-!
## Actual native prime-power colour coefficients

This is Alpoge's Kc, with original inertia mean, native Lambda(n)
and the EXACT ratio |(Z/2)^2 × H|/|Phi| = 2. It is not an assumed
square-root-saving character estimate.
-/

theorem alpogeNativePrimeValue_trivial
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (inertia : ℕ → AddSubgroup G) (frob : ℕ → G) (n : ℕ) :
    alpogeNativeFrobInertiaPrimeValue inertia frob
      (0 : AddChar G ℂ) n = 1 := by
  classical
  unfold alpogeNativeFrobInertiaPrimeValue
  apply Finset.prod_eq_one
  intro p _hp
  unfold alpogeNativeInertiaCosetMean
  simp only [AddChar.zero_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
  refine div_self ?_
  rw [Nat.cast_ne_zero]
  exact Finset.card_ne_zero.mpr ⟨0, by simp⟩

/-- Fourier-side coefficient at one genuine native integer n. -/
def alpogeNativeColourKernel
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (n : ℕ) (g : AlpogeNativeE0 × H) : ℂ :=
  (1 / ((alpogeNativePhiSet H).card : ℂ)) *
    ∑ ψ : AddChar (AlpogeNativeE0 × H) ℂ,
      starRingEnd ℂ (ψ g) *
        alpogeNativeFrobInertiaPrimeValue inertia frob ψ n

/-- Original ORTHO-RAM on the actual physical Lambda prime-power
population. The factor 2 is earned from the EXACT two-bit host.
Every ramified inertia coset is retained at its exact cardinality. -/
open Classical in theorem alpogeNativeColourKernel_primePower
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (p i : ℕ) (hp : p.Prime) (hi : 0 < i)
    (g : AlpogeNativeE0 × H) :
    alpogeNativeColourKernel inertia frob (p ^ i) g =
      if g - i • frob p ∈ inertia p then
        2 / (((Finset.univ.filter
            (fun u : AlpogeNativeE0 × H => u ∈ inertia p)).card : ℕ) : ℂ)
      else 0 := by
  classical
  let S : Finset (AlpogeNativeE0 × H) :=
    Finset.univ.filter (fun u => u ∈ inertia p)
  have hS : (S.card : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    apply Finset.card_ne_zero.mpr
    exact ⟨0, by simp [S]⟩
  have hsum :
      (∑ ψ : AddChar (AlpogeNativeE0 × H) ℂ,
        starRingEnd ℂ (ψ g) *
          alpogeNativeFrobInertiaPrimeValue inertia frob ψ (p ^ i)) =
        if g - i • frob p ∈ inertia p then
          (Fintype.card (AlpogeNativeE0 × H) : ℂ) / (S.card : ℂ)
        else 0 := by
    simp_rw [alpogeNativeFrobInertiaPrimeValue_primePower inertia frob
      _ p i hp hi, alpogeNativeCharStarNeg]
    simpa only [S] using
      (alpogeNativeCosetCharacterOrthogonality
        (inertia p) (i • frob p) g)
  unfold alpogeNativeColourKernel
  rw [hsum]
  by_cases h : g - i • frob p ∈ inertia p
  · simp only [if_pos h]
    rw [alpogeNativeCardDoublePhi]
    have hPhi := alpogeNativePhiCard_ne_zero (H := H)
    change (1 / ((alpogeNativePhiSet H).card : ℂ)) *
        (2 * ((alpogeNativePhiSet H).card : ℂ) / (S.card : ℂ)) =
      2 / (S.card : ℂ)
    field_simp [hPhi, hS]
  · simp [h]

end RHLean.Analysis

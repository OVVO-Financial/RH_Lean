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

open Classical in
/-- Exact complete-character response of ONE REAL inertia coset.
The distinguished output site survives iff g-a belongs to inertia.
The normalizer is the TRUE cardinality of inertia, never an
independent arbitrary coefficient or a missing bad-prime term. -/
theorem alpogeNativeCosetCharacterOrthogonality
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
    simp only [ite_eq_left h0, ite_eq_right h1]
    ring
  · by_cases h1 : ψ = alpogeNativeChC H
    · simp only [ite_eq_right h0, ite_eq_left h1]
      ring
    · simp only [ite_eq_right h0, ite_eq_right h1]
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

open Classical in
/-- Original ORTHO-RAM on the actual physical Lambda prime-power
population. The factor 2 is earned from the EXACT two-bit host.
Every ramified inertia coset is retained at its exact cardinality. -/
theorem alpogeNativeColourKernel_primePower
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
  · simp only [ite_eq_left h]
    rw [alpogeNativeCardDoublePhi]
    have hPhi := alpogeNativePhiCard_ne_zero (H := H)
    change (1 / ((alpogeNativePhiSet H).card : ℂ)) *
        (2 * ((alpogeNativePhiSet H).card : ℂ) / (S.card : ℂ)) =
      2 / (S.card : ℂ)
    field_simp [hPhi, hS]
  · simp [h]


/-- Exact native von Mangoldt source census: every nonzero Lambda
coefficient is one and only one genuine prime power. This is the
finite Fubini/reindex step in Alpoge's ASK expansion, not a
probabilistic statement about prime positions. -/
theorem alpogeNativeLambda_primePowerFubini
    (N : ℕ) (X : ℕ → ℂ)
    (hX : ∀ p i, p.Prime → 1 ≤ i → N < p ^ i → X (p ^ i) = 0) :
    (∑ n ∈ Finset.Icc 1 N, (Λ n : ℂ) * X n) =
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
        ∑ i ∈ Finset.Icc 1 N,
          (Real.log p : ℂ) * X (p ^ i) := by
  classical
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij_ne_zero (fun x _ _ => x.1 ^ x.2) ?_ ?_ ?_ ?_
  · intro x hx hne
    rw [Finset.mem_product, Finset.mem_filter,
      Finset.mem_range, Finset.mem_Icc] at hx
    obtain ⟨⟨_, hp⟩, hi1, _⟩ := hx
    have hle : x.1 ^ x.2 ≤ N := by
      by_contra hn
      exact hne (by rw [hX x.1 x.2 hp hi1 (not_le.mp hn), mul_zero])
    show x.1 ^ x.2 ∈ Finset.Icc 1 N
    rw [Finset.mem_Icc]
    exact ⟨Nat.one_le_pow _ _ hp.pos, hle⟩
  · intro x hx _ y hy _ hxy
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hx hy
    obtain ⟨⟨_, hp⟩, hi1, _⟩ := hx
    obtain ⟨⟨_, hq⟩, hj1, _⟩ := hy
    have hpq : x.1 = y.1 := by
      have hd : x.1 ∣ y.1 ^ y.2 := by
        rw [← hxy]
        exact dvd_pow_self _ (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hd)
    have hij : x.2 = y.2 := by
      rw [hpq] at hxy
      exact Nat.pow_right_injective hq.two_le hxy
    exact Prod.ext hpq hij
  · intro n hn hne
    rw [Finset.mem_Icc] at hn
    have hΛ : Λ n ≠ 0 := by
      intro hz
      apply hne
      show (Λ n : ℂ) * X n = 0
      rw [hz]
      simp
    rw [ArithmeticFunction.vonMangoldt_ne_zero_iff,
      isPrimePow_nat_iff] at hΛ
    obtain ⟨p, k, hp, hk, rfl⟩ := hΛ
    have hpN : p ≤ p ^ k := Nat.le_self_pow (by omega) p
    have hkN : k < p ^ k := Nat.lt_pow_self hp.one_lt
    refine ⟨(p, k), ?_, ?_, rfl⟩
    · rw [Finset.mem_product, Finset.mem_filter,
        Finset.mem_range, Finset.mem_Icc]
      exact ⟨⟨Nat.lt_succ_of_le (hpN.trans hn.2), hp⟩,
        hk, (hkN.trans_le hn.2).le⟩
    · intro hzero
      apply hne
      show (Λ (p ^ k) : ℂ) * X (p ^ k) = 0
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
        ArithmeticFunction.vonMangoldt_apply_prime hp]
      exact hzero
  · intro x hx _
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hx
    show (Real.log x.1 : ℂ) * X (x.1 ^ x.2) =
      (Λ (x.1 ^ x.2) : ℂ) * X (x.1 ^ x.2)
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hx.1.2]


/-- Native PRINCIPAL prime-power channel is literally the original
weighted von Mangoldt source, including every ramified prime power.
This does not use the nonprincipal Dirichlet analogue. -/
theorem alpogeNativeFrobInertiaPrimeSum_principal
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (inertia : ℕ → AddSubgroup G) (frob : ℕ → G)
    (x : ℝ) :
    alpogeNativeFrobInertiaPrimeSum inertia frob
      (0 : AddChar G ℂ) x = (alpogeNativePrincipalPrimeSum x : ℂ) := by
  classical
  unfold alpogeNativeFrobInertiaPrimeSum alpogeNativePrincipalPrimeSum
    alpogeNativePrimePowerWeight
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [alpogeNativePrimeValue_trivial inertia frob n]
  push_cast
  ring

/-- Exact MAIN-correction for the principal GPsi channel on the
FULL native physical source: no dropped constant, fractional
boundary, prime power, or logarithm. -/
theorem alpogeNativeFrobInertiaASK_principal
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (inertia : ℕ → AddSubgroup G) (frob : ℕ → G)
    (ell : AddChar G ℂ → ℂ)
    (N : ℕ) (a W : ℝ)
    (ha : 0 < a) (hW : 0 < W) (hN : a / W ≤ (N : ℝ)) :
    alpogeNativeFrobInertiaASK inertia frob
      (0 : AddChar G ℂ) N a W =
      (W : ℂ) * alpogeNativeFrobInertiaGPsi inertia frob ell
        0 (a / W) +
      ((a * Real.log a - a * Real.log W -
        (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) := by
  rw [alpogeNativeFrobInertiaASK_eq_primeSum
        inertia frob (0 : AddChar G ℂ) N a W ha hW hN,
      alpogeNativeFrobInertiaGPsi_principal,
      alpogeNativeFrobInertiaPrimeSum_principal,
      alpogeNativeGzArithmetic_eq_principal]
  have hwa : W * (a / W) = a := by field_simp
  have hwaC : (W : ℂ) * ((a / W : ℝ) : ℂ) = (a : ℂ) := by
    rw [← Complex.ofReal_mul, hwa]
  rw [Real.log_div ha.ne' hW.ne']
  push_cast
  have hWc : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  field_simp [hWc]
  ring


/-!
## Native full finite ASK Fourier expansion (physical site source)

The following is the actual untruncated von Mangoldt-weighted character
sum on all non-Phi sites. Its target is the SAME source with each n
carrying the *proved* inertia-coset kernel. Both sums are finite, with
all prime powers and every width w(partner(t,g)) kept in place.
-/

def alpogeNativeSiteCut {H : Type*} [AddCommGroup H]
    (a : ℝ) (w : AlpogeNativeE0 × H → ℝ) (t : H)
    (n : ℕ) (g : AlpogeNativeE0 × H) : ℂ :=
  ((max (a / (n : ℝ) - w (alpogeNativePartner t g)) 0 : ℝ) : ℂ)

def alpogeNativeFullFourierASK
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (N : ℕ) (a : ℝ) (t : H)
    (w : AlpogeNativeE0 × H → ℝ) : ℂ := by
  classical
  exact (1 / ((alpogeNativePhiSet H).card : ℂ)) *
    ∑ g ∈ Finset.univ.filter (fun g : AlpogeNativeE0 × H =>
        ¬ alpogeNativeInPhi g),
      ∑ ψ : AddChar (AlpogeNativeE0 × H) ℂ,
        starRingEnd ℂ (ψ g) *
          alpogeNativeFrobInertiaASK inertia frob ψ
            N a (w (alpogeNativePartner t g))

/-- The SAME physical ASK with the actual Fourier coefficient at each
prime-power source site n. This is not an assumed image of the original
count: it is proved equal below by finite character Fubini. -/
def alpogeNativeFullKernelASK
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (N : ℕ) (a : ℝ) (t : H)
    (w : AlpogeNativeE0 × H → ℝ) : ℂ := by
  classical
  exact ∑ n ∈ Finset.Icc 1 N, (Λ n : ℂ) *
    ∑ g ∈ Finset.univ.filter (fun g : AlpogeNativeE0 × H =>
        ¬ alpogeNativeInPhi g),
      alpogeNativeColourKernel inertia frob n g *
        alpogeNativeSiteCut a w t n g

/-- The exact native physical ASK expansion: every original
von Mangoldt site and width is retained on both sides, and no
independence or cancellation estimate is used. -/
theorem alpogeNativeFullFourierASK_eq_kernel
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (N : ℕ) (a : ℝ) (t : H)
    (w : AlpogeNativeE0 × H → ℝ) :
    alpogeNativeFullFourierASK inertia frob N a t w =
      alpogeNativeFullKernelASK inertia frob N a t w := by
  classical
  unfold alpogeNativeFullFourierASK alpogeNativeFullKernelASK
    alpogeNativeFrobInertiaASK
  change (1 / ((alpogeNativePhiSet H).card : ℂ)) *
      ∑ g ∈ Finset.univ.filter (fun g : AlpogeNativeE0 × H =>
          ¬ alpogeNativeInPhi g),
        ∑ ψ : AddChar (AlpogeNativeE0 × H) ℂ,
          starRingEnd ℂ (ψ g) *
            (∑ n ∈ Finset.Icc 1 N,
              ((Λ n : ℝ) : ℂ) *
                alpogeNativeFrobInertiaPrimeValue inertia frob ψ n *
                  alpogeNativeSiteCut a w t n g) =
      ∑ n ∈ Finset.Icc 1 N,
        (Λ n : ℂ) * ∑ g ∈ Finset.univ.filter
          (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g),
            alpogeNativeColourKernel inertia frob n g *
              alpogeNativeSiteCut a w t n g
  calc
    _ = ∑ g ∈ Finset.univ.filter
        (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g),
      ∑ n ∈ Finset.Icc 1 N,
        (Λ n : ℂ) * (alpogeNativeColourKernel inertia frob n g *
          alpogeNativeSiteCut a w t n g) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun g _ => ?_)
            simp only [alpogeNativeColourKernel, Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl
              (fun n _ => Finset.sum_congr rfl (fun ψ _ => ?_))
            ring
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]


/-!
## Complete physical prime-power ASK census

Not a model or bound: the following is the actual sharp nonnegative
class mass for each physical prime p and power p^i. The site criterion
is the TRUE Frobenius/inertia coset, with the exact coefficient
2/|I(p)|, including every exceptional ramified prime.
-/

def alpogeNativePrimePowerCensusASK
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (N : ℕ) (a : ℝ) (t : H)
    (w : AlpogeNativeE0 × H → ℝ) : ℂ := by
  classical
  exact ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
    ∑ i ∈ Finset.Icc 1 N,
      (Real.log p : ℂ) *
        ∑ g ∈ Finset.univ.filter
          (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g),
          (if g - i • frob p ∈ inertia p then
            (2 : ℂ) /
              ((Finset.univ.filter
                (fun u : AlpogeNativeE0 × H => u ∈ inertia p)).card : ℂ)
            else 0) *
              alpogeNativeSiteCut a w t (p ^ i) g

private theorem alpogeNativePartner_inPhi
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (t : H) (g : AlpogeNativeE0 × H)
    (hg : ¬ alpogeNativeInPhi g) :
    alpogeNativeInPhi (alpogeNativePartner t g) := by
  change (alpogeNativePartner t g).1.1 = 0
  rw [alpogeNativePartner_fst,
    (alpogeNativeNotPhi_iff g).mp hg]
  decide

/-- The actual sharp cutoff is exactly zero beyond N whenever
the physical site belongs to Phi and a/w <= N. This is the
source condition required by genuine prime-power reindexing. -/
theorem alpogeNativeSiteCut_zero_above
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (N n : ℕ) (a : ℝ) (t : H)
    (w : AlpogeNativeE0 × H → ℝ)
    (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 < w ρ)
    (hN : ∀ ρ, alpogeNativeInPhi ρ → a / w ρ ≤ (N : ℝ))
    (g : AlpogeNativeE0 × H)
    (hg : ¬ alpogeNativeInPhi g) (hn : N < n) :
    alpogeNativeSiteCut a w t n g = 0 := by
  let ρ := alpogeNativePartner t g
  have hρ : alpogeNativeInPhi ρ :=
    alpogeNativePartner_inPhi t g hg
  have hW : 0 < w ρ := hw ρ hρ
  have hupper : a / w ρ ≤ (N : ℝ) := hN ρ hρ
  have hlt : (N : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by
    have h0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hprod : a < (n : ℝ) * w ρ := by
    apply (div_lt_iff₀ hW).mp
    exact lt_of_le_of_lt hupper hlt
  have hquot : a / (n : ℝ) < w ρ := by
    apply (div_lt_iff₀ hn0).mpr
    nlinarith [mul_comm (n : ℝ) (w ρ)]
  unfold alpogeNativeSiteCut
  rw [max_eq_right (by linarith : a / (n : ℝ) - w ρ ≤ 0)]
  simp

/-- The literal RHLean Lambda(n) physical ASK is exactly the complete
finite Alpoge prime-power/inertia population, with zero truncated
contributions rather than an assumed tail or randomized model. -/
theorem alpogeNativeFullKernelASK_eq_primePowerCensus
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (N : ℕ) (a : ℝ) (t : H)
    (w : AlpogeNativeE0 × H → ℝ)
    (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 < w ρ)
    (hN : ∀ ρ, alpogeNativeInPhi ρ → a / w ρ ≤ (N : ℝ)) :
    alpogeNativeFullKernelASK inertia frob N a t w =
      alpogeNativePrimePowerCensusASK inertia frob N a t w := by
  classical
  let X : ℕ → ℂ := fun n =>
    ∑ g ∈ Finset.univ.filter
      (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g),
        alpogeNativeColourKernel inertia frob n g *
          alpogeNativeSiteCut a w t n g
  have hX (p i : ℕ) (hp : p.Prime) (hi : 1 ≤ i)
      (hlt : N < p ^ i) : X (p ^ i) = 0 := by
    dsimp [X]
    apply Finset.sum_eq_zero
    intro g hg
    have hgn : ¬ alpogeNativeInPhi g := (Finset.mem_filter.mp hg).2
    rw [alpogeNativeSiteCut_zero_above N (p ^ i) a t w
      hw hN g hgn hlt, mul_zero]
  have hfubini := alpogeNativeLambda_primePowerFubini N X hX
  unfold alpogeNativeFullKernelASK
  change (∑ n ∈ Finset.Icc 1 N, (Λ n : ℂ) * X n) = _
  calc
    (∑ n ∈ Finset.Icc 1 N, (Λ n : ℂ) * X n) =
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
        ∑ i ∈ Finset.Icc 1 N,
          (Real.log p : ℂ) * X (p ^ i) := hfubini
    _ = alpogeNativePrimePowerCensusASK inertia frob N a t w := by
      unfold alpogeNativePrimePowerCensusASK
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      dsimp [X]
      apply Finset.sum_congr rfl
      intro g _hg
      rw [alpogeNativeColourKernel_primePower inertia frob
        p i (Finset.mem_filter.mp hp).2 (Finset.mem_Icc.mp hi).1 g]


/-!
## Exact published ASK - MAIN = De, on RHLean arithmetic

The four channels here are the ACTUAL native Gz and additive-character
Frobenius/inertia GPsi. In particular MAIN is not defined by setting
the left side equal to De: it is the independently explicit closed
logarithmic expression from Alpoge's original arithmetic. The proof
uses the principal/nonprincipal sharp ASK formulas, the *proved*
ColourSum, and the partner bijection.
-/

/-- Exact logarithmic MAIN term in the original two-bit physical
character host. Every real width enters through the original Phi set. -/
def alpogeNativeMAIN
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (a : ℝ) (w : AlpogeNativeE0 × H → ℝ) : ℂ :=
  (a : ℂ) * (((Real.log a - 1 -
    Real.eulerMascheroniConstant : ℝ) : ℂ) +
      ell (alpogeNativeChC H) -
      (((1 / ((alpogeNativePhiSet H).card : ℝ)) *
        ∑ ρ ∈ alpogeNativePhiSet H, Real.log (w ρ) : ℝ) : ℂ))

/-- Original complete nonprincipal De, retaining all character
coefficients and a/w(x) shifts. This is NOT an assumed upper bound. -/
def alpogeNativeDe
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (a : ℝ) (t : H)
    (w : AlpogeNativeE0 × H → ℝ) : ℂ := by
  classical
  exact (1 / ((alpogeNativePhiSet H).card : ℂ)) *
    ∑ g ∈ Finset.univ.filter (fun g : AlpogeNativeE0 × H =>
        ¬ alpogeNativeInPhi g),
      ∑ ψ : AddChar (AlpogeNativeE0 × H) ℂ,
        starRingEnd ℂ (ψ g) *
          ((w (alpogeNativePartner t g) : ℝ) : ℂ) *
            alpogeNativeFrobInertiaGPsi inertia frob ell ψ
              (a / w (alpogeNativePartner t g))

/-- Alpoge's original exact FINITE ASK/MAIN identity, carried through
with native Lambda, physical inertia, all prime powers, and the
original principal Gz. This theorem does not assert or assume any
height, covolume or power-saving inequality. -/
theorem alpogeNativeFullASK_sub_MAIN_eq_De
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) (a : ℝ) (t : H)
    (w : AlpogeNativeE0 × H → ℝ)
    (ha : 0 < a)
    (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 < w ρ)
    (hN : ∀ ρ, alpogeNativeInPhi ρ → a / w ρ ≤ (N : ℝ)) :
    alpogeNativeFullKernelASK inertia frob N a t w -
        alpogeNativeMAIN ell a w =
      alpogeNativeDe inertia frob ell a t w := by
  classical
  rw [← alpogeNativeFullFourierASK_eq_kernel inertia frob N a t w]
  unfold alpogeNativeFullFourierASK
  have hinner :
      ∀ g ∈ Finset.univ.filter
          (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g),
      ∀ ψ : AddChar (AlpogeNativeE0 × H) ℂ,
        alpogeNativeFrobInertiaASK inertia frob ψ N a
          (w (alpogeNativePartner t g)) =
        ((w (alpogeNativePartner t g) : ℝ) : ℂ) *
          alpogeNativeFrobInertiaGPsi inertia frob ell ψ
            (a / w (alpogeNativePartner t g)) +
          (if ψ = 0 then
            ((a * Real.log a - a * Real.log
              (w (alpogeNativePartner t g)) -
                (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ)
          else -(a : ℂ) * ell ψ) := by
    intro g hg ψ
    have hg' : ¬ alpogeNativeInPhi g := (Finset.mem_filter.mp hg).2
    have hρ := alpogeNativePartner_inPhi t g hg'
    by_cases hψ : ψ = 0
    · subst ψ
      simpa using alpogeNativeFrobInertiaASK_principal
        inertia frob ell N a (w (alpogeNativePartner t g))
        ha (hw _ hρ) (hN _ hρ)
    · have hh := alpogeNativeFrobInertiaASK_eq_GPsi_nonprincipal
        inertia frob ell ψ N a (w (alpogeNativePartner t g))
        hψ ha (hw _ hρ) (hN _ hρ)
      simpa only [ite_eq_right hψ, sub_eq_add_neg, neg_mul] using hh
  have hsum :
      (∑ g ∈ Finset.univ.filter
        (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g),
        ∑ ψ : AddChar (AlpogeNativeE0 × H) ℂ,
          starRingEnd ℂ (ψ g) *
            alpogeNativeFrobInertiaASK inertia frob ψ N a
              (w (alpogeNativePartner t g))) =
      (∑ g ∈ Finset.univ.filter
        (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g),
        ∑ ψ : AddChar (AlpogeNativeE0 × H) ℂ,
          starRingEnd ℂ (ψ g) *
            ((w (alpogeNativePartner t g) : ℝ) : ℂ) *
              alpogeNativeFrobInertiaGPsi inertia frob ell ψ
                (a / w (alpogeNativePartner t g))) +
      (∑ g ∈ Finset.univ.filter
        (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g),
        ∑ ψ : AddChar (AlpogeNativeE0 × H) ℂ,
          starRingEnd ℂ (ψ g) *
          (if ψ = 0 then
            ((a * Real.log a - a * Real.log
              (w (alpogeNativePartner t g)) -
                (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ)
          else -(a : ℂ) * ell ψ)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun g hg => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun ψ _ => ?_)
    rw [hinner g hg ψ]
    ring
  have hcorr :
      ∀ ψ : AddChar (AlpogeNativeE0 × H) ℂ,
      (∑ g ∈ Finset.univ.filter
        (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g),
        starRingEnd ℂ (ψ g) *
          (if ψ = 0 then
            ((a * Real.log a - a * Real.log
              (w (alpogeNativePartner t g)) -
                (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ)
          else -(a : ℂ) * ell ψ)) =
      (if ψ = 0 then
        ∑ g ∈ Finset.univ.filter
          (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g),
          ((a * Real.log a - a * Real.log
            (w (alpogeNativePartner t g)) -
              (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ)
       else 0) +
      (if ψ = alpogeNativeChC H then
        (a : ℂ) * ell (alpogeNativeChC H) *
          ((alpogeNativePhiSet H).card : ℂ)
       else 0) := by
    intro ψ
    by_cases h0 : ψ = 0
    · have h1 : ψ ≠ alpogeNativeChC H :=
        fun h => alpogeNativeChC_nontrivial (h ▸ h0)
      simp only [ite_eq_left h0, ite_eq_right h1, add_zero]
      refine Finset.sum_congr rfl (fun g _ => ?_)
      simp [h0]
    · simp only [ite_eq_right h0, zero_add]
      rw [← Finset.sum_mul, alpogeNativeColourSum ψ]
      simp only [ite_eq_right h0]
      by_cases h1 : ψ = alpogeNativeChC H
      · simp only [ite_eq_left h1]
        rw [h1]
        ring
      · simp only [ite_eq_right h1, zero_mul]
  have hB :
      (∑ g ∈ Finset.univ.filter
        (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g),
        ∑ ψ : AddChar (AlpogeNativeE0 × H) ℂ,
          starRingEnd ℂ (ψ g) *
          (if ψ = 0 then
            ((a * Real.log a - a * Real.log
              (w (alpogeNativePartner t g)) -
                (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ)
          else -(a : ℂ) * ell ψ)) =
      (∑ g ∈ Finset.univ.filter
        (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g),
        ((a * Real.log a - a * Real.log
          (w (alpogeNativePartner t g)) -
            (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ)) +
        (a : ℂ) * ell (alpogeNativeChC H) *
          ((alpogeNativePhiSet H).card : ℂ) := by
    rw [Finset.sum_comm,
      Finset.sum_congr rfl (fun ψ _ => hcorr ψ),
      Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hC :
      (∑ g ∈ Finset.univ.filter
        (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g),
        (a * Real.log a - a * Real.log
          (w (alpogeNativePartner t g)) -
            (1 + Real.eulerMascheroniConstant) * a)) =
      ((alpogeNativePhiSet H).card : ℝ) *
        (a * Real.log a - (1 + Real.eulerMascheroniConstant) * a) -
        a * ∑ ρ ∈ alpogeNativePhiSet H, Real.log (w ρ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.sum_const,
      ← Finset.mul_sum,
      alpogeNativeSumPartner t (fun ρ => Real.log (w ρ)),
      alpogeNativeCardNotPhi]
    simp only [nsmul_eq_mul]
    ring
  rw [hsum, hB, ← Complex.ofReal_sum, hC]
  have hPhi := alpogeNativePhiCard_ne_zero (H := H)
  unfold alpogeNativeDe alpogeNativeMAIN
  push_cast
  field_simp
  ring


/-!
## Literal concrete cyclotomic arithmetic host (no imported field theorem)

The original geometry uses the modulus 2^(e+2) * q * d and an additive
host ((Z/2)^2 × H_e), with H_e the dyadic units modulo the sign -1.
We now construct the actual arithmetic map from modular units using
quadratic characters at q,d and the true dyadic quotient. This is
NOT an abstract new source bound or an external RH theorem.
-/

/-- Concrete dyadic local class: units modulo 2^(e+2), quotient -1. -/
abbrev AlpogeNativeDyadicH (e : ℕ) : Type :=
  Additive (((ZMod (2 ^ (e + 2)))ˣ) ⧸
    Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ))

instance (e : ℕ) : Fintype (AlpogeNativeDyadicH e) :=
  Fintype.ofFinite _

instance (e : ℕ) : DecidableEq (AlpogeNativeDyadicH e) :=
  Classical.decEq _

/-- Exactly Alpoge's conductor modulus. -/
def alpogeNativeHostN (e q d : ℕ) : ℕ := 2 ^ (e + 2) * q * d

theorem alpogeNativeD_dvd_hostN (e q d : ℕ) :
    d ∣ alpogeNativeHostN e q d := by
  unfold alpogeNativeHostN
  exact dvd_mul_left d _

theorem alpogeNativeQ_dvd_hostN (e q d : ℕ) :
    q ∣ alpogeNativeHostN e q d := by
  unfold alpogeNativeHostN
  exact dvd_mul_of_dvd_left (dvd_mul_left q _) d

theorem alpogeNativeTwo_dvd_hostN (e q d : ℕ) :
    2 ^ (e + 2) ∣ alpogeNativeHostN e q d := by
  unfold alpogeNativeHostN
  exact dvd_mul_of_dvd_left (dvd_mul_right _ q) d

/-- Physical quadratic sign of a ±1 unit, as an additive bit. -/
def alpogeNativeSign2 : ℤˣ →* Multiplicative (ZMod 2) where
  toFun s := Multiplicative.ofAdd (if s = 1 then 0 else 1)
  map_one' := by simp
  map_mul' := by decide

/-- Genuine quadratic Dirichlet character on the mod-ell unit group. -/
def alpogeNativeLegU (N ell : ℕ) [Fact ell.Prime]
    (h : ell ∣ N) : (ZMod N)ˣ →* ℤˣ :=
  (quadraticChar (ZMod ell)).toUnitHom.comp (ZMod.unitsMap h)

/-- Actual arithmetic residue map of modular units to the complete
two-bit-plus-dyadic additive host. Both sign bits are quadratic and
the third component is a genuine quotient of local units. -/
def alpogeNativeRecMap (e q d : ℕ)
    [Fact q.Prime] [Fact d.Prime] :
    (ZMod (alpogeNativeHostN e q d))ˣ →*
      Multiplicative (AlpogeNativeE0 × AlpogeNativeDyadicH e) where
  toFun u := Multiplicative.ofAdd
    ((Multiplicative.toAdd
        (alpogeNativeSign2
          (alpogeNativeLegU _ d (alpogeNativeD_dvd_hostN e q d) u)),
      Multiplicative.toAdd
        (alpogeNativeSign2
          (alpogeNativeLegU _ q (alpogeNativeQ_dvd_hostN e q d) u))),
      Additive.ofMul
        (QuotientGroup.mk
          (ZMod.unitsMap (alpogeNativeTwo_dvd_hostN e q d) u)))
  map_one' := by
    simp only [map_one]
    rfl
  map_mul' u v := by
    simp only [map_mul]
    rfl

/-- Original actual Frobenius choices on the residue classes, not
free prime labels. This is exactly the arithmetic CRT construction;
existence and uniqueness of the selected unit are separate properties. -/
def alpogeNativeLocalUnits (N p : ℕ) :
    Subgroup (ZMod N)ˣ :=
  (ZMod.unitsMap (Nat.ordCompl_dvd N p)).ker

def alpogeNativeIsFrobUnit (N p : ℕ) (u : (ZMod N)ˣ) : Prop :=
  ((u : ZMod N).cast : ZMod (ordCompl[p] N)) =
      (p : ZMod (ordCompl[p] N)) ∧
  ((u : ZMod N).cast : ZMod (ordProj[p] N)) = 1

def alpogeNativeFrobUnit (N p : ℕ) : (ZMod N)ˣ := by
  classical
  exact if h : ∃ u, alpogeNativeIsFrobUnit N p u then h.choose else 1

/-- Actual complete finite arithmetic host data from modular units. -/
structure AlpogeNativeArithData
    (H : Type*) [AddCommGroup H] [Fintype H] [DecidableEq H] where
  q1 : ℕ
  d : ℕ
  inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H)
  frob : ℕ → AlpogeNativeE0 × H

def alpogeNativeCftData
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (N q d : ℕ)
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H)) :
    AlpogeNativeArithData H where
  q1 := q
  d := d
  inertia p :=
    Subgroup.toAddSubgroup' ((alpogeNativeLocalUnits N p).map r)
  frob p := Multiplicative.toAdd (r (alpogeNativeFrobUnit N p))

/-- No abstract Frobenius or inertia label remains in this data:
both are computed from the same concrete modular-unit character map. -/
def alpogeNativeHostData
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] :
    AlpogeNativeArithData (AlpogeNativeDyadicH e) :=
  alpogeNativeCftData (alpogeNativeHostN e q d) q d
    (alpogeNativeRecMap e q d)

/-- The full native physical ASK/MAIN theorem specialized to Alpoge's
literal modular-unit host. There is no imported geometric theorem:
only the already-proved finite arithmetic identity is used. -/
theorem alpogeNativeConcreteHostASK_sub_MAIN_eq_De
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (ell : AddChar
      (AlpogeNativeE0 × AlpogeNativeDyadicH e) ℂ → ℂ)
    (N : ℕ) (a : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (ha : 0 < a)
    (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 < w ρ)
    (hN : ∀ ρ, alpogeNativeInPhi ρ → a / w ρ ≤ (N : ℝ)) :
    alpogeNativeFullKernelASK
      (alpogeNativeHostData e q d).inertia
      (alpogeNativeHostData e q d).frob N a t w -
      alpogeNativeMAIN ell a w =
    alpogeNativeDe
      (alpogeNativeHostData e q d).inertia
      (alpogeNativeHostData e q d).frob
      ell a t w :=
  alpogeNativeFullASK_sub_MAIN_eq_De
    _ _ ell N a t w ha hw hN


/-!
## Direct arithmetic check of the concrete host's unramified sites

For p prime not dividing the conductor modulus N, the local-unit
kernel is literally trivial. This is proved from the native
ZMod and modular-congruence definitions; no HostLocal witness is assumed.
-/

private theorem alpogeNativeCast_eqNatCast_iff
    {N : ℕ} [NeZero N] (x : ZMod N) (c k : ℕ) :
    (x.cast : ZMod c) = (k : ZMod c) ↔
      x.val ≡ k [MOD c] := by
  rw [← ZMod.natCast_val, ZMod.natCast_eq_natCast_iff]

private theorem alpogeNativeCast_eq_one_iff
    {N : ℕ} [NeZero N] (x : ZMod N) (c : ℕ) :
    (x.cast : ZMod c) = 1 ↔
      x.val ≡ 1 [MOD c] := by
  rw [← alpogeNativeCast_eqNatCast_iff, Nat.cast_one]

private theorem alpogeNativeUnitsMap_eq_one_iff
    {N c : ℕ} [NeZero N] (hc : c ∣ N) (u : (ZMod N)ˣ) :
    ZMod.unitsMap hc u = 1 ↔
      (u : ZMod N).val ≡ 1 [MOD c] := by
  rw [Units.ext_iff, ZMod.unitsMap_val,
    Units.val_one, alpogeNativeCast_eq_one_iff]

private theorem alpogeNativeUnits_ext_modEq
    {N : ℕ} [NeZero N] {u v : (ZMod N)ˣ}
    (h : (u : ZMod N).val ≡
      (v : ZMod N).val [MOD N]) : u = v := by
  apply Units.ext
  have hh := (ZMod.natCast_eq_natCast_iff _ _ N).2 h
  simpa using hh

/-- An ordinary unramified prime has no additional local inertia.
This is the first concrete HostLocal requirement proved, not postulated. -/
theorem alpogeNativeLocalUnits_unramified
    (N p : ℕ) [NeZero N]
    (hp : p.Prime) (hpN : ¬ p ∣ N) :
    alpogeNativeLocalUnits N p = ⊥ := by
  have hcompl : ordCompl[p] N = N :=
    (Nat.ordCompl_eq_self_iff_zero_or_not_dvd N hp).2
      (Or.inr hpN)
  rw [eq_bot_iff]
  intro u hu
  have hu' : (u : ZMod N).val ≡ 1 [MOD N] := by
    have hk : ZMod.unitsMap (Nat.ordCompl_dvd N p) u = 1 :=
      (MonoidHom.mem_ker).mp hu
    have hv := (alpogeNativeUnitsMap_eq_one_iff
      (Nat.ordCompl_dvd N p) u).mp hk
    rw [hcompl] at hv
    exact hv
  rw [Subgroup.mem_bot]
  apply alpogeNativeUnits_ext_modEq
  have hone : ((1 : (ZMod N)ˣ) : ZMod N).val ≡
      1 [MOD N] := by
    rw [← alpogeNativeCast_eq_one_iff]
    simp
  exact hu'.trans hone.symm

end RHLean.Analysis

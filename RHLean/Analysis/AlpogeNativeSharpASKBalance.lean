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

end RHLean.Analysis

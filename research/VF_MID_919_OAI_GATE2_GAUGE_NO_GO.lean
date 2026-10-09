import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.Field.GeomSum

/-!
# GATE-2 is a gauge choice, not a signed VF channel

The #919 OAI weld proposes, for complex compensated character-row amplitudes
`Z_u` and `(X_u, Y_u) = Phi(Z_u) = (Re Z_u - Im Z_u, Re Z_u + Im Z_u)`,

  sum_u |Z_u|^2 = sum_u X_u Y_u + (1/2) sum_u (X_u - Y_u)^2,        (GATE-2)

and reads `sum_u X_u Y_u` as the candidate signed VF Co/Div channel, to be
identified with the original Sector Six Gram.  The pair `(X, Y)` is exactly
`RHLean.Proof.stableFarComplexToRealPair Z`; it is written out here so this
module imports no StrongPNT-dependent research chain.

This module proves that the split carries no information beyond the Hermitian
moment and an arbitrary choice of row phases.

1. `Phi` is realification after multiplying by the fixed scalar `1 + i`.
2. `X Y = Re(Z^2)` and `(X - Y)^2 / 2 = 2 (Im Z)^2`.
3. A row gauge `Z_u -> g_u Z_u` with `|g_u| = 1` fixes every `|Z_u|` but
   moves the signed channel across the whole interval `[-H, H]`, where
   `H = sum_u |Z_u|^2`.  Both endpoints are attained.  A signed-channel or
   anti-diagonal bound valid in every gauge is exactly a bound on `H`.
4. Over the orbit of a primitive `k`-th root of unity with `k > 2`, in
   particular the six sextic units, the signed channel sums to zero.
5. Exact local compensation `G + v^{-1} H = 0` cancels in the linear `Phi`
   layer but makes the two signed channels equal: squaring identifies `w`
   with `-w`.
6. In the natural gauge on the full Dirichlet family modulo `q`, with real
   coefficients, `sum_chi Z_chi^2 = phi(q) sum_{m n = 1 mod q} a_m a_n`.  This
   is a product-inverse correlation, not the diagonal `m = n` that the
   Hermitian moment counts.  For coefficients supported on `[2, N]` with
   `N^2 <= q`, it vanishes for every coefficient vector, and the anti-diagonal
   carries the whole Hermitian energy.

No estimate, independence statement, or new hypothesis is introduced.  The
numerical companion is `scripts/vf_919_gate2_gauge_probe.py`.
-/

noncomputable section
open scoped BigOperators
open Complex

namespace RHLean.Geometry

/-! ## The two GATE-2 summands -/

/-- GATE-2 signed summand `X * Y` for `(X, Y) = (Re z - Im z, Re z + Im z)`. -/
def vf919Gate2Signed (z : ℂ) : ℝ :=
  (z.re - z.im) * (z.re + z.im)

/-- GATE-2 anti-diagonal summand `(X - Y)^2 / 2`. -/
def vf919Gate2AntiDiagonal (z : ℂ) : ℝ :=
  ((z.re - z.im) - (z.re + z.im)) ^ 2 / 2

/-- The realification `Phi` is the standard real pair of `(1 + i) z`.  It is a
fixed complex-linear map followed by the identification `ℂ = ℝ²`, so it can
transport an identity but cannot add information to it. -/
theorem vf919Gate2_coordinates_eq_realify_one_add_I (z : ℂ) :
    (z.re - z.im, z.re + z.im) = (((1 + I) * z).re, ((1 + I) * z).im) := by
  refine Prod.ext ?_ ?_ <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem vf919Gate2Signed_eq_re_sq (z : ℂ) :
    vf919Gate2Signed z = (z ^ 2).re := by
  rw [pow_two, Complex.mul_re]
  unfold vf919Gate2Signed
  ring

/-- The "anti-diagonal energy" is twice the squared imaginary part. -/
theorem vf919Gate2AntiDiagonal_eq_two_im_sq (z : ℂ) :
    vf919Gate2AntiDiagonal z = 2 * z.im ^ 2 := by
  unfold vf919Gate2AntiDiagonal
  ring

/-- Pointwise GATE-2. -/
theorem vf919Gate2_split (z : ℂ) :
    ‖z‖ ^ 2 = vf919Gate2Signed z + vf919Gate2AntiDiagonal z := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  unfold vf919Gate2Signed vf919Gate2AntiDiagonal
  ring

/-- A twist by `m` acts on the signed channel through `m^2`. -/
theorem vf919Gate2Signed_mul (m z : ℂ) :
    vf919Gate2Signed (m * z) = (m ^ 2 * z ^ 2).re := by
  rw [vf919Gate2Signed_eq_re_sq, mul_pow]

/-- Multiplying a row by `i` leaves its Hermitian energy fixed and reverses
its signed channel. -/
theorem vf919Gate2Signed_I_mul (z : ℂ) :
    vf919Gate2Signed (I * z) = -vf919Gate2Signed z := by
  rw [vf919Gate2Signed_mul, vf919Gate2Signed_eq_re_sq, I_sq]
  simp

theorem abs_vf919Gate2Signed_le (z : ℂ) :
    |vf919Gate2Signed z| ≤ ‖z‖ ^ 2 := by
  rw [vf919Gate2Signed_eq_re_sq, ← norm_pow]
  exact Complex.abs_re_le_norm _

theorem vf919Gate2AntiDiagonal_le (z : ℂ) :
    vf919Gate2AntiDiagonal z ≤ 2 * ‖z‖ ^ 2 := by
  rw [vf919Gate2AntiDiagonal_eq_two_im_sq, Complex.sq_norm, Complex.normSq_apply]
  nlinarith [sq_nonneg z.re]

theorem norm_sq_unimodular_mul {m : ℂ} (hm : ‖m‖ = 1) (z : ℂ) :
    ‖m * z‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [norm_mul, hm, one_mul]

/-! ## Both gauge extremes are attained -/

/-- **Aligning gauge.**  Some unimodular phase puts the whole Hermitian energy
in the signed channel and none in the anti-diagonal. -/
theorem exists_unimodular_vf919Gate2Signed_eq_energy (z : ℂ) :
    ∃ m : ℂ, ‖m‖ = 1 ∧ vf919Gate2Signed (m * z) = ‖z‖ ^ 2 ∧
      vf919Gate2AntiDiagonal (m * z) = 0 := by
  by_cases hz : z = 0
  · exact ⟨1, by simp, by simp [hz, vf919Gate2Signed],
      by simp [hz, vf919Gate2AntiDiagonal]⟩
  have hr : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  have hmz : (starRingEnd ℂ) z / ((‖z‖ : ℝ) : ℂ) * z = ((‖z‖ : ℝ) : ℂ) := by
    rw [div_mul_eq_mul_div, mul_comm ((starRingEnd ℂ) z) z, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, div_eq_iff hn]
    push_cast
    ring
  refine ⟨(starRingEnd ℂ) z / ((‖z‖ : ℝ) : ℂ), ?_, ?_, ?_⟩
  · rw [norm_div, Complex.norm_conj, Complex.norm_real, norm_norm, div_self hr]
  · rw [hmz]
    simp [vf919Gate2Signed, pow_two]
  · rw [hmz]
    simp [vf919Gate2AntiDiagonal]

/-- **Anti-aligning gauge.**  Some unimodular phase makes the signed channel
equal to minus the Hermitian energy, and the anti-diagonal twice it. -/
theorem exists_unimodular_vf919Gate2Signed_eq_neg_energy (z : ℂ) :
    ∃ m : ℂ, ‖m‖ = 1 ∧ vf919Gate2Signed (m * z) = -‖z‖ ^ 2 ∧
      vf919Gate2AntiDiagonal (m * z) = 2 * ‖z‖ ^ 2 := by
  obtain ⟨m, hm, hs, -⟩ := exists_unimodular_vf919Gate2Signed_eq_energy z
  have hIm : ‖I * m‖ = 1 := by rw [norm_mul, Complex.norm_I, hm, one_mul]
  refine ⟨I * m, hIm, ?_, ?_⟩
  · rw [mul_assoc, vf919Gate2Signed_I_mul, hs]
  · have h := vf919Gate2_split (I * m * z)
    rw [norm_sq_unimodular_mul hIm, mul_assoc, vf919Gate2Signed_I_mul, hs] at h
    rw [mul_assoc]
    linarith

/-! ## Family level: gauge-uniform channel bounds are Hermitian bounds -/

section Family

variable {ι : Type*}

/-- The GATE-2 total is gauge invariant; only the split between its two
summands moves. -/
theorem vf919Gate2_family_split_gauge {s : Finset ι} (Z g : ι → ℂ)
    (hg : ∀ u, ‖g u‖ = 1) :
    ∑ u ∈ s, (vf919Gate2Signed (g u * Z u) + vf919Gate2AntiDiagonal (g u * Z u)) =
      ∑ u ∈ s, ‖Z u‖ ^ 2 := by
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← vf919Gate2_split, norm_sq_unimodular_mul (hg u)]

/-- A gauge-uniform upper bound on the signed channel is exactly an upper
bound on the Hermitian moment. -/
theorem vf919Gate2_signed_le_all_gauges_iff (s : Finset ι) (Z : ι → ℂ) (A : ℝ) :
    (∀ g : ι → ℂ, (∀ u, ‖g u‖ = 1) →
        ∑ u ∈ s, vf919Gate2Signed (g u * Z u) ≤ A) ↔
      ∑ u ∈ s, ‖Z u‖ ^ 2 ≤ A := by
  constructor
  · intro h
    choose g hg hs _ using fun u => exists_unimodular_vf919Gate2Signed_eq_energy (Z u)
    simpa [hs] using h g hg
  · intro hA g hg
    refine le_trans (Finset.sum_le_sum fun u _ => ?_) hA
    calc vf919Gate2Signed (g u * Z u) ≤ |vf919Gate2Signed (g u * Z u)| := le_abs_self _
      _ ≤ ‖g u * Z u‖ ^ 2 := abs_vf919Gate2Signed_le _
      _ = ‖Z u‖ ^ 2 := norm_sq_unimodular_mul (hg u) _

/-- A gauge-uniform lower bound `-A` on the signed channel is again exactly the
Hermitian bound `H <= A`. -/
theorem vf919Gate2_neg_le_signed_all_gauges_iff (s : Finset ι) (Z : ι → ℂ) (A : ℝ) :
    (∀ g : ι → ℂ, (∀ u, ‖g u‖ = 1) →
        -A ≤ ∑ u ∈ s, vf919Gate2Signed (g u * Z u)) ↔
      ∑ u ∈ s, ‖Z u‖ ^ 2 ≤ A := by
  constructor
  · intro h
    choose g hg hs _ using fun u => exists_unimodular_vf919Gate2Signed_eq_neg_energy (Z u)
    have := h g hg
    simp only [hs, Finset.sum_neg_distrib] at this
    linarith
  · intro hA g hg
    have : ∑ u ∈ s, -‖Z u‖ ^ 2 ≤ ∑ u ∈ s, vf919Gate2Signed (g u * Z u) := by
      refine Finset.sum_le_sum fun u _ => ?_
      have h1 := neg_abs_le (vf919Gate2Signed (g u * Z u))
      have h2 := abs_vf919Gate2Signed_le (g u * Z u)
      rw [norm_sq_unimodular_mul (hg u)] at h2
      linarith
    rw [Finset.sum_neg_distrib] at this
    linarith

/-- A gauge-uniform bound on the anti-diagonal energy is exactly the Hermitian
bound `2 H <= B`. -/
theorem vf919Gate2_antiDiagonal_le_all_gauges_iff (s : Finset ι) (Z : ι → ℂ) (B : ℝ) :
    (∀ g : ι → ℂ, (∀ u, ‖g u‖ = 1) →
        ∑ u ∈ s, vf919Gate2AntiDiagonal (g u * Z u) ≤ B) ↔
      2 * ∑ u ∈ s, ‖Z u‖ ^ 2 ≤ B := by
  constructor
  · intro h
    choose g hg _ ha using fun u => exists_unimodular_vf919Gate2Signed_eq_neg_energy (Z u)
    simpa [ha, Finset.mul_sum] using h g hg
  · intro hB g hg
    refine le_trans ?_ hB
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun u _ => ?_
    have h := vf919Gate2AntiDiagonal_le (g u * Z u)
    rwa [norm_sq_unimodular_mul (hg u)] at h

end Family

/-! ## Root-of-unity orbits kill the signed channel -/

/-- Over the orbit of a primitive `k`-th root of unity with `k > 2`, the signed
channel sums to zero. -/
theorem sum_vf919Gate2Signed_primitiveRoot_orbit {k : ℕ} (hk : 2 < k) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ k) (z : ℂ) :
    ∑ j ∈ Finset.range k, vf919Gate2Signed (ζ ^ j * z) = 0 := by
  have h2 : ζ ^ 2 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt two_ne_zero hk
  have hk2 : (ζ ^ 2) ^ k = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hgeom : ∑ j ∈ Finset.range k, (ζ ^ 2) ^ j = 0 := by
    rw [geom_sum_eq h2, hk2, sub_self, zero_div]
  calc ∑ j ∈ Finset.range k, vf919Gate2Signed (ζ ^ j * z)
      = ∑ j ∈ Finset.range k, ((ζ ^ 2) ^ j * z ^ 2).re := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [vf919Gate2Signed_mul, ← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = ((∑ j ∈ Finset.range k, (ζ ^ 2) ^ j) * z ^ 2).re := by
        rw [Finset.sum_mul, Complex.re_sum]
    _ = 0 := by rw [hgeom, zero_mul, Complex.zero_re]

/-- Over the same orbit the Hermitian energy is `k |z|^2`, so the anti-diagonal
carries all of it. -/
theorem sum_vf919Gate2AntiDiagonal_primitiveRoot_orbit {k : ℕ} (hk : 2 < k) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ k) (z : ℂ) :
    ∑ j ∈ Finset.range k, vf919Gate2AntiDiagonal (ζ ^ j * z) = k * ‖z‖ ^ 2 := by
  have hnorm : ∀ j, ‖ζ ^ j‖ = 1 := fun j => by
    rw [norm_pow, hζ.norm'_eq_one (by omega), one_pow]
  have hsplit : ∀ j, vf919Gate2AntiDiagonal (ζ ^ j * z) =
      ‖z‖ ^ 2 - vf919Gate2Signed (ζ ^ j * z) := fun j => by
    have h := vf919Gate2_split (ζ ^ j * z)
    rw [norm_sq_unimodular_mul (hnorm j)] at h
    linarith
  simp only [hsplit, Finset.sum_sub_distrib,
    sum_vf919Gate2Signed_primitiveRoot_orbit hk hζ z, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, sub_zero]

/-- Sextic instance: the six sextic-unit gauges of one row have total signed
channel zero. -/
theorem sum_vf919Gate2Signed_sextic_orbit (z : ℂ) :
    ∑ j ∈ Finset.range 6,
        vf919Gate2Signed (Complex.exp (2 * Real.pi * I / 6) ^ j * z) = 0 := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * I / 6)) 6 := by
    exact_mod_cast Complex.isPrimitiveRoot_exp 6 (by norm_num)
  exact sum_vf919Gate2Signed_primitiveRoot_orbit (by norm_num) hζ z

/-! ## Exact compensation doubles the signed channel -/

/-- For `G + v⁻¹ H = E`, the signed channels of the two compensating rows
differ by `Re(E (G - v⁻¹ H))`; they do not cancel. -/
theorem vf919Gate2Signed_compensated_sub (G H E v : ℂ) (h : G + v⁻¹ * H = E) :
    vf919Gate2Signed G - vf919Gate2Signed (v⁻¹ * H) = (E * (G - v⁻¹ * H)).re := by
  rw [vf919Gate2Signed_eq_re_sq, vf919Gate2Signed_eq_re_sq, ← Complex.sub_re, ← h]
  congr 1
  ring

/-- **Linear layer cancels, quadratic layer doubles.**  Under exact
compensation `G + v⁻¹ H = 0`, both realified coordinates cancel, while the two
signed channels add to `2 Re(G^2)`. -/
theorem vf919Gate2_exact_compensation (G H v : ℂ) (h : G + v⁻¹ * H = 0) :
    (G.re - G.im) + ((v⁻¹ * H).re - (v⁻¹ * H).im) = 0 ∧
      (G.re + G.im) + ((v⁻¹ * H).re + (v⁻¹ * H).im) = 0 ∧
      vf919Gate2Signed G + vf919Gate2Signed (v⁻¹ * H) = 2 * vf919Gate2Signed G := by
  have hre : G.re + (v⁻¹ * H).re = 0 := by
    have := congrArg Complex.re h
    rwa [Complex.add_re, Complex.zero_re] at this
  have him : G.im + (v⁻¹ * H).im = 0 := by
    have := congrArg Complex.im h
    rwa [Complex.add_im, Complex.zero_im] at this
  refine ⟨by linarith, by linarith, ?_⟩
  have := vf919Gate2Signed_compensated_sub G H 0 v h
  simp only [zero_mul, Complex.zero_re] at this
  linarith

/-! ## Natural gauge on the full Dirichlet family -/

/-- `ℂ` has enough roots of unity of every positive order.  This is proved
locally from `Complex.isPrimitiveRoot_exp` so the module avoids the
algebraic-closure import chain. -/
theorem vf919Gate2_hasEnoughRootsOfUnity (n : ℕ) [NeZero n] :
    HasEnoughRootsOfUnity ℂ n where
  prim := ⟨_, Complex.isPrimitiveRoot_exp n (NeZero.ne n)⟩
  cyc := inferInstance

section Dirichlet

variable {q : ℕ} [NeZero q]

/-- **Natural-gauge signed moment.**  With real coefficients, the sum of the
squared row amplitudes over all Dirichlet characters modulo `q` counts pairs
with `m n = 1 (mod q)`. -/
theorem vf919Gate2_dirichlet_sum_sq (s : Finset ℕ) (a : ℕ → ℝ) :
    ∑ χ : DirichletCharacter ℂ q, (∑ n ∈ s, (a n : ℂ) * χ n) ^ 2 =
      (q.totient : ℂ) * ∑ m ∈ s, ∑ n ∈ s,
        if ((m * n : ℕ) : ZMod q) = 1 then (a m : ℂ) * a n else 0 := by
  haveI : NeZero (Monoid.exponent (ZMod q)ˣ) :=
    ⟨Monoid.exponent_ne_zero_of_finite⟩
  haveI := vf919Gate2_hasEnoughRootsOfUnity (Monoid.exponent (ZMod q)ˣ)
  calc ∑ χ : DirichletCharacter ℂ q, (∑ n ∈ s, (a n : ℂ) * χ n) ^ 2
      = ∑ χ : DirichletCharacter ℂ q, ∑ m ∈ s, ∑ n ∈ s,
          (a m : ℂ) * a n * χ ((m * n : ℕ) : ZMod q) := by
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
        rw [Nat.cast_mul, map_mul]
        ring
    _ = ∑ m ∈ s, ∑ n ∈ s,
          (a m : ℂ) * a n * ∑ χ : DirichletCharacter ℂ q, χ ((m * n : ℕ) : ZMod q) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum]
    _ = (q.totient : ℂ) * ∑ m ∈ s, ∑ n ∈ s,
          if ((m * n : ℕ) : ZMod q) = 1 then (a m : ℂ) * a n else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [DirichletCharacter.sum_characters_eq]
        split_ifs <;> ring

/-- **Short supports have zero signed channel.**  If every coefficient sits on
`[2, N]` with `N^2 <= q`, the natural-gauge GATE-2 signed channel over the full
Dirichlet family vanishes for every real coefficient vector. -/
theorem vf919Gate2_dirichlet_signed_eq_zero_of_short {N : ℕ} (hNq : N * N ≤ q)
    (s : Finset ℕ) (hs : ∀ n ∈ s, 2 ≤ n ∧ n ≤ N) (a : ℕ → ℝ) :
    ∑ χ : DirichletCharacter ℂ q, vf919Gate2Signed (∑ n ∈ s, (a n : ℂ) * χ n) = 0 := by
  have key : ∀ m ∈ s, ∀ n ∈ s, ((m * n : ℕ) : ZMod q) ≠ 1 := by
    intro m hm n hn h
    obtain ⟨hm2, hmN⟩ := hs m hm
    obtain ⟨hn2, hnN⟩ := hs n hn
    have hmn : m * n ≤ q := le_trans (Nat.mul_le_mul hmN hnN) hNq
    have h4 : 2 * 2 ≤ m * n := Nat.mul_le_mul hm2 hn2
    have h1 : ((m * n : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by simpa using h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega : 1 < q)] at h1
    rcases lt_or_eq_of_le hmn with hlt | heq
    · rw [Nat.mod_eq_of_lt hlt] at h1
      omega
    · rw [heq, Nat.mod_self] at h1
      omega
  simp_rw [vf919Gate2Signed_eq_re_sq]
  rw [← Complex.re_sum, vf919Gate2_dirichlet_sum_sq]
  rw [Finset.sum_eq_zero fun m hm => Finset.sum_eq_zero fun n hn => if_neg (key m hm n hn),
    mul_zero, Complex.zero_re]

/-- On the same short supports the anti-diagonal is the whole Hermitian
moment. -/
theorem vf919Gate2_dirichlet_antiDiagonal_eq_energy_of_short {N : ℕ} (hNq : N * N ≤ q)
    (s : Finset ℕ) (hs : ∀ n ∈ s, 2 ≤ n ∧ n ≤ N) (a : ℕ → ℝ) :
    ∑ χ : DirichletCharacter ℂ q, vf919Gate2AntiDiagonal (∑ n ∈ s, (a n : ℂ) * χ n) =
      ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ s, (a n : ℂ) * χ n‖ ^ 2 := by
  have h0 := vf919Gate2_dirichlet_signed_eq_zero_of_short hNq s hs a
  have hsum : ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ s, (a n : ℂ) * χ n‖ ^ 2 =
      ∑ χ : DirichletCharacter ℂ q, vf919Gate2Signed (∑ n ∈ s, (a n : ℂ) * χ n) +
        ∑ χ : DirichletCharacter ℂ q,
          vf919Gate2AntiDiagonal (∑ n ∈ s, (a n : ℂ) * χ n) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun χ _ => vf919Gate2_split _
  rw [hsum, h0, zero_add]

/-- **Non-vacuity.**  A single short atom `n₀` coprime to `q` has zero
natural-gauge signed channel, while its Hermitian moment is at least the
trivial-character contribution `1`. -/
theorem vf919Gate2_dirichlet_short_atom_nonvacuous {N n₀ : ℕ} (hNq : N * N ≤ q)
    (h2 : 2 ≤ n₀) (hN : n₀ ≤ N) (hcop : n₀.Coprime q) :
    ∑ χ : DirichletCharacter ℂ q, vf919Gate2Signed (χ n₀) = 0 ∧
      1 ≤ ∑ χ : DirichletCharacter ℂ q, ‖χ n₀‖ ^ 2 := by
  constructor
  · have h := vf919Gate2_dirichlet_signed_eq_zero_of_short hNq {n₀}
      (by simp only [Finset.mem_singleton]; rintro n rfl; exact ⟨h2, hN⟩) (fun _ => 1)
    simpa using h
  · have hu : IsUnit ((n₀ : ℕ) : ZMod q) := (ZMod.isUnit_iff_coprime n₀ q).mpr hcop
    have h1 : ‖(1 : DirichletCharacter ℂ q) n₀‖ ^ 2 = 1 := by
      rw [MulChar.one_apply hu]
      simp
    rw [← h1]
    exact Finset.single_le_sum (f := fun χ : DirichletCharacter ℂ q => ‖χ n₀‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ _)

end Dirichlet

end RHLean.Geometry

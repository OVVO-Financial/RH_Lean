import «research.ALPOGE_LOCAL_PRIME_FIBRES»

set_option autoImplicit false
noncomputable section
open scoped BigOperators ArithmeticFunction.vonMangoldt
open RHLean.Analysis

example {H : Type*} [AddCommGroup H] [Fintype H] (Q D : H) (i : ℕ)
    (v : ZMod 2 × H → ℂ) :
    localityFibre (fun h : H => ((0 : ZMod 2), (i : ZMod 2), h)) v = -localityMean v ∧
    localityFibre (fun b : ZMod 2 => ((0 : ZMod 2), b, i • Q)) v = -localityMean v ∧
    localityFibre (fun b : ZMod 2 => (b, (i : ZMod 2), i • D)) v =
      v ((i : ZMod 2), i • D) - localityMean v :=
  ⟨locality_two i v, locality_q i Q v, locality_d i D v⟩

example (v : ZMod 2 × ZMod 1 → ℂ) :
    localityFibre (fun b : ZMod 2 => (b, (1 : ZMod 2), (0 : ZMod 1))) v =
      v (1, 0) - localityMean v := by simpa using locality_d 1 (0 : ZMod 1) v

example (v : ZMod 2 × ZMod 1 → ℂ) :
    localityFibre (fun b : ZMod 2 => (b, (0 : ZMod 2), (0 : ZMod 1))) v =
      v (0, 0) - localityMean v := by
  have he : ((2 : ℕ) : ZMod 2) = 0 := by decide
  simpa [he] using locality_d 2 (0 : ZMod 1) v

example {S : Type*} [Fintype S] [DecidableEq S] (s : S) (v : S → ℝ) (w : ℝ)
    (hw : ∀ t, |v s - v t| ≤ w) : |v s - (∑ t, v t) / Fintype.card S| ≤
      (((Finset.univ.erase s).card : ℝ) / Fintype.card S) * w := locality_width s v w hw

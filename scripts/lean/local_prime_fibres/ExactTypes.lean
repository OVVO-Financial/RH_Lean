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
  have h := locality_d 2 (0 : ZMod 1) v
  have he : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [he] at h
  simpa only [nsmul_zero] using h

example {S : Type*} [Fintype S] [DecidableEq S] (s : S) (v : S → ℝ) (w : ℝ)
    (hw : ∀ t, |v s - v t| ≤ w) : |v s - (∑ t, v t) / Fintype.card S| ≤
      (((Finset.univ.erase s).card : ℝ) / Fintype.card S) * w := locality_width s v w hw

example (e q d k : ℕ) (hq : q.Prime) (hd : d.Prime)
    (hQ : q.Coprime (2 ^ (e + 2))) (hD : d.Coprime (2 ^ (e + 2)))
    [Fintype (LocalityDyadic e)] (a b c : ZMod 2 × LocalityDyadic e → ℂ) :
    (Λ (2 ^ (k+1)) : ℂ) * localityFibre (fun h => ((0 : ZMod 2), ((k+1 : ℕ) : ZMod 2), h)) a +
    (Λ (q ^ (k+1)) : ℂ) * localityFibre (fun s : ZMod 2 => ((0 : ZMod 2), s, (k+1) • localityClass e q hQ)) b +
    (Λ (d ^ (k+1)) : ℂ) * localityFibre (fun s : ZMod 2 => (s, ((k+1 : ℕ) : ZMod 2), (k+1) • localityClass e d hD)) c =
    -(Real.log 2 : ℂ) * localityMean a - (Real.log q : ℂ) * localityMean b +
      (Real.log d : ℂ) * (c (((k+1 : ℕ) : ZMod 2), (k+1) • localityClass e d hD) - localityMean c) :=
  locality_primePower e q d (k+1) hq hd (Nat.succ_ne_zero k) hQ hD a b c

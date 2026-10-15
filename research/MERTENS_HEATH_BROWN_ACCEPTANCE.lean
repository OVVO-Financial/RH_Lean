import «research.MERTENS_SIGNED_HYPERBOLA»

open RHLean.Analysis.MertensFiniteExtension

example (a : ArithmeticFunction Int) (k : Nat) :
    ArithmeticFunction.moebius - heathBrownLift a k =
      ArithmeticFunction.moebius * inverseDefect a ^ k := heathBrownLift_error a k

example {N n k : Nat} (hn : n < (N + 1) ^ k) :
    heathBrownLift (mobiusPrefix N) k n = ArithmeticFunction.moebius n :=
  heathBrownLift_prefix_exact hn

example (a : ArithmeticFunction Int) : heathBrownLift a 2 = newtonLift a :=
  heathBrownLift_two a

example (f g : Nat -> Int) {X U V : Nat}
    (hU : U <= X) (hV : V <= X) (hUV : U * V <= X)
    (hcover : X < (U + 1) * (V + 1)) :
    signedHyperbola f g X = leftHyperbola f g X U + rightHyperbola f g X V -
      (Finset.sum (Finset.Icc 1 U) f) * (Finset.sum (Finset.Icc 1 V) g) :=
  signedHyperbola_split f g hU hV hUV hcover

example (f g : ArithmeticFunction Int) (X : Nat) :
    Finset.sum (Finset.range (X + 1)) (fun n => (f * g) n) =
      signedHyperbola f g X := convolution_sum_eq_signedHyperbola f g X

example (f g : ArithmeticFunction Int) {X U V : Nat}
    (hU : U <= X) (hV : V <= X) (hUV : U * V <= X)
    (hcover : X < (U + 1) * (V + 1)) :
    Finset.sum (Finset.range (X + 1)) (fun n => (f * g) n) =
      Finset.sum (Finset.Icc 1 U) (fun i => f i * Finset.sum (Finset.Icc 1 (X / i)) g) +
      Finset.sum (Finset.Icc 1 V) (fun j => g j * Finset.sum (Finset.Icc 1 (X / j)) f) -
      (Finset.sum (Finset.Icc 1 U) f) * (Finset.sum (Finset.Icc 1 V) g) :=
  convolution_sum_hyperbola f g hU hV hUV hcover

example : inverseDefect (mobiusPrefix 10) 11 * inverseDefect (mobiusPrefix 10) 13 = 1 :=
  fresh_prime_defect_product (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

#print axioms RHLean.Analysis.MertensFiniteExtension.inverseDefect_eq_tail_mul
#print axioms RHLean.Analysis.MertensFiniteExtension.inverseDefect_mul_moebius
#print axioms RHLean.Analysis.MertensFiniteExtension.heathBrownLift_error
#print axioms RHLean.Analysis.MertensFiniteExtension.inverseDefect_heathBrownLift
#print axioms RHLean.Analysis.MertensFiniteExtension.heathBrownLift_eq_geometric
#print axioms RHLean.Analysis.MertensFiniteExtension.heathBrownLift_two
#print axioms RHLean.Analysis.MertensFiniteExtension.heathBrownLift_three
#print axioms RHLean.Analysis.MertensFiniteExtension.heathBrownLift_four
#print axioms RHLean.Analysis.MertensFiniteExtension.inverseDefect_zero_below
#print axioms RHLean.Analysis.MertensFiniteExtension.convolution_pow_zero_below
#print axioms RHLean.Analysis.MertensFiniteExtension.heathBrownLift_agrees_below_power
#print axioms RHLean.Analysis.MertensFiniteExtension.heathBrownLift_prefix_exact
#print axioms RHLean.Analysis.MertensFiniteExtension.inverseDefect_prefix_one
#print axioms RHLean.Analysis.MertensFiniteExtension.fresh_prime_defect_product
#print axioms RHLean.Analysis.MertensFiniteExtension.signedHyperbola_split_filtered
#print axioms RHLean.Analysis.MertensFiniteExtension.hyperbola_overlap_sum
#print axioms RHLean.Analysis.MertensFiniteExtension.signedHyperbola_split
#print axioms RHLean.Analysis.MertensFiniteExtension.convolution_sum_eq_signedHyperbola
#print axioms RHLean.Analysis.MertensFiniteExtension.leftHyperbola_eq_prefixSums
#print axioms RHLean.Analysis.MertensFiniteExtension.rightHyperbola_eq_leftSwap
#print axioms RHLean.Analysis.MertensFiniteExtension.signedHyperbola_split_prefixSums
#print axioms RHLean.Analysis.MertensFiniteExtension.convolution_sum_hyperbola

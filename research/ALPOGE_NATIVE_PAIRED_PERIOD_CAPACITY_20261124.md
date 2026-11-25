# Paired period elimination in the native complete signed capacity comparison
2026-11-24, #1201.
Status: exact paper argument and submitted Lean proof text, awaiting hosted verification.
No closed supplier, no unconditional RH claim.

## The upstream cut

The community version's `Count5` gives the lower count, upper count and pairwise
variation of the measured `T`. The native degree and count comparisons below
eliminate the common period term on each fiber using those actual counts.
[Pinned community count definition](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean#L70-L76).

Use the literal Data, original prime-power gain and original MAIN. Let A=sumA,
W=sum_j(1/f)sum_rho log(w_jrho), J=muCC+h-Fo, E_C=cCount*(La+m^2*La/k).
At each u0,u, the required original relative-degree and count inequalities are:

    J <= m*sum_t ph(a_t) - m*A*P - A*log(T) + EDiv
    W + m*(gam-LpL-P) + m*lg - E_C <= log(T).

Since A>=0, multiplying the second by A and combining gives

    J <= MAIN - m*A*lg + A*E_C + EDiv,

using the exact MAIN formula and no sign-discarding. The same actual P
appears on both sides and cancels. No hypothesis P=logOm or lower bound
P>=logOm-rho is needed. No v, h, Fo, muCC, ASK or Ga field is overwritten.
For independently measured periods the residual on the right is
`m*A*(P_count-P_degree)`. The pointwise order `P_count ≤ P_degree` makes
that term nonpositive. Equivalently the count inequality at `P_count`
implies the count inequality at `P_degree` because its coefficient is
`-m`. A positive mismatch contributes the displayed signed amount on that fiber.
In particular a supplier that uses logOm through the independent count
still owes the stated coupled count inequality with the actual P; it is
not automatically implied by this reduction.

## Direct native proof

NativeSquareCapacityPeriod.lean now contains:
- NativeCoupledDegree, NativeCoupledCount, NativeCountRest.
- nativeRelativeDegreeCount_le (exact finite sum cancellation).
- nativeGa_bound_of_coupled_period (use quotient slope lower and the relative
  bound instead of the old absolute-period DIV and Count lower).
- nativeMean_bound_of_coupled_period (same original errorTermWith).
- physicalTopExcess_div_le_errorTerm_of_coupled_period (same physical source
  and exact original positive divisor, no period debt).
- `NativeCoupledCount.mono` and `physicalTopExcess_div_le_errorTerm_of_ordered_periods`
  apply the two measured comparisons under the pointwise order. The physical
  theorem keeps the full signed numerator, projection divisor and error term.

The remaining count upper and pairwise variation, actual mean-loss,
quotient-slope, rank-gap, HH and FParams hypotheses are unchanged. Neither
relative degree nor counting has been proved for a constructed native
family. Thus this is a meaningful elimination of a supplier requirement,
not a proof of the critical estimate. Combined with the earlier offset
normalization, do not require absolute CM period, absolute Fo, or absolute
muCC independently when the two actual relative suppliers can be proved.
The native physical attachment is explicit; the existing strong error
window and scalar size theorems remain usable without a new estimate.

## Disposition

Keep existing CM modules and repair their reached errors, but do not make
their absolute period identity or the upstream definite-side backbone a
mandatory new research target. Attack actual independent local recovery,
relative degree + count together, rank and signed mean loss on a single
native object. The reduction retains all quantitative premises; it may not
be used to choose synthetic relative height or periods.
Four new roots are added to both existing source audit files; no CI
policy, toolchain, or proof check is weakened. No local Lean run.

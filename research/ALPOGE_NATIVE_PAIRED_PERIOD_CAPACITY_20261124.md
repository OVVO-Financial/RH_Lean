# Paired period elimination in the native complete signed capacity comparison
2026-11-24, #1201.
Status: exact paper argument and submitted Lean proof text, awaiting hosted verification.
No closed supplier, no unconditional RH claim.

## The upstream cut

The pinned source
https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32cfa1badf05931879a37c3f8a2b03b4/src/Formalism/SizeWindowBrackets/SBrDiv.lean
already isolates DivFree, CountFree, CountRest and VElim. In particular
VElim permits eliminating the positive scalar v in a paired period comparison.
The native proof uses direct algebra rather than selecting a new v or rewriting
any measured geometry. It permits a *different measured P at each fiber*.

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
If the two supplier periods differ, the cancellation fails: the residual
is m*A*(P_count-P_degree), so require identical periods or pay that debt.
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

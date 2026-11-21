# Alpoge direction in RHLean: a compressed native arithmetic cost step

2026-11-21. Scope: proven algebraic/finite source estimate, not an RH proof. The root-library file is RHLean/Analysis/AlpogeNativeSharpShell.lean. Its exact-head compiler and axiom audit must pass before it can be called Lean-certified.

## Actual arithmetic source and new cost

For a>0, b>0, and b<=w<=b+h with h>=0, the signed tangent-corrected original sharp ASK kernel has exact collar

  C_n = max(a/n-w,0) - max(a/n-b,0) + 1_(a/n>b)*(w-b).

The new source-exact lemma proves without prime-distribution assumptions:

  0 <= C_n <= h*1_(b<a/n<=b+h)

and, with EVERY actual von Mangoldt prime power retained,

  0 <= sum_(1<=n<=N) Lambda(n)*C_n
     <= h*sum_(n in true cutoff shell) Lambda(n)
     <= h*log(N)*#(true cutoff shell).

This is a real quantitative bound on a positive physical cost, not a renamed interface. For positive a,b, the shell is contained in the integer interval [a/(b+h), a/b), so elementary integer counting additionally gives

  shell cardinal <= 1+a*h/[b*(b+h)].

At the original ASK scale a=b*X the width-cost term is bounded by

  h*log(N)*(1 + X*h/(b+h)).

The product X*h^2/b is smaller than the naive X*h width loss when h/b is small. The finite Lambda shell inequalities are in Lean; the last interval-cardinality corollary remains a paper derivation here.

## A failed short amplifier, identified precisely

An independent natural arithmetic multiplicity is the m-fold Dirichlet convolution mu^{*m}. The Euler factor equals (1-z)^m. For a squarefree integer with k different prime factors the coefficient is exactly (-m)^k: on pq it is m^2, and on pqr it is -m^3. Thus an m=sqrt(X) jet has at least cubic unsigned growth already at n=30. This **does not disprove a signed determinant gain**, but it proves that m purely formal Euler/Boolean derivatives do not automatically provide an O(m) cost bound.

Exact integer enumeration for all n<=R^2-1 of g_R(n)=prod_(p^e||n) (-1)^e choose(R,e):
R=8: L1=9615;
R=56: L1=17286300671300;
R=317: L1=12325921622778895012796079471.
These are finite diagnostics, not asymptotic evidence.

## Compressed independent-proof route

1. Native actual Lambda and ASK-MAIN: merged PR #1166.
2. Native original Gz and one-sided square endpoint sampling: open PR #1170.
3. Full matched K2-(Lambda*Lambda) signed Selberg cancellation: on main plus draft #1169. Do not claim the canceled rank-one principal credit as a saving.
4. Local width collar: THIS PR; the genuine Lambda source now has an unconditional narrow-shell cost.
5. Required independent discovery: build a source-specific determinant with m about sqrt(X) genuinely **paid** arithmetic multiplicity, height/covolume and divisibility on the SAME full ASK-MAIN population; prove the normalized global topExcess at root scale. The external geometric theorem cannot be replaced by a Boolean jet or imported as the conclusion.

The present result is deliberately small and unconditional, but it does not close item 5 or prove RH. No claim of a new Mertens exponent. Do not merge without exact-head warning-fatal build, root manifest audit, transitive-axiom audit and human review.

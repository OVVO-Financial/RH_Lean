# Alpöge arithmetic handoff and native consequences

Date: 2026-11-23 (America/New_York).

This change implements the user's request to formalize the exact arithmetic
handoff and its conditional consequences before returning to the upstream
proof of the bound. The source identification is unconditional. The critical
estimate is an explicit hypothesis of every theorem that uses it. This is
conditional transfer infrastructure, not a new unconditional source estimate.

Starting native revision: `5696ba5a8ebaa5c4aa6f6dcdbaf3ec9e639aacb1`, the
human-reviewed merge of #1204. The inspected upstream source is pinned at
`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4` in
[`src/Formalism/StatementOC.lean`](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/StatementOC.lean).

## 1. The exact handoff quantity

The upstream definitions are reconstructed in a native namespace using the
actual Mathlib von Mangoldt function:

\[
S_z(x)=\sum_{1\le n\le\lfloor x\rfloor}\Lambda(n)(x/n-1),
\qquad
G_z(x)=S_z(x)-x\log x+(1+\gamma)x.
\]

The new handoff module proves equality with `alpogeNativePrincipalPrimeSum`
and `alpogeNativeGzArithmetic`. At a natural argument it proves equality with
`nativeAlpogeGz`. This is finite algebra: it requires no estimate, geometric
witness, or RH assumption. All prime powers, the floor endpoint, the kernel,
and the Euler constant are retained. No external Lean module or compiled
upstream proof artifact is imported.

The interface is therefore after the full weighted von Mangoldt expression
has been assembled. A valid proof of a bound on the reconstructed upstream
expression is a proof of the corresponding bound on the native expression.
An isomorphism of the two projects' entire geometric developments is not
required for this equality.

## 2. The quantitative hypotheses and RH consumers

The real-window interface preserves the quantifier order

\[
\forall\eta>0\;\exists C_\eta\;\forall Y_0\;\exists Y\ge Y_0\;
\forall y\in[Y,Y^{1+\delta}],\quad
G_z(y)\le C_\eta y^{1/2+\eta},\qquad\delta>0.
\]

The constant is chosen before the requested location of a window. The bound
holds at every real point of each selected window. A sequence of isolated
good endpoints does not supply this hypothesis. The existing native
`riemannHypothesis_of_Gz_windows` consumes it without additional geometric
premises and concludes Mathlib's original `RiemannHypothesis`.

The separate square-clock interface preserves exactly

\[
\forall\eta>0\;\exists C_\eta\ge0\;\exists R_{0,\eta}\;
\forall R\ge\max(2,R_{0,\eta}),\quad
G_z(R^2-1)\le C_\eta R^{1+\eta}.
\]

It is consumed by the existing native square-clock criterion. Both interfaces
are one-sided. Neither asks for an absolute-value estimate or a separate
bound on each signed constituent.

An eventual all-real critical bound is also transferred to the window
consumer and to the natural arithmetic source. Natural thresholds are
obtained with an explicit ceiling; replacing the constant by its absolute
value preserves the upper bound and provides the required nonnegativity.

### Fixed coefficient and small epsilon

The upstream-style window output has exponent `1/2 + K * ε`, where `K` and
a positive `ε₁` are fixed and estimates are available for every
`0 < ε < ε₁`. Its full windows have endpoint `Y^(3/2)`. The formalization
converts that input into the native all-eta window interface with
`δ = 1/2`.

For each desired positive `η`, choose a sufficiently small positive `ε`
using `|K| + 1`, so that `K * ε ≤ η`. Request a window starting at least at
one. Monotonicity of real powers on that window then gives the desired
exponent. The coefficient of the bound can be replaced by its absolute
value before the window location is chosen. This works for any real fixed
`K`; no positivity assumption on `K` is silently added.

This normalization proves an implication between fully quantified bounds.
It does not construct the upstream families that would supply its premise.

## 3. Exact return to the native signed history

For `N ≥ 1`, put

\[
s_n=\frac{\psi(n)-n}{n(n+1)},\qquad
U_N=\sum_{1\le n<N}\max(s_n,0),\qquad
L_N=\sum_{1\le n<N}\max(-s_n,0).
\]

The native NNS history is exactly

\[
\frac{G_z(N)}{N}
=U_N-L_N+H_N-\log N+\gamma.
\]

The formalization connects the older `alpogeErdosGz` and current
`nativeAlpogeGz` definitions, then proves the normalized identity and the
pointwise equivalence

\[
G_z(N)\le C N^{1/2+\eta}
\quad\Longleftrightarrow\quad
U_N-L_N+H_N-\log N+\gamma\le C N^{-1/2+\eta}.
\]

It also states the equivalent upper-channel inequality with the entire
correction on the right. The eventual quantified equivalence preserves
the same coefficient, exponent loss, and natural threshold in each direction.
The original square endpoint `N = R^2 - 1` has its own conditional RH
consumer using the exact normalized expression.

These are the positive and negative masses of this particular reciprocal
Chebyshev-error source. They are not statements about arbitrary NNS data,
separate bounds on the two masses, or a two-sided error bound.

## 4. Exact return to candidate capacity and composite removal

For any actual finite candidate set `C_N` contained in `[1,N]` and containing
every prime through `N`, the independently defined native masses satisfy

\[
G_z(N)=\mathcal C(C_N,N)-\mathcal D(C_N,N).
\]

Here `𝒞` contains the logarithmically weighted candidate mass, the complete
proper-prime-power correction, and the centering terms. `𝒟` is the weighted
mass removed at the composite candidate sites. Their definitions do not
use `G_z` as an assigned field.

The bound is therefore equivalent to

\[
\mathcal D(C_N,N)\ge
\mathcal C(C_N,N)-C_\eta N^{1/2+\eta}.
\]

The new formalization lifts this pointwise identity to an eventual
quantified equivalence and specializes it to the actual square-prefix
candidate sets. The cutoff condition `cutoff r ≤ r` proves that every prime
is retained; no additional analytic estimate is hidden in that condition.
The square-prefix removal criterion also reaches the native square-clock
RH theorem with its full explicit estimate as input.

The combined `nativeAlpogeConsequences_of_eventualRealBound` theorem returns
RH, the centered-history estimate, and the removal estimate from one eventual
all-real source hypothesis. Its single `C` and `N₀` work simultaneously for
the history and every prime-complete candidate set at every large endpoint.
Both estimates are derived directly from the supplied source bound, without
using RH as an intermediate step. The separate weaker window interface is
not silently strengthened to an all-scale estimate.

This is cumulative weighted accounting through `N`. Subtracting two
one-sided bounds does not give a bound for an individual square interval.
The theorems make no claim of a prime in every consecutive-square interval.

## 5. Formal evidence and remaining work

Implementation:

- [AlpogeNativeBoundHandoff.lean](../RHLean/Analysis/AlpogeNativeBoundHandoff.lean)
  contains the exact source match, explicit sufficient bound interfaces,
  exponent normalization, and conditional RH consumers.
- [AlpogeNativeBoundConsequences.lean](../RHLean/Analysis/AlpogeNativeBoundConsequences.lean)
  contains the normalized history and candidate-removal consequences.
- [ALPOGE_NATIVE_BOUND_HANDOFF_AUDIT_20261123.lean](ALPOGE_NATIVE_BOUND_HANDOFF_AUDIT_20261123.lean)
  checks the public theorem types and guards the transitive terminal axioms
  of the selected roots against the permitted standard list.

Hosted validation evidence belongs to the reviewable PR at its exact source
revision. The acceptance checks are the changed research closure, warning-fatal
native build, root manifest, static assumption scan, and exact elaborated
declaration graph. Lean is executed only in GitHub Actions. An axiom audit
does not discharge an explicit quantitative hypothesis.

What remains for the next task is to verify and transfer a genuine supplier
of one of these complete uniform bounds. The existing intermediate
`Ga_bound5` is not, by itself, that final bound. A supplying proof must retain
its actual recovery, compatibility, signed-source, and total-cost premises,
or directly prove the required complete source estimate. This change does
not establish that a new mechanism is necessary: a valid upstream proof
may be transferred. It also does not certify that the entire upstream
supplying closure has already been checked.

Once a complete bound with one of the stated quantifier patterns is proved,
the relevant conditional native RH theorem needs no further P1/P2/P3
construction. Those obligations concern proving a bound by a particular
mechanism; they are not additional assumptions after the final bound has
been supplied.

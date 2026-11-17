# Owner capacity and complete double-centering

Date: 2026-11-17. Implementation base: `52fdc0cab0fe0cffc4668212a6889423e0090189`.

Status: on main through the human merge of
[PR #1141](https://github.com/OVVO-Financial/RH_Lean/pull/1141), merge commit
`319fc5798658e66baea1fed758b0d4b6dd126889`. All 17 current checks passed at
the final PR head `dfd3197117410ad491d7c94b66448753ae8e4d63`, including all
47 public declarations and 28 exact-type examples. Evidence and source hashes
are recorded in `EV-PR-1141`; the final certification run is
[Preservation source reductions](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44099085547).

Research disposition: **supporting infrastructure**. The source identities and
diagonal/remainder estimates do not supply an independent subcritical
arithmetic estimate. Sections 5–7 explain the exact strength and limits of the
remaining targets. Those sections are mathematical deductions from the
certified ingredients and an independent session review, not additional Lean
declarations or a new endpoint improvement.

## 1. Complete owner capacity throughout the next prefix

Retain the actual Mertens function and strict centered history

\[
K_R=\max_{0\le y<R}\frac{(M(y)-1)^2}{y+1},\qquad
E(R)=\max_{1\le y<R}\frac{|M(y)|}{\sqrt y}.
\]

For an integer `R <= x < R^2`, the owner set is exactly the primes `R < p <= x`.
The map `(p,m) -> p*m`, for `1 <= m <= floor(x/p)`, is injective: two different
owners would give a product of two primes greater than `R` dividing an integer
strictly below `R^2`. Every image lies in `(R,x]`. Therefore

\[
\sum_{R<p\le x}\left\lfloor\frac{x}{p}\right\rfloor\le x-R,
\qquad
D_R(x)\le(x-R)E(R)^2\le3(x-R)K_R.
\]

The first diagonal inequality is generic in the real prefix sequence and
uses the existing `prefixAmplitude` API. The specialization uses `K_R >= 1`,
the actual values `M(1)=1`, `M(2)=0`, and for `y>=3` the centered envelope.
This improves the existing `diagonal_le_log` estimate by removing its entire
factor `1+2*log R`; no positive power is spent on the diagonal.

The same file defines the original full smooth mass, strict owner transport,
and complete signed compensation at every `x<R^2`. It proves

\[
M(x)=S_R(x)-T_R(x),\qquad
M(x)^2=D_R(x)+\Gamma_R(x),
\]

and exact endpoint adapters to the existing `nativeA`, `ownerDiagonal`, and
`fullOwnerGamma`. This native owner Gram is not identified with the different
legal-ancestry Gram by notation alone.

For `B >= 0`, the attached consumer retains its whole signed premise:

\[
\bigl[\forall R\le x<R^2:\ \Gamma_R(x)\le BxK_R\bigr]
\quad\Longrightarrow\quad K_{R^2}\le(4+B)K_R.
\]

Its more general form permits any `L >= K_R`, `C >= 0`, and an explicit premise
`Gamma_R(x) <= C*x*L`. It concludes `K_(R^2) <= (4+C)*L`. Thus a future
subcritical estimate can feed the existing full-prefix machinery. No such
estimate is supplied by the diagonal theorem.

Source: `research/NATIVE_OWNER_DIAGONAL_CAPACITY_20261117.lean`.

## 2. Symmetric centering on the original frozen Euler source

Put `N=R-1`, `X=R^2-1`, `t=(R+1)/(R-1)`, and retain

\[
m_R=\sum_{a<R}\frac{\mu(a)}a,\quad
u_a=\{N/a\},\quad v_{ab}=\{X/(ab)\}.
\]

Actual historical floor inversion gives `sum mu(a)*u_a=N*m_R-1`.
Combining this with the original fractional bilinear decomposition and
`t*N^2=X` proves

\[
Q_R=2(R+1)m_R-t+
\sum_{a,b<R}\mu(a)\mu(b)(t u_a u_b-v_{ab}).
\]

The divisor-row union uses `a divides N OR b divides N`, counted once. Its
literal complement is `Xi_R`, with both ordered orientations and the original
Mobius coefficients retained. The source file proves the exact partition and
an adapter back to the original complex `eulerSelfDualBilinear`.

The quantitative remainder uses the elementary bound `|m_R|<=1`. The complete
divisor-row contribution is bounded using only squarefree divisors: the Mobius
coefficient vanishes on every other row. There are exactly `2^omega(N)`
squarefree divisors, where `omega(N)=N.primeFactors.card`. Thus

\[
|Q_R-\Xi_R|\le2R+5+2(R-1)2^{\omega(R-1)}.
\]

The implementation also proves the bound with the full divisor count
`tau(N)=N.divisors.card`. The pre-existing internally proved divisor estimate
then gives

\[
\forall\varepsilon>0\ \exists C_\varepsilon\ge0\ \forall R\ge2:
\quad |Q_R-\Xi_R|\le C_\varepsilon R^{1+\varepsilon}.
\]

There is no asserted upper bound of this size on `Xi_R` itself.

Sources: `research/EULER_DOUBLE_CENTERED_SOURCE_20261117.lean` and
`research/EULER_DOUBLE_CENTERED_REMAINDER_20261117.lean`.

## 3. DAG placement and unresolved arithmetic

The registry gains two supporting entries: uniform complete owner capacity,
and the complete double-centered frozen-source reduction. They are attached
to the existing native-owner/MU-LIFT and frozen-source/FINITE-AC mechanisms.
The already-certified terminal consumers are reused.

The all-prefix signed bound
`Gamma_R(x)^+ <= C_epsilon*x*R^epsilon*K_R^lambda` with fixed `1<=lambda<2`,
and a sufficient strict historical-power bound for `Xi_R`, remain open.
`OPEN-FINITE-AC`, `OPEN-AMPLIFICATION-SUBPOWER`, `OPEN-MU-LIFT`,
`OPEN-NATIVE-OWNER-FRACTIONAL`, and RH retain their OPEN status.

## 4. Verification contract

The dedicated GitHub Actions workflow compiles the two independent import
closures with warnings fatal at Lean 4.34.1 and the repository's exact Mathlib
pin. Exact-type acceptance fixes the cutoffs, constants, carriers, and explicit
signed hypotheses. Every new public declaration is inventoried and audited
for terminal axioms; the only permitted terminal axioms are `propext`,
`Classical.choice`, and `Quot.sound`. Dependency checks require the original
source identities and the actual new quantitative bounds.

The independent Python regression uses integers and rational arithmetic. It
checks the original Mobius values by factorization and divisor inversion,
all declared small full-prefix owner cases, generic diagonal profiles, the
complete frozen decomposition, and the endpoints 317 and 1027. Negative
controls detect omitted orientations and incorrect root/horizon cutoffs.
Finite regression is supporting evidence, not an asymptotic proof.

## 5. The remaining estimates have the existing graded boundary strength

### 5.1 The complete owner compensation is Mertens energy up to the paid diagonal

Write `Gamma_R(x)^+ = max(Gamma_R(x),0)`. Because the original diagonal is a
sum of squares, the compiled identity and capacity theorem give

\[
\Gamma_R(x)^+\le M(x)^2
\le\Gamma_R(x)^++3(x-R)K_R
\le\Gamma_R(x)^++3xK_R.
\]

Consequently, whenever `L_R >= K_R`, the existence of a uniform constant in
`Gamma_R(x)^+ <= C*x*L_R` is equivalent to the existence of one in
`M(x)^2 <= C'*x*L_R`. The forward direction permits `C'=C+3`; the reverse
permits `C=C'`. These are comparisons of bounds with adjustable constants,
not equality of their optimal constants. The full signed estimate has not
become a weaker arithmetic target by paying the diagonal.

### 5.2 Exact positive-loss grading

Fix `1 <= lambda < 2` and `eta >= 0`. Define the following two assertions,
with constants chosen before both growing scales:

\[
\begin{aligned}
G_{\lambda,\eta}:\quad
&\forall\varepsilon>0\ \exists C_\varepsilon\ge0\quad
\forall R\ge2\ \forall x\in\mathbb N,\ R\le x<R^2:\\
&\Gamma_R(x)^+\le
C_\varepsilon xR^{2\eta+\varepsilon}K_R^\lambda;\\[2mm]
X_{\lambda,\eta}:\quad
&\forall\varepsilon>0\ \exists C_\varepsilon\ge0\ \forall R\ge2:\\
&|\Xi_R|\le C_\varepsilon
R^{1+\eta+\varepsilon}K_R^{\lambda/2}.
\end{aligned}
\]

Here and below `R` is an integer, `Theta = zetaRightmostRealPart`, and
`h=max(Theta,1/2)-1/2`. The exact consequences are

\[
\boxed{
G_{\lambda,\eta}\ \Longleftrightarrow
X_{\lambda,\eta}\ \Longleftrightarrow
(2-\lambda)h\le\eta\ \Longleftrightarrow
\Theta\le\frac12+\frac{\eta}{2-\lambda}.
}
\]

For the forward owner implication, set
`L_R=R^(2*eta+epsilon)*K_R^lambda`. Since `K_R>=1`, the stated parameter
range gives `L_R>=K_R`. The existing preservation consumer yields

\[
K_{R^2}\le(4+C_\varepsilon)
R^{2\eta+\varepsilon}K_R^\lambda.
\]

Use `historical_log_ratio_tendsto` in
[`UNIVERSAL_ENVELOPE_LAWS.lean`](../research/UNIVERSAL_ENVELOPE_LAWS.lean):
`log(K_R)/log(R) -> 2h`. Dividing the logarithm of the preceding inequality
by `log R` gives `4h <= 2eta+epsilon+2lambda*h`. Letting epsilon decrease
to zero proves the displayed boundary, including equality.

Conversely, `envelopeBound_iff_rightmost_le` supplies, for every alpha>0,

\[
|M(r^2-1)-1|\le
A_\alpha r^{1+\eta+\alpha}K_r^{\lambda/2}.
\]

For an arbitrary allowed prefix `x>=3`, put `r=floor(sqrt(x+1))<=R`.
Then `x-(r^2-1)<=2r`, `K_r<=K_R`, and the actual Mobius unit bound gives
`|M(x)-M(r^2-1)|<=2r`. With `alpha=epsilon/2`, squaring gives

\[
\Gamma_R(x)^+\le M(x)^2
\le2(A_{\varepsilon/2}+3)^2
xR^{2\eta+\varepsilon}K_R^\lambda.
\]

The remaining `x=2` case uses `M(2)=0`. This supplies every prefix, not only
the square endpoint.

For Xi, the certified error `|Q_R-Xi_R|<=D_epsilon R^(1+epsilon)` is
absorbed in the displayed scale because `K_R>=1` and `eta,lambda>=0`.
The triangle inequality transfers the bound in both directions with constant
`C_epsilon+D_epsilon`. The existing
[`frozenQEnvelope_iff_rightmost_le`](../research/UNIVERSAL_ENVELOPE_FROZEN_Q.lean)
then gives the same boundary. This Xi equivalence also holds for
`0<=lambda<2`; the owner proof above uses `lambda>=1` to absorb the diagonal.

Thus `eta=0` is an RH-strength target for every fixed `lambda<2` in the
stated range. At `eta>0`, any certified boundary `h<=h_base` already supplies
the grades `eta>=(2-lambda)*h_base`. A different notation or a smaller
historical power accompanied by this compensating loss is not an improvement.
The critical `lambda=2, eta=0` every-positive-loss envelope is already proved
by `universal_frozenQ_envelope`; the displayed ratio is undefined at lambda=2.

### 5.3 Fixed constants and every-positive-loss bounds remain distinct

A single constant `B`, uniform in R and x, in
`Gamma_R(x)^+<=B*x*K_R` gives bounded square-doubling
`K_(R^2)<=(4+B)*K_R`. Conversely, a bound `K_(R^2)<=C*K_R` bounds
`M(x)^2/(x*K_R)` on the whole window, and therefore bounds the positive
compensation. This fixed-constant condition has the bounded historical
square-doubling strength; it must not be identified with its every-positive-
power relaxation. The policy retains finite amplification as a sufficient
criterion whose converse from RH has not been established.

Likewise, the current root-subpower remainder does not by itself transfer a
fixed `C*R*sqrt(K_R)` bound between Q and Xi. It transfers the quantified
positive-loss grades above. No assertion that `2^omega(R-1)` is uniformly
bounded, or absorbed by a fixed multiple of `sqrt(K_R)`, is made.

## 6. What a planted owner model tests

A proposed control must specify its coefficients, summatory function G,
strict historical maximum, actual smoothness mask, owner factorization and
all signed terms. Defining the smooth term afterwards as `S=G+T` verifies
only an arranged algebraic identity. A source comparison must check each
arithmetic premise actually used by the candidate proof.

If a model has verified `|G(n)| asymp n^beta`, with `beta>1/2`, and satisfies
the full energy identity and diagonal bound, then

\[
K_R^G\asymp R^{2\beta-1},\qquad
(\Gamma_R^G(R^2-1))^+\asymp R^{4\beta},\qquad
\frac{(\Gamma_R^G(R^2-1))^+}{(R^2-1)K_R^G}
\asymp R^{2\beta-1}.
\]

Indeed the paid diagonal is only `O(R^(2beta+1))`, strictly below the
endpoint square `R^(4beta)`. Beta=0.9 therefore predicts the normalized
power R^0.8. A graded bound for this model would require
`eta>=(2-lambda)*(beta-1/2)`. This is a conditional scaling calculation,
not a certification of any particular script or finite experiment.

Such a control can refute inference from the shared owner ingredients. A
single beta=0.9 example does not refute every possible exponent improvement.
It also violates the already-paid input `P(b_base)` with `b_base<7/8`.
To test a proposed renewal `P(b) -> P(Phi(b))`, a countermodel must satisfy
all input hypotheses and have `Phi(b)<beta<=b`. A finite table alone does
not prove the model's all-scale growth or identities.

The discriminator need not be a new external analytic theorem. It may be
an already-proved native Mobius identity used in a new quantitative step.
The full normalized divisor-inversion identity determines Mobius uniquely,
so an alternate coefficient model cannot simultaneously retain that complete
identity and represent a different sequence. An owner control is therefore
not automatically a counterexample to the original Euler-floor route.

## 7. The balanced Euler block still contains hyperbolic interactions

For `R/2<a,b<R`, historical floors are one. With `N=R-1`, `P=R+1`,
`X=R^2-1` and `t=P/N`, the exact centered kernel is

\[
\begin{aligned}
J_R(a,b)
&=\left\lfloor\frac{X}{ab}\right\rfloor
-\frac Pa-\frac Pb+t\\
&=1+t-\frac Pa-\frac Pb
+\mathbf1_{ab\le X/2}+\mathbf1_{ab\le X/3}.
\end{aligned}
\]

This has a fixed piecewise smooth shape after rescaling, with at most two
quotient jumps in a row. It is not of constant sign. Exact rational examples
on nondivisor indices with nonzero Mobius products are

\[
J_{10}(6,6)=-4/9,\qquad J_{10}(7,7)=5/63.
\]

On an integer interval rectangle `A x B` lying wholly inside one
constant-quotient cell k,
define `U_A=sum_(a in A) mu(a)` and `V_A=sum_(a in A) mu(a)/a`. Then

\[
\sum_{a\in A,b\in B}\mu(a)\mu(b)J_R(a,b)
=(k+t)U_AU_B-PV_AU_B-PU_AV_B.
\]

The ordinary separate historical and Abel bounds for these products give
`O(R*K_R)`, the critical historical power. This is the precise scope of
the product argument.

The entire balanced block contains the two moving hyperbolic cutoffs.
For a retained balanced index set I, its exact quadratic form is

\[
(1+t)U_I^2-2P U_I V_I+H_{2,I}+H_{3,I},\qquad
H_{j,I}=\sum_{\substack{a,b\in I\\jab\le X}}\mu(a)\mu(b).
\]

On the full balanced index set, the cutoff-matrix rows are nested initial
segments with cutoffs
`floor(X/(j*a))`, j=2,3; their rank is not bounded independently of R.
On the strip `a>2R/3, b>R/2`, the j=3 term vanishes and distinct nonzero
j=2 initial-segment rows are linearly independent. The remaining additive
kernel has rank at most two. Thus the full block cannot be replaced by a
fixed collection of rectangular products. Rowwise bounded variation alone
also does not provide a scale-uniform bound for discrete mixed variation.
For the actual Xi mask, the only divisor of N in the balanced interval is
N itself, so its balanced index interval is `floor(R/2)+1 <= a <= R-2`.
Deleting that one row and column does not bound the cutoff ranks.
These are observations about the kernel's algebraic structure, not lower
bounds or cancellation estimates for the actual Mobius quadratic form.

No subcritical saving has been supplied by the centering identity. A new
argument using genuine Mobius correlations across these cutoff curves, or
interactions with the retained complement, has not been ruled out by this
geometric observation. Any such proposal must identify the first independent
arithmetic estimate and its complete endpoint consumer.

Under [BOOTSTRAP_TO_HALF_V1](RHLEAN_BOOTSTRAP_TO_HALF_20261116.md), owner
capacity and exact double-centering remain reusable supporting infrastructure.
The displayed target equivalences alone do not admit an active candidate.
The Y-tilt remains parked under its already-recorded supplier and continuation
barriers. No new route, zero bound, verified eta, or Lean equivalence is claimed
by this documentation review.

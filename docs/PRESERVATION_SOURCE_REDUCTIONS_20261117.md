# Owner capacity and complete double-centering

Date: 2026-11-17. Implementation base: `52fdc0cab0fe0cffc4668212a6889423e0090189`.

Status: certified by hosted Lean compilation and exact-type, source-dependency,
and terminal-axiom audits at proof head
`5286b43f6a64e9debc4b1be5acba5112c144e2e0` in
[PR #1141](https://github.com/OVVO-Financial/RH_Lean/pull/1141). All 17 checks
passed, including all 47 public declarations and 28 exact-type examples.
The PR is unmerged; the registry keeps this deployment status separate from
the open arithmetic estimates. Evidence and source hashes are recorded in
`EV-PR-1141`; the certification run is
[Preservation source reductions](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44098246482).

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

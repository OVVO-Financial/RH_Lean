# Universal historical envelopes: formalization and exact route equivalences

**PR:** [#1135](https://github.com/OVVO-Financial/RH_Lean/pull/1135).  
**Source baseline:** main `59612bc8b5c30c528d8367667ea5846a8053f114`.  
**Verification:** the core, analytic-kernel and fractional-owner proof sources have passed warning-fatal compilation, exact-type checks and terminal-axiom audits in the pinned GitHub Actions environment. The dated source-head evidence is recorded below. No local Lean execution was used.

This change formalizes the mathematical content needed for the universal-envelope law and its route dictionary. It supplies estimates and equivalences for the existing arithmetic objects. It does not establish an improved zeta-zero boundary, RH, or a finite amplification constant.

## 1. Objects and quantifiers

The definitions already on main are retained:

\[
X_R=R^2-1,\qquad
K_R=\max_{0\le y<R}\frac{(M(y)-1)^2}{y+1},
\]

\[
\alpha_R=\frac{(M(X_R)-1)^2}{R^2K_R},\qquad
A(X)=\max_{R\ge2,\ X_R\le X}\alpha_R,\qquad
q(X)=\frac{\log(1+A(X))}{\log X}.
\]

In particular the history is **strictly below R**. The zero term gives the proved baseline `K_R >= 1` for `R >= 1`. The new prefix budget agrees, for `B >= 2`, with the original uncentered quantity

\[
E(B)=\max_{1\le n<B}\frac{|M(n)|}{\sqrt n}.
\]

The prefix-budget implementation reuses `prefixAmplitude nativeM`; its least-upper-bound theorem explicitly identifies the literal norm/square-root maximum. It is not a substitute centered maximum.

Write

\[
\Theta=\texttt{zetaRightmostRealPart},\qquad
h=\max(\Theta,1/2)-1/2.
\]

The maximum keeps the statements valid under the existing supremum convention for an empty set of nontrivial zeros. The analytic identification `growthExponent_eq_rightmost` is imported from the already proved Mertens converse; it is not assumed as a new project axiom.

`EnvelopeBound lam eta` means

\[
\forall\varepsilon>0\ \exists C\ge0\ \forall R\ge2,
\quad |M(R^2-1)-1|
\le C R^{1+\eta+\varepsilon}K_R^{\lambda/2}.
\]

The order of these quantifiers matters. Constants may depend on the positive loss and fixed parameters; they may not depend on R. A finite amplification constant has a different, stronger quantifier pattern.

## 2. Analytic input: finite inversion and a true historical lower bound

[`UNIVERSAL_ENVELOPE_KERNEL.lean`](../research/UNIVERSAL_ENVELOPE_KERNEL.lean) proves finite Möbius inversion with an arbitrary product weight, its real-cutoff divisor-kernel form, and complex Abel summation. The signed Möbius prefixes are retained until after the exact identity.

For a potential F with F(1)=0 and derivative `kappa(u)/u`, a uniform bound C on its complete divisor kernel yields

\[
\|F(N)\|\le 8C\sqrt{K_N}\sqrt N.
\]

The Abel terminal weight is F(1)=0. Consequently the M(N) boundary term vanishes before taking norms: only n<N enters the historical estimate. No enlarged maximum containing N is introduced.

[`UNIVERSAL_ENVELOPE_ZERO_FORCED.lean`](../research/UNIVERSAL_ENVELOPE_ZERO_FORCED.lean) specializes the construction to an actual zero rho of zeta, with `0 < beta = rho.re < 1`, using the pinned PNT+ Euler estimate and the potential

\[
F_\rho(u)=\frac{1-\rho}{\rho}(u^\rho-1)-\log u.
\]

Its explicit constant is

\[
C_\rho=2|1-\rho|\left(1+\frac{|\rho|}{\beta}\right)+|\rho|+1.
\]

The exposed finite estimate, for integer N>=1, is

\[
\left|\frac{1-\rho}{\rho}\right|(N^\beta-1)-\log N
\le 8C_\rho\sqrt{K_N}\sqrt N.
\]

For beta>1/2, `zero_forces_historical_power` therefore supplies c>0 such that

\[
cR^{2\beta-1}\le K_R
\quad\text{for every sufficiently large integer }R.
\]

This is the required all-scale lower bound. The constants here are deliberately coarser than the original handoff. This PR does **not** claim a Lean certificate for the handoff's continuous integral identity or its sharper `2 sqrt(2)` constant. The exact finite inversion/Abel formulation supplies all the subsequent exponents.

## 3. Complete power laws and logarithmic limits

[`UNIVERSAL_ENVELOPE_ARITHMETIC.lean`](../research/UNIVERSAL_ENVELOPE_ARITHMETIC.lean) proves the upper historical power from a Mertens power and interpolates complete-square endpoint bounds to every integer using `|mu(n)| <= 1`. If Mertens growth is at most b and the envelope has parameters lambda, eta, the new growth exponent is

\[
b_{\mathrm{next}}=\frac12+\frac\eta2+
\frac\lambda2\left(b-\frac12\right).
\]

Evaluating this genuine improvement at the independently defined zero boundary proves the forward dictionary without an imported numerical starting exponent and without assuming a historical lower bound.

[`UNIVERSAL_ENVELOPE_LAWS.lean`](../research/UNIVERSAL_ENVELOPE_LAWS.lean) combines the actual-zero lower bound with the upper Mertens estimate. For every positive tolerance it supplies uniform upper and eventual lower powers for K. It then proves

\[
\lim_{R\to\infty}\frac{\log K_R}{\log R}=2h,
\qquad
|M(R^2-1)-1|\le C_\varepsilon R^{1+\varepsilon}K_R.
\]

[`UNIVERSAL_ENVELOPE_HISTORY.lean`](../research/UNIVERSAL_ENVELOPE_HISTORY.lean) proves the finite inequality

\[
K_Y\le8(1+A(Y))K_{\lfloor\sqrt Y\rfloor+1}.
\]

This uses the exact admitted endpoints and pays their intervening gaps by the unit Möbius bound. Together with the two historical power envelopes it gives a lower bound for `1+A(Y)` at every sufficiently large Y, not merely a sequence of record endpoints.

[`UNIVERSAL_ENVELOPE_AMPLIFICATION_LAW.lean`](../research/UNIVERSAL_ENVELOPE_AMPLIFICATION_LAW.lean) proves both amplification powers and the actual limit

\[
\boxed{\lim_{X\to\infty}q(X)=h.}
\]

[`UNIVERSAL_ENVELOPE_MERTENS_MAX.lean`](../research/UNIVERSAL_ENVELOPE_MERTENS_MAX.lean) supplies the original E coordinate, comparisons `K_B <= 4 E(B)^2` and `E(B)^2 <= 9 K_B`, and

\[
\lim_{B\to\infty}\frac{\log E(B)}{\log B}=h,
\qquad
E(B^k)\le C_{k,\varepsilon} B^\varepsilon E(B)^k
\quad(k\ge1).
\]

All of these limits are along the full integer scale. The near-supremum zero used for a lower power is selected before the scale; this argument does not supply an effective numerical threshold near Theta.

## 4. Exact dictionary, including the original frozen source

For `0 <= lambda < 2` and `eta >= 0`, the terminal theorem is

\[
\boxed{\operatorname{EnvelopeBound}(\lambda,\eta)
\iff \Theta\le\frac12+\frac\eta{2-\lambda}.}
\]

The reverse direction is supplied by the actual historical lower power; it is not left as a hypothesis. `EnvelopeBound 2 0` is the unconditional boundary case, stated separately because the dictionary denominator then vanishes.

[`UNIVERSAL_ENVELOPE_FROZEN_Q.lean`](../research/UNIVERSAL_ENVELOPE_FROZEN_Q.lean) applies the same dictionary to the existing **complete** `eulerSelfDualBilinear` source. It consumes the exact identity

\[
Q_R=2M(R-1)-M(R^2-1)
\]

and bounds the change from the centered numerator by `3R`. Every permitted envelope absorbs this term. Neither mixed orientation, any root correction, nor a sign is removed to obtain the estimate.

[`UNIVERSAL_ENVELOPE_SQUARED_DICTIONARY.lean`](../research/UNIVERSAL_ENVELOPE_SQUARED_DICTIONARY.lean) proves, for p>=2,

\[
\left[\forall\varepsilon>0\ \exists C_\varepsilon\ge0\ \forall R\ge2,
\ (M(R^2-1)-1)^2\le C_\varepsilon R^{p+\varepsilon}K_R\right]
\iff\Theta\le\frac{p-1}{2}.
\]

| Squared root exponent p | Exact zero-boundary ceiling |
|---|---|
| 11/4 | 7/8 |
| 11/4 - 2 delta, with 0<=delta<=3/8 | 7/8 - delta |
| 5/2 | 3/4 |
| 2 | 1/2 |

This is a meter for the strength of an input inequality. It does not produce a new input inequality below the currently certified boundary.

## 5. Equivalent targets and the stronger finite-constant premise

The following equivalences have explicit Lean proofs in this change:

- Zero logarithmic amplification iff `MertensGrowthAtMost (1/2)`.
- Zero native owner loss `NativeOwnerBound 0` iff the same Mertens half-exponent, on the original complete signed owner source.
- Actual uniform fractional owner contraction iff the same half-exponent. Its consumer retains the existing original-source analytic seed and is compiled in the separate fractional job.
- Any fixed subcritical prefix lift r<k iff the same half-exponent. The original existential subpower-gain theorem allows every real r<k, including negative r; the directly quantified every-positive-loss presentation also has a separate nonnegative-r API. The theorem includes **eventual bounds along any integer sequence B_j tending to infinity**, with the exact hypothesis `Tendsto B atTop atTop`. No recurrence relation between successive B_j is needed. The original gain satisfies `log G_j/log B_j -> 0`.

[`UNIVERSAL_ENVELOPE_RH_BRIDGES.lean`](../research/UNIVERSAL_ENVELOPE_RH_BRIDGES.lean) connects the half-exponent, the repository's `MertensEnergyBoundedStatement`, the open-critical-strip zero formulation, and **Mathlib's full `RiemannHypothesis` proposition**. The latter bridge uses the existing unconditional Mertens-energy-to-RH theorem, and proves the reverse restriction directly.

These are equivalences of open arithmetic propositions. Equivalent output targets do not identify their distinct source mechanisms or justify cancelling independent research routes.

The original finite-A target implies the critical squared envelope and RH. Its stronger epsilon-free iteration is retained:

\[
\exists B\ge1\ \forall j\ge0,\qquad K_{2^{2^j}}\le B^j.
\]

This is the exact discrete form behind the polylogarithmic square-root Mertens consequence discussed in the existing `SQUARE_ENDPOINT_STEP_POLYLOG_STRENGTH` module. No implication from RH or zero-log growth to a finite A is added.

## 6. Numerical corrections and proof evidence

The [numerical review](UNIVERSAL_ENVELOPE_NUMERICAL_REVIEW_20261115.md) records the complete reproduced census, the corrected analytic toy-kernel constant, the unbounded toy coefficients and two-endpoint interpolation, and the exact external-record comparator. A sampled kernel maximum is never used as a proved uniform constant. The toy's full asymptotic exponent depends on `max(a,Theta)`; a planted zero alone does not justify replacing that maximum by a.

The archived [original handoff](external/2026-11-15/universal-envelope-law-handoff.md) is preserved for provenance. Its original paper labels and finite numerical interpretations are historical; the corrected statements and status distinctions are in these two review documents and the theorem types.

The dedicated workflow has four independent jobs: bounded numerical checks, complete core proofs, the analytic kernel supplier, and the original-source fractional-owner integration. Core and kernel proofs have no OAI import. Exact-type examples pin the literal definitions and quantifiers; the audit inventories and checks every new public declaration. The only permitted terminal axioms are `propext`, `Classical.choice`, and `Quot.sound`. A failed proof, missing declaration, unrecognized axiom, or source change during verification fails the job.

One infrastructure routing change excludes the two OAI-dependent fractional leaves from the generic native-only research job. Their dedicated fractional job performs full warning-fatal compilation, exact-type checks, and axiom audits using the established pinned ancestor pipeline.

### Verified source evidence

| Proof group | Public declarations audited | Exact-type examples | Successful job |
|---|---:|---:|---|
| Complete core | 118 | 42 | [Core audit at `c401144`](https://github.com/OVVO-Financial/RH_Lean/actions/runs/43775607055/job/133001085271) |
| Independent analytic kernel | 32 | 5 | [Kernel audit at `c401144`](https://github.com/OVVO-Financial/RH_Lean/actions/runs/43775607055/job/133001085451) |
| Original-source fractional owner | 8 | 4 | [Fractional audit at `c401144`](https://github.com/OVVO-Financial/RH_Lean/actions/runs/43775607055/job/133001085509) |

The kernel declarations are a subset of the core inventory, and four owner declarations occur in both the core and fractional inventories. Together the groups verify **122 distinct new public declarations**. Each job recompiles its new source files and acceptance examples with warnings treated as errors, then checks the transitive axioms of every inventoried declaration. The uploaded evidence records source hashes, the import closure, exact types, terminal axioms and the tested commit.

All three proof groups were verified at source head `c401144dedcb6ffd785bd4b25b5830eb83b3c93c`. The observed snapshot at `2026-11-15T23:49:51Z` records **18 of 18 successful repository checks**, with no failed or pending checks. The [complete proof workflow](https://github.com/OVVO-Financial/RH_Lean/actions/runs/43775607055) includes the numerical job. Evidence archives: [core](https://github.com/OVVO-Financial/RH_Lean/actions/runs/43775607055/artifacts/14186066990), [kernel](https://github.com/OVVO-Financial/RH_Lean/actions/runs/43775607055/artifacts/14186257216), and [fractional owner](https://github.com/OVVO-Financial/RH_Lean/actions/runs/43775607055/artifacts/14186717674). Subsequent registry and documentation updates retain these verified Lean source files unchanged. The proof milestone is certified in this unmerged PR; the RH-strength arithmetic propositions remain open.

The compiler is pinned to Lean `v4.34.1`, Mathlib to `d13f23b723b8a846827a245b89c10fc7d3f11612`, and the fractional job's original `openai/math` source to `1581d4cbdd69a0faf34b2089614fe2a814316a6a`. The native core has a complete cold-build path to the PNT+ Euler-summation prerequisite through its declared native targets.

For local non-Lean checks:

```bash
python3 scripts/audit_universal_envelope.py --group core --source-only
python3 scripts/audit_universal_envelope.py --group kernel --source-only
python3 scripts/envelope_kernel_check.py --quick
python3 scripts/envelope_toy_falsifier.py --quick
gcc -O2 -Wall -Wextra -Werror -o /tmp/envelope_census scripts/envelope_census.c -lm
/tmp/envelope_census --quick /tmp/envelope_quick.csv
```

Lean verification remains in the pinned GitHub Actions environment required by the repository. The PR remains unmerged for human review.

# Alpoge -> native signed Selberg -> negative Chebyshev semivariance
Date: 2026-11-21 (status updated 2026-11-22)

## Status

**Unconditional RH-derived mathematical corollary; the native Lean
analytic bridge is not yet discharged.** Three layers are kept separate:

1. **Mathematics (unconditional).** RH is a verified theorem (next
   subsection), and RH implies the LPM2 bound below by the classical
   RH-to-Chebyshev estimate. Conversely the all-\(\varepsilon\) LPM2 bound
   implies RH (section "Converse"), so the estimate is RH-equivalent.
2. **Native RH_Lean arithmetic (Lean, checked by CI).** The exact signed
   identity \(C_R-B_R=E(X_R)\log^2X_R\) with complete prime-power accounting,
   the exact normalized LPM2 identity, the unconditional finite moment
   inequality, and the conditional exponent transfer from
   `NativeSquareDyadicChebyshevBound`.
3. **Not yet in RH_Lean's kernel.** A proof of
   `NativeSquareDyadicChebyshevBound` (RH plus a quantitative RH-to-\(\psi\)
   bound against RH_Lean's own `nativePsi`), and the converse transfer of
   the "Converse" section. Until then the Lean growth theorem keeps that
   supplier as an explicit premise. The premise-free target is recorded as
   `AlpogeNativeSquareNegativeLPM2Endpoint` in
   `RHLean/Analysis/AlpogeNativeLPM2Endpoint.lean`. It is stated, not proved.
   A completed endpoint must prove exactly that statement, with no
   `NativeSquareDyadicChebyshevBound` in its dependency closure.

A *direct* derivation of the same LPM2 estimate from Alpöge's geometric
lattice mechanism (last section) is a separate, independent research
objective and is not claimed here.

### Verification of the RH input (as of 2026-11-22)

- [Joint statement by the Lean and Mathlib communities, endorsed by the Lean
  FRO and the Mathlib Initiative](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/)
  (2026-11-21): certifies that both the statement and the proof are correct.
  The proved theorem was matched to Mathlib's `RiemannHypothesis` by two
  independent tools (comparator and `con-leche --compare`). The exported
  proof was checked by Lean's kernel, con-leche, con-ron and third-party
  checkers.
- [A. Sutherland (MIT), verification files](https://math.mit.edu/~drew/grh/)
  (page updated 2026-11-22 04:35 UTC):
  - all 175,187 modules compile (Lean/Mathlib v4.33.1);
  - the five headline theorems depend only on `propext`,
    `Classical.choice` and `Quot.sound`;
  - `leanchecker` replays every module;
  - nanoda and con-leche accept the full export, and lean4lean accepts every
    compiled module;
  - the `--compare` modes of con-leche and con-ron confirm all five theorems;
  - a sandboxed `lake build` reproduces the export byte for byte.

  At that time the end-to-end `lake comparator` run and the Lean-kernel
  replay of the export were still in progress. "GRH" there means Dirichlet
  L-functions only.

## The unconditional mathematical corollary (RH input verified externally)

Let
\[
X_R=R^2-1,\qquad E(N)=\psi(N)-N
\]
and let \(C_R-B_R\) denote the *complete original* signed second-Selberg
source as defined in
`research/ALPOGE_LITERAL_GZ_SELBERG_TRANSLATION_20261120.lean`.
All prime powers, quotient returns, floor defects and first-Selberg terms
are retained. That source has the **proved algebraic identity**
\[
C_R-B_R=E(X_R)\log^2 X_R.
\]

**Theorem (unconditional as ordinary mathematics, using Alpöge's RH theorem,
verified as described above, and the classical RH-to-Chebyshev explicit
formula).**
For every \(\varepsilon>0\), there exists \(K_\varepsilon\ge0\) such that
for all integers \(H\ge2\),
\[
\sum_{H\le R<2H}\frac{(B_R-C_R)_+^2}{\log^4X_R}
\le K_\varepsilon H^{3+\varepsilon}.
\]
At \(H=1\) the unique term has \(X_1=0\); use the native LPM2
definition directly (the displayed logarithmic quotient is not defined).

**Proof.** By the exact signed source identity, and the positivity of
\(\log X_R\) for \(R\ge2\),
\[
\frac{(B_R-C_R)_+^2}{\log^4 X_R}
=\big(\max\{-E(X_R),0\}\big)^2.
\]
RH holds (Alpöge's theorem, verified as described above). The classical
explicit formula under RH gives constants \(A,x_0\) for which
\[
|E(x)|\le A\sqrt{x}(\log x)^2\quad(x\ge x_0).
\]
Enlarge \(A\) to cover the finitely many smaller square endpoints.
For \(H\le R<2H\), \(X_R<R^2\le4H^2\), and hence
\[
\max(-E(X_R),0)^2\le A'^2R^2\log^4(4H^2)
\le4A'^2H^2\log^4(4H^2).
\]
There are exactly \(H\) integers in the dyadic interval. Therefore
\[
Q_-(H)\le4A'^2H^3\log^4(4H^2)
\le K_\varepsilon H^{3+\varepsilon},
\]
since every fixed power of \(\log H\) is \(O_\varepsilon(H^\varepsilon)\).
This proves the corollary as an unconditional statement of mathematics
with an **external proved RH input**; it is NOT a direct lattice-energy proof.

## Converse: the all-ε LPM2 bound implies RH

**Status: paper proof only. None of the steps below is formalized in
RH_Lean.** In particular, the tail identity, the dyadic summation and the
Landau step are not Lean-checked here.

Write \(E(t)=\psi(t)-t\) and \(N(t)=(t-\psi(t))_+=\max\{-E(t),0\}\), so that
\[
Q_-(H)=\sum_{H\le R<2H}N(X_R)^2
\]
is the native zero-target LPM2 `alpogeNativeSquareNegativeLPM2 H`. By
`alpogeFullMatchedSquareNegativeLPM2_eq_native` it is also the normalized
negative semivariance of the complete signed source \(C_R-B_R\).

**Claim.** Suppose that for every \(\delta>0\) there is \(K_\delta\) with
\(Q_-(H)\le K_\delta H^{3+\delta}\) for all \(H\ge2\). Then for every
\(\delta\in(0,2)\), \(G_z(x)\ll_\delta x^{1/2+\delta/4}\) for large \(x\),
and hence RH holds.

1. **Cauchy–Schwarz.** \(\sum_{H\le R<2H}N(X_R)\le\sqrt{H\,Q_-(H)}\le
   K_\delta^{1/2}H^{2+\delta/2}\).
2. **Monotone interpolation.** \(\psi\) is nondecreasing and
   \(X_{R+1}=X_R+2R+1\). So for \(X_R\le t\le X_{R+1}\),
   \(N(t)\le N(X_R)+2R+1\).
3. **Tail identity.** Partial summation gives
   \(S_z(x)=\sum_{n\le x}\Lambda(n)(x/n-1)=x\int_1^x\psi(t)t^{-2}\,dt\).
   The Laurent expansion of \(-\zeta'/\zeta\) at \(s=1\), together with the
   prime number theorem for convergence, gives
   \(\int_1^\infty(\psi(t)-t)t^{-2}\,dt=-1-\gamma\). Hence
   \[
   G_z(x)=S_z(x)-x\log x+(1+\gamma)x
         =-x\int_x^\infty\frac{\psi(t)-t}{t^2}\,dt
         \le x\int_x^\infty\frac{N(t)}{t^2}\,dt .
   \]
4. **Dyadic summation.** Let \(R_0=\lfloor\sqrt{x+1}\rfloor\), so
   \(X_{R_0}\le x\). For \(R\ge2\) we have \(X_R\ge R^2/2\) and
   \(2R+1\le3R\). By step 2,
   \[
   \int_x^\infty\frac{N(t)}{t^2}\,dt
   \le\sum_{R\ge R_0}\frac{(2R+1)\,(N(X_R)+2R+1)}{X_R^2}
   \le\sum_{R\ge R_0}\Big(\frac{12\,N(X_R)}{R^3}+\frac{36}{R^2}\Big).
   \]
   The second sum is \(\le 72/R_0\). For the first, split \(R\) into blocks
   \([2^k,2^{k+1})\). By step 1, a block contributes
   \(\le 2^{-3k}K_\delta^{1/2}2^{k(2+\delta/2)}=K_\delta^{1/2}2^{-k(1-\delta/2)}\).
   Summed over the blocks meeting \([R_0,\infty)\), this is
   \(\ll_\delta R_0^{-(1-\delta/2)}\). Since \(R_0\asymp\sqrt{x}\),
   \(G_z(x)\ll_\delta x^{1/2+\delta/4}\).
5. **Landau.** Alpöge's
   `ConditionalMainTheorem.riemann_hypothesis_of_power_bound` turns the
   one-sided bound \(G_z(x)\le x^{1/2+C\varepsilon}\), for every small
   \(\varepsilon\) and all large \(x\), into RH. It is the classical Landau
   argument applied to \(\int G_z(x)x^{-s-1}\,dx=-\zeta'(s)/(s(s-1)\zeta(s))\)
   plus elementary terms.

Together with the corollary above,
\[
\big(\forall\delta>0:\ Q_-(H)\ll_\delta H^{3+\delta}\big)\iff\mathrm{RH}.
\]
Porting route inside RH_Lean: start from the existing exact identity
\(G_z(N)=N\cdot\mathrm{centeredErdosHistory}(N)\)
(`RHLean/Analysis/AlpogeGzErdosReciprocalHistory.lean`), then add the tail
identity using the pinned PNT+, and the Landau step.

## What the newly added native Lean module actually proves

`RHLean/Analysis/AlpogeNegativeSelbergSemivariance.lean` includes:

1. `alpogeFullMatchedSecondSelberg_eq_nativeError`: exact complete original
   signed Selberg identity, with both lower logarithmic and floor-defect
   terms, and the genuine fully matched prime-power source.
2. `alpogeFullMatchedSquareNegativeLPM2_eq_native`: exact equality of the
   normalized squared negative matched source with the native zero-target
   LPM2 on all square endpoints \(H\le R<2H\), \(H\ge2\). No
   cancellation is assumed after splitting terms.
3. `alpogeNativeSquareNegativeLPM2_le_uniform`: the genuinely
   unconditional *finite* inequality
   \(Q_-(H)\le H\cdot\max_{H\le R<2H}|E(X_R)|^2\).
4. `alpogeNativeSquareNegativeLPM2_of_dyadicChebyshev`: a proved
   exponent-preserving implication from a **named** quantitative
   pointwise square-root supplier to the required \(H^{3+\varepsilon}\)
   negative semivariance bound.

**Lean verification status:** these declarations count as checked only once
hosted CI passes on the current PR head, covering both the root `RHLean`
build and the research-closure build of
`research/ALPOGE_LITERAL_GZ_SELBERG_TRANSLATION_20261120.lean`. The
downstream critical bound still has `NativeSquareDyadicChebyshevBound` as an
explicit premise.

## The remaining cross-repository import and classical bridge

These are separate obligations, not silently axiomatized facts:

* Import the verified theorem `riemannHypothesis` (`Main.lean`, proved by
  `rhOfAll`) from Alpöge's library into a compatible environment. Mirrors
  include `CocoSgt/riemann-hypothesis-lean` and `Deicyde/riemann-hypothesis`.
  That library is built with Lean/Mathlib v4.33.1, while RH_Lean is pinned at
  Lean 4.34.1 with a different dependency graph. An `.olean` from another
  toolchain is not a substitute.
* Supply and check the quantitative *RH -> psi(x)-x* explicit-formula
  theorem against RH_Lean's actual `nativePsi` (sum of all prime-power
  von Mangoldt weights) and turn its logarithms into square-root-index
  exponent bounds.
* Compose these suppliers with
  `alpogeNativeSquareNegativeLPM2_of_dyadicChebyshev`.

Do NOT claim a self-contained Lean proof of the unconditional estimate
until those three steps are kernel checked.

## Why no isolated band or covariance can shortcut this

The already verified `alpogeNNSBand_principalMode_cancels` and
`alpogeNNSSecondSelbergSource_eq_first_times_log` show that
\(K_2-(\Lambda*\Lambda)=-\Lambda\log\) *for the same physical source*.
The apparent isolated near-root \(-S_R^2\) principal gain is canceled
by the ordered product convolution. A negative quadratic band gain cannot
be counted again as a free credit.

The prospective **direct** lattice-to-LPM2 theorem must therefore pay
\[
\sum_{H\le R<2H}
 \frac{[-(A_R+F_R)]_+^2}{\log^4X_R},
\qquad A_R+F_R=E(X_R)\log^2X_R,
\]
using the *full* joint covariance, and must account for the reciprocal
\(\Lambda\) channel when passing from Alpoge's one-sided \(G_z\) estimate
to the negative Chebyshev error. The exported geometric route need not
prove this particular moment bound directly, so it is a new proof goal.
By the "Converse" section, an unconditional direct proof of this LPM2 bound
would itself be an independent proof of RH. This is the separate research
objective, distinct from formalizing the now-verified RH consequence in
native arithmetic.

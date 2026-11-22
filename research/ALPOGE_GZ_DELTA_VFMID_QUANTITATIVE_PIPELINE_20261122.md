# Alpöge Gz × VF_mid: the real delta(t) and native signed source

**Implementation:** PR #1184; files
\`RHLean/Analysis/AlpogeGzVFMidDeltaTransfer.lean\` and
\`RHLean/Analysis/AlpogeGzPrimeDeltaArithmetic.lean\`.
**Audit principle:** An exact identity is not a power-saving bound;
a proved theorem about RH is not automatically a proved Lean theorem
\`RH -> Gz O(sqrt x)\`.

## 1. Every REAL cutoff: classical delta = actual VF discrepancy + deterministic error

Use the *same* real prime staircase as RH_Lean's von-Koch bridge:
\[
L_2(t)=\int_2^t\frac{du}{\log u},\quad
\Delta(t)=\pi(t)-L_2(t),\quad
D_{\rm VF}(t)=\pi(t)-VF_{\rm mid}(t),\quad
Q(t)=VF_{\rm mid}(t)-L_2(t).
\]

Then exactly, at every \(t\),
\[
\boxed{\Delta(t)=D_{\rm VF}(t)+Q(t).}
\]

Existing compiled theorem:
\`vfMidPrimeLiError_eq_primeError_add_liError\`.
New explicit Alpöge-facing theorem:
\`alpogeRealPrimeDelta_eq_vfMid_add_quadrature\`.

At squares, RH_Lean's *unconditional* midpoint-quadrature theorem gives
\(|Q(R^2)|\le C_{\rm quad}\). Do NOT infer \(|Q(t)|=O(1)\)
uniformly for all real t or \(\int K_x Q=O(1)\).

## 2. THE correct continuous Abel kernel (including its sign)

Set
\[
K_x(t)=\frac1t+\frac{x(\log t-1)}{t^2}
       =-\frac{d}{dt}\left[\log t\left(\frac{x}{t}-1\right)\right].
\]

Then **exactly**, pointwise,
\[
K_x(t)\Delta(t)=K_x(t)D_{\rm VF}(t)+K_x(t)Q(t).
\]

Its formal signed interval-integral companion is proved under the
corresponding integrability hypotheses, and its finite sum companion
is proved for *arbitrary* real (even negative) test weights.

Mathematically, standard partial summation over *genuine* primes
then gives, for \(x\ge2\):
\[
\begin{aligned}
G_z(x)
={}&\int_2^x K_x(t)\Delta(t)\,dt\\
&+\sum_{\substack{p^k\le x\\k\ge2}}
   \log p\left(\frac{x}{p^k}-1\right)\\
&+(\gamma-\log2)x+2.
\end{aligned}
\tag{A}
\]

Substitute the EXACT delta decomposition to obtain
\[
\boxed{
G_z(x)=\int_2^x K_x(t)D_{\rm VF}(t)\,dt
       +\int_2^x K_x(t)Q(t)\,dt
       +PP(x)+(\gamma-\log2)x+2.
}
\tag{B}
\]

**Formalization status:** The original real-cutoff delta identity
and its weighted integral linearity are in Lean. The complete real
Stieltjes/partial-summation step establishing (A) is not yet a theorem
in the new modules; it must not be silently claimed from the
linearity statement.

## 3. COMPLETED exact discrete analogue of the whole source

For integer \(N\ge1\), put
\[
W_N(n)=\log n\left(\frac Nn-1\right),\quad
\Delta_n=\pi(n)-L_2(n),\quad
L'_n=L_2(n)-L_2(n-1).
\]
Define genuine higher-prime-power mass as
\[
PP_N=\sum_{\substack{1\le n\le N\\n\ {\rm not\ prime}}}
     \Lambda(n)\left(\frac Nn-1\right).
\]

The new Lean module establishes every identity in the chain
\[
\begin{aligned}
G_z(N)
={}&\sum_{n=1}^N
   W_N(n)(\pi(n)-\pi(n-1))+PP_N-N\log N+(1+\gamma)N\\
={}&\sum_{n=1}^N W_N(n)(\Delta_n-\Delta_{n-1})
  +\sum_{n=1}^N W_N(n)L'_n\\
&\quad+PP_N-N\log N+(1+\gamma)N.
\end{aligned}
\tag{C}
\]

Using the actual all-real \(D_{\rm VF}+Q=\Delta\) at the natural
sites \(n,n-1\) produces the exact physical source:
\[
\boxed{
\begin{aligned}
G_z(N)
={}&\sum_{n=1}^N W_N(n)
  \left[D_{\rm VF}(n)-D_{\rm VF}(n-1)\right]\\
 &+\sum_{n=1}^N W_N(n)[Q(n)-Q(n-1)]\\
 &+\sum_{n=1}^N W_N(n)[L_2(n)-L_2(n-1)]\\
 &+PP_N-N\log N+(1+\gamma)N .
\end{aligned}}
\tag{D}
\]

No prime powers are lost: \`PP_N\` is the literal nonprime
von-Mangoldt sum. No absolute values intervene before (D).
This is a nontrivial exact native arithmetic translation,
not a \`def residual := Gz - alleged approximation\` tautology.

Theorems:
- \`nativeAlpogeGz_eq_lambdaRamp\`
- \`alpogeNativeLambdaRamp_eq_prime_add_higher\`
- \`alpogeNativePrimeRamp_eq_primeLogRamp\`
- \`alpogePrimeCountIncrement_eq_indicator\`
- \`alpogePrimeIncrement_eq_delta_add_li\`
- \`alpogeOrdinaryPrimeRamp_eq_delta_add_li\`
- \`alpogeDeltaFiniteAbelHistory_eq_vfMid_add_quadrature\`
- \`nativeAlpogeGz_eq_weightedVFMidDelta_and_primePowers\`.

## 4. Square-lattice sampling and NNS

The earlier same-PR module proves an exact signed interpolation
\[
G_z(N)=\operatorname{Chord}_R(G_z)(N)+J_R(N)-P_R(N)
\]
on \([R^2,(R+1)^2]\), and \(|J_R-P_R|\le L(2R+1)\)
with an explicit absolute constant \(L\) from Mertens 1.

**If** the authentic source (D) is proved to satisfy, for some
\(C\ge0\), every \(R\ge2\),
\[
|G_z(R^2)|\le CR,
\tag{SQ}
\]
then Lean's downstream theorems yield
\[
|G_z(N)|\le(2C+3L)\sqrt N\quad(N\ge4)
\]
and the complete signed NNS reciprocal-history estimate
\[
\left|\texttt{nativeAlpogeCenteredHistory}(N)\right|
\le\frac{2C+3L}{\sqrt N}.
\]

Names:
\`alpogeSquareCritical_of_complete_VFMid_source\`,
\`alpogeCriticalAllGz_of_square\`,
\`alpogeCriticalNNSHistory_of_square\`.

The already proved
\`vfMidVonKochBounded_iff_primeLiVonKochBounded\`
then gives the exact VF / Li quantitative equivalence, with
\`vfMidSquareEndpointVonKochBounded_iff_primeLiVonKochBounded\`
recovering the square-cutoff form.

## 5. Source audit of the **UPSTREAM** terminal theorem

The Alpöge public source provides:
\`Main.riemannHypothesis : RiemannHypothesis\`,
via \`rhOfAll\`, \`allChi\`,
\`UpperTheory.FinalTheorems.everyCharacter\`, and
\`UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter\`.
It ALSO supplies the exact representation theorem
\`UpperTheory.Comparison₂.Gz_eq\`:
\`Formalism.Gz = An.G = Deduction.G\` at each real cutoff.

These two statements are *not* themselves a Lean proof of the
downstream theorem \`RiemannHypothesis -> |Gz(x)| <= C*sqrt x\`.
That requires the smoothed explicit formula and summability of
\(1/|\rho(\rho-1)|\), or a direct geometric quantitative statement
with the correct physical Gz normalization.

The proposed Lean interface is named
\`AlpogeRHToSharpGzAndVonKochStatement\`; its **inhabitance is open**
in RH_Lean. Nothing in this PR creates an \`axiom\` or \`sorry\`
to supply it. A complete source-to-source Lean import of Alpöge's
Main theorem would also require matching the upstream Lean toolchain
and verifying the exact dependencies.

**The outstanding new work is now sharply identified:**

1. Verify and expose upstream terminal \`RiemannHypothesis\` on a
   compatible Lean build; avoid copying it as an opaque theorem.
2. Prove the *analytic transfer* \`RH -> Gz O(sqrt x)\` (and classical
   \`RH -> pi-Li O(sqrt x log x)\`) in Lean, or extract a later
   quantified one-sided \(G_z\) estimate from Alpöge's geometric route.
3. Feed its square restriction into the already-proved (SQ) consumer.
4. Close the equivalence back to the original signed VF, Li and NNS
   coordinates. The only analytic input of Step 3 must be visible.

Never substitute the conditional \`CoreAt\` / \`ValuesAtX\`
estimate or another \`topExcess\` condition as an unconditional theorem.

## Build compatibility: native Lake roots versus historic research imports

The two validated VF_mid sources under `research/` are used by both the
research-closure runner and the native `RHLean` root build. The former has
historically compiled these modules to **flat** output files
`.lake/build/lib/lean/research.VF_MID_*.olean`. Lean source therefore imports
them as the quoted single-atom names `«research.VF_MID_*»`.

A dotted Lake root such as `\`research.VF_MID_VON_KOCH_BRIDGE` instead
selects a hierarchical output `research/VF_MID_VON_KOCH_BRIDGE.olean`,
which **does not satisfy** the historic quoted import. This caused the
November 22 hosted build failure before elaboration of the new theorems.

The PR now registers exactly the two **quoted** Lake roots and includes two
tracked symbolic links at the repository root:
`research.VF_MID_VON_KOCH_BRIDGE.lean` and
`research.VF_MID_LI_UNIFORM_QUADRATURE.lean`.
They point to the original files in `research/`; the original research
source and its import spelling remain unchanged. Lake and the research-closure
compiler then produce the same module names and reuse the original
mathematics, without globbing the exploratory research tree.

Acceptance requires both the native hosted build and the research-closure
checks to succeed. This is a compiler/import fix, not a new RH-strength
arithmetic estimate.

## Post-merge validation

The branch has been synchronized with the current `main` proof and
retains all three new signed Gz/VF/NNS root imports in the sorted root
manifest. The full build must explicitly check both exact flat
research-module imports and the new arithmetic modules. This merge
resolved the former GitHub conflict; it does **not** supply the still
open unconditional sharp Gz estimate. CI and the no-owned-warning
audit remain the only acceptance criteria for this compiler repair.

# Alpöge \(G_z\): exact signed square-lattice interpolation

**Status:** Source-exact arithmetic reduction. The interpolation formula,
two-sided local slope, and propagation are Lean theorems proposed in this PR.
The RH-strength square-endpoint estimate is **not** claimed or proved.

## The actual arithmetic, not a VF fantasy proxy

Write, at positive integer endpoints,

\[
G_z(N)=A(N)-F(N)+(1+\gamma)N,\quad
A(N)=N\sum_{n\le N}\frac{\Lambda(n)}n-\psi(N),\quad
F(N)=N\log N.
\]

The complete prime-power source \(A(N)\) is never replaced with a
surrogate, average, nonnegative majorant, or a separately estimated
Selberg band.

Take \(a=R^2\), \(b=(R+1)^2\), \(a\le N\le b\), and
\(t=(N-a)/(b-a)\). Let \({\rm Chord}(f)(N)=(1-t)f(a)+tf(b)\).

The following **exact signed identity** holds without RH:

\[
\boxed{
G_z(N)-{\rm Chord}(G_z)(N)
 =
\underbrace{{\rm Chord}(F)(N)-F(N)}_{J_R(N)}
 -
\underbrace{[{\rm Chord}(A)(N)-A(N)]}_{P_R(N)} .
}
\]

In the code:
- \`alpogeSquareLogChordDefect\` is \(J_R\);
- \`alpogeSquareArithmeticChordDefect\` is \(P_R\);
- \`alpogeSquareSignedCorrection\` is \(J_R-P_R\);
- \`nativeAlpogeGz_sub_squareChord_eq_signedCorrection\` is the
  source-preserving identity.

The cancellation \(J_R-P_R\) is exact, not a proposed conjecture.

## The proved unconditional local bound

Mertens' first theorem in \`NativePNTSelberg\` gives

\[
-1\le \sum_{n\le N}\Lambda(n)/n-\log N\le\log 4+2.
\]

Together with the exact one-step recurrence for \(G_z\) and elementary
bounds for \((N+1)(\log(N+1)-\log N)\), this yields the two-sided
uniform slope bound

\[
|G_z(N+1)-G_z(N)|\le L,
\qquad
L=\log 4+5+|\gamma|.
\]

The existing \`AlpogeSquareClockSignedHistorySampling.lean\` proved only
the forward one-sided slope. This PR proves the missing reverse slope,
telescopes both sides and interpolates using barycentric weights.

In particular, for \(R^2\le N\le(R+1)^2\),

\[
\boxed{
|J_R(N)-P_R(N)|\le L(2R+1).
}
\]

This \(O(R)\) interpolation loss is unconditional. It is enough to
preserve the critical \(O(R)\) endpoint exponent.

**Important:** The potentially stronger \(O(\log R)\) local bound
discussed earlier is *not* asserted here. Establishing that would
require a separate, sharper local-shell calculation; the critical
square-to-global implication does not need it.

## Complete critical-scale propagation

If the *genuine arithmetic* square-bound witness holds:

\[
\boxed{
(\exists C\ge0)(\forall R\ge2)\;
|G_z(R^2)|\le C R,
}
\tag{SQ}
\]

then the following is formally derived from the unconditional
interpolation theorem:

\[
\boxed{
(\forall N\ge4)\quad
|G_z(N)|\le (2C+3L)\sqrt N.
}
\tag{ALL}
\]

The pre-existing native Erdős identity

\[
G_z(N)=N\left(
  \texttt{nativePNTWeightedErrorMass}(N-1)
  +H_N-\log N+\gamma
\right)
\]

then yields the same quantitative statement for the original complete
signed NNS reciprocal history:

\[
\left|
  \texttt{nativeAlpogeCenteredHistory}(N)
\right|
\le
\frac{2C+3L}{\sqrt N}.
\]

The Lean names are:
- \`nativeAlpogeGz_square_lattice_signed_remainder\`
- \`nativeAlpogeGz_square_lattice_exact\`
- \`nativeAlpogeGz_all_of_square_lattice_critical\`
- \`nativeAlpogeCenteredHistory_all_of_square_lattice_critical\`.

## Related criteria

The Omega Institute’s $U(x)$ agrees with $G_z(x)$ at integer arguments. Under RH its envelope theorem bounds $e^{-y/2}|U(e^y)|$ for all sufficiently large $y$. Taking $y=\log(R^2)$ and enlarging the constant for the finitely many early squares gives (SQ). [Definition of $U$](https://github.com/the-omega-institute/trureturing/blob/bfe7fd370bcd2a0f97d0921c00b334020cdb585e/D5/S3/Arith/Robin/CompleteMertensPeak.lean#L43-L45) and [envelope theorem](https://github.com/the-omega-institute/trureturing/blob/bfe7fd370bcd2a0f97d0921c00b334020cdb585e/D5/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope.lean#L196-L200).

Conversely, (ALL) extends to real $x$ because the arithmetic sum is affine between integers and the smooth term has second derivative $-1/x$. The one-sided criterion for this same ramp at $\theta=1/2$ then gives RH directly. [bramble_trace, Theorem 1](https://rstation.ai/problems/riemann_hypothesis/papers/190).

There is also an ordinary-prime criterion. The dyadic prime-power deficit $-U(x)+3U(x/2)-2U(x/4)$ is then $O(\sqrt x)$. Removing higher prime powers costs $O(\sqrt x)$. If RH fails, the ordinary-prime deficit exceeds $x^\theta$ at arbitrarily large squares for some $\theta>1/2$, contradicting that bound. The square case appears in bramble_trace’s earlier proof. Crossley gives both signs at every fixed power. [Earlier square result, revision 24](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=24) and [Crossley’s fixed-power theorem](https://doi.org/10.5281/zenodo.24414757).

## Unpaid mathematical frontier

(SQ) remains the actual RH-strength claim. No proof of (SQ) is present
here or in the previously identified ASK/MAIN cost-route files.
The earlier PR \`#1182\` identifies the full finite character
ASK−MAIN source with native NNS partial moments, but does not
unconditionally discharge that source's global cost bound.

The task for Alpöge's independently checked geometric/automorphic
route is now sharper: **prove only (SQ), or a comparable one-sided
critical endpoint inequality if that is what the original argument
actually supplies.** The square-to-all theorem and native signed
history transfer do not need to be repeated.

The extension is proved only for integer \(N\), which matches the
current native Gz definition. A continuous-real source may be handled
by the same arithmetic kernels but is not asserted in this PR.

## Verification

Run the repository's ordinary root import, research closure and Lean
audit gates. Inspect \`#print axioms\` for the exported theorems. Do not
merge on the strength of a source-text argument alone.

No \`sorry\`, imported RH statement, vacuous certificate, or hypothetical
square-bound is presented as an unconditional result.

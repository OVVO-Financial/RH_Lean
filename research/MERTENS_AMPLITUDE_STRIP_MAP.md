# Mertens amplitude band mapped to horizontal strip coordinates

User-directed finite-scale formalization, 2026-10-15. Base:
`main@1434da1159fb33e16567dc5d07cb381d7868898a`, which includes merged #949.
Live `AGENTS.md` and `CURRENT_PROOF_CONTRACT.md` were read from this pinned base.
This addition does not change the canonical VF, actual arithmetic, or existing theorems.

## Exact finite map

For every real x > 1 and positive amplitude A, define

\[
 s_x(A)=\frac{\log A}{\log x},\qquad A^*=\frac{x}{A}.
\]

The inverse is x raised to the coordinate. For every real l,u:

\[
 A\in[x^l,x^u]\quad\Longleftrightarrow\quad s_x(A)\in[l,u].
\]

`image_amplitudeBand` additionally proves equality of the image of the full
amplitude interval with the full horizontal interval. There is no sampling
approximation and no asymptotic limit in this result.

The special interval requested is

\[
 [x^{1/8},x^{7/8}]\longleftrightarrow[1/8,7/8].
\]

The full interval [1,x] maps to [0,1]. Unit amplitude maps to 0, linear
amplitude to 1, and sqrt(x) to 1/2. Every real power x^s maps to s.

## Exact reflection and crossing

\[
 s_x(A^*)=1-s_x(A),\quad A A^*=x,\quad (A^*)^*=A.
\]

The unique positive fixed point is sqrt(x). A symmetric amplitude band
[x^(1-a),x^a] is invariant under this reflection, and is equivalently

\[
 |s_x(A)-1/2|\le a-1/2.
\]

At a particular finite scale:

\[
 x^a<A\quad\Longleftrightarrow\quad a<s_x(A)
 \quad\Longleftrightarrow\quad s_x(x/A)<1-a.
\]

Consequently, crossing above the 1/8 amplitude curve is exactly equivalent
to the reflected coordinate moving below 7/8. This is a coordinate identity,
not a claim that the reflected amplitude is another observed Mertens sum.

An envelope constant is also tracked exactly:

\[
 s_x(Cx^a)=a+\frac{\log C}{\log x},\qquad C>0.
\]

## Genuine Mertens samples and zero handling

`mertensAmplitude n` is the norm of the existing genuine `mertensSummatory n`.
It is not clipped. Its finite sample coordinate is `mertensAmplitudeCoordinate n`.
This returns `some (log amplitude / log n)` only for n >= 2 and nonzero
amplitude. It returns `none` for M(n)=0 and n<=1.

Mathlib's real logarithm is totalized with log(0)=0; the checked Option API
prevents that convention from silently assigning coordinate 0 to zero amplitude.
All theorems interpreting the algebraic coordinate carry the required domain
hypotheses. Absolute value/norm discards the sign; the original signed Mertens
sum remains available and is not identified with the reflected amplitude.

The finite integer-sum theorem proves that every nonzero Mertens amplitude
is at least one. Combined with |M(n)|<=n, all valid sample coordinates lie
in [0,1]. The generic interval and reflection theorems are specialized to
these actual arithmetic amplitudes.

Exact regressions:

- M(2)=0 and its actual amplitude coordinate is `none`.
- M(3)=-1 and its actual amplitude coordinate is `some 0`.
- The actual nonzero amplitude at n=3 lies outside [3^(1/8),3^(7/8)].

These tests distinguish a coordinate map of a specified band from the much
stronger, false claim that every actual sample belongs to that band.
No unverified decimal computations or primality certificates are imported.

## Connection to the merged asymptotic identification

For a nonzero sample, the actual coordinate equals the earlier `mertensLogSlope`.
For the asymptotic interface only, clipping is displayed explicitly:

\[
 \limsup_{n\to\infty}\frac{\log\max(1,|M(n)|)}{\log n}
 =\texttt{zetaRightmostRealPart}.
\]

`amplitude_limsup_eq_rightmost` uses the merged #949 theorem on the unchanged
definitions. No assertion identifies an individual finite sample coordinate
with a zeta zero; no unconditional 7/8 bound or RH proof is added.

## Files and verification

- `MERTENS_AMPLITUDE_COORDINATES.lean`: finite positive-amplitude geometry.
- `MERTENS_AMPLITUDE_STRIP_MAP.lean`: actual Mertens samples and asymptotic bridge.
- `MERTENS_AMPLITUDE_ACCEPTANCE.lean`: exact signatures and regression tests.
- `.github/workflows/mertens-amplitude-map.yml`: warning-fatal import closure
  and exact kernel dependency audit.

CI, not this document, determines the compiled status. The audit accepts only
`propext`, `Classical.choice`, and `Quot.sound`. No new axiom, proof hole,
weakened existing theorem, linter suppression, local Lean execution, merge,
or auto-merge is part of this change. Human review and merge remain required.

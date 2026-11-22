# Square-lattice interpolation

The Lean theorems for Alpöge’s $G_z$ give the signed interpolation formula, a two-sided slope bound and the passage from squares to all integer endpoints. They take the square-endpoint estimate (SQ) as a hypothesis.

## The arithmetic

Write, at positive integer endpoints,

```math
G_z(N)=A(N)-F(N)+(1+\gamma)N,\quad
A(N)=N\sum_{n\le N}\frac{\Lambda(n)}n-\psi(N),\quad
F(N)=N\log N.
```

The arithmetic term $`A(N)`$ includes every prime-power contribution.

Take $`a=R^2`$, $`b=(R+1)^2`$, $`a\le N\le b`$, and $`t=(N-a)/(b-a)`$. Let $`{\rm Chord}(f)(N)=(1-t)f(a)+tf(b)`$.

The signed interpolation identity holds unconditionally.

```math
\boxed{
G_z(N)-{\rm Chord}(G_z)(N)
 =
\underbrace{{\rm Chord}(F)(N)-F(N)}_{J_R(N)}
 -
\underbrace{[{\rm Chord}(A)(N)-A(N)]}_{P_R(N)} .
}
```

Lean calls $J_R$ `alpogeSquareLogChordDefect` and $P_R$ `alpogeSquareArithmeticChordDefect`. Their difference is `alpogeSquareSignedCorrection`. The theorem `nativeAlpogeGz_sub_squareChord_eq_signedCorrection` proves the displayed identity.

The equality retains the sign of $`J_R-P_R`$.

## Local bound

Mertens' first theorem in `NativePNTSelberg` gives

```math
-1\le \sum_{n\le N}\Lambda(n)/n-\log N\le\log 4+2.
```

Together with the exact one-step recurrence for $`G_z`$ and elementary bounds for $`(N+1)(\log(N+1)-\log N)`$, this yields the two-sided uniform slope bound

```math
|G_z(N+1)-G_z(N)|\le L,
\qquad
L=\log 4+5+|\gamma|.
```

The existing `AlpogeSquareClockSignedHistorySampling.lean` proved only the forward one-sided slope. This PR proves the missing reverse slope, telescopes both sides and interpolates using barycentric weights.

In particular, for $`R^2\le N\le(R+1)^2`$,

```math
\boxed{
|J_R(N)-P_R(N)|\le L(2R+1).
}
```

This $`O(R)`$ interpolation loss is unconditional. It is enough to preserve the critical $`O(R)`$ endpoint exponent.

The Lean estimate used here is $`O(R)`$. The proposed $`O(\log R)`$ refinement would need a separate estimate of the local prime-power sum.

## Integer endpoints

Assume the bound (SQ) at integer square endpoints.

```math
\boxed{
(\exists C\ge0)(\forall R\ge2)\;
|G_z(R^2)|\le C R,
}
\tag{SQ}
```

The interpolation theorem then bounds every integer endpoint.

```math
\boxed{
(\forall N\ge4)\quad
|G_z(N)|\le (2C+3L)\sqrt N.
}
\tag{ALL}
```

The pre-existing native Erdős identity

```math
G_z(N)=N\left(
  \texttt{nativePNTWeightedErrorMass}(N-1)
  +H_N-\log N+\gamma
\right)
```

then gives the corresponding bound for the complete signed NNS reciprocal history.

```math
\left|
  \texttt{nativeAlpogeCenteredHistory}(N)
\right|
\le
\frac{2C+3L}{\sqrt N}.
```

The proofs use these Lean declarations.

- `nativeAlpogeGz_square_lattice_signed_remainder`
- `nativeAlpogeGz_square_lattice_exact`
- `nativeAlpogeGz_all_of_square_lattice_critical`
- `nativeAlpogeCenteredHistory_all_of_square_lattice_critical`.

## Related criteria

The Omega Institute’s $U(x)$ agrees with $G_z(x)$ at integer arguments. Under RH its envelope theorem bounds $e^{-y/2}|U(e^y)|$ for all sufficiently large $y$. Taking $y=\log(R^2)$ and enlarging the constant for the finitely many early squares gives (SQ). [Definition of $U$](https://github.com/the-omega-institute/trureturing/blob/bfe7fd370bcd2a0f97d0921c00b334020cdb585e/D5/S3/Arith/Robin/CompleteMertensPeak.lean#L43-L45) and [envelope theorem](https://github.com/the-omega-institute/trureturing/blob/bfe7fd370bcd2a0f97d0921c00b334020cdb585e/D5/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope.lean#L196-L200).

Conversely, (ALL) extends to real $x$ because the arithmetic sum is affine between integers and the smooth term has second derivative $-1/x$. If $U_+(x)\le K\sqrt{x}$ on the tail, then $\int_Y^{Y^\lambda}U_+(x)x^{-3/2}\,dx\le K(\lambda-1)\log Y$ for fixed $\lambda>1$. This is at most $Y^\eta$ for every $\eta>0$ once $Y$ is sufficiently large, as required by the one-sided criterion at $\theta=1/2$. That criterion gives RH. [bramble_trace, Theorem 1](https://rstation.ai/problems/riemann_hypothesis/papers/190).

There is also an ordinary-prime criterion. The dyadic prime-power deficit $-U(x)+3U(x/2)-2U(x/4)$ is then $O(\sqrt x)$. Removing higher prime powers costs $O(\sqrt x)$. If RH fails, the ordinary-prime deficit exceeds $x^\theta$ at arbitrarily large squares for some $\theta>1/2$, contradicting that bound. The square case appears in bramble_trace’s earlier proof. Crossley gives both signs at every fixed power. [Earlier square result, revision 24](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=24) and [Crossley’s fixed-power theorem](https://doi.org/10.5281/zenodo.24414757).

## Square endpoints

The open input is (SQ). [PR #1182](https://github.com/OVVO-Financial/RH_Lean/pull/1182) identifies the full finite character ASK−MAIN source with native NNS partial moments. Its global cost bound remains open.

An independent geometric or automorphic argument supplying (SQ), or a sufficient one-sided endpoint inequality, would complete this approach.

The Lean propagation theorem uses integer $`N`$, the domain of the native definition. The comparison above extends the same arithmetic kernel to real arguments.

## Verification

Run the root import, research closure and Lean audit checks. Inspect `#print axioms` for the exported theorems.

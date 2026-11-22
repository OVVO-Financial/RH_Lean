# Complete thin-source supplier audit

Status: source audit and precise next dependency, not a new analytic theorem or an upstream compilation claim. The finite projection/freezing files in this directory use only Mathlib and existing RHLean library modules. This note does not add an import or revive the separate seven-eighths proof DAG.

Upstream pin: `CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

Native pin: `OVVO-Financial/RH_Lean@608b5702a20ab34a9efcd38b5d59e09f9f565f61`.

## 1. The actual positive supplier

[`QH.thin`](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/MeanSquareBounds/Thin.lean) is a theorem with a proof, not an assumed `ThinScales` interface. Its quantifiers are:

```text
forall eps A c c0 > 0,
exists x0, forall x >= x0,
forall N != 0 and primitive Dirichlet character chi mod N,
  log N <= A * x^(eps/5) * (log x)^2 ->
  (chi^2 = 1 -> chi != 1 -> NoExc c0 chi) ->
  forall y >= exp(x^(eps/3))/3,
    norm(G0 chi y) <= y * exp(-c*x^(eps/8)).
```

Here `NoExc c0 chi` means exactly that `LFunction chi beta != 0` for every real `1-c0 < beta < 1`. `G0` branches on **the actual Dirichlet character**: it is the centered principal `G1` when `chi=1`, otherwise the full `Gchi` containing `+ y * logDerivLAtOne chi`. Definitions are in [`MeanSquareBounds/PrimeSetTwoBounds.lean`](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/MeanSquareBounds/PrimeSetTwoBounds.lean).

The response scale `y >= exp(x^(eps/3))/3` is much larger than the critical thick-response scale of order `x`. This theorem is not a square-root bound at the critical scale.

### Its three actual analytic suppliers

1. [`QH.psi_thin`](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/MeanSquareBounds/PsiThin.lean): for fixed `c0>0`, it constructs constants `C,c>0`, uniform over primitive characters and `lam >= max(1,log N)`, subject to the same real-character `NoExc` premise, and proves

   ```text
   norm(psi0 chi u) <=
     C*u*(log u + lam)^2*exp(-c*log u/(lam + sqrt(log u)))
   ```

   for `u >= exp 1`. The proof explicitly obtains `Formalism.ZeroFreeDirichlet.zFRDirichlet`, `explicitFormula_closed`, and `zerosWindow_closed`. It bounds the finite zero sum, uses the primitive functional equation to separate low zeros from zero, and charges both explicit-formula errors. It does not call the terminal RH theorem.

2. [`QH.g_integral`](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/MeanSquareBounds/GIntegral.lean): for every primitive character and `y>=1`,

   ```text
   G0 chi y = -y * integral_(u>y) psi0 chi u / u^2.
   ```

   This is where the original affine `ell` cancellation is proved. For nonprincipal characters it consumes `GL2a2.log_deriv_series`, identifying the reciprocal-prime series with `-L'/L(1)`. For the principal character it consumes `GL2a2.psi_zero_integral_constant`. The actual file proves absolute tail integrability using `Formalism.ZeroFreeDirichlet.siegelWalfisz`; replacing that integrability proof by an already established suitable `psi` estimate is a possible compression, not something the current native source-identification theorem has done.

3. [`QH.int_thin`](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/MeanSquareBounds/IntThin.lean): an elementary improper-integral estimate absorbs the displayed conductor-dependent envelope when `lam <= A*x^(eps/5)*log(x)^2` and `y >= exp(x^(eps/3))/3`. In `QH.thin`, the input is `lam=max(1,log N)` and the envelope constant becomes `A+1`.

The exact closed declarations behind the explicit formula and zero counting are in [`Formalism/PeriodIntegrals/ExplicitFormulaCounts/ExplicitFormula.lean`](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/PeriodIntegrals/ExplicitFormulaCounts/ExplicitFormula.lean). They assemble `chk_lBoundRight`, `chk_zetaBoundRight`, `chk_lInvRight`, `chk_discFactor`, and `chk_discLog`. The exceptional-zero region itself is assembled in [`Formalism/LandauZeroFreeBounds/NoZeroComplex.lean`](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/LandauZeroFreeBounds/NoZeroComplex.lean). This source audit is not a fresh transitive axiom audit or a hosted build of those upstream declarations.

## 2. How the original host actually supplies nonexceptionality

[`QH.thinH`](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/MeanSquareBounds/GaussSumFunctionEq.lean) proves `UpperTheory.Top.ThinH`, whose precise host conditions are defined in [`CharacterBoxes/PairGood.lean`](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean):

```text
exists c>0, forall B eps with 0<eps<1/52,
exists x0, forall x>=x0 and actual hosts H,
  oddPart(H.QS) <= B ->
  log(H.condN) <= 2*x^(eps/5)*log(x)^2 ->
  RealBox H -> H.ChebyshevCharacterBound x eps c.
```

The proof chooses `c=1`. It uses `QH.thin` with conductor constant `2`. For a real nonprincipal character:

- If its conductor is divisible by the selected `q` or `d`, **the same host's `RealBox`** excludes a real zero in `(1-1/400,1)`.
- Otherwise `real_cond` proves that its conductor divides `8*oddPart(H.QS)`, hence is at most `8*floor(B)`. [`QH.small_zeros`](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/MeanSquareBounds/SmallZeros.lean) constructs a common positive zero-free interval over this genuinely finite family, from continuity of each nonprincipal L-function and Mathlib's `LFunction_apply_one_ne_zero`.

The chosen `c0` is the minimum of the finite-family interval and `1/400`.

[`UpperTheory.Top.realBox`](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/CharacterBoxes/RealBox.lean) derives `RealBox H` from the **actual `PairGood` prime-pair witnesses**: it decomposes each real host character into a bounded base character and selected quadratic twists, then applies `PairGood.boxes`. This is a character/prime-choice supplier, not a consequence of merely having many lattice maps.

Finally [`UpperTheory.T3.hostOfFieldOf`](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/ShortNorms/hostOfFieldOf.lean) constructs its host, proves the modulus bound on that host, obtains the real boxes from the same `PairGood`, and invokes `QH.thinH`. There is also [`GlobalTheory.EX.thinChoice_host`](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/CharacterBoxes/ThinChoice.lean), choosing decay constant `1/2` and conductor constant `3` from the corresponding host assumptions.

## 3. What the native bridge does and does not supply

[`AlpogeCompletePrimitiveASK.lean`](https://github.com/OVVO-Financial/RH_Lean/blob/608b5702a20ab34a9efcd38b5d59e09f9f565f61/RHLean/Analysis/AlpogeCompletePrimitiveASK.lean) already proves:

- `alpogeNativeCftGPsi_eq_primitiveGPsi`: exact response identity for the actual modular-unit `r` and its `cftData`, including ramified zeros and every prime power.
- `alpogeNativeCftASK_sub_MAIN_eq_completePrimitiveDe`: the complete native physical source equals its primitive Dirichlet expansion with all original widths.
- `alpogeNativeCanonicalHostEll`: the actual derivative quotient `L'/L(1)` at the primitive conductor.
- `alpogeNativeCanonicalHostASK_sub_MAIN_eq_primitiveDe`: the same full identity with that canonical constant, assuming original positive heights/widths and the actual finite cutoff.

These are exact algebraic identities. They do **not** prove the conductor-uniform `psi` estimate, tail integrability, logarithmic-derivative series at one, or a same-host real-zero exclusion.

An essential extra identification premise must be preserved: the native `GPsi` branches on additive `psi=0`, whereas upstream `G0` branches on primitive Dirichlet `chi=1`. The native exact identities accept an **arbitrary homomorphism**

```text
r : (ZMod N)^units ->* Multiplicative(E0 x H).
```

For a non-surjective `r`, a nonzero additive character can become the principal Dirichlet character. In that case the native nonprincipal formula `GchiArithmetic` is not automatically the centered principal `Gz`. A transfer of `QH.thin` to every native response must therefore supply, on the **same constructed host**, `psi!=0 -> primitiveCharacter(r,psi)!=1`; surjectivity of `r` is a sufficient finite condition. This is separate from, and must not be hidden inside, the exact arithmetic bridge. The same host's conductor-divisibility theorem must turn its actual modulus bound into the uniform `log N` bound required above.

Native `AlpogeNativeClassGroupNNSIntegral.lean` concerns integral class-group characters/lattice data; it is not a uniform Dirichlet PNT theorem. Native `StrongPNT` support concerns the zeta channel; it does not by itself control every varying host character.

## 4. Relation to the new finite paid step

The new finite thick-freezing argument keeps the signed original thin return exactly. Its output is

```text
Q*(retainedSignal - excludedCharacterMass) + signedThinAverage
  <= originalPhysicalTopExcess
     + 2*h*m*sum_(t in TT) nativePsi(floor(a_t/b)),

Q = |TT|*m*b*(|T2|/|H|)/2.
```

Under `a_t/b<=X`, the normalized freezing charge is at most

```text
4*h*(log 4+2)*X/(b*Delta),  Delta=|T2|/|H|.
```

That cost is proved using the actual nonnegative inertia kernel with total mass at most two; no character-count factor or per-character bound is inserted there.

The original thin supplier acts only after the canonical response and thin-scale conditions are established. If all actual thin arguments `a_t/w` are at least `X'/3` and every full canonical response has norm at most `(a_t/w)*theta`, then `w*norm(GPsi(a_t/w))<=a_t*theta`. This cancellation uses the original width exactly. Summing the full finite character/colour source gives the original per-row bound `2*fPhi*a_t*theta`, where `fPhi=2*|H|`; with `a_t<=(x+1)b`, its normalized contribution is at most `4*fPhi*(x+1)*theta/Delta`. This is a deduction from the genuine analytic supplier, not a new unconditional theorem in the current PR. The all-character factor here is explicit and can be absorbed only with the original host-size and exponential-decay estimates.

The new freezing charge and the thin analytic charge thus have distinct sources. Neither proves the actual physical geometric top-excess bound or constructs the necessary integral lattice witness.

## 5. Optional existing comparison; no current import

[`OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_dirichlet_nonzero`](https://github.com/OVVO-Financial/RH_Lean/blob/608b5702a20ab34a9efcd38b5d59e09f9f565f61/research/oai_434/VF919NativeSevenEighthsReplay.lean) has the type

```text
forall q, q!=0 -> forall chi s,
  7/8 < Re(s) -> not(chi=1 and s=1) -> LFunction chi s != 0.
```

As a mathematical comparison this supplies `NoExc (1/8)` for every real nonprincipal character, eliminating the exceptional-host selection specifically for this analytic branch. Its direct file dependencies are `research.oai_434.VF919NativeSourceMoments`, `OAI.NumberTheory.DirichletL.Moments.DetectorPlainSlotProfile`, `research.VF_919_SEVEN_EIGHTHS_SIGNED_COVARIANCE_20261019`, and `research.VF_919_SEVEN_EIGHTHS_SQUARE_SHELL_BRIDGE_20261019`; its proof uses the native detector/common-probe/supremum reconstruction and `HeckeDirichlet.dirichlet_seven_eighths_of_hecke`. It is not Mathlib-only and carries the large separate OAI proof DAG.

Per the current assignment, this remains an optional dependency comparison. The finite proof PR does not import it, rebuild it, or use it to hide a missing conductor-uniform estimate. Even if used later, nonvanishing alone would not provide the uniform explicit-formula/tail-integral bounds or the necessary same-host source identification.

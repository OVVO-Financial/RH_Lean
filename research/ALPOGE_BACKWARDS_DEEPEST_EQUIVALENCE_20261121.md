# Alpöge proof, worked backward: deepest source-preserving equivalence

Date: 2026-11-21. Read from the actual Lean declarations in the original mirror, not a PDF headline. This is a dependency audit, not an RH proof.

## 0. Distinguish the TWO terminal routes

The literal kernel exported terminal theorem in
`src/Supplements/Kernels/MainTheorems.lean` is:
```lean
theorem allChi : UpperTheory.EveryCharacter :=
  UpperTheory.FinalTheorems.everyCharacter
theorem rhOfAll : RiemannHypothesis :=
  Formalism.VW.rh_of_every allChi
```
The `everyCharacter` supplier in
`src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean`
takes the actual Galois-row source `galoisLocalGlobalStrong_recParameter`.
That comes from `galoisRepresentations_of_thetaLift`, which invokes BOTH
`UpperTheory.Gal.Int.Geo.geoOne_holds` and `UpperTheory.TP.K.tLiftK`.
This is the direct terminal dependency chain; it is NOT simply a call to
the conditional `Gz`/SizeWindows branch below. An attractive theorem in
the analytic branch is not automatically an ancestor of `rhOfAll`.

There is a separate, explicitly formalized **analytic terminal route**:
`Gz(x) <= x^(1/2+C*eps)` eventually for all sufficiently small eps
 -> `riemann_hypothesis_of_power_bound`
 -> one-sided `zetaLandauEps`
 -> half-plane zero-freeness
 -> RH. See `Formalism/SizeWindowBrackets/ChainSlopeWindows/RiemannHypothesisOfPowerBound.lean`,
`Formalism/ZetaNonvanishing/ZetaLandau.lean`, and
`Formalism/ZetaNonvanishing/RHofHalfPlane.lean`.
This second route is the best place to REMOVE geometric exposition if a
full physical-source inequality can be established in native RH_Lean.

## 1. Deepest EXACT iff found: eliminate geometric scalar v

The proved theorem `Formalism.LFunctionChainParameters.LBrDiv.v_elimination`
(`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/PBrDiv.lean`)
realizes `VElim` from `src/Formalism/SizeWindowBrackets/SBrDiv.lean`:

```
(forall u0 j rho, 0 < D.w u0 j rho) ->
((exists v : Real, 0 < v
    and (withV D v).DIV C and Count5 (withV D v) C)
  iff
 (exists omega : Real, DivFree D C omega
     and CountFree D C omega and CountRest D C))
```

It is NOT an approximate equivalence. The inverse scalar is explicit:

  v = pi * exp(D.gam - D.LpL - omega).

`periodicity_solvable` produces it; `divisibility_of_free` and
`free_count_of_count` then recover the original DIV and Count5.
The reverse implication extracts `omega=(withV D v).logOm`.
Exactly the D parameters/weights and the remaining CountRest inequalities
must be retained. This removes an entire normalization variable and all
its redundant use-site calculations.

## 2. Deeper one-way ELIMINATION: replace arbitrary geometry index W by Unit

The proved `LChain.exists_data_completion : DataCompletion` in
`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean` constructs
`D1 : Data U0 (fun _ => Unit) Top m f` from a *visible* `D0`.
The `SameVisible` record preserves EXACTLY:

  x, eps, a, b, b', k, L, La, B0, Nc, gam, LpL, aT, w, ASK.

In `PChain.compl` one can verify the definitions:

  D1.T u0 ()      = exp(sLog D0 u0)
  D1.muCC u0      = D0.ASK u0 - D0.LoP C
  D1.muMinCC u0   = D0.ASK u0 - D0.LoP C
  D1.HH u0        = D0.x ^ C.cHH * D0.b
  D1.d u0 ()      = 1
  D1.delBar = D1.etaBar = D1.eBar = 0.

The new D1 satisfies the ENTIRE formal `SizeData₂` package
(HidaSetting, DIV, EComp5, HComp, Count5, Slopes,
QuotientSlopeBoundsWith, LossBounds, SlopeIneq, HHBound, FParams),
but **ONLY IF** D0's physical source has the genuine, strong top inequality:

  FOR ALL u0,
  D0.ASK u0 <= D0.Main u0
      + C.cDiv * D0.nT * D0.a * D0.La
      + C.cDiv * m * (D0.B0 + D0.Nc)
          * D0.x ^ (C.eDiv * D0.eps)
      + D0.LoP C.

It also requires the explicit positivity and log-weight budget:

  0 <= sLog D0 u0 <= C.cCount*m*D0.L.

This is a mathematically valid **data-completion reduction**, NOT an
equivalence of a real theta-lift lattice with Unit or a proof of the top
inequality. The completed fields are algebraic (muCC is DEFINED using ASK).
Therefore it eliminates presentation/auxiliary proof bureaucracy after
the inequality has been earned, not the actual RH-strength estimate.

`LChain.chain_reduction_of_top : ChainCoreOfTop` uses this same construction
with the exact source identification `Ident`, all SizeWindows, and the
analytical side conditions. This is the specific backward cut, not a vague
heuristic appeal to source identities.

## 3. The independent isometry equivalence in the geometric route

Original `Formalism.HN.Rerealize` in
`src/Formalism/HarderNarasimhan/QuotRealize.lean` and its proved
`Rerealization.transfer` in
`.../HarderNarasimhanProofs/Rerealize.lean` preserve
height, size, HN slopes, muMin/muMax, ranks, degrees, covolumes,
saturation and quotient covolumes when an injected K-linear map
identifies the actual placewise Hermitian norms.

RH_Lean PR #1173 reconstructs the LITERAL `vecAt/fcoord/normAt`
definitions from `Formalism/HermitianLattices/StatementMaj.lean`
and at head af10dbf proves the exact identity

  nativeNormAt (b.map e) X v (e x) = nativeNormAt b X v x.

The native C->R matrix [[1,-1],[1,1]] is exhibited as a genuine
K-linear equivalence with inverse using /2. It commutes with arbitrary
complete signed coefficient matrices and maps actual O_K-submodules.

This transport theorem is sufficient to remove duplicate RE-REALIZATION
proofs, once the actual same-family identification is supplied.
It DOES NOT identify an arbitrary Selberg 2I-J real-log coefficient
operator with the arithmetic-geometric theta-lift family by itself.

## 4. Exact analytic source below both geometric interfaces

RH_Lean has already proved, without importing the external RH theorem:

  Gz(N) = N * centeredErdosHistory(N),

in `RHLean/Analysis/AlpogeGzErdosReciprocalHistory.lean`;
`Gz(N) <= B iff centeredErdosHistory(N) <= B/N` for N>=1.
The centered history retains the ENTIRE signed Chebyshev-error prefix and
actual harmonic/log/Gamma centering.

The original proof's `mellin_Gz_n` is also a critical exact identity:

  Mellin(Gz)(s) = nZ(s)/(s*(s-1))  (Re s>1).

The **one-sided** eventual bound for Gz at exponent 1/2+eps gives
the required zero-free half-plane through the formalized Landau theorem;
one does not need an absolute pointwise bound on E(x). Conversely RH
implies power bounds by classical von Koch/Chebyshev estimates, but
do not silently label that direction checked by this particular file.

## 5. The minimal attack: a ONE-SCALAR physical bound, not a NEW structure

Recommended proof: work in the analytic route and express the
original `PChain` visible-data ASK as the complete native
prime-power `alpogeNativeSharpASK`/Selberg/Erdos source.
Keep the full coefficient, 2/q/d exceptional ramification, all
non-thick/partner returns, collar, signed principal mode, and exact
Frobenius/inertia masks.

Then prove exactly the `hTop` inequality above with the same
parameter family and the original size-window normalization.
Once hTop is proved, `exists_data_completion` manufactures Unit W,
`chain_reduction_of_top` gives the chain, cost calculations give the
one-sided Gz power bound, and Landau gives RH.

The remaining difficult content is the genuinely quantitative
full-source `hTop` at all large x and every small eps with correct
multiplicity and SizeWindows. A scalar RH equivalence, a finite prime
census, an integer determinant of the bare signed 2I-J operator, or
a transport isometry alone cannot establish hTop.

***Bottom line:***
- **Deepest literal IFF:** `v_elimination` (DIV + Count5 iff scalar
  DivFree + CountFree + CountRest; positive weights).
- **Strongest structural compression:** `exists_data_completion`
  (after the one full physical hTop upper bound, arbitrary W collapses
  to Unit with unchanged observables).
- **Biggest genuine geometry replacement:** `Rerealize` plus the native
  norm-preserving C->R lattice equivalence in PR #1173.
- **Shortest target for independent proof:** full-source hTop; this is
  RH-strength, and has NOT been derived here.

## Direct source files

- https://github.com/CocoSgt/riemann-hypothesis-lean/blob/main/src/Supplements/Kernels/MainTheorems.lean
- https://github.com/CocoSgt/riemann-hypothesis-lean/blob/main/src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean
- https://github.com/CocoSgt/riemann-hypothesis-lean/blob/main/src/Formalism/SizeWindowBrackets/SBrDiv.lean
- https://github.com/CocoSgt/riemann-hypothesis-lean/blob/main/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/PBrDiv.lean
- https://github.com/CocoSgt/riemann-hypothesis-lean/blob/main/src/Formalism/SizeWindowBrackets/SChain.lean
- https://github.com/CocoSgt/riemann-hypothesis-lean/blob/main/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean
- https://github.com/CocoSgt/riemann-hypothesis-lean/blob/main/src/Formalism/HarderNarasimhan/QuotRealize.lean
- https://github.com/CocoSgt/riemann-hypothesis-lean/blob/main/src/Formalism/ZetaNonvanishing/ZetaLandau.lean

## 6. CRITICAL backward-audit correction: the analytic gates DO NOT disappear

The source-specific `hTop` inequality above is **not the only missing
supplier**. The exact original `GrowthInequalityRemainingHyps` in
`Formalism/SizeWindowBrackets/SChain.lean` additionally requires
`ThinScales D ell X' theta` AND `ValuesAtX D ell x eps CL`.
By definition in `GrowthBoundGivesRiemannHypothesis.lean`,
`ValuesAtX` bounds all THREE nonzero characters psC, chC, chpsC:

  ||GPsi D ell psi x|| <= x^(1/2+eps),

plus bounds for ell. `ThinScales` controls ALL characters at y>=X'/3
at a much smaller relative scale. Neither of these is inferred from
`DataCompletion` or from the finite `ModelText.family` size-window
construction.

### Serious toy-host obstruction visible in literal original definitions

The example `Model.DA` in `PChain.lean` has
q1=11, d=7, `frob p = 0` for EVERY p and
`inertia p = bot` except p=7, where inertia is {0, sgc0}.
The character `psC` depends only on the second ZMod 2 coordinate and
`sgc0=((1,0),0)`, hence `psC(sgc0)=1`.
Therefore `psC` is trivial on ALL these inertia subgroups and on
all Frobenius elements. By the literal definitions
`cosetMean` and `primVal` in `FirstPrimeNeSecondPrime.lean`,

  primVal Model.DA psC n = 1       for EVERY n>=1.

The "text" host uses `ell = fun _ => 0`; `psC != 0`, so

  GPsi Model.DA ell psC x
    = sum_{1<=n<=floor x} Lambda(n) * (x/n-1)
    = Sz(x)  (exact source algebra).

For x>=2 all summands are nonnegative, and the n=2 term gives

  Sz(x) >= (log 2) * (x/2 - 1).

This is at least a constant multiple of x for all x>=4, while the
required `ValuesAtX` bound for any fixed 0<eps<1/2 is
`||GPsi psC x|| <= x^(1/2+eps)`.
Thus the **particular synthetic Model.DA host with ell=0 CANNOT
satisfy this analytic input eventually**. This follows by elementary
growth comparison, not a numerical experiment or RH.

**Status:** this is a complete direct source-level paper derivation;
the specific impossibility statement has NOT been compiled as a Lean
theorem in RH_Lean. It is a falsification of the synthetic model as a
terminal ANALYTIC witness, not a flaw in the proven `VElim` or
`DataCompletion` implications. In particular one must not claim
`chain_sizes_eventually` provides all `ChainCore` conditions.

This strengthens the proof-compression research direction: use
`VElim`, `Rerealize`, and `DataCompletion` to DELETE auxiliary
bookkeeping, but reconstruct the *actual physical Frobenius/Hecke*
character source, genuine same-family full `hTop`, `ValuesAtX`,
`ThinScales`, and the quantitative SizeWindows package without
relying on the toy host. The terminal kernel route based on
`UpperTheory.FinalTheorems.everyCharacter` is distinct and does not
automatically pass through the synthetic model.

### Tightest honest theorem frontier

```
  Actual prime-power ASK/MAIN + Frobenius/inertia source
  + full hTop upper inequality (complete signed, paid)
  + ValuesAtX (three genuine character signals)
  + ThinScales (whole large-y character family)
  + growth/width/multiplicity/size windows
    =>
  exists_data_completion / v_elimination (no geometric scaffolding)
    =>
  one-sided Gz(x) <= x^(1/2+O(eps))
    =>
  Landau => RH.
```

None of the geometric equivalences alone supplies the three analytic
suppliers above. This is the exact mathematical frontier rather than
a new hypothesis disguised as an equivalence.

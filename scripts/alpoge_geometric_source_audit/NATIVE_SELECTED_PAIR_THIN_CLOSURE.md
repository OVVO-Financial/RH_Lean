# Constructed selected pairs and native same-host thin estimates

## Concrete deliverable

The staged `RHLean.Analysis.AlpogeThin` closure contains 363 newly source-derived
modules and shares two existing Landau modules, with 51,733 lines in the
365 pinned originals. It includes the actual
proofs of `QH.pairEx`, `UpperTheory.Top.realBox`, and `QH.thinH`, together with
all their non-Mathlib imports. The only external library is Mathlib. The selected-pair branch shares `CharFamily` and `LandauZeroFreeCriterion`
with the existing Landau closure; the Mertens upper-bound dependency imports
that existing native module rather than duplicating it.

`NativeHostThin.lean` identifies the original response with existing native
Gz/Gchi arithmetic. Its terminal `nativeSelectedPairThin` constructs the prime
pair and supplies the bound for all characters of every compatible host with
those same primes. Neither prime-pair existence nor an exceptional-zero-free
hypothesis is an input to this terminal theorem.

All new source-derived declarations are nested under
`RHLean.Analysis.AlpogeThin`, preserving their original relative namespaces.
Every module explicitly sets `autoImplicit false`. The source attribution,
exact pin, and hashes are recorded in `THIN_SOURCE_MANIFEST.json`.

No Lean process has been run locally. This staged reconstruction requires
hosted verification on its published head; source completeness and the scan
for proof shortcuts do not replace that kernel check.

## The actual analytic payment

`QH.g_integral` proves the exact identity, for primitive characters and y>=1,

`G0(chi,y) = -y * integral_(y,infinity) psi0(chi,u)/u^2 du`.

This is where the original logarithmic derivative is paid as an integral
constant. The principal identity retains Euler's constant. It does not throw
away the affine ell term. The proof has its own closed convergence suppliers:
Siegel-Walfisz, the logarithmic-derivative series, and the principal psi
integral constant.

`QH.psi_thin` proves a uniform primitive-character estimate

`norm(psi0(chi,u)) <= C*u*(log(u)+lambda)^2 *
 exp(-c*log(u)/(lambda+sqrt(log(u))))`.

It uses the proved explicit formula `explicitFormula_closed`, the proved zero
count `zerosWindow_closed`, and the proved exceptional-zero region
`Formalism.ZeroFreeDirichlet.zFRDirichlet`. The potential real exceptional zero
is explicitly retained as `NoExc` at this intermediate theorem.

`QH.IntThin` integrates that estimate in the original parameter range.
`QH.thin` therefore gives, for positive eps,A,c,c0, a threshold x0 such that
all primitive chi with

`log(N) <= A*x^(eps/5)*log(x)^2`

and the appropriate real-character exclusion satisfy

`norm(G0(chi,y)) <= y*exp(-c*x^(eps/8))`

simultaneously for every `y >= exp(x^(eps/3))/3`. The conductor, thin argument,
and exponent relations are the original ones.

## How the actual same-host construction discharges NoExc

The proof of `QH.thinH` splits a real primitive host character by whether its
conductor contains q or d.

- If q or d divides its conductor, `RealBox H` supplies nonvanishing in the
  fixed real strip `beta > 1-1/400` for that exact host character.
- Otherwise `QH.real_cond` proves that its conductor divides
  `8*ordCompl[2] H.QS`. The odd part is bounded by B, so `QH.small_zeros`
  supplies one positive exclusion width for the finite set of characters with
  conductor at most `8*floor(B)`. This latter proof uses continuity and the
  actual nonvanishing of L(1,chi), followed by finite minima.

Thus no exceptional-zero-free assumption remains in `thinH` beyond the
concrete same-host box input. The universal thin constant is chosen as one in
the original proof; its public statement existentially quantifies a positive
constant before B, eps, x, the host, and the character.

The reconstructed `UpperTheory.Top.realBox` supplies that box input from the
same `PairGood M eps Y X H.q H.d`. Its `realSplit` proof writes each relevant
real host character as a base real primitive character of conductor dividing
`8*ordCompl[2] H.QS` times one of the three nontrivial q,d twists. The
`PairGood.boxes` field applies to those actual twists. The required host
conditions are that primes dividing H.QS divide 2*M and
`ordCompl[2] H.QS` divides M.

`QH.pairEx` constructs q,d and the entire `PairGood` record. It invokes the
actual pair-selection and character mean-square proofs, preserving both the
response bounds and the real-character boxes. For M=1, the response-bound
field has the three q,d,qd twists; the box field still includes every real
primitive base character of conductor dividing eight. The latter field must
not be reduced to only three unbased twists.

## Native terminal theorem and quantifier order

`nativeSelectedPairThin` proves:

1. There exists one c>0.
2. For every positive natural M, every 0<eps<1/52, every A>=1, and every B,
   there are thresholds Y0 and x0.
3. For every Y>=Y0, there are actual primes q,d satisfying
   `PairGood M eps Y (Y^A) q d`.
4. For every x>=x0 and every compatible host H with H.q=q and H.d=d, with
   the original odd-part, conductor-log, and prime-support conditions, every
   primitive character belonging to that host satisfies the complete native
   thin response bound at every permitted y.

The native response is exactly existing `alpogeNativeGzArithmetic` in the
principal branch. The nonprincipal branch is existing
`alpogeNativeGchiArithmetic` with the actual value `L'(1,chi)/L(1,chi)`.
`hostResponse_eq_nativeResponse` proves the identity for every real y by
reducing the max on the original finite floor cutoff. Every prime power is
retained.

The theorem still needs an actual compatible arithmetic host from the
geometric construction. It does not identify unrelated host data, nor does it
assert a complete global geometric source bound. Its result is the actual
uniform all-character thin supplier needed to pay the variable-width thin
return; it does not rely on a false translation cancellation of site-dependent
top widths.

## Principal native modulus specialization

The separate `NativePrincipalThin.lean` makes the principal application more
direct. `principalPair_uniform_noExc` constructs one positive real exclusion
width for every real primitive character whose conductor divides `2^k*q*d`,
uniformly over every k and every selected `PairGood 1` pair. The actual
`realSplit` decomposition has a base conductor dividing eight. If both twist
bits vanish, `small_zeros 8` applies; otherwise the real-character box of the
same selected q,d applies. No number-field HostRaw record is needed for this
arithmetic argument.

`nativePrincipalSelectedPairThin` then constructs q,d using `QH.pairEx 1` and
proves, simultaneously for every k and every primitive conductor
`N` dividing `2^k*q*d`,

`norm(nativeResponse(chi,y)) <= y*exp(-x^(eps/8))`

whenever x is past its fixed threshold,
`log(N) <= 2*x^(eps/5)*log(x)^2`, and
`y >= exp(x^(eps/3))/3`.

This directly accepts the conductors of the existing native characters on
the common modulus `2^(e+2)*q*d`, using Mathlib's conductor-divides-level
theorem and the existing complete primitive/Frobenius-inertia bridges.
The ambient dyadic host is retained. The theorem does not assume NoExc,
PairGood, or existence of a number-field host; it constructs the first two
suppliers and states the original quantitative conductor condition explicitly.

## Source and verification

Source: Levent Alpöge (with Claude), mirrored at
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
The original toolchain is Lean4.33.1/Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`; the native target is
Lean4.34.1/Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

The archive/mirror states no license. Attribution is retained without
assigning a new license to source-derived material. No terminal RH import,
retired OAI proof replay, or introduced axiom is used. The research guard
prints axioms for the selected-pair construction, the same-host real-box
supplier, the full thin theorem, the native identity, and their combined
native terminal result.

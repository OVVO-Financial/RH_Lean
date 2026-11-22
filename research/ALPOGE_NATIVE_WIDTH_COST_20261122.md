# Complete native signed width payment: source and cost audit

## Status and scope

Native base: `OVVO-Financial/RH_Lean` main
`608b5702a20ab34a9efcd38b5d59e09f9f565f61`.

External source pin: `CocoSgt/riemann-hypothesis-lean`
`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

Mathlib pin from the native base's `lake-manifest.json`:
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

The external statements and relevant construction bodies cited below were
**SOURCE_INSPECTED**. They have not been independently kernel-checked here.
The native files are **LEAN_DRAFTS / HOSTED_CI_PENDING** until their exact PR
head passes compilation and the assumption audit. No local Lean execution
was performed. The first hosted pass found two local proof-script errors and
lint warnings; the current files repair those, but their next check is pending.

This work proves a finite, quantitative upper-direction width comparison.
It does not construct the entire original field/lattice/metric family,
bound the surviving midpoint source, or prove the global critical estimate.

## Exact finite result

Write

\[
D_a(w)=\operatorname{Re}\{\operatorname{ASK}_N(a,w)
                         -\operatorname{MAIN}(a,w)\}.
\]

The native source is the full Frobenius/inertia ASK with `Lambda(n)` on all
prime powers. Its real site coefficient is

\[
v_{n,g}=\Lambda(n)\operatorname{Re}K(n,g)\ge0.
\]

At an actual prime power `n=p^i`, `i>0`, the native colour theorem gives
`K(n,g)=2/|I_p|` on its actual inertia coset and zero otherwise. At every
other `n`, `Lambda(n)=0`. Thus this positivity retains all powers and all
original character contributions.

For two profiles `w0,w1`, set `c=(w0+w1)/2` pointwise. The exact identity is

\[
D_a(c)=\tfrac12(D_a(w_0)+D_a(w_1))+J_{\log}-J_{\rm ASK}.
\]

The actual physical ASK Jensen collar satisfies `J_ASK>=0`. Its sign is
favorable for this upper bound. If every Phi width is at least `beta>0` and
`|w0(rho)-w1(rho)|<=d`, then

\[
0\le J_{\log}\le\frac{a d^2}{8\beta^2}\quad(a\ge0).
\]

The hinge identities hold at equality thresholds too: no case
`a/n=c`, `a/n=w0`, or `a/n=w1` is removed. Prime-power and square-clock
boundary terms remain in the exact finite source.

The scalar proof is

\[
\log\frac{u+v}{2}-\frac{\log u+\log v}{2}
=\frac12\log\left(1+\frac{(u-v)^2}{4uv}\right)
\le\frac{(u-v)^2}{8uv}\le\frac{d^2}{8\beta^2}.
\]

The `1/|Phi|` in MAIN cancels the cardinal of its own log sum. No host factor
is erased from an unproved norm. In particular, no separate positive collar
estimate is necessary in this direction.

The finite comparison holds for any common cutoff `N`. Identifying that
finite source with the existing complete native `De` still requires every
ratio `a_t/w(rho)<=N`, for both actual rows and the reference profile.
`N=Nat.ceil(A/beta)` is sufficient under the displayed positive width and
height bounds. At the original thin minimum this is of size `x*n*X'`, so
one cannot replace the full cutoff by `x=R_V^2-1` merely because the thick
signal is evaluated near that square endpoint. The thin sector includes
genuine larger prime powers. The native bridge preserves its cutoff premise.

For an arbitrary positive reference profile, the separately drafted tangent
identity uses the fixed orientation

\[
D(c)=D(w)+C+J_{\log}-J_{\rm coll}.
\]

Here `C` includes both the ASK prefix slope and the MAIN log slope. Both
remainders are nonnegative under the stated positivity hypotheses. For a
pointwise midpoint, `C(c,w0)+C(c,w1)=0` exactly.

## Actual HC family and source compatibility

The external predicate
`GlobalTheory.EX.HCVal` contains a single integer base `b1(tau)` and, at every
site and every `j:Fin m`,

\[
\mathrm{hc}.b_j=b_1+jh_0,\qquad
\mathrm{hc}.e_j=\mathrm{hc}.b_j+h_0/2.
\]

It also fixes the top, thick and ordinary thin base clauses. This is an
actual row-family equality, not a barycenter hypothesis invented for the
native theorem. Consequently

\[
w_j(\rho)=v(\rho)+(j+\tfrac12)h_0,
\quad
w_j+w_{m-1-j}=2v+mh_0.
\]

The native row-pair theorem applies with midpoint `v+mh0/2` and displacement
bound `d=m*h0`. A midpoint lattice is unnecessary. The midpoint remains
site-dependent; it is not the constant thick profile `b`.

`GlobalTheory.EX.exists_hc_family` constructs the integer base by selecting
one thick anchor `tau0` and adding a torsion correction `sh` only there. This
shift is independent of the row `j` and the code word. It is therefore
retained in `v`, and cancels from the pair's displacement. The more general
HCVal interface already suffices for rowwise affine cancellation; its proof
does not need the stronger one-anchor property or a balanced top selector.

The physical width is `wj`, equivalently `wPl`, which uses `hc.e_j` for the
physical row indexed `j+1`. The shifted weight `wJ` is a different object.
The `CapLe.lean` source explicitly rewrites
`wPl D (j+1) z = ((D.hcW u (tauPl D z)).e j : Real)` using `D.hcW_e`.
Any eventual native bridge must preserve this indexing and the same host,
inertia, Frobenius, height, characters, and top/thick masks.

Pinned sources:

- [HCVal, RankVal, HostVal, h0v](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/PairRowIffQdRows.lean).
- [exists_hcParam_of_code; exists_hc_family](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsHcParamOfCode.lean).
- [Physical wPl/wj identification in CapLe](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CapLe.lean).

## True row multiplicity and original normalizer

Summing the pair comparison under the actual involution
`j -> m-1-j` gives

\[
mD_a(v+mh_0/2)
\le\sum_{j<m}D_a(w_j)
    +\frac{ma(mh_0)^2}{8\beta^2}.
\]

This counts every row once, works for odd `m` too, and uses no geometric
multiplicity beyond the actual number of rows. It holds for each frame and
each variable height `a_t` separately. If `a_t<=A`, summing the original
frame/top variables and dividing by

\[
Q=Tmb\Delta/2
\]

gives normalized curvature price

\[
\frac{A(mh_0)^2}{4b\beta^2\Delta}.
\]

The native full-host `AlpogePhysicalCompleteTopExcess` uses an average
`1/|H|` over translated frames `u in H`. For that special case, take the
generic finite-family index set to be `H x TT`: its cardinal is `n*T`, its
normalizer is `n*Q`, and its ratio is the full-host averaged numerator
divided by `Q`.

The actual upstream `CharacterBalanceMoves.core` and the new native subgroup
projection instead average over `u in A0`, with factor `1/|A0|`. For that
consumer, instantiate the generic family theorem with `A0 x TT`, cardinal
`|A0|*T` and normalizer `|A0|*Q`. This gives the same width-payment constant.
The ambient host cardinal `n=|H|` still occurs in the thin minimum and Delta.
These two signed frame averages must not be identified without an additional
theorem. The width result works for each of them separately and creates no
extra frame-count factor.

This subgroup scope was checked directly in the pinned
[ChCore.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean):
`Deduction.CharacterBalanceMoves.sum_Th` sums over `u:A0` and retains
`PsiA A0`; `Deduction.CharacterBalanceMoves.core` assumes its geometric
`gapA<=Err` on `u0 in A0`. The width comparison does not replace that
character-completed projection by the full-host four-character special case.

The actual smallest HC base is

\[
\beta=b''=\frac{b}{nX'},
\quad b=e^{x^\varepsilon},\quad X'=e^{x^{\varepsilon/3}}.
\]

The finite normalized price is therefore exactly

\[
\frac{A(mh_0)^2n^2(X')^2}{4b^3\Delta}.
\]

With the actual height-window inequality `A<=2*x*b`, it is at most

\[
\frac{x(mh_0)^2n^2(X')^2}{2b^2\Delta}.
\]

Both substitutions are drafted as native finite Lean theorems. The host
factor `n^2` from the genuine thin minimum is retained.

## Numerical suppliers and decay ledger

The following list applies to the **same actual RankVal/HostVal/HCVal
family**. It is stronger than some generic downstream interfaces. Merely
having the wider ChCore inequality `m<=x^(1/2+epsilon/2)` does not license
the sharper RankVal bound below.

1. `RankVal` literally requires
   `sqrt(x*delta1)<=m<=2*sqrt(x*delta1)` and
   `n<=2*x^(2+8*epsilon)`.
2. `Formalism.BasicNotions.Scale.delta1 = x^(-epsilon/8)`.
   `Formalism.MainNotions.J.delta1_le_one` proves `delta1<=1` from Scale's
   `x>1` and `epsilon>0`. Hence actual RankVal implies `m<=2*sqrt(x)`.
3. `GlobalTheory.EX.rank_basic_bounds`, also exposed as
   `GlobalTheory.T.explicitRanks_basic_bounds_large_scale`, proves the
   sharper `m<=2*x^(1/2-epsilon/16)` for each fixed `0<epsilon<1/52` and
   sufficiently large `x`, under `RankVal`.
4. `GlobalTheory.EX.exists_ranks_rankVal_frame` and
   `exists_ranks_cyclic_frame` construct ranks satisfying RankVal at large
   scale, with their stated frame hypotheses. They do not alone construct
   the full compatible host, lattices, metrics or analytic prime pair.
5. `h0v s ch = 2*Nat.ceil(x^ch)`. With `x>1` and `ch>=402`,
   `ceil(x^ch)<=x^ch+1<=2*x^ch`, so `h0<=4*x^ch`.
6. `HostVal` contains `x^(-epsilon)*n<=|T2|`. With
   `Delta=|T2|/n` and `n>0`, this gives `Delta>=x^(-epsilon)`.

Thus the complete normalized width curvature is at most

\[
\boxed{128\,x^{2c_h+6+17\varepsilon}
      \exp(2x^{\varepsilon/3}-2x^\varepsilon).}
\]

The constants are `4` from `m^2`, `16` from `h0^2`, `4` from `n^2`, divided
by `2` from the finite price. The exponent is
`1+1+2*ch+(4+16*epsilon)+epsilon`.

For fixed `epsilon>0` and fixed `ch`, eventually
`2*x^(epsilon/3)<=x^epsilon`; the exponential is then at most
`exp(-x^epsilon)`, which beats every fixed power of `x`. Accordingly this
width component is `O_B(x^(-B))` for every fixed `B>0`. The implication is a
paper proof until the optional native asymptotic module is checked. It is
not uniform as `epsilon` tends to zero.

Further pinned sources:

- [Scale.L, b, a, X', b', w'', delta1; physical wj; SizeData₂.aT_win and typeDensity_eq_card_div](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/LocalRingCardinality/DataParams₂.lean).
- [J.delta1_pos; J.delta1_le_one](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSa.lean).
- [rank_basic_bounds](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExplicitRanksBasicBoundsLargeScale.lean).
- [Alias explicitRanks_basic_bounds_large_scale](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExplicitRanksBasicBoundsLargeScaleStatement.lean).
- [exists_ranks_rankVal_frame; exists_ranks_cyclic_frame](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsRanksRankValFrame.lean).

The first file defines `L=x^epsilon`, `b=exp L`, `a=x*b`,
`X'=exp(x^(epsilon/3))`, `b'=a/X'`, and `w'' n=b'/(x*n)`.
Its `SizeData₂.aT_win` gives
`a_t<=a+a/(k*x^(Scale.A/2))`, with `Scale.A=26`; for `k>=1,x>1`,
this implies `a_t<=2*x*b`. Thus the `A` in the finite-family theorem is
an upper bound on the actual variable heights, not an assumption that
all those heights equal one constant chooser.

## Remaining mathematical obligation

The comparison controls the width passage from the actual HC row family
to its pointwise midpoint. The midpoint retains the complete signed thin,
top, thick, ramified and character returns. Bounding that surviving source
requires the compatible geometric/analytic supplier. The finite width
theorem does not make separate existence statements into one witness and
does not pay lattice maps, rank saturation, height, covolume, or residual
analytic tails by itself.

The new local contribution is a reusable all-character one-sided
semiconvexity theorem with an exact finite-family normalization. It is
independent of RH-strength hypotheses, but it is not the proposed central
Signed Square-Lattice Coercivity Theorem.

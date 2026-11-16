# Euler correction and complete signed response: audit of a bootstrap to one half

## Status and decision

**Status: source audit and conditional paper derivations; SELF_AUDIT only.**
No Lean execution, new zero-free theorem, independent Referee acceptance, or
global exponent improvement is asserted here. The prime partial-sum input in
Section 5 is an explicit unproved input for the required expanded family. It is
not supplied by the existing finite-residue zero bound merely by changing a
type name.

The Euler-factor extraction by itself does **not** provide a bootstrap to
`1/2`. Its direct upper-bound map fixes `3/5`; its reflected zero map has the two
exact fixed real parts `4/7` and `3/5`. Multiplying by the exact signed local
principal response does not remove the responsible factor. This route should
be parked as an RH bootstrap unless an additional mechanism eliminates these
survivors.

There is a more useful conditional result for the finite response: cancellation
in the actual weighted prime averages gives the threshold

\[
 F_5(b)=\frac{b+2}{5}=\frac12+\frac{b-1/2}{5}.
\]

This threshold applies to the **complete retained finite response symbol**,
including geometric powers and mixed slot products. It does not, by itself,
give an operator bound on arbitrary bounded functions or prove an endpoint at
`F_5(b)`. Section 7 gives a legitimate Gaussian Mellin way to consume it for the
actual signal and obtain a positive, slot-dependent improvement from a current
boundary `b`. Applying that mechanism to the common supremum of an infinite
angular family also requires a positive exponent gain uniform across the
family at each fixed `b`, or a separate extremal argument. The present LOW
bound, angular-family closure, and numerator-zero obstruction remain unpaid.
Consequently there is still no complete bootstrap to `1/2` in this note.

## 1. Provenance and notation

Read-only repository state checked on 2026-11-16:

- RH_Lean main: `076195b75278869d4f18fd924b9ebdaedf723108`.
- Live `AGENTS.md` blob: `5bf6b1dd837bad943286d05c7dd08441d6a22635`.
- All upstream mathematical source references below are pinned to
  openai/math `1581d4cbdd69a0faf34b2089614fe2a814316a6a`.
- No moving upstream HEAD was used as mathematical evidence.

Let `Q > 1` be a prime-ideal norm and put

\[
 q=Q^{-1},\qquad D=\eta Q^{-s},\qquad
 R=AQ^{3-6s},\qquad B=\overline\eta Q^s.
\]

On unramified source primes `|eta| = 1`, so `BD = 1`. The symbols `D`, `R`,
and `B` in this section are local Euler coordinates; `R` is not a dyadic row
count, and the scalar boundary `b` below is not a physical-window endpoint.

The actual source phase is

\[
 A_P=\overline{\operatorname{angularFactor}(p)}^{\,6}
       \operatorname{elementCoeff}(\eta,p)^6.
\]

`FiniteGaussPhase.angularFactor p` is the complex embedding of `p` divided by
its modulus. Its sixth power is insensitive to the choice of an Eisenstein
unit. Write the element phase as `lambda(p)`; its sixth-power combinations
descend to ideals. The actual phase is `lambda^(-6) eta^6`, not an independently
chosen unit phase. No claim that `lambda` itself is independent of a generator
is needed.

Sources: pinned [EulerCoordinates](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/EulerCoordinates.lean)
defines `coordR`, `coordD`, `coordK`, and `actualAPhase`;
[ActiveGaussFactorization](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/PrimeRows/ActiveGaussFactorization.lean)
defines `angularFactor` and proves its product identity.

## 2. Exact principal-slice correction and signed grouping

At the principal slice `w = 1`, `z = 1/6`, one has `V = W = q` and
`K = (1-q)D`. The latter identity is `principal_K_signed` in
[VF919PrincipalSignedRemainder](https://github.com/OVVO-Financial/RH_Lean/blob/076195b75278869d4f18fd924b9ebdaedf723108/research/oai_434/VF919PrincipalSignedRemainder.lean).

The pinned definition

\[
 \operatorname{markedFactor}(R,V,q,K,J,1)
 =\frac{[R(1-q)-KV]/(1-V)+J}{1-R}
\]

with `J = -D + qR` therefore gives

\[
 P_* = \frac{(1+q)(R-D)}{1-R}.
\]

Substituting this into the pinned continued correction

\[
 C_Q(s)=\frac{1-VW+(1-V)(1-W)P_*}{1-D}
\]

gives the exact identities

\[
 U=1-qR-(1-q)D,
 \qquad
 C_Q(s)=\frac{(1-q^2)U}{(1-R)(1-D)},                    \tag{E1}
\]

\[
 \widetilde C_Q(s):=(1-R)C_Q(s)
 =(1-q^2)\left(1+\frac{q(D-R)}{1-D}\right).             \tag{E2}
\]

These are identities where the displayed denominators are nonzero. They were
checked independently by symbolic subtraction, which returned exactly zero.
Their source definitions are pinned
[Detector/Euler](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/Euler.lean)
and [Detector/Local](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/Local.lean).

For every fixed `alpha > 1/2`, (E2) suggests, and elementary local estimates
give after making the finite exclusion threshold large enough, a bound
uniform on `Re s >= alpha` of the shape

\[
 |\widetilde C_Q(s)-1|
 \ll_\alpha Q^{-2}+Q^{-1-\alpha}+Q^{2-6\alpha}.         \tag{E3}
\]

All three powers are summable over prime ideals. This identifies the
convergent residual product to construct; it does not identify the original
infinite product with a continuation below its original convergence region.
That global equality and its dependence on exclusions remain separate proof
obligations.

The exact negative-normalized principal slot is, on its established source
domain,

\[
 S_Q(s):=-\operatorname{principalSlot}_Q(s)
   =q+(1-q)\frac{1-BR}{U}.                              \tag{E4}
\]

This is `principal_slot_response_exact` in
[VF919PrincipalFiniteResponse](https://github.com/OVVO-Financial/RH_Lean/blob/076195b75278869d4f18fd924b9ebdaedf723108/research/oai_434/VF919PrincipalFiniteResponse.lean).
Exact multiplication, retaining every sign, yields

\[
 C_Q S_Q
 =\frac{(1-q^2)N}{(1-R)(1-D)},
 \quad
 N=1-q^2R-q(1-q)D-(1-q)BR.                             \tag{E5}
\]

Using `B = 1/D`,

\[
 N\big|_{R=1}=\frac{(1-q)(D-1)(1-qD)}{D}.              \tag{E6}
\]

This is not identically zero. In particular, for `0 < q < 1` and
`0 < |D| < 1` it is nonzero. Thus exact local grouping does not cancel the
`1-R` denominator, and it does not replace `Q^(3-6s)` by
`Q^(5/2-6s)`. Finite averaging or a change in the physical exponents is not an
algebraic license to make that replacement.

## 3. Which arithmetic factor is extracted?

At the mathematical character level, define

\[
 \psi=\eta^6\lambda^{-6}.
\]

The extracted factor is the incomplete angular Hecke Euler product

\[
 \prod_{P\notin E}(1-\psi(P)Q_P^{-(6s-3)})^{-1}.
                                                               \tag{E7}
\]

On `Re(6s-3) > 1`, the character Euler product identifies this with

\[
 L(\psi_{\rm prim},6s-3)
 \prod_{P\in E\cup\operatorname{supp}(M)}
  (1-\psi_{\rm prim}(P)Q_P^{-(6s-3)}),                 \tag{E8}
\]

with duplicate primes counted once and factors at primitively ramified primes
equal to one. Here `M` retains the original finite modulus; taking a sixth
power can reduce its primitive conductor, so the omitted factors at the
original modulus must be restored explicitly. A bridge using a primary
normalization modulo three may add that finite exclusion as well. No such
factor is silently suppressed in (E8).

Every finite factor in (E8) is nonzero when `Re(6s-3) > 0`, because its
nonconstant term has modulus strictly less than one. The infinite angular
factor is the important remaining factor.

The upstream repository already contains the relevant **kind** of arithmetic
object:

- [AngularHeckeCharacter](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularHeckeCharacter.lean)
  defines `angularResidueIdealChar`, proves its multiplicativity and
  conjugation identity, and retains the finite Euler exclusions under
  primitive reduction.
- [PrimitiveHeckeProof](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/CubicMoment/Estimates/PrimitiveHeckeProof.lean)
  proves `primitiveAngularHeckeInput_proved`.
- [PublishedAngularHecke](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/CubicMoment/Estimates/PublishedAngularHecke.lean)
  states the exact completed functional equation: the dual has conjugate
  finite character and opposite angular type, and the variable changes from
  `u` to `1-u`. The Gamma shift is `|ell|/2`; it does not move the symmetry
  center away from `1/2`.

No compiled bridge from the detector's actual `O`/ideal characters to this
`CubicFirstMoment` representation is established by this note. In particular,
the existing
[HeckeFamily.Character](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Hecke/Family.lean)
has a finite residue character and periodic coefficients; it does not already
contain nonzero angular types as an extra field.

## 4. Exact failure of the Euler-only bootstrap

Grant for this section the unpaid global factorization, a nonvanishing
residual product, and an analytic returned signal strong enough to force a
zero of its numerator whenever the target denominator vanishes. A target zero
`rho` then forces

\[
 L(\psi,6\rho-3)=0.                                   \tag{E9}
\]

Multiplicity must also be retained if this is used to cancel a pole. This
section only needs the necessary implication for the zero location.

Even after granting a zero bound `b` for a family closed under this character
map, (E9) gives only

\[
 b\longmapsto F_6(b)=\frac{b+3}{6},\qquad
 F_6(b)-\frac35=\frac{b-3/5}{6}.                       \tag{E10}
\]

Starting at one gives `1, 2/3, 11/18, 65/108, ...`, tending to `3/5`.
For a zero whose transformed argument lies in the open critical strip,
functional reflection gives the folded real-part map

\[
 T(x)=\max(6x-3,4-6x)
      =\frac12+6\left|x-\frac7{12}\right|.             \tag{E11}
\]

It has the two exact fixed points

\[
 T(3/5)=3/5,\qquad T(4/7)=4/7.                         \tag{E12}
\]

These are precise falsifiers of a claim that these implications alone force
the zero supremum to `1/2`. They are not claims that arithmetic zeros exist at
those real parts. The zero-location and character-closure rules permit the
following abstract surviving orbits:

- At `Re rho = 3/5`, use the direct branch. Heights multiply by six. For an
  initial angular type zero, the types are
  `0, -6, -42, -258, ...`, namely `ell_n = (6/5)(1-6^n)`.
- At `Re rho = 4/7`, use the reflected branch. Heights change sign and
  multiply by six. Angular types follow `ell -> 6-6 ell`.

For an angular target `(chi, ell)`, the direct map is
`(chi^6, 6 ell - 6)` and its dual is `(conj(chi)^6, 6-6 ell)`.
Therefore even the contemplated iteration needs an unbounded angular family;
the existing finite-residue family is not closed under it. Conjugation can
produce both signs of the angular twist, but does not invalidate the fixed
real-part examples.

A genuine half-centered affine map with slope six would instead be

\[
 6s-\frac52,\qquad
 b\longmapsto\frac{b+5/2}{6}
   =\frac12+\frac{b-1/2}{6}.                           \tag{E13}
\]

It would require a genuine `Q^(-1/2)` improvement in the relevant source
weight, or a different complete source identity. Merely extracting this
preferred factor leaves the residual ratio
`(1-Q^(-1/2)R)/(1-R)`, whose defect still has the original leading `R` size.
The missing half power has not been paid by a normalization change.

## 5. A different conditional input: actual angular prime cancellation

Let a target character be `eta = chi lambda^ell`, with `ell` a multiple of six,
and let `b > 1/2` be a proposed common boundary for a family large enough for
the operations below. The starting finite-residue targets have `ell = 0`.

**Prime input (P), not proved here.** For every character `varphi` required by
the `W`-containing terms of the finite expansion and every original ray mask,
and for every `epsilon > 0`,

\[
 \sum_{Q_P\le X}\operatorname{mask}(P)\varphi(P)
   =O_{\varphi,\operatorname{mask},\epsilon}(X^{b+\epsilon}).
                                                               \tag{P}
\]

This is an estimate for the actual prime ideals and original ray mask. If the
mask is expanded by finite ray-character orthogonality, (P) must hold for
every resulting finite twist. Finite exclusions are retained. A bound for
unmasked primes or a surrogate phase is not (P). A suitable zero bound for all
these angular Hecke characters could supply (P) through a proved explicit
formula; neither that family extension nor that transfer is assumed to be
already compiled here.

The actual residue weights are

\[
 w_P(Q)=W(Q/P)Q^{-5/6}.                                \tag{P1}
\]

They are `residueWeights` in pinned
[PrincipalResidueActual](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/PrincipalResidueActual.lean).
For a nonzero nonnegative original smooth window and its original ray class,
the mass input needed below is

\[
 \mathcal M(P)=\sum_{Q\ {
m in\ pool}}W(Q/P)Q^{-5/6}
       \gg P^{1/6}/\log P.                            \tag{P2}
\]

The raw number of primes has size `P/log P`, but the actual residue mass has
size `P^(1/6)/log P`. The proof must cite the actual ray-prime mass supplier;
abstract positivity in `SlotBounds.mass_pos` alone does not give (P2).

## 6. Conditional full finite-symbol lemma

The finite response in
[VF919PrincipalResponseMass](https://github.com/OVVO-Financial/RH_Lean/blob/076195b75278869d4f18fd924b9ebdaedf723108/research/oai_434/VF919PrincipalResponseMass.lean)
is the exact labelled expansion of

\[
 q+(1-q)(1-\mathcal W)\sum_{k=0}^{K}\mathcal H^k,
 \qquad
 \mathcal H=qR+(1-q)D,
 \quad \mathcal W=BR.
\]

Subtracting one, with no terms discarded, gives

\[
 (1-q)\left(\sum_{k=1}^{K}\mathcal H^k
              -\mathcal W\sum_{k=0}^{K}\mathcal H^k\right).       \tag{S1}
\]

Consider a term of `W H^k` with `r` copies of `qR` and `j` copies of `D`,
where `r+j=k`. Its properties are exactly:

| Quantity | Value |
|---|---|
| Degree/delay multiplier | `n = 6r+j+5` |
| Mellin delay | `n log Q` |
| Real coefficient power | `Q^(2r+3)` |
| Character phase | `lambda^(-6(r+1)) eta^(6r+j+5)` |
| Additional real factor | `(1-Q^(-1))^(j+1)` times the binomial coefficient |

For `eta = chi lambda^ell`, its angular type is

\[
 (6r+j+5)\ell-6(r+1).                                 \tag{S2}
\]

For every `ell` in `6Z` this is nonzero. Indeed, writing `ell=6h`, it is six
times `(6r+j+5)h-(r+1)`: this is negative for `h <= 0` and at least
`5r+j+4 > 0` for `h >= 1`. Thus these terms have no principal main term, even
after a finite ray twist. The required family is closed under these actual
integer powers and angular twists; a single estimate for `eta^5 lambda^(-6)`
does not cover all retained terms when `K` is positive.

**Conditional derivation.** Apply partial summation to (P), using the original
weight (P1), `Q^(-n i t)`, and `(1-Q^(-1))^(j+1)`. On a fixed annulus the
derivative cost is at most a constant depending on `K` and the fixed smooth
window times `1+|t|`. Divide by (P2). Absorbing a logarithm into an arbitrarily
small positive loss gives

\[
 \left|\operatorname{Avg}_{w_P}
   [(1-q)\mathcal W(qR)^r((1-q)D)^j](\theta+it)\right|
 \ll (1+|t|)P^{b+2+2r-(6r+j+5)\theta+\epsilon}.        \tag{S3}
\]

The exponent is

\[
 b+2-5\theta+r(2-6\theta)-j\theta.
\]

For `theta > 1/2`, every extra `r` or `j` strictly improves it. Thus the
leading `W` term determines this family's threshold:

\[
 b+2-5\theta<0\quad\Longleftrightarrow\quad
 \theta>F_5(b)=\frac{b+2}{5}.                          \tag{S4}
\]

The terms in (S1) without `W` need no prime cancellation: absolute averaging
gives the powers `P^(2r-(6r+j)theta)`, for `r+j >= 1`. Including them, for each
fixed finite `K` the complete averaged slot response satisfies

\[
 |r_{P,K}(\theta+it)|
 \ll (1+|t|)P^{-\kappa},\qquad
 \kappa=\min\{\theta,6\theta-2,5\theta-b-2-\epsilon\}>0.        \tag{S5}
\]

All constants may depend on the fixed source, `K`, the finite ray twists,
`theta`, `b`, and the chosen losses, but must be fixed before the outer scale.
No bound uniform in an arbitrarily increasing `K=K(Z)` is claimed.

For the complete `N`-slot product, expand
`product_j (1+r_j)-1` over every nonempty slot subset. If
`P_j=Z^(ell_j)` and `m=min ell_j > 0`, (S5) gives

\[
 |\Phi_Z(\theta+it)-1|
   \ll (1+|t|)^N Z^{-m\kappa}.                        \tag{S6}
\]

This proof retains all mixed slot products. It does not assume the individual
symbols are uniformly small for all heights: expansion over finitely many
subsets controls their polynomial height growth directly.

## 7. What can consume the symbol estimate?

### 7.1 What it does not prove

Decay of `Phi_Z(theta+it)-1` does not imply a small operator norm on arbitrary
weighted `L-infinity` functions. The delays and coefficients depend on the
outer scale. An arbitrary function can match the coefficient signs at the
finitely many delayed arguments. The absolute mass theorem in FFR3 deliberately
avoids that issue, but its present supplier only contracts for `theta > 3/5`.

Therefore (S4) is a half-centered **symbol threshold**, not an already proved
global endpoint recurrence. It cannot be substituted for the `mass` hypothesis
of `signal_power_bound_of_eventual_response`.

### 7.2 A direct route for the actual Gaussian Mellin signal

There is an alternative conditional consumer which does not use an operator
norm on arbitrary functions. Suppose a current boundary `b` licenses the actual
signal representation on `a=b+delta_a`, with `delta_a>0`:

\[
 f(Z)=\frac1{2\pi i}\int_{a+i\mathbb R}
       Z^{s+c}\mathcal A(s)\,ds,
 \qquad
 \mathcal A(s)=e^{(s-5/6)^2}H(s)/L_\chi(s),             \tag{M1}
\]

and suppose

\[
 \int_{\mathbb R}(1+|t|)^N|\mathcal A(a+it)|\,dt<\infty.         \tag{M2}
\]

The representation (M1) is required for every positive signal argument, including arguments below one: the complete finite response evaluates f at all its delayed arguments. These are explicit analytic inputs. For lines below the currently proved
correction region, the actual continuation of `H` must first be constructed
and identified; a change of symbols does not supply (M1). Gaussian decay can
absorb polynomial height growth once that continuation and the current
zero-free reciprocal bound are available.

The exact all-delay Mellin identity from
[VF919PrincipalAllDelayReturn](https://github.com/OVVO-Financial/RH_Lean/blob/076195b75278869d4f18fd924b9ebdaedf723108/research/oai_434/VF919PrincipalAllDelayReturn.lean)
then puts the actual complete response inside this same integral. From (S6),

\[
 |\mathcal K_Zf(Z)|\ll Z^{a+c-m\kappa(a,b)}.           \tag{M3}
\]

For each fixed `b>1/2`, put

\[
 \kappa_0=\min\{b,6b-2,4b-2\}>0.
\]

Choose the prime-estimate loss at most `kappa_0/4` and
`0 < delta_a <= m kappa_0/4`. Then `kappa(a,b) >= 3 kappa_0/4`, and (M3)
implies

\[
 |\mathcal K_Zf(Z)|\ll Z^{b+c-m\kappa_0/2}.            \tag{M4}
\]

At `b>2/3` the unmarked `D` term can decay more slowly than the leading `W`
term; the minimum defining `kappa_0` retains this fact. At this stage (M4) is a
statement for one fixed target character and its fixed source. In particular,
`m`, the implied constant, and the scale from which the bound holds may depend
on that character.

If the **same complete physical source** separately supplies

\[
 |f(Z)+\mathcal K_Zf(Z)|\ll Z^{b+c-\delta_{\rm phys}},
 \qquad\delta_{\rm phys}>0,                            \tag{M5}
\]

then subtraction gives a strict signal-growth improvement by
`min(delta_phys, m kappa_0/2)`. This is weaker numerically than asserting an
endpoint at `F_5(b)`, but it is a genuine one-step mechanism for the actual
signal, conditional on the stated inputs.

For an infinite closed angular family, a positive gain for each individual
character does **not** by itself lower the family's common zero supremum:
the gains may tend to zero along characters whose boundaries approach that
supremum. To use (M4)-(M5) at a fixed common boundary `b>1/2`, it is sufficient
to provide numbers `m_*(b)>0` and `delta_*(b)>0` such that every target character
can use a source with `m >= m_*(b)` and `delta_phys >= delta_*(b)`, while its
prime-estimate losses satisfy the same budget `epsilon <= kappa_0(b)/4`.
The analytic and zero-transfer steps must retain the resulting common exponent
gain

\[
 \Delta(b)=\min\{\delta_*(b),m_*(b)\kappa_0(b)/2\}>0. \tag{M6}
\]

Implied constants and starting scales may still depend on the character;
uniform exponent gain is the requirement here. A gain uniform as `b` tends to
`1/2` is unnecessary. An alternative argument that supplies an extremal
character, or otherwise prevents vanishing gains near the common supremum,
could replace this uniformity input, but no such argument is proved here.

## 8. Why this still is not a complete bootstrap

There are two independent downstream obstructions, in addition to the
expanded-family input.

**LOW / complete physical return.** The existing total-slot-mass LOW condition
forces `x+y >= 7/9`, and its boundary is

\[
 29/36+(x+y)/12\ge47/54.
\]

Thus the present LOW estimate does not supply (M5) for arbitrary `b>1/2`.
The required replacement may estimate the complete signed probe jointly;
there is no demand here for a stronger separate norm on each component. But
the complete estimate must actually be proved.

**Numerator cancellation.** A strict bound on the signal `H/L_chi` need not
exclude a zero of `L_chi` if `H` has a zero there. The existing variable-boundary
transfer explicitly assumes an analytic, nonvanishing multiplier through its
`|H-1| <= 1/2` hypothesis. Its current supplier only reaches `Re s > 21/25`.
The extraction in Sections 2-4 potentially extends analyticity of the actual
multiplier, but leaves its angular `L(psi,6s-3)` factor. The surviving locations
in (E12) therefore remain even if (P), (M1)-(M5), and family closure are granted.

Changing finite exclusions cannot remove a global numerator zero: its finite
Euler factors are nonzero for `Re s>1/2`. Changing `X,Y`, the Gaussian windows,
or a finite retained slot response also does not supply an identity eliminating
that factor. A proof that the relevant numerator and target cannot share these
zeros, or a genuinely different complete multiplier, is an additional
arithmetic obligation. Continuation alone is insufficient.

Sources for this paragraph and the LOW floor are
[VF919FiniteSlotReflectedGain](https://github.com/OVVO-Financial/RH_Lean/blob/076195b75278869d4f18fd924b9ebdaedf723108/research/oai_434/VF919FiniteSlotReflectedGain.lean),
especially `sourceCorrection_analytic_wide`, `sourceCorrection_bound_wide`, and
`nonzero_of_probe_bounds_variable_boundary`, and
[VF919TotalMassLowPhysical](https://github.com/OVVO-Financial/RH_Lean/blob/076195b75278869d4f18fd924b9ebdaedf723108/research/oai_434/VF919TotalMassLowPhysical.lean).

## 9. Exact unpaid-lemma list and admission rule

| Obligation | Exact content | Status in this note |
|---|---|---|
| `ANGULAR-BRIDGE` | Identify the actual detector coefficients, ideals, norm, primary normalization, conjugation, and exclusions with the angular-character package. | Not compiled here. |
| `ANGULAR-BOUND` | Extend a common current boundary to the closed angular/ray-twisted family and obtain the prime-sum consequence for the nonprincipal characters needed in (P). Unmarked terms may be bounded absolutely. | Unproved input; not supplied by the finite-residue boundary. |
| `ORIGINAL-MASS` | Supply (P2) for the unchanged actual ray pools and residue weights, with constants before scale. | Required explicit supplier; positivity alone is insufficient. |
| `SIGNED-SYMBOL` | Prove (S3)-(S6) from (P) and the original mass bound for fixed finite `K,N`, preserving every mixed term. | Conditional paper derivation above. |
| `ACTUAL-MELLIN` | Establish (M1)-(M2) for the unchanged signal on `a>b`, with the original complete response identity. | Existing FFR identities are reusable; expanded analytic continuation and family bounds remain to be connected. |
| `COMPLETE-RETURN` | Prove (M5), including the full signed LOW, HIGH, principal, and complementary terms, for each `b>1/2` in the closed family. | Open; present LOW floor is `47/54`. |
| `FAMILY-GAIN` | At each fixed common boundary `b>1/2`, supply a positive exponent gain uniform across the closed angular family as in (M6), with controlled slot exponents, physical-return gains, and loss budgets, or prove a replacement extremal argument. Implied constants may depend on the character; uniformity as `b` tends to `1/2` is not required. | Open; per-character positive gains alone do not lower an infinite family's common supremum. |
| `NO-HIDDEN-ZERO` | Remove or control numerator cancellation so improved `H/L_chi` growth improves the actual zero boundary past both Euler survivors. | Open; exact Euler extraction alone fails this test. |

A path qualifies as a bootstrap to `1/2` only after its **complete** consumer
has a strict improvement of the relevant common boundary for every possible
actual supremum above `1/2`, or another proved mechanism eliminates every
stopping value. For an infinite character family, this includes `FAMILY-GAIN`
or its proved replacement. The positive component exponent in (S4), a
continuation theorem, or a formal conditional wrapper alone does not meet that
condition.

## 10. Checks performed

An independent scratch calculation, with exact rational/symbolic arithmetic,
verified:

- (E1), (E2), (E5), and (E6), each by zero symbolic difference;
- both fixed points in (E12);
- the exact first iterates in (E10);
- the angular orbit `ell_n=(6/5)(1-6^n)` and the reflected recurrence;
- the identity in (E13).

The accompanying stdlib checker `euler_exact_check.py` provides 49 reproducible
exact checks, using `Fraction` coefficients and canonical sparse polynomial
normal forms. Rational identities are checked after clearing denominators;
their mathematical interpretation keeps the stated nonzero-denominator
conditions. In addition to the displayed Euler identities and fixed-point
formulas, it checks the finite response recursion, mixed-slot recursion,
monomial signatures, angular nonprincipality certificates, and original
weight normalization. Run from the repository root:

```sh
python3 bootstrap_half_20261116/analysis/euler_exact_check.py
```

The callable `run_checks()` returns a structured `PASS` result when every
identity succeeds and raises `AssertionError` otherwise. The checker does not
use numerical sampling as a proof of polynomial identities.

These checks validate the displayed algebra, not the prime input, infinite
product identity, complete physical estimate, or noncancellation claim. No
local Lean execution or remote repository mutation was performed for this
audit.

# Reconstructing the PAID Stepanov amplification cost in RH_Lean
November 20, 2026. Status: source-grounded partial reconstruction; no RH proof.

## 1. Actual proof chain inspected

External published mirror: https://github.com/CocoSgt/riemann-hypothesis-lean
Relevant Lean declarations:
- src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean: GrowthInequalityExplicit, SizeWindows, GrowthSizeBound.
- src/Formalism/SizeWindowBrackets/SChain.lean: ChainCore, ErrWindows and source-size controls.
- src/Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean: the complete error bracket.
- src/Formalism/MeanHeightDescent/CovolumeEstimateAnchoredWeights.lean: the arithmetic-geometric integral lattice and covolume cost.
- src/Formalism/ZetaNonvanishing/ZetaLandau.lean: zetaLandauEps works with EITHER fixed sign, +1 OR -1.
- src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean: full automorphic-to-RH bridge.

The external project uses Lean 4.33.1/Mathlib 0df444a360eaa60ab8c11dca51a86af692955474;
RH_Lean uses Lean 4.34.1/Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
An import of the full proof is an additional toolchain and dependency project, not a substitute for an independently proved arithmetic cost bound.

## 2. What Alpoge ACTUALLY pays

GrowthInequalityExplicit has the schematic real form

  T*m*b*(delta/2)*(G(x)-3*x^(1/2+eps)-moveCost)
  <= Err + T*m*(2*f*(x+1)*b*theta+6*f*(x+1)*(eta+1)).

Here T is the retained top count and delta the thick density.
Its algebraic consequence for positive T,m,b,delta is

  G(x) <= 3*x^(1/2+eps)+moveCost
        +2*Err/(T*m*b*delta)+4*f*(x+1)*theta/delta
        +12*f*(x+1)*(eta+1)/(b*delta).

The SizeWindows budget includes a global x^(C*eps) factor times

  Err0=T*aE*(1+m^2/k)
       +m*(2*n*m*b*x^eps+nT2*k*b*x^eps/(n*(n*x^(-eps)))).

Set r=sqrt(x), u=x^eps, delta=nT2/n. Then

  Err0/(T*m*b*delta)
   = aE/(m*b*delta)*(1+m^2/k)
     +2*n*m*u/(T*delta)+k*u^2/(n*T).

This EXACT normalization has a companion Lean theorem. For x>=1,
the external SizeWindows implications give the weaker conditions

  r,u>=1; T,n,m,k,b,delta>0;
  aE<=2*r^2*b; r<=m*u; m<=r*u;
  delta*u>=1; n<=2*u*T;
  r^2*m<=k; k*u<=n^2*r.

Under these, term by term,

  aE/(m*b*delta) <= 2*r*u^2,
  aE*m/(b*delta*k) <= 2*u,
  2*n*m*u/(T*delta) <= 4*r*u^4,
  k*u^2/(n*T) <= 2*r*u^2.

Consequently Err0/(T*m*b*delta) <= 10*r*u^4.
The original x^(C eps) cost multiplies this by u^C; SmallCosts additionally
controls movement, thin modes and width. Thus a TRUE family satisfying all
the hypotheses yields an RH-strength root exponent. Mere rank does not
provide the original Err bound, k, delta or geometric widths.

## 3. Exact falsifier of "rank buys a free 1/m"

In merged PR #1157 the selected physical Mobius incidence has the form

  B_ij=-mu(q_j)*1_(j<=i).

The unsigned matrix L_ij=1_(j<=i) has determinant 1 and inverse given
by first differences. Thus L maps the full integer lattice Z^m onto Z^m;
there is NO index, p-adic divisibility or covolume improvement from
this minor.

Its FORWARD norm is large even though its inverse is bounded.
On the genuine negative sign direction v=(-1,...,-1), Lv=(-1,-2,...,-m).
The lower partial second moment is exactly

  LPM2_0(Lv)=1^2+...+m^2=m*(m+1)*(2*m+1)/6 >= m^3/3,

whereas the input square energy is m. The corresponding UPM2 is zero.

The selected signed second-Selberg physical block is evaluated at
reciprocal quotient 1, hence E(1)=-1, so this is exactly its adverse
response orientation (with positive logarithmic weights). This is a
rigorous stress test of the proposed amplifier: independent directions
and a unit determinant DO NOT justify dividing the whole Err by m.
This does not refute Alpoge's DIFFERENT geometric construction.

## 4. The useful sign switch: use UPM2, not LPM2

Alpoge's Landau theorem permits BOTH fixed signs of G. The exact
unconditional classical identity

  G(x) = -x*integral_x^infty (psi(t)-t)/t^2 dt

implies

  -G(x) <= x*integral_x^infty max(psi(t)-t,0)/t^2 dt.

Thus the source-native UPPER partial square semivariance

  Q_+(H)=sum_(H<=R<2H) max(psi(R^2-1)-(R^2-1),0)^2

satisfying Q_+(H) <<_eps H^(3+eps) for EVERY eps>0 is enough to
prove RH (via dyadic Cauchy-Schwarz, monotone square interpolation,
and the published one-sided Landau theorem, fixed sign s0=-1).

This is equivalent in strength to RH and is still UNPROVED.
But its sign is aligned with the known negative signed Selberg
semiprime block. In the FULL native recurrence at X_R=R^2-1,

  E(X_R)*log^2(X_R)=C_R-B_R,

where B_R is the selected negative semiprime part and C_R is the
COMPLETE signed complement (including all square, ghost, high/low,
movement and floor terms), the new target is

  Q_+(H)=sum_(H<=R<2H) ((C_R-B_R)_+)^2/log^4(X_R).

The selected B_R now reduces the dangerous POSITIVE overshoot.
No assumption of independent prime signs or omission of any
signed complementary carriers is permitted. The existing negative
semivariance route remains valid; the positive route may better
match this particular source.

## 5. Deliverables and exact scope

The proposed Lean module proves finite prefix identities, the cubic
one-sided energy counterexample, the exact normalized error-bracket
algebra, and defines the actual-source UPM2 plus OPEN uniform critical
proposition. The executable regression checks exact integer and
rational identities, not a probabilistic model.

The NEXT independently hard theorem is the SAME-family complete
source cost: construct multiplicity m>=x^(1/2-eps) accompanied by
nontrivial integral divisibility (or a genuinely equivalent signed
covariance saving), and an upper bound for full Err WITH all
compensators; prove thin, width and covolume taxes remain small.
The unit-prefix source does not yet supply any of those gates.

No genuine new RH/Mertens exponent is claimed and none of the new
Lean declarations is certified until exact-head CI passes.

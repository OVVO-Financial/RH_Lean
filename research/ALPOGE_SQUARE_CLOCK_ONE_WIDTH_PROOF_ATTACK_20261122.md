# A short native RH proof attack through the exact square-clock ASK collar

**2026-11-22. Status: new finite arithmetic estimate, not an RH proof.**

## The physical square-clock parameters

For each integer R >= 2, set X = R^2-1, a = R*X, and the two literal ASK widths b = R, B = R+1. Then

    a/b = X = R^2 - 1
    a/B = R(R-1) = R^2-R.

The strict crossing collar R(R-1) < n < R^2-1 has exactly R-2 integer sites.

For the genuine von Mangoldt source, define

    J_R = sum_{2<=n<=X} Lambda(n) *
      { [(a/n - R)_+ + (a/n - (R+1))_+]/2
        - [a/n - (R+1/2)]_+ }.

The already-certified native Jensen lemma says that the braces are
nonnegative, vanish outside the collar and never exceed 1/4. Since
Lambda(n) <= log n <= log X, this gives the unconditional inequality

    0 <= J_R <= (1/4) sum_{R(R-1)<n<X} Lambda(n)
             <= (R-2)*log(X)/4 = O(R log R).

This is on the ORIGINAL prime-power ASK, including all ramified prime
powers. The new source file
RHLean/Analysis/AlpogeSquareClockSharpCollar.lean
formalizes the exact cutoffs, crossing interval and principal bound.
Compilation is subject to CI; no terminal RH theorem is claimed.

## Why an R-factor saving might actually matter

Alpoge's formal GrowthInequalityExplicit bounds a principal Gz signal
with a generic width/character charge, which after division by its
positive leading coefficient has the term

    12*fPl(H)*(x+1)*(eta+1)/(b*delta2).

The actual source defines fPl(H)=card(PhiSet)=2*card(H).
His SizeWindows includes

    m >= x^(1/2-eps),
    k >= x*m,
    k <= card(H)^2 * x^(1/2-eps).

Consequently card(H)^2 >= x, so fPl(H) >= 2*sqrt(x).
At x ~ R^2, b=R, eta=1, the original *generic* width charge is
at least order R^2/delta2: too large for the desired root-scale bound.

At precisely these same widths the NEW CENTERED principal
source cost is only O(R log R). This is the concrete R-factor
improvement worth testing against Alpoge's physical theta-lift family.

IMPORTANT: this does NOT authorize replacing the full generic width
charge in Alpoge's inequality with J_R. The other original components
include signed nonprincipal characters, inertia/Frobenius return maps,
site-dependent widths and global topExcess/covolume normalization.

## A candidate short proof if the full remaining geometric bill is paid

1. Retain the exact native ASK minus MAIN equals De identity, the
   original characters and the whole signed topExcess.
2. Replace the *principal centered* width payment by the proved
   R-2-site Jensen collar. Prove an all-character/partner counterpart
   with one global signed covariance, not separated absolute values.
3. Construct actual multiplicity m ~ R and true covolume/height
   witnesses ensuring the complete normalized topExcess plus remaining
   cost is O_epsilon(R^(1+epsilon)).
4. Deduce Gz(R^2-1)=O_epsilon(R^(1+epsilon)). The EXISTING Lean
   square-clock one-sided interpolation transfers this to every large
   integer with O(R) overhead; the real-x Lipschitz and Landau
   steps then prove RH.

The unproved part is **step 3 together with the full-source part of
step 2**. It is a concrete, noncircular geometric/arithmetic task, not
a renamed assumption that RH holds. No complete-root estimate,
nonprincipal covariance payment, or independent short proof is
currently claimed.

## Negative controls

- A midpoint reference is valid only with the corresponding common
  or weighted-barycenter character/width population.
- The finite-group Fourier transform may leave aliased Frobenius
  residues; orthogonality alone is not a power saving.
- All 2,q,d ramified prime-power returns must remain in the source.
- The matched K2 - Lambda*Lambda kernel cancels its isolated negative
  principal mode. Do not reuse that nonexistent credit.
- Record fPl(H), delta2, T, m, b and ALL geometric costs before
  assigning a global power exponent.

Upstream audited sources:
CocoSgt/riemann-hypothesis-lean/src/Formalism/SizeWindowBrackets/
 GrowthBoundGivesRiemannHypothesis.lean and SChain.lean;
Formalism/ThickAverageLoss/ThickAverageProofs/ThickAverage.lean.
Native source:
RHLean/Analysis/AlpogeSharpASKCollar.lean.


## Full physical-colour upgrade (mathematical derivation; Lean formalization next)

The preceding bound was for the principal Lambert prime-power ASK.
In fact the *genuine fully character-inverted source* from
RHLean/Analysis/AlpogeNativeSharpASKBalance.lean also admits an exact
host-uniform estimate with no factor card(H).

Fix a finite abelian host H and arbitrary genuine data inertia(p)
(an additive subgroup of E0 x H), Frobenius(p) in E0 x H, a logarithmic
derivative parameter ell, and a colour t in H. For the original
physical ASK, use a constant width function on all positive sites:
w_c(g) = c. Write ASK_R(c) for the REAL part of
alpogeNativeFullKernelASK inertia frob X_R a_R t w_c.
Write MAIN_R(c) for the REAL part of
alpogeNativeMAIN ell a_R w_c. Their signed difference
D_R(c) = ASK_R(c)-MAIN_R(c) is EXACTLY
Re(alpogeNativeDe inertia frob ell a_R t w_c),
by the existing kernel-certified algebraic identity.

For every genuine prime power p^i (including ramified), the
kernel-certified ORTHO-RAM formula is

    K(p^i,g) =
      (2 / |I_p|) * 1_{g-i*Frob(p) in I_p}.

Each inertia coset has |I_p| elements, hence even after restricting to
non-Phi colour sites,

    K(p^i,g) >= 0,
    sum_{g notin Phi} K(p^i,g) <= 2.                    (F1)

This is a deterministic coset-cardinality bound with NO factor |H|.
For integers that are not prime powers, Lambda(n)=0, so they do
not contribute. The real-valued ASK at any constant c therefore is
the exact weighted sum

    ASK_R(c)
      = sum_{n<=X_R} Lambda(n) *
          [sum_{g notin Phi} K(n,g)] * (a_R/n-c)_+.

Let j_n be the Jensen midpoint gap for widths R, R+1 at a_R/n.
The earlier physical crossing identity implies
j_n>=0, j_n=0 unless R(R-1)<n<X_R, and j_n<=1/4.
Using (F1), all characters FIRST combined at the physical source,

    0 <= JASK_R :=
      (ASK_R(R)+ASK_R(R+1))/2-ASK_R(R+1/2)
       <= (1/2) sum_{R(R-1)<n<X_R} Lambda(n)
       <= (R-2)*log(X_R)/2.                            (F2)

No absolute value of a nonprincipal character sum was needed.
The Frob/inertia modes, including p=2,q,d, were all retained.

MAIN is an independently defined scalar:

    MAIN_R(c)
      = a_R*(log a_R - 1 - gamma + Re ell(chC) - log c).

Therefore its exact midpoint curvature is

    JMAIN_R :=
      (MAIN_R(R)+MAIN_R(R+1))/2-MAIN_R(R+1/2)
      = a_R*[log(R+1/2)-(log R+log(R+1))/2]
      = (a_R/2)*log(1+1/[4R(R+1)]).

Since log(1+t) lies in [0,t] for t>=0,

    0 <= JMAIN_R <= a_R/[8R(R+1)] = (R-1)/8.          (F3)

Subtracting (F3) from (F2) gives the FULL SIGNED, source-exact
uniform-width curvature bound

    -(R-1)/8 <=
        [D_R(R)+D_R(R+1)]/2-D_R(R+1/2)
                <= (R-2)*log(X_R)/2.                  (F4)

**F4 is a genuinely full ASK-MAIN/De finite arithmetic inequality**
with all nonprincipal character modes already accounted for via
their original physical Fourier inversion, and with no group
cardinality, theta theorem, PNT error, or RH hypothesis.

This proof is a mathematical derivation from already-formalized Lean
source identities and elementary inequalities. F1-F4 are NOT yet new
kernel-checked declarations: formalize their coset-cardinality and
log-midpoint bounds before marking F4 Lean-certified.

### Why F4 is not an RH proof

It is only a *centered second difference* of the whole signed De in
the **same uniform width across all colour sites**. It does not bound
D_R(R) itself, supply an anchor value, or prove source curvature
dissipation across the actual theta-lift family. Most importantly
the original Alpoge CostWindows constraint at x~R^2,
fPl~|H|>=R, b=R, eta>=0 is violated by these width choices:
6*fPl*(x+1)*(eta+1) <= b/x is NOT satisfied.

Consequently F4 is not an instance of the original upstream
growth estimate. A genuinely new short proof must REPLACE the generic
width-cost lemma by a paid centered-width theorem for the actual
geometrically realized partner widths, coupled with the original
topExcess height/covolume witnesses. Applying the upstream growth
inequality with our b=R choice would be an invalid inference.

**Research target:** prove the general all-site *weighted barycentric*
analogue of F4 for the theta-family's ACTUAL partner widths, then
show the centered return can be assembled without an enormous
first-order drift or lost rank-one term. If this is possible, the
same-source coset normalization may eliminate a factor |H| that the
generic characterwise width majorant pays unnecessarily.

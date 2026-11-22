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

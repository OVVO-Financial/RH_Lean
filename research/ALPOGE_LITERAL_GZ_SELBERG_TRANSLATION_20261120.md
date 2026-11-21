# Exact arithmetic translation: Alpöge Gz ↔ RH_Lean Euler/Möbius ↔ complete signed Selberg

Date: 2026-11-20 (US Eastern). **Mathematical status: exact finite equalities, Lean CI pending. This does NOT re-prove RH or provide the missing geometric/error estimate.**

## Original proof APIs — verified against source declarations, not paraphrase

External pinned source [CocoSgt/riemann-hypothesis-lean](https://github.com/CocoSgt/riemann-hypothesis-lean) (Lean 4.33.1):

- src/Formalism/StatementOC.lean defines exactly
    Sz(x) = sum_(1<=n<=floor(x)) Lambda(n)*(x/n-1),
    Gz(x) = Sz(x)-x*log(x)+(1+EulerGamma)*x.
- src/Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean:
    ArithData(H) = (q1,d,inertia,frob),
    HostFacts(D), primVal(D,chi,n), GPsi(D,ell,chi,y),
    ASK(D,N,a,t,w), MAIN(ell,a,w), De(D,ell,a,t,w),
    AskMainBalance: ASK-MAIN=De under genuine host/weight hypotheses.
  In particular GPsi(D,ell,0,y) = Gz(y) DEFINITIONALLY, without using
  a Möbius/prime-band matrix.
- src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean:
    GrowthInequalityExplicit, SizeWindows,
    GrowthInequalityDataExists C eps x,
    GrowthBoundGivesRiemannHypothesis.
  Here GrowthInequalityDataExists is a *family* of same-source geometric
  and analytic witnesses: finite H, frob/inertia, weights w, thick top
  sets TT/T2, normalized topExcess, character estimates and ALL costs.
- src/Formalism/ZetaNonvanishing/ZetaLandau.lean and
  src/Formalism/SizeWindowBrackets/ChainSlopeWindows/RiemannHypothesisOfPowerBound.lean:
  proved one-sided Gz-to-zeta-zero exclusion.
- src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:
  everyCharacter follows from the actual Galois/automorphic/row theorem.
- src/Supplements/Kernels/MainTheorems.lean:
    allChi := FinalTheorems.everyCharacter,
    rhOfAll := Formalism.VW.rh_of_every allChi.
  The FINAL exported proof uses this EVERY-CHARACTER chain; DO NOT
  assume the SizeWindows reduction is definitionally the exported
  theorem's direct last-mile proof without a transitive DAG audit.

## What is NOW translated, literally and with exact proof statements

Companion Lean source:
  research/ALPOGE_LITERAL_GZ_SELBERG_TRANSLATION_20261120.lean

At ANY NATURAL N (no limiting theorem, no probabilistic assumptions):

(1) The literal Alpöge integer Gz source is the native source:
    Gz(N)
      = N*LambdaRecip(N) - psi(N)
        - N*log(N)+(1+gamma)*N.

(2) PR #1156's established source identity mu*log=Lambda lifts this
    SAME Gz(N) to the original Möbius/Euler convolution coordinate
    without truncating virtual divisors or losing prime powers.

(3) Algebraic regrouping gives a crucial *exact* relation:
    Gz(N)
       = N*(LambdaRecip(N)-log(N)+gamma) - E(N),
    E(N)=psi(N)-N.

  **The reciprocal-Lambda channel is NOT a harmless zero.** The PNT
  supplies at best o(N) in this expression; at the RH-strength root
  exponent this term must be retained and quantitatively controlled or
  incorporated via the original Alpöge weighted source.

(4) Using the EXISTING second signed-Selberg theorem, the exact original
    full source (no triangle inequality) is

    S2(N) := S(N)*log(N) - (Lambda*S)(N)
            + (K2*E)(N) - floorDefect(N)
           = E(N)*log(N)^2,

    K2 = Lambda*Lambda - Lambda*log.

    Therefore
       Gz(N)*log(N)^2
         = N*(LambdaRecip(N)-log(N)+gamma)*log(N)^2 - S2(N).

This is an exact SOURCE-TO-CONSUMER identity for the SAME Gz as Alpöge,
not a new RH-equivalent conjecture pasted into a note.

At square endpoints X_R=R^2-1:

(5) Define the exact arithmetic site predicate
      BANDSITE_R(n) iff exists prime p,q in [3R/4,R), n=p*q.
    The full SECOND Selberg K2*E coefficient sum partitions by a genuine
    finite filter:
      (K2*E)(X_R) = K2band_R + K2other_R.
    The complement includes ALL off-band prime squares, prime powers,
    semiprime cross-band pieces, all reciprocal quotient depths, etc.
    NO claim that disjoint 3x3 minors form a block-diagonal full source.

(6) Put
    CREDIT_R := -K2band_R,
    COMPLEMENT_R := S(X_R) log X_R -(Lambda*S)(X_R)
                    +K2other_R -floorDefect(X_R).
    Then **exactly**
       E(X_R)*log(X_R)^2 = COMPLEMENT_R-CREDIT_R.
    This is the source-faithful version of prior informal C_R-B_R.

(7) The literal external analytic signal is now
       Gz(X_R)*log(X_R)^2
         = X_R*(LambdaRecip(X_R)-log(X_R)+gamma)*log(X_R)^2
           -(COMPLEMENT_R-CREDIT_R).
    A source-quantitative upper bound on the RHS <= M*log(X_R)^2,
    with R>=2, implies Gz(X_R)<=M. A nontrivial full-source estimate
    is NOT asserted. Note that upper semivariance of E alone controls
    the opposite sign -Gz through an analytic tail; this direct algebra
    is signed correspondingly and MUST NOT invert the sign.

## Exact algebraic API versus the STILL MISSING witness API

The newly typed target is NOT a replacement for the external
GrowthInequalityDataExists. Its arithmetic side has the correct Gz
observable and FULL K2+Euler compensation. To inherit Alpöge's
GrowthInequalityExplicit AND his root-bound consumer, one must now
supply a genuine external-compatible witness family with:

  H, group instances, D=(q1,d,inertia,frob) satisfying HostFacts,
  ell (logarithmic character constants), N,m,TT,T2,a,w,b,b',eta,X',
  theta,Cd,CL,Err and the exact ASK/MAIN/De identity;
  topExcess<=Err, ThinScales, NodeSizes, ValuesAtX,
  Lipschitz/derivative, SmallCosts, SizeWindows,
  plus underlying integral Hecke/height/covolume inputs.

**Important type no-go:** Since a multiplicative character generally
has chi(p^2)=chi(p)^2 for unramified p while mu(p^2)=0, the raw Möbius
function cannot be substituted as an unramified character. The safe
translation passes through the common von Mangoldt/Gz observable or
constructs the ACTUAL character via Frobenius/inertia from the external
source, not by renaming mu as chi.

**Independent project**: Direct port/packaging of the external verified
theorem into RH_Lean's Lean 4.34.1/Mathlib d13f... must either update the
external source to this toolchain and reproduce its kernel check, or
preserve the external Lean 4.33.1 environment as an independent
certificate. An .olean from a different compiler is not a substitute.

## Proof acquisition targets

A. Run the new module with exact-head, -DwarningAsError=true research
   closure. Correct any Lean errors without changing propositions.
B. Prove the finite filter K2band_R is EQUIVALENT to the ordered
   all-prime-band D(2I-J)D face, with each p*q counted once. Current
   PR #1160 establishes pairwise coefficients and square quotient one;
   the finite-set reindexing is a distinct uncompleted theorem.
C. Obtain the complete SAME-FAMILY geometric/character cost estimate,
   not a rank/condition-number proxy. The source-compatible hard
   witness is GrowthInequalityDataExists or the actual EveryCharacter
   branch's upstream admissible row source.
D. Import external verified proof using toolchain-compatible kernel
   replay; separately establish which native assumptions, if any,
   replace which exact hypotheses in the upstream proof DAG.

A success at (A) establishes a **literal exact arithmetic translation**
that previously existed only in prose. It does NOT establish (B)-(D),
nor a bound on Gz or RH.

# ALPOGE RECONSTRUCTION INSIDE RH_LEAN OWN ARITHMETIC

2026-11-20. This implements the user-requested independent native route.
The Lean source does NOT import the external Alpoge RH theorem or his
completed Galois/automorphic development. No new RH result is claimed.

## Genuine prime-power Euler and multiplicative Dirichlet characters

New: RHLean/Analysis/AlpogeNativeFourCharacterArithmetic.lean

Actual RHLean arithmetic weight:
  W_x(n) = Lambda(n)*(x/n-1),  1 <= n <= floor(x)
including ALL prime powers and the correct floor convention.

For an ACTUAL DirichletCharacter chi modulo q:
  S_chi(x)=sum_n W_x(n)*chi(n)
  Gchi(x)=S_chi(x)+x*ell_chi
  Gz(x)=x*nativeLambdaRecip(floor x)-nativePsi(floor x)
        -x log x+(1+gamma)*x.
The logarithmic L-derivative ell_chi is an input rather than a
fictitious formally evaluated analytic quantity.

Four-channel arithmetic:
  T_AB(x)=sum_n W_x(n)*(1+chiB(n)-chiA(n)-chiA(n)*chiB(n)).

On the physically quadratic unramified class (a,b) in {+1,-1}²,
  1+b-a-ab=4 if (a,b)=(-1,+1), else 0.
This recovers the central 1+B-A-AB sign pattern of external Gsig.
The explicit BAD_RETURN contains every actual character site that
is not both plus/minus one, including ramification or nonbinary
phases. No prime power or signed remainder is discarded:

  T_AB=4*SelectedQuadraticPrimePowerSource+BAD_RETURN.

A separate exact finite-character Fubini result:
  sum_{chi in T} a(chi)*S_chi(x)
    = sum_{n<=floor x} W_x(n) *
       sum_{chi in T} a(chi)*chi(n)

is the native ASK/De arithmetic trace interface. This is NOT a
claim to have proved the external ASK-MAIN=De theorem, which
also needs actual Frobenius/inertia data and geometric weights.

## Complete native signed Selberg

The same Lean module imports original RHLean arithmetic:
  E(N)*log² N = S(N)*log N -(Lambda*S)(N)
                +(K2*E)(N)-floorDefect(N).
For EVERY REAL x, N=floor(x), it derives:
  Gz(x)*log² N =
    [x*(LambdaRecip(N)-log x+gamma)+(x-N)]*log² N
       - CompleteSignedSource(N).
All mixed, prime-square, prime-power, first-Selberg, and
floor return terms remain inside the full K2 source.

## Actual finite quadratic-character census

scripts/alpoge_native_quadratic_character_trace.py uses the two
quadratic Dirichlet characters modulo 15 lifted from mod 3 and mod 5,
both zero on every nonunit modulo 15. It calculates ACTUAL Λ(n)
including every prime power. Trace = fourfold selected + ramified return:

 x       selected powers     ramified powers      trace
 101         7                    6           241.085702
 317.5      16                    8          1108.707909
 1027       43                   10          4775.284314
 10000     308                   13         69193.145711
 100000   2399                   17        922032.692650

The trace is pointwise nonnegative for x>=1 in this genuine
quadratic example, but Gsig also has a large negative x log x
main term and L-derivative constants. This is NOT RH-level
cancellation. In particular, a single fixed modulus is not
a substitute for the growing geometric host in external
SizeWindows.

## Exact correspondence to original source

- Formalism.Gz: same finite von Mangoldt source, complete signed K2.
- GPsi nonprincipal branch: genuine Dirichlet character twist at
  every prime power; analytic ell(chi) explicitly retained.
- Gsig 1+B-A-AB: literal four-channel projector with true
  quadratic multiplicative characters and explicit bad return.
- ASK-MAIN=De: only its finite arithmetic character trace is
  reconstructed, not the Frobenius/inertia positive ASK identity.
- GrowthInequalityDataExists: NOT proved or imported. The original
  movement/height/covolume/SizeWindows bill is not established.

The next theorem must establish a uniform paid full-source estimate
for the SAME Gsig with growing conductor and complete signed returns.
There are no new assumptions of RH, no made-up independent prime signs
and no library import of Alpoge external proof.

CI with warningAsError on the exact head is necessary before
calling the new native theorems Lean-certified.

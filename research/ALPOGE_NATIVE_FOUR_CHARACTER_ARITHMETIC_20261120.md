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


## Second actual finite proof layer: SHARP ASK, not another abstract hypothesis

The companion native module
RHLean/Analysis/AlpogeNativeSharpASKBalance.lean now reconstructs
the key finite positive-part cutoff from external
Formalism.SizeWindowBrackets.ChainSlopeWindows.StronglyIrreducible.
It is proved FROM RHLean's own coefficients.

For arbitrary actual complex arithmetic c(n), a>0, W>0 and
N>=a/W, EXACTLY (not asymptotically):

  sum_{n<=N} c(n)*max(a/n-W,0)
      = W*sum_{n<=floor(a/W)} c(n)*(a/W/n-1).

The proof uses Nat.floor, the true cutoff condition and a finite
reindexing; no smooth approximation or character sum bound.

Specializing c(n)=Lambda(n)*chi(n) for a genuine DirichletCharacter,
then using the same native Gchi definition gives the native
nonprincipal inner ASK balance

  ASK_chi(N,a,W)
    = W*Gchi(a/W) - a*ell_chi.

For ANY finite family of moving physical weights w_j, the theorem
sums this equality over all j exactly, so it reproduces the
ASK-to-Gchi weighted family algebra with *no missing integer*.
The original Alpoge formalism then adds Galois/Frobenius/inertia
data to produce positive ASK and geometric/full error control.
Those extra analytic/geometry costs remain genuine tasks;
the native sharp ASK theorem does NOT declare their values.

This is the precise next arithmetic component demanded by the
original roadmap: genuine Gsig projector and sharp ASK balance
joined to RHLean's complete signed second Selberg recurrence.
The new module requires exact-head Lean compilation before
it can be called kernel-certified.


## Quadratic projector POSITIVITY actually proved on the native source

The original source now contains a **new proved arithmetic estimate**, not
another \`HostFacts\`/RH-strength premise. It is conditional only on the
elementary algebraic statement that two genuine Dirichlet characters
modulo the SAME \`q\` satisfy \`chiA^2=chiB^2=1\`.
Such characters genuinely exist (e.g. the two quadratic lifts mod 15).

Write \`w_x(n)=Lambda(n)*(x/n-1)\` with \`1<=n<=floor(x)\`, \`x>=0\`.
Then \`w_x(n)>=0\` (proved, no PNT used), and genuine quadratic characters
satisfy the exact identity at EVERY integer n:

    (1-chiA(n))*(1+chiB(n))
       = 4          if n is a unit mod q, chiA(n)=-1, chiB(n)=1;
       = 0          if n is a unit mod q, other character signs;
       = 1          if n is NOT a unit mod q.

The last line is important. Dirichlet characters both vanish on a
nonunit; ramified prime powers have factor 1 and therefore **cannot**
be treated as arbitrary complex errors. Their mass is literally

    Ram_q(x) = sum_(1<=n<=floor x, not IsUnit(n mod q))
                 Lambda(n)*(x/n-1) >= 0.

Since Lambda is supported on prime powers, this support comprises
exactly the prime powers p^k with p dividing q, without discarding any
prime power. The corresponding full positive trace is

    Trace_AB(x) = 4*Selected_AB(x) + Ram_q(x),
    Re Trace_AB(x) >= 0.

The Lean proofs derive binary values on units directly from \`chi^2=1\`
and \`MulChar.pow_apply'\`, and derive ramified zero values directly
from \`MulChar.map_nonunit\`. They then prove the positivity of the
actual \`Lambda(n)\` weight under the sharp floor and the **paid,
unconditional bound**

    0 <= Ram_q(x) <= x*nativeLambdaRecip(floor x).

This latter bound is not root-scale. It is already a genuine upper
bound on the full actual ramified source, not an interface with an
open estimate masquerading as a proof. It also makes clear why
positivity alone does not prove the desired \`Gz=O(x^(1/2+eps))\`.

An elementary refinement (mathematical argument, NOT YET Lean-certified)
is \`Ram_q(x) <= x * sum_(p|q prime) log(p)/(p-1) <= x*log(q)\`,
by splitting Lambda into its prime-power fibres and summing the
geometric series. This highlights the conductor-growth cost of
varying q; no unproved \`O(sqrt x)\` or square-root cancellation claim
is attached to this refinement.

### What is and is not reconstructed

**Proved arithmetic mechanism:** exact quadratic Fourier projector,
character-induced vanishing on nonunits, positive and quantitatively
bounded complete ramified return, selected-class positivity,
prime-power weights and floor endpoints, plus earlier exact ASK/Gchi
and signed Selberg identities.

**NOT proved:** that these true Dirichlet-character traces are the
automorphic theta-lift periods in the published construction;
positive relative trace formula \`ASK-MAIN=De\`; m-fold arithmetic
multiplicity with a fixed-sign cost bound; Bost slope, p-adic
divisibility, full covolume estimates, or the claimed numerical
root-strength bound on the COMPLETE signed source. None of these
are hidden in a new abstract predicate. This is a first **actual
unconditional local inequality** on RHLean's original arithmetic,
not a claimed completion of Alpoge's proof.

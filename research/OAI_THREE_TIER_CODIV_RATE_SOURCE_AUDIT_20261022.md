# Three-tier Co-Div rate: exact arithmetic gain versus source obligations

**Status 2026-10-22:** native finite Cauchy-Schwarz formalized with no new analytic assumptions, but original OAI rowwise source decomposition, actual source transport, and pairwise nonuniform Poisson estimates remain open until proven. Warning-fatal Lean 4.34.1 CI is required for this PR.

## 1. Actual original source variables

Pinned source \`openai/math@1581d4cb\`, \`Detector/EulerCoordinates.lean\`:
\`V=Q^(-6z)\`, \`R=A Q^(4-6x-6z)\`,
\`W=v Q^(-w)\`, \`D=eta*conj(v)*Q^(-x)\`,
\`K=eta*(Q-1)*Q^(-x-w)\`, \`B=conj(eta)*Q^x\`.
\`V\` is ROW-INDEPENDENT; \`D\` is the harmonic \`v^-1 = v^5\` on \`mu_6\`.
The user-proposed formula \`V=chi_P(u) Q^-x\` does not describe OAI's \`coordV\`.

The exact local normalized cancellation in \`Detector/Local.lean\` is
\`\`\`text
CompReplacement + vInv * ContinuedCorrection
= [(1-V)(1-W)/(1-D)] *
    [ (vInv-q)(V/(1-V)-D)
      +(B+vInv-q)(Pstar+D) ].
\`\`\`
Here \`Pstar\` is the ACTUAL \`markedFactor\`, NOT \`-V\`.
This is TWO exact bills, not an established *three-term signed identity*
\`D+BR+BKV\`. Source-exact extraction is mandatory before using native
tier-energy bounds. Multiplying the BR/BKV pieces by source rational
prefactors is required; bare products \`B R\` and \`B K V\` are bounds
on contributions to the marked-error envelope, not entire physical
summands unless explicitly identified.

At x.re>=7/8, w.re>=0, z.re=17/50:
\`\`\`text
|B R| <= Q^(4-5*x.re-6*z.re) <= Q^(-483/200).
|B K V| <= Q^(1-w.re-6*z.re) <= Q^(-26/25).
|D| <= Q^(-x.re) <= Q^(-7/8).
\`\`\`
On x.re=a+16e, w.re=1-a-6e, the BKV exponent
is \`a+6e-51/25\`, reaching \`-233/200\` at a=7/8,e=0.
The original \`PrimeRows/CentralSlots.lean\` theorem restricts
\`0<e<=1/1000\`, although the local algebraic inequalities only
require \`w.re>=0\`. Extending the entire physical source to
\`e<=1/48\` is therefore not inherited from the pinned source theorem.

Furthermore \`B*K = (Q-1)Q^(-w)\` for unit eta.
Thus the LEADING \`B K V\` term is independent of the sextic row phase.
Do NOT send it to a nonprincipal character large sieve.

## 2. Valid finite tier-energy bounds

Let \`W=sum_u rho_u\`, \`Q_P=N P>0\`, all \`rho_u>=0\`.
For any actual source-extracted tier amplitudes with
\`|BR_P(u)|<=C_BR Q_P^(-483/200)\`, the native theorem gives

\`\`\`text
E_BR <= C_BR^2 W
         (sum_(P in S) Q_P^(-7/4))
         (sum_(P in S) Q_P^(-77/25)).
\`\`\`
The second factor is bounded by a Dedekind zeta upper bound for
prime-ideal norms, so BR is unconditionally paid at the diagonal rate
once source extraction and Q>=4 are justified.

For \`|BKV_P(u)|<=C_BKV Q_P^(-26/25)\`, one obtains

\`\`\`text
E_BKV <= C_BKV^2 W
          (sum_(P in S) Q_P^(-7/4))
          (sum_(P in S) Q_P^(-33/100)).
\`\`\`

At a=7/8,e=0, assuming the stronger pointwise norm rate -233/200
gives the factor \`sum_P Q_P^(-29/50)\`.
NEITHER -33/100 nor -29/50 is summable across all prime ideals.
For dyadic P~Q, the relative factor grows roughly as
\`Q^(67/100)/log Q\` or \`Q^(21/50)/log Q\` respectively.
Thus BR is closed; BKV has an unconditional improvement but is
NOT CLOSED at the diagonal rate and cannot simply be discarded.
If the desired goal is merely o(W), BKV alone does decay in a dyadic
band by a separate absolute summation argument.

## 3. What sextic nonresonance really establishes

For distinct prime-ideal coordinates P != Q and harmonic 1<=m<=5,
the exponent vector \`P^m Q^(6-m)\` is nonzero modulo 6 at P.
This is a purely finite algebraic nonresonance certificate.
It does not prove that the ORIGINAL Hecke source characters factor
through these vectors for all admitted masks.

Uniform complete \`mu_6\` averages of a nontrivial character vanish.
The original physical row weights are NOT uniform; PR #1005 proves
the exact remaining *weighted six-sector defect* rather than its
vanishing. The proposed expression
\`(1/6) sum_{coprime u} rho_u = 0\` is false for positive rho;
it is a weight mean, not a character sum.

For the sixth moment, the 3! collision bound applies to
ordered triples of *identical ideal products* and, for primitive
harmonics m=1 or 5, to equality of sixth-power characters across
triple factors (valuation differences lie in [-3,3]).
For m=2 or 4, three repeated copies of one prime create a trivial
sixth-power character; for m=3, two repeated copies already do so.
The exact nonprimitive resonant collision classes must be included
rather than dismissed via ideal factorization.

## 4. Gauss conditional consumer and the true bottleneck

If source analysis proves for distinct P,Q a *physical weighted pair*
bound that already includes the actual D-harmonic coefficients,
\`\`\`text
|cross(P,Q)| <= C_G * W * c_m^2 *
                   (N P * N Q)^(-11/8),
\`\`\`
then finite Cauchy-Schwarz unconditionally gives an off-diagonal
bound by \`C_G W c_m^2 (sum(NP)^(-7/4))(sum(NP)^(-1))\`,
up to any ordered-pair prefactor.

This final step is a CONDITIONAL consumer. There is no universal
\`(NP*NQ)^(-1/2)\` Poisson estimate for arbitrary nonuniform rows:
even with a nontrivial sextic character, one may concentrate
all physical mass on rows of the same character phase.

A faithful source-based Poisson theorem must specify its original
Schwartz test, actual Eisenstein lattice, modulus, conductor and
different-ideal/copime admission conditions, true dual-frequency
transform and boundary errors, and a uniform estimate depending on
the row scale U relative to N(PQ). Saying U >> P^2 alone is not a
quantitative Gauss gain. No unproved large-sieve hypothesis should
be called an unconditional NNS bound.


## 5. Pay the nonprimitive m=4 cubic triple collisions exactly

The dominant original compensated local term is
\`-vInv*D=-eta*(conj v)^2*Q^(-x)\`, winding m=4, order three.
In a sixth-moment expansion with three positive and three negative
prime slots, a local multiplicity difference obeys
\`6 | 4(c_P-d_P)\` iff its difference is divisible by 3.
Because 0<=c_P,d_P<=3, the ONLY possibilities are
equal local multiplicities, or \`(3,0)\` and \`(0,3)\`.

Thus the nonprimitive resonant classes are identical ideal triples
(at most 3! permutations) **plus** pure cubes on different prime
ideals. The latter have N² possible pair labels, but a direct
fully unconditional finite inequality gives

\`\`\`text
 |sum_{P != Q} a_P^3 conj(a_Q^3)|
   <= (sum_P |a_P|^3)^2.
\`\`\`

For N<=C*P and |a_P|<=c*P^(-7/8), the RHS is
<= C^2*c^6*P^(-13/4). Hence cubic repeat collisions are
small in the ONE-PRIME scalar dyadic model; this is an explicit
candidate payment for Route B, not a proof of the weighted
sixth-moment on original Hecke row tests. The source
identification and actual sixth-power masks remain essential.

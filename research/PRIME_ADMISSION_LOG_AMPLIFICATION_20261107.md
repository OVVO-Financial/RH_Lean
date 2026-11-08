# Exact prime-admission logarithmic amplification

This formalization records the direct logarithmic calculation on the original
Mertens amplification. It proves finite identities and identifies the exact
historical maximum. The zero limiting power-growth exponent remains open.

## Original quantities

For an integer root `R >= 2`, let

\[
X_R=R^2-1,\qquad
K_R=\max_{0\le y<R}\frac{(M(y)-1)^2}{y+1},\qquad
\alpha_R=\frac{(M(X_R)-1)^2}{R^2K_R}.
\]

The maximum includes `y=0`, so `K_R >= 1`. The native profile module proves
that `K_R <= K` is equivalent to the existing
`LowerMertensCriticalEnvelope R K`. Consequently its concrete ratio is the
same arithmetic object used by `SquareRootMertensEndpointAmplificationStatement`.

Define the finite running maximum and the requested ratio by

\[
\mathcal A(X)=\max_{\substack{R\ge2\\R^2-1\le X}}\alpha_R,
\qquad
q(X)=\frac{\log(1+\mathcal A(X))}{\log X}.
\]

The implementation uses natural cutoffs `X`, with empty maxima extended by
zero. It proves the exact upper-bound characterization of this maximum,
pointwise domination, and monotonicity. The natural-cutoff limit `q(X) -> 0`
is exposed as the proposition `SquareRootAmplificationZeroLogGrowthStatement`.
There is no theorem asserting that proposition.

The existing fixed-constant amplification statement is proved equivalent to
uniform boundedness of the concrete ratios and of this running maximum.
These identifications do not assert boundedness or equate boundedness with
the weaker zero-log-growth target.

## Actual arithmetic states and logarithmic return

Keep the physical endpoint `X_R` fixed. At candidate cutoff `p`, let

\[
F_p=\Re(\mathrm{eulerAdmissibleState}(R,p))-1,
\qquad
m_p=\begin{cases}M(\lfloor X_R/p\rfloor),&p\text{ prime},\\0,&\text{otherwise}.
\end{cases}
\]

The previously proved `eulerAdmissibleState_step` supplies
`F_p = F_(p-1) - m_p` for every `R <= p <= X_R`. The new module specializes
that theorem to centered real states; it does not take the recurrence as an
extra arithmetic hypothesis. The initial state contains exactly the original
product-admissible population with prime factors `< R`. Full admission gives
`F_(X_R) = M(X_R)-1`.

Set `W = R^2*K_R`. For every real `F,m` and `W>0`, the native algebra module
proves that both logarithm arguments below are positive and that

\[
\log\!\left(1+\frac{(F-m)^2}{W}\right)
=\log\!\left(1+\frac{F^2}{W}\right)
+\log\!\left(1+\frac{m^2-2Fm}{W+F^2}\right).
\]

The actual arithmetic telescope is therefore

\[
\boxed{
\log(1+\alpha_R)
=\log\!\left(1+\frac{F_{R-1}^2}{W}\right)
+\sum_{p=R}^{X_R}
\log\!\left(1+\frac{m_p^2-2F_{p-1}m_p}{W+F_{p-1}^2}\right).
}
\]

The inclusive boundary `p=R` remains present when prime. Composite stages
are proved to have zero logarithmic increment. Every genuine daughter has
cutoff strictly below `R`, and primes above `X_R/2` have daughter exactly `1`.
The denominator is the same positive historical maximum throughout the sum.

The final finite-cutoff consumer directly links this sum to the requested
ratio. For `X >= 2` and `epsilon >= 0`, it proves

\[
q(X)\le\varepsilon
\quad\Longleftrightarrow\quad
\forall R\ge2\ (X_R\le X),\quad
\mathrm{eulerAdmissibleLogReturn}(R,R^2K_R)
\le\varepsilon\log X.
\]

This retains all admitted square endpoints and one common right side.
It supplies an exact consumer for a future signed-return estimate; it does
not prove that estimate.

Every signed mixed term and the initial population are retained. No estimate
on their complete return is proved by this identity. In particular, this PR
adds no finite-`A` theorem, no global Mertens exponent improvement, and no RH
claim. The earlier paper discussion of a zero-supremum exponent is outside
this formalization.

## Public declarations and dependency map

| Source | Main declarations | Purpose |
| --- | --- | --- |
| [PrimeAdmissionLogPotential](../RHLean/Proof/PrimeAdmissionLogPotential.lean) | `primeAdmissionLogPotential_step`, `primeAdmissionLogIncrement_argument_pos`, `primeAdmissionLogPotential_telescope` | Exact real logarithm algebra, positivity and finite telescope. |
| [SquareRootAmplificationLogGrowth](../RHLean/Proof/SquareRootAmplificationLogGrowth.lean) | `squareRootHistoricalK_le_iff`, `squareRootAmplificationMax_le_iff`, `squareRootMertensEndpointAmplification_iff_boundedRunningMax` | Original denominator and ratio, finite maximum, and correspondence with the existing finite-`A` statement. |
| [Arithmetic specialization](PRIME_ADMISSION_LOG_AMPLIFICATION_20261107.lean) | `eulerAdmissibleCenteredRealState_step`, `eulerAdmissibleLogReturn_eq_endpoint`, `squareRootEndpointAmplification_log_identity`, `squareRootAmplificationLogRatio_le_iff_primeAdmissionLogReturn` | Original Möbius states, original normalization, full signed logarithmic return and the direct finite-cutoff ratio consumer. |
| [Exact type acceptance](PRIME_ADMISSION_LOG_AMPLIFICATION_ACCEPTANCE_20261107.lean) | Explicit typed examples | Reject hidden recurrence/cancellation premises and test the `R=2` normalization. |

The arithmetic specialization imports the established
[Euler population source](EULER_ADMISSIBLE_PRIME_POPULATION_CODIV_20261028.lean).
The two new native modules are exported from `RHLean.lean`. The research
consumer is compiled through the repository's content-validated research
import-closure action.

## Verification

The dedicated [GitHub Actions workflow](../.github/workflows/prime-admission-log-amplification.yml)
checks out the exact PR head, uses the existing Lean `4.34.1` and Mathlib pins,
compiles the full research import closure and the explicit type acceptance,
and recompiles the two new native modules with warnings fatal.

The [audit script](../scripts/audit_prime_admission_log_amplification.py)
checks the exact inventory of 45 public theorems, both native exports, the
absence of proof shortcuts, and every theorem's terminal axioms. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted. The ratio and
zero-limit proposition receive definition checks, not assertions of truth.
Evidence includes the source hashes, checked commit, compiler log and axiom
inventory. The workflow result at the current PR head determines compilation
status.

The kernel regression at `R=2` has `K_2=1` and `alpha_2=1`, since `M(3)=-1`.
It uses actual Möbius values and cannot be replaced by the seed-only world's
different endpoint value.

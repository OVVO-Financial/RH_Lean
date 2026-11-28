# Full-rank scalar reconciliation: a sharp forward-height cost

Continuation from e0bc29d, on the same sparse projected star and its two
actual split-factorial depth profiles (NATIVE_SPARSE_ANCHOR_GLOBAL_HEIGHT_20261128.md
and NATIVE_POSITIVE_TWIST_TEST_HEIGHT_20261128.md). No new conditional
closure interface or terminal theorem.

Upstream tether (pinned Sernau 72fead102f663d5c7a407964a13dc0cf9d977207):
Rows/HeckeValueHeight.lean:154--238, Rows/ComparisonForms.lean:200--228,
Rows/LiftVolumeHeight.lean:103--127, Endgame/LongForms.lean:22--74.
The readable TwistedValueHeights.lean explains the four factors.
The forward and inverse bounds must be independently earned on compatible
rows; a scalar on an exterior line is not a common scalar on the whole
table.

## 1. Test the proposed scalar reconciliation on the measured profiles

Keep a fixed sparse pivot and all its retained layers, with original
counts n_i>0, depths D_i,E_i>0, and the same unimodular incidence B.
In layer-amplitude coordinates the two maps are diag(D_i)B and
diag(E_i)B in the same counting metric diag(n_i). Consider the proposed
full-rank scalar comparison
    U_E^* g_E = gamma U_D^* g_D.
For matrices G_D,G_E of layer amplitudes this implies exactly
    G_E = gamma diag(D_i/E_i) G_D,
by cancellation of B^T and the common counting metric. This relation
also holds for any fixed full-rank minor of a rectangular test table.
No diagonal assumption on the test matrices is made. These are the
fixed-depth carriers, not arbitrary new lift spaces or changed metrics.

Test the volume-normalized common scalar demanded if the exterior
ratio is distributed uniformly through the rank:
    |gamma|^(2r) = (prod_i E_i/D_i)^2.
This is the condition that the test-matrix determinant norms are equal,
not a condition claimed for every upstream Hecke scalar. It is exactly
the geometric-mean scalar candidate for these fixed native profiles.

At a prime p let v=-log_p |.|_p, s_i=v_p(D_i/E_i), mu=(sum s_i)/r.
The ordinary and conjugate embeddings of the same complex scalar have
valuations a,b with a+b=-2 mu, since gamma*conj(gamma) is the positive
real r-th root of (prod E_i/D_i)^2. Roots of unity or other phases do
not change this equation. This uses the same gamma at both embeddings,
as in the conjugate-side test of upstream heightLe_inv_ratio.

## 2. Local determinant bound with full finite clearing retained

Fix a square independent minor G_D of the untwisted algebraic tests,
integral at every finite embedding, with det G_D nonzero. Allow an
arbitrary integral nonsingular column clearing matrix M at an embedding
so that G_E M is integral there. G_D M is also integral. Every entry of
row i of G_D M has valuation at least
    f_i(a)=max(0,-a-s_i).
The determinant expansion therefore gives
    v(det G_D) + v(det M) >= sum_i f_i(a).
This does not require M to be diagonal, and the bound applies to the
chosen fixed independent minor. At the conjugate embedding apply the
same argument with a possibly different integral clearing M'.

The elementary convexity identity/inequality is
    f_i(a)+f_i(b) >= 2 max(0,mu-s_i)
    2 max(0,mu-s_i)=|s_i-mu|-(s_i-mu).
Sum over the rows and use sum_i(s_i-mu)=0. Thus
    v(det G_D)+v(conj(det G_D))+
      v(det M)+v_conj(det M') >= sum_i |s_i-mu|.
Here v_conj is the valuation of the clearing at the conjugate
embedding; the two det G_D terms are taken at the original embedding.
The arithmetic inequality is submitted in NativeCommonScalarCost.lean.
The matrix application and all-place step are paper proofs.

## 3. Global price, even for algebraic phase and mixed tests

Suppose the local comparison is provided for every finite embedding,
with one fixed algebraic integral G_D, and with a common uniform upper
budget E_p for the sum of the two log clearing costs
    (v(det M)+v_conj(det M')) log p <= E_p.
Let L=sup_sigma log|sigma(det G_D)| over all complex embeddings.
The nonzero algebraic integer H=det G_D*conj(det G_D) has archimedean
allowance 2L; this does not assume that arbitrary sigma commute with
complex conjugation. Every finite-place log norm of H is at most
E_p-(sum_i|s_i-mu|)log p. The number-field product formula, or its
rational norm proof, yields
    L + (1/2) sum_p E_p >= (1/2) sum_p log p sum_i |s_i-mu|.
Finite sums on the right include the primes dividing the fixed depth
ratios; the clearing sum must be bounded on all places. A separate
per-embedding allowance e_p gives E_p=2 e_p. This is a joint
archimedean/finite bound on the actual test determinant, not a
definition of the desired signed prime sum.

Sharpness (allow algebraic test scalars): put gamma=prod_p p^(-mu_p),
and take G_D diagonal with entries prod_p p^max(0,mu_p-s_(p,i)).
All fractional powers are positive real algebraic roots, with all
conjugates of the same modulus. G_E then has entries
prod_p p^max(0,s_(p,i)-mu_p). Both matrices are algebraic integral,
and both determinants have identical absolute norms, because the
centered exponents sum to zero. Both tables are full rank, M=I,
and equality holds in the global bound. Thus a more clever phase
or integral basis mixing cannot beat this price on the fixed
carrier under this prescribed scalar relation.

## 4. Specialization to the native depth reading and multiplicities

If p occurs in just one of r retained directions and has signed
exponent s there, the half-deviation is (1-1/r)|s|. If p occurs
with the same exponent s in m of r directions, the price is
m(1-m/r)|s|. The general formula above keeps all actual incidences,
including different exponents on different directions. Rank one
has zero spread; grouping identical local valuations removes this
particular bill, but does not give the independently bounded forward
height for the reassembled global comparison.

In the complete arithmetic product R_full, each prime factor is
recorded once, so on its direct-sum depth coordinates with r>=2
the normalized price is
    (6/c)(1-1/r) sum_p |beta_p-alpha_p| log p,
    c=floor sqrt(x).
The previous independently calibrated split-factorial calculation
gives (6/c) sum_p |beta_p-alpha_p| log p=2 kappa x+o(x),
kappa>0 by ordinary PNT, including the previously unserved labels.
Thus charging this common-scalar reconciliation as an error on
the complete product does not give the necessary square-root bound.
The complete arithmetic direct sum is not the original physical
retained incidence rank. On a physical sparse star use the actual
local rank and multiplicities; a single prime in rank r>=2 costs
at least |s|/2, while omitted or singleton layers must be accounted
for in the existing incidence ledger. Do not assert that the
served subset alone has both full linear masses.

## 5. Consequence for the forward estimate

The direct attempt to convert the already attained exterior ratio
into one full-rank scalar on the same fixed depths has a sharp
unsigned cost. This closes that particular proposed shortcut; it
does not exclude a different independent common main amount which
pays such a cost in BOTH comparisons, nor genuinely different
tested lift spaces with the upstream norm relation.

The next unpaid operation remains the original signed comparison:
build the actual short-form family or prove an independent
inequality on the calibrated factorial and original depth
allocation, with the forward height, rank and lower determinant
on the same rows. The nonzero Mellin component and the complete
source cannot be discarded. No bound on log R_full, no cofinal
window supplier, and no native_riemannHypothesis are claimed.
Preserve the #1214 acceptance gate and #1205 consumer.

Exact integer-scaled regression: scripts/research/check_native_common_scalar_cost.js.
67,518 paired-phase checks, 744 balanced equality checks,
105,056 multiplicity checks. Finite regressions do not prove the
asymptotic bound or Lean elaboration. Five proof roots are submitted
to the existing strict and explicit hosted audits; kernel status
pending.

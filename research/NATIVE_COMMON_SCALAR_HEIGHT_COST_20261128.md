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

## 6. The forward height and its independent supplier

Write $H=D.\mathrm{mainHeight}$, $R=D.\mathrm{remainder}$ and
$L=D.\log B\cdot D.\mathrm{budget}$ in the pinned compact edition. For
a fixed family of $n$ independent rows, $V$ bounds the log squared
covolume of their untwisted lifts at every complex embedding and
$\delta$ bounds their finite clearing index. The forward conclusion is
\[
\mathrm{HeightLe}\!\left(V+2\delta+D.\mathrm{rowDim}\,D.b,\
     \iota\mapsto\mathfrak z(\theta_\iota)/\mathfrak z(1)\right).
\]
Here $\mathfrak z$ is already a squared lift volume. The
$D.\mathrm{rowDim}\,D.b$ term pays for completing those same rows to a
basis with the crude rows. When combined with the independently bounded
inverse ratio, this gives $D.\mathrm{rowDim}(H-3L)\le V+2\delta$.
The upper bound $V\le n(H-mR+L)$ comes from A and B.
[Forward height and use in C](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Endgame/LongForms.lean#L34-L92).

The independent size input is the all-conjugate jet norm estimate on
the actual composite lift $B_\mu$. For a source column of log squared
size at most $b_\phi$, it bounds the log squared size of the image by
\[
 b_\phi+h_0+2\sum_p g_p\log p+D.\mathrm{budget}.
\]
Here $g_p$ is the local Euler gain, zero outside the specified nonsplit
set, and $h_0$ contains the real level term $-|\mathrm{tops}|a\log N$.
The level window gives $h_0\le H-mR+D.\mathrm{budget}$ by Stirling.
The same maps have independently proved finite-place divisibility
$g_p-\mathrm{allowedLoss}(p)$ on submodules of controlled index,
with rounding as in the cited declarations. Therefore scaling the
images by $\prod_p p^{\lfloor\mathrm{allowedLoss}(p)-g_p\rfloor}$
subtracts the gross $2\sum_p g_p\log p$ from the size bound and
charges the allowed losses in the index. At the level prime $N$,
the finite index is bounded through the Fourier operator on the
ramified columns. That is the separate input needed to use the
real level term on the same images.
[Jet norm and local divisibility](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Columns/LocalStatement.lean#L198-L226) ·
[Level-prime index](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Seesaw/LiftCharacters.lean#L125-L167) ·
[Short rows and their index](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Endgame/ShortAndEnough.lean#L44-L70)
([scaling and index](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Endgame/ShortAndEnough.lean#L128-L168)).

## 7. Optimal forward cost over mixed retained frames

Use the physical amplitudes of the fixed sparse star. The incidence
change of coordinates is unimodular and the untwisted counting weights
are $w_i=n_i>0$. Put $r_i=D_i/E_i$. In the existing positive-twist
construction the inverse normalized relative lift at $\iota$ is diagonal
with entries
\[
\eta_{\iota,i}=\frac{t_\iota(E_i)/E_i}{t_\iota(D_i)/D_i},
\qquad
v_\iota(\eta_{\iota,i})=v_p(r_i)
\]
because the two chosen roots are units. The untwisted relative lift is
the identity in physical amplitudes. At full rank the squared volume
ratio is $\prod_i\eta_{\iota,i}^2$. Its finite norm agrees with that of
$(\prod_i r_i)^2$, so this orientation has height $-2\log\prod_i r_i$.
[Positive twist and its exact height](NATIVE_POSITIVE_TWIST_TEST_HEIGHT_20261128.md#4-exact-reciprocal-height-computation).

Take any fixed rank-$n$ frame $Y$ with algebraic entries on these $r$
directions. Let $V(Y)$ be the supremum over complex embeddings $\sigma$
of $\log\det(\sigma(Y)^*\operatorname{diag}(w_i)\sigma(Y))$.
At $p$, use one upper allowance $e_p$ for the log determinant index of
the column-clearing matrices. They can vary with the embedding and
with the tested lift. The compact index condition includes the
untwisted lift as well as the selected fitted lift. Use $\delta=\sum_p e_p$.

For any $n$-element set $I$ with $d_I=\det Y_I\ne0$, entrywise finite
integrality after clearing gives
\[
v_\iota(d_I)\log p+e_p\ \ge\
   \log p\ \max\!\left(0,-\sum_{i\in I}v_p(r_i)\right).
\]
Indeed, the $I$ minor of the cleared untwisted frame contributes
$v_\iota(d_I)+v_\iota(\det C_1)$. The fitted minor contributes that of
$d_I$, its own clearing matrix, and the sum of the displayed
valuations of the fitted lift. The two clearing matrices may be
different. Cauchy–Binet gives
$V(Y)\ge\sum_{i\in I}\log w_i+2\log|\sigma(d_I)|$ at each
$\sigma$. Average the finite inequalities over the embeddings of a
number field containing $Y$, and use the product formula on $d_I$.
Averaging the real inequality then gives
\[
 V(Y)+2\delta\ \ge\ \sum_{i\in I}\log w_i+
     2\sum_p\log p\ \max\!\left(0,-\sum_{i\in I}v_p(r_i)\right).
\]
The proof uses a fixed nonzero minor. Thus it permits arbitrary mixing
and algebraic phases, including different clearing matrices on the
ordinary and conjugate sides. It also works for repeated physical
incidences with the displayed sum taken before the positive part.

When the prime labels are distinct and $r_i=p_i^{s_i}$, the exact
minimum of $V+2\delta$ over all rank-$n$ frames is the sum of the $n$
smallest numbers
\[
              \log w_i+2(-s_i)_+\log p_i.
\]
For equality, take the corresponding coordinate columns
$p_i^{(-s_i)_+}e_i$. Both lifts are integral at every selected
embedding with zero clearing cost. This is the forward cost with
the compact index condition on the literal fixed-depth lifts.
If the only finite requirement is the selected fitted lift, the
same argument removes the maximum with zero. The exact minimum
then sums the $n$ smallest numbers $\log w_i-2s_i\log p_i$,
attained by the columns $r_i^{-1}e_i$. At full rank, after removing
the common counting volume $\sum_i\log w_i$, that is exactly
$-2\log R$. Specializing to the selected twist therefore leaves the
signed size to be bounded independently.

On the complete calibrated arithmetic direct sum, distinct labels
and ordinary PNT give
$(6/c)\sum_i(-s_i)_+\log p_i=\kappa x+o(x)$ with $\kappa>0$.
Each $|s_i|\log p_i=O(c\log x)$. Hence omitting $o(r)$ directions,
where $r\asymp x/\log x$, saves only $o(cx)$ in the prime part.
Even after subtracting the minimum rank-$n$ counting volume,
the first minimum still has a linear cost on the $G_z$ scale.
The exact minor inequality applies separately to the physical retained
stars. This asymptotic uses the complete prime population including
the unserved labels.
[Calibration and both sign masses](SIGNED_MOBIUS_SPLIT_COMPENSATION_20261127.md#4-the-signed-prime-sum-that-survives) ·
[Complete source and per-layer size](NATIVE_SPARSE_ANCHOR_GLOBAL_HEIGHT_20261128.md#5-complete-the-arithmetic-handoff-including-the-unserved-labels).

The native level-prime construction supplies a norm element
$\pi\bar\pi=N$. On the fixed-depth lifts, using a fresh level prime to
rescale the frame cannot improve the preceding optima. Recovering the
upstream level benefit requires a tested lift with an independent
all-conjugate norm estimate and a finite repair on the same ramified
images. The positive-root construction and the fixed-depth forward
optimization leave the square-root bound on $R_{\mathrm{full}}$ open.
[Native level-prime construction](../RHLean/Analysis/AlpogeThin/NativeRayHostLevelPrime.lean).

## Verification

Exact integer-scaled regression: scripts/research/check_native_common_scalar_cost.js.
67,518 paired-phase checks, 744 balanced equality checks,
105,056 multiplicity checks. Finite regressions do not prove the
asymptotic bound or Lean elaboration. Five proof roots are submitted
to the existing strict and explicit hosted audits. At `02df460`, the
research job emitted `NativeCommonScalarCost` and then failed in
`NativePositiveTwist`. The repair evaluates the two constant
coefficients before cast simplification and removes the unreachable
tactic from `class_scalar`. [Hosted log](https://github.com/OVVO-Financial/RH_Lean/actions/runs/46156778872/job/141015191744).

For Section 7 an exact rational check compared the lower bound for
each nonzero maximal minor in 640 mixed frames with the actual minimal
local Smith indices. It attained both stated minima in 1,300 coordinate
cases. Section 7 is a paper result.

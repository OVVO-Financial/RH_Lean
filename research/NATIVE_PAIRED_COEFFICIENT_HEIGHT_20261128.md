# Native paired coefficient height and exact local index cost

Continuation of the pinned Alpöge comparison at #1214, starting at 02c3890. Paper proofs and exact finite regression, not a Lean-verified terminal supplier. No new closure interface.

## 1. Four upstream operations on the actual native data

Pinned upstream: lsernau/grh-lean 72fead102f663d5c7a407964a13dc0cf9d977207, grh-compact/src/New/Rows/HeckeValueHeight.lean (class-sum inversion and factorisation at lines 23–65; integral coefficient test at 95–153; heightLe_inv_ratio at 154–216), Rows/Separation.lean:83–98, Heights/Heights.lean:21–22,65–end, Rows/LiftVolumeHeight.lean and Endgame/LongForms.lean.

The native depth, class-sum recovery and actual projected coefficient are already present in NativeRankOneEulerRepayment.lean (chartRead_eq, common_jet, exists_classTest_ge, common_jet_twisted_read, projected_test_pair). NativeWheelFitProjector.lean proves the common zero character, actual coefficient A, archimedean signed witness Q=r A^2/F (F=multiFactorial alpha), and exact local paired projector price h Q. Do not duplicate these lemmas with abstract interfaces.

There is a sharper conclusion than the existing maximum estimate. For the actual native dyadic inertia, every *nonzero* channel readAt(p,chi) has precisely |A|_p at the selected place, independently of the embedding and the character:
- At unramified primes the inertia is trivial.
- At 2 and q the chart reading is constant, so only the trivial character gives a nonzero channel. The same conclusion holds outside the cutoff.
- At d (odd), the chart is (1,d^k), the normalized character values are (1 +/- d^k)/2; for k>0 both are units, and for k=0 only the plus choice is nonzero. The factors from other primes are unchanged.
These are the actual case splits of dyadic_all_channels, not an assumption about general Fourier transforms.

It follows that every nonzero paired tested entry in any fixed nominal row has norm |h Q|_p, also when the second test is measured at the conjugate embedding. This is stronger than existence of an attaining pair. The statement holds for each character power and each profile for which the entries are nonzero. For a fixed pair of profiles, nonzero ratios of their tested entries thus have norm |R|_p, with R=(h_1 Q_1)/(h_2 Q_2) a fixed nonzero rational. It does not follow that the actual upstream lift ratio has this norm.

## 2. Exact height for these ratios, including arbitrary auxiliary witnesses

Use the literal upstream definition of HeightLe: a fixed H != 0, archimedean allowance alpha for all conjugates of H, finite allowances e_l for H*y_iota, and eventual sum alpha+sum e_l <= C.

If |iota(y_iota)|=|R|_l for every iota, R a fixed nonzero rational, then the optimal bound is exactly -log|R|. For the upper bound choose H=R^(-1), alpha=-log|R|, e_l=0. Conversely any height witness (H,alpha,e) for y also gives a witness (HR,alpha+log|R|,e) for the constant family 1, since the finite norms agree at every embedding. Apply HeightLe.nonneg, the upstream product-formula lemma. This proves the lower bound even for an arbitrary algebraic auxiliary H; no restriction to rational witnesses.

Therefore the inverse and forward tested-entry ratios both admit exact height computations and the sum of their optimal bounds is zero. In the orientation y=Q_flat/Q_nonflat (class multiplier one), the exact inverse height is log Q_nonflat-log Q_flat. The existing nominal_signed_witness bounds log Q_nonflat by -log F+log r+full nominal ASK. This supplies a concrete tested-entry height, not a claim about the missing independently measured lift ratio. If a genuinely fitted lift has this inverse ratio, its relative norm and forward comparison must still be supplied separately, as in Separation and LongForms. Merely changing the inertia character cannot improve the bound. A nontrivial twist on a larger class space must change the relative lift data, not just the character name.

## 3. Independent optimal integral pairing on the retained physical row lattice

The diagonal measured row form in NativeWheelFitProjector.lean has entries Q_i=r_i A_i^2/F_i, and the line tests have entries h_i Q_i. Work at a prime p with L=Z_p^D in the actual distinct translated monomial coordinates. Let B be this rational diagonal bilinear form (class factors included if they occur in the comparison). Allow a common scalar clearing p^c, c>=0. Put
    t_i=max(0,-v_p(B_ii)-c), T=sum_i t_i.
Take arbitrary integral sublattices W,V of L of ranks r,s. Write W0,V0 for their saturations and delta_W=length(W0/W), delta_V=length(V0/V). Suppose p^c B(W,V) is integral. Let S_k be the sum of the k largest t_i (S_0=0). Then
    delta_W+delta_V >= max(0, T-S_(D-r)-S_(D-s)).
This is a theorem on the actual diagonal tested pairing; it allows arbitrary integral linear combinations of the native rows, not just a selected list of them.

Proof. Let L0={x in L : p^c B(x,L) subset Z_p}. The finite module G=L/L0 is the direct sum of Z/p^t_i Z. The pairing induced by p^c B modulo Z_p on G is perfect: a unit diagonal coefficient gives a nondegenerate pairing at each pole. The image of W0 has cardinal at least p^(T-S_(D-r)). Indeed the quotient by that image is generated by D-r elements since W0 is a direct summand of L. A quotient of G generated by k elements has length at most S_k: at each layer p^(j-1)G/p^jG its dimension is bounded by both k and the number of t_i >= j; summing proves the claim. Passing to W loses at most delta_W in length. Similarly for V. The two images are orthogonal. For a perfect finite pairing their orders multiply to at most |G|=p^T. Taking base-p logarithms proves the inequality. All steps are independent of any zeta estimate.

### Uniform pole case: sharp bound and actual construction

When t_i=t for all i, the sharp joint price is
    delta_W+delta_V >= t max(0,r+s-D).
It is attained in the native coordinate lattice: W is spanned by the first r measured coordinates; V is spanned by the last s, multiplying precisely the overlap coordinates by p^t. Off-overlap pairings are zero and on-overlap pairings are units. The saturated ranks are exactly r,s, the index sum is t times the overlap count, and the tests really are integral for the given diagonal pairing. This is a local paired-lattice construction, not permission to use different row spaces in an upstream theorem requiring the same rows.

For a single common retained lattice W=V of rank r, the necessary inequality is
    2 delta_W >= t max(0,2r-D).
In particular if r>D/2 and W is primitive, no positive common pole may remain. With a common scalar clearing c and an unscaled uniform pole f this reads
    c + 2 delta_W/(2r-D) >= f.
If the comparison uses separate left and right scalar denominators d_L,d_R, take c=v_p(d_L)+v_p(d_R). For full rank and no further index cost this recovers the exact two-denominator bound. For identical full-rank clearing d it gives v_p(d)>=ceil(f/2).

For nonuniform poles the general bound above gives a simultaneous, computable lower price without choosing a specific basis; for full rank the minimum joint index is T, attained by multiplying one side by p^t_i on each coordinate. For distinct p these coordinate clearings can be multiplied prime by prime, with the logarithmic index sum exact (and fixed coordinate supports); for arbitrary place-dependent subspaces, only the local lower bounds are claimed here.

## 4. Apply to the existing translated thick mask, not a fabricated profile

For all translations of a fixed nominal thick mask, F_i=F is common: translation permutes the site orders. At any odd split prime outside the wheel's admitted factors (or any odd prime outside the cutoff), A_i are p-units by split_prime_clearing / outside_wheel_price. The dyadic metrics r_i are units. With class multipliers that are p-units, every diagonal entry has the same pole f=v_p(F), by the exact projector price. Thus the uniform theorem applies to every pair of integral retained test lattices on this family. More general class factors are covered by the nonuniform bound and cannot be ignored.

The retention fraction in upstream Theorem B is 1-4/b^2. For r,s at least that fraction of D, the joint index satisfies
    delta_W+delta_V >= (f-c)_+ (1-8/b^2) D
whenever b^2>8. A small rank deficit cannot remove the factorial pole even via correlated changes of basis. Sum over the relevant finite primes to get an explicit log-index lower bound, retaining the common clearing cost separately. This is not the asserted asymptotic budget; it is a necessary price to compare against that budget on the same section. For the x=65 nominal diagnostic already in the ledger (orders 100000,50000,50000,50000, cutoff 130), f at 131 is 1917. For a single rank-one pairing the combined left/right clearing is at least 1917 and identical denominators require 959. If one uses multiple translated copies with the same order multiset, this restriction persists at near-full retained rank.

## 5. What this does and does not transport

The depth, class-sum, tested pairing, exact reciprocal height on those entries, and the cheapest paired integral recovery on the uniform-pole model are now explicitly evaluated. The price is not controlled at the required scale by any of these elementary steps alone. In Alpöge the flat/nonflat algebraic norms, the test-form orthogonality and DenominatorLe.rank_one_bound apply to *the same actual lift line*, not merely to its coefficient entry. We have not identified the tested-entry ratio with that relative lift norm or established the signed short-form comparison after paying the index. Do not promote a ratio defined from Q into the lift norm, or add a new conditional closure interface. The full primitive physical lattice and the nominal Fock lattice still need their common tested map with paid determinant, rank and metric change. The original complete-window bound remains open.

Exact finite regression: node scripts/research/check_native_paired_index.js verifies 44,604 optimal coordinate constructions, 71 orthogonal-complement cardinalities and 406 orthogonal cyclic subgroup pairs in small finite modules, 325 nonzero binary inertia channels, and the nominal pole 1917 / symmetric clearing 959. These are regression checks, not a substitute for the paper proof or Lean kernel verification.

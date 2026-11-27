# V9 — height-free joint numerical comparison and native controlled overlap

2026-11-25. Research priority on #1213, superseding the requirement to reconstruct a geometric divisor height in V8. Keep #1201 as final integration. No claim that the original RH theorem has been replayed without every disputed object: [upstream #466](https://github.com/leanprover-community/riemann-hypothesis/pull/466) removed GeoP/anyGeometry/GeoCl and rebuilt its affected cone, not the deeper degenerate datum or height. [Independent geometry-field excision](https://github.com/mrnathanhumphrey-droid/levent-rh-proof-anygeometry-excision-test) reports Main builds using cached upstream modules. Our change of approach follows from the actual frame theorem, not an unverified full excision claim. Preserve every substantive norm, integral pairing, rank, valuation and signed-loss obligation. Paper-level results below; not Lean-checked or a new RH-strength estimate.

## 1. Eliminate the geometric height, not its numerical inequalities

Use the pinned existing [StatementFrameF](https://github.com/OVVO-Financial/RH_Lean/blob/efb7debf682b3cee46187f157c86e004668a39e9/RHLean/Geometry/AlpogeAllPlace/Formalism/HarderNarasimhan/StatementFrameF.lean), [TheoremFSharp](https://github.com/OVVO-Financial/RH_Lean/blob/efb7debf682b3cee46187f157c86e004668a39e9/RHLean/Geometry/AlpogeAllPlace/Formalism/HarderNarasimhan/HarderNarasimhanProofs/TheoremFSharp.lean), [MeanBoundSecondForm](https://github.com/OVVO-Financial/RH_Lean/blob/efb7debf682b3cee46187f157c86e004668a39e9/RHLean/Geometry/AlpogeSignedSlope/Formalism/RankGapBounds/MeanBoundSecondForm.lean) and [LevelOfCongruence](https://github.com/OVVO-Financial/RH_Lean/blob/efb7debf682b3cee46187f157c86e004668a39e9/RHLean/Geometry/AlpogeSignedSlope/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean). In TheoremFSharp the real function h_i need only upper-bound htMap(B_i) for nonzero actual integral maps B_i. It is not required to be a divisor height.

For a fixed u0 suppress the index u0 and use i for its actual words. Set A=sumA >= 0, S=SDiv=m sum_t(ph(a_t)-a_t logOm), E=EDiv, F=Fo, c=muCC. Define the numerical cap

    hcap_i = S + E + F - c - A log T_i.

The one joint inequality to prove is

    c + htMap(B_i) - F + A log T_i <= S+E    (B_i != 0).

Also prove actual map lattice containment and all actual frame bounds. This joint inequality implies htMap(B_i)<=hcap_i. Apply the real upper-bound input of TheoremFSharp with hcap. The DIV scalar inequality is then equality by the definition of the cap, **not a proof of the joint inequality**. HComp's left side (variation of h_i + A log T_i) is exactly zero for this cap. This removes a separate height-construction and height-variation obligation. Do not set the *actual* pairing norm equal to hcap. Do not transfer an abstract SlopeIneq premise after changing h; instead apply the actual frame theorem with the new norm bound, real metrics, dimension ties, and measured frame parameters. HH (lower target slope cutoff) still needs an independent bound. If an old valid h existed, h<=hcap and s_cap<=s_old; that is a check, not an assumption in the new construction.

With d_i the actual source ranks and wmean their normalized weighted mean, define Z_i=muN_i+A log T_i and Zmax_i=muMaxN_i+A log T_i. Then

    s_cap = wmean(Z) - (S+E+F-c)
    u_cap = max_i Zmax_i - wmean(Z)
    s_cap - c = wmean(Z) - S-E-F.

Thus no geometric height occurs in the residual comparison. The upper cap is on the SAME integral map used for slope transport. Field membership, nonzero pairing, local valuation, row/column lattice and metric ties, exceptional costs are indispensable.

## 2. New log-free quantitative frame bound (paper proof)

TheoremFSharp's proof introduces Nt(t) as the source high-slope filtration at threshold s-t+h_i and St(t) as the corresponding target filtration at s-t. Using integral B_i and htMap(B_i)<=h_i, it proves sum_i B_i Nt(t) <= St(t). The existing thmF_place applies to ANY Nt family, with the loss parameter equal to its actual relative codimension. Use it that way instead of first replacing that codimension by u/(u+t).

Let x_{ij} be the actual source slope list minus h_i (using the original 2*slopeList+slopeNormalisingConstant convention and all field-degree multiplicities), y_j the actual target slope list in the same convention, and s a lower bound on the source mean. Denote normalized uniform means over those lists by E_src and E_tgt; ranks are the actual multiplicities, so E_src(x)=wmean(muN-h). Assume y_j>=s-H with H>=0. Let

    alpha(t) = fraction of source slopes x < s-t
    beta(t)  = fraction of target slopes y < s-t
    kappa    = eta + 4 sqrt(e).

By the actual hMle, hplace, hcnt argument in TheoremFSharp, with alpha(t) in place of u/(u+t),

    beta(t) <= (4 alpha(t)+kappa)/(1-delta), 0<=t<=H.

This uses exactly the original frame overlap, near-isometry and ambient codimension assumptions. Integrate these finite step functions, or partition into finitely many intervals with endpoints s-x and s-y. Then

    s - E_tgt(y) <= E_tgt((s-y)_+)
        = integral_0^H beta(t) dt
        <= [4 E_src(min(H,(s-x)_+)) + kappa H]/(1-delta).

If E_src(x)>=s and x<=s+u, u>=0, then E_src((s-x)_+)<=E_src((x-s)_+)<=u. Consequently the original frame error
    [4 u log(1+H/u) + kappa H]/(1-delta)
can be replaced by the smaller of its old bound and
    [4 E_src(min(H,(s-x)_+)) + kappa H]/(1-delta)
and in particular by [4u+kappa H]/(1-delta). At u=0 use zero for the corresponding term; all source slopes are >=s in the mean-bound case. The exact truncated source downside is no worse than the old integral of u/(u+t), because the original pointwise rank-share bound remains valid. The existing sharp theorem has no log(number of words) loss; do not count removal of that loss as new. This new refinement eliminates the log(H/u) penalty in the source-deficit term, and retains the full overlap/minimum-slope debt. No asymptotic exponent improvement follows solely from removing a logarithm.

### Direct height-free Ga estimate

With hcap use the preceding bound, defining Fframe=[4 E_src(min(H,(s_cap-x)_+))+kappa H]/(1-delta). From s_cap-c<=Fframe follows

    wmean(muN + A log T) <= S+E+F+Fframe.

Use the existing lower QuotientSlopeBoundsWith:
    muN_i >= muM_i+Ga+F-Ee_i-Lo5_i.

Then without any divisor height:
    Ga <= S+E+wmean(Ee-muM+Lo5-A log T)+Fframe.

By Count5, EComp5, Slopes and the exact key_identity5, this yields
    Ga-MAIN <= E
      + A C.cCount (La+m^2 La/k)
      + m C.cE B0
      + C.cSlope nT a La (1+m/k)
      + wmean(Lo5)
      + Fframe.
Mean ASK-Ga and IO losses are still paid by the existing Losses/strong error-window path. No new terminal assumption. For the maximum spread u_cap an even more direct bound follows by comparing every Zmax_i to every Z_j: use osc(A log T - Ee) rather than a sum of separate variations. In the original constants,
    u_cap <= C.cSlope nT a La (2+m/k)
          + 2 C.cE m B0 + C.cSl1 m B0
          + A C.cCount log k + wmean(Lo5).
There is no C.cH height-variation contribution. The original sign, MAIN, normalizer and all remaining errors stay intact. This is an explicit finite conditional improvement of the proof consumer, not discharge of the joint numerical inequality.

## 3. What a joint norm-covolume comparison actually measures

For real full-rank square lattice maps, let E,F be bases of source L and target M of rank r, let C=F A E^(-1) be the actual map, and let A be its nonzero-determinant integral matrix. Use the squared-norm slope convention mu(L)=-log det(E^* E)/r and analogously mu(M). A direct determinant calculation gives

    mu(M)+log ||C||_op^2-mu(L)
      = (2/r) log |det A| + log( ||C||_op^2 / |det C|^(2/r) ).

The first term is the actual finite index, the second is nonnegative spectral anisotropy. Uniform scaling of the target metric cancels exactly on the left and in the singular-value ratio. This is a genuine joint comparison of the SAME map, not an independently manufactured height. For a number field use the actual placewise metrics and ideal index/product formula; for rectangular maps use a justified full-rank selected frame and retain its rank losses. The displayed equality is for the real square case, not a replacement for those general proofs. Hadamard alone bounds the determinant from above and gives a LOWER bound for the joint cost; it cannot prove the required upper bound. A legitimate upper bound needs a controlled actual index and anisotropy.

## 4. New native multiplicative frame: root-scale Gram defect

Let N>=1 and V be the physical squarefree carrier S_N={n<=N: mu(n)^2=1}, n positive, D=|S_N|. For integer z>=2, a number is z-rough if all its prime factors exceed z (1 included). Define the ACTUAL truncated divisor map on the integral coordinate lattice Z^S_N by

    Z[a,b] = 1_{a|b, b/a z-rough}.

The order by n makes Z upper triangular with diagonal 1. Its inverse on this divisor-closed carrier has entries mu(b/a) times the same incidence. With the natural squared norm sum_n n |x_n|^2, write B=diag(sqrt n) Z diag(1/sqrt n), so B[a,b]=sqrt(a/b) Z[a,b]. Both maps are integral in the original lattice basis; the weighted real matrix is a metric realization, not an integer matrix.

**Joint norm/volume supplier.** det Z=1, so the exact relative index and normalized covolume change vanish. Schur's test with positive weights n^(-1/2) gives
    ||B||^2, ||B^(-1)||^2 <= H_N * max_{n<=N} 2^{omega_{>z}(n)}
                           <= H_N * N^{log 2/log(z+1)}.
Rows give sum_{d<=N/a,z-rough} 1/d <= H_N; columns give the rough divisor count. In particular for z tending to infinity the bound is subpower (and log norm O(log log N+log N/log z)). This is a controlled native coordinate change, not an earned prime gain.

**Exact shared Gram kernel.** Let K=B^*B and A_z(g)=product_{p|g,p>z}(1+1/p). For b,c in S_N, g=gcd(b,c), u=b/g,v=c/g:

    K[b,c] = A_z(g)/sqrt(uv)   if u,v both z-rough,
             0               otherwise.

Indeed the eligible common divisors are precisely a=g/d with d a z-rough divisor of g, and sum a/sqrt(bc) gives the formula. This holds at the actual physical cutoff: there is no extension to a complete Euler cube. In particular K[b,b]=A_z(b).

**Quantitative overlap theorem.** Uniformly in N,z>=2,
    ||K-I||_HS^2 = O(N/(z log z)).
Proof: for Y>=1,
    sum_{g<=Y} A_z(g)^2 <= Y product_{p>z}(1+2/p^2+1/p^3)
                        <= Y exp(3/z).
Use the squarefree divisor expansion and count multiples by floor(Y/d)<=Y/d; this requires no sign or independence assumption. The diagonal defect sum (A_z(g)-1)^2 is bounded by sum(A_z(g)^2-1), hence O(Y/(z log z)) using Chebyshev's prime-count bound and a dyadic prime tail. For off-diagonal pairs, symmetry permits u>=v and u>z. Sum over g<=N/u (drop coprimality and squarefreeness for an upper bound). The result is bounded by
    2 N exp(3/z) sum_{u>1,z-rough} (1+log(u/z))/u^2.
Here v=1 or z<v<=u, so sum 1/v<=1+log(u/z). Factor each u>1 by its least prime p>z, drop all remaining restrictions on w=u/p, and sum (1+log(p/z)+log w)/(p^2 w^2). Since sum 1/w^2 and sum log(w)/w^2 converge and Chebyshev gives sum_{p>z}(1+log(p/z))/p^2=O(1/(z log z)), the result follows. An elementary weaker explicit bound (not even using prime distribution) is <=35 N/z: use exp(3/z)<=5, exp(3/z)-1<=15/z, and the integral of (1+log(t/z))/t^2 from z to infinity equal to 2/z. All constants uniform.

D asymptotic to (6/pi^2)N (existing squarefree density; even D>=N/4 suffices). For a single frame with gamma=1 put e=||K-I||^2/D and Q=B B^*. Since tr K>=D,
    eta = D tr(Q^2)/(tr Q)^2 -1
        = [D ||K-I||^2 - (tr K-D)^2]/(tr K)^2
        <= e = O(1/(z log z)).
This is a proved frame defect estimate, not an empirical fit or a sum of unrelated coordinate norms. At N=R^2-1,z=R the total squared Gram defect is O(R/log R), at the desired root scale. These are the e,eta quantities for THIS single multiplicative decoder, not yet the e,eta for Alpoge's period maps or an arbitrary concatenated family. The map includes the identity and mixes parities; it is NOT the approximate sign-reversing involution of V7 or a proof that U~L with root-scale error.

## 5. Even cheaper common historical rank payment at the square cutoff

N=R^2-1, z=R. Every b<=N has at most one prime >R. Write Z=I+S, S=sum_{p>R} S_p, with S_p e_{ap}=e_a on actual squarefree sites (zero otherwise). Then S_p S_q=0 for all p,q>R. All ranges lie in the common HISTORICAL subspace W=span{e_a:a<R}. This is true simultaneously for arbitrarily many subsets of the high primes, not one independent rank charge per prime. Weighted real realizations preserve W.

The weighted matrix S has pairwise disjoint row supports, since each high child has a unique prime >R. Put t_a=sum_{R<p<=N/a}1/p for squarefree a<R. The nonzero squared singular values of S are t_a. Set L1=sum t_a, L2=sum t_a^2. In this notation S denotes its weighted real matrix in the next formulas:
    rank S=#{a:t_a>0} <= dim W <= R-1
    tr K = D+L1
    ||K-I||^2 = 2L1+L2
    tr K^2 = D+4L1+L2
    log ||B||^2=log||B^(-1)||^2=2 asinh(sqrt(max t_a)/2).
These follow by orthogonal decomposition into the two-dimensional shears [1,sqrt(t_a);0,1] and identity directions. Chebyshev (or PNT) bounds max t_a<=sum_{R<p<=N}1/p=O(1). Thus high-prime coordinate changes have uniformly bounded operator norm and inverse, determinant one, and O(R/log R) total Gram defect.

**Common-output rank perturbation lemma.** For any actual maps A_i into V and source subspaces L_i, let B_i=(I+S_{P_i}) A_i, with any chosen subsets P_i of the high primes. The image of B_i-A_i is in W. The images of sum_i B_i L_i and sum_i A_i L_i in V/W are equal; hence
    |dim sum_i B_i L_i - dim sum_i A_i L_i| <= dim W.
This pays the shared high-prime deletion rank at most ONCE across every chart, irrespective of how many primes or charts are used. It holds for each threshold filtration L_i(t); in a normalized layer-cake comparison over [0,H], extra rank deficit costs at most H dim(W)/D. Actual map operator log-norm increases at most a uniform constant. Integral lattice containment is preserved if the actual target lattice is stable under these integer coordinate changes, and source/output coordinates are genuinely tied. The rank lemma does not require that lattice stability; using it in the arithmetic proof does. Arbitrary chart conjugations with different output W, adjoint insertions, or unrelated period lattices need separate proofs. This sharp shared rank payment avoids the generic sqrt(e) loss for this particular perturbation when a baseline threshold recovery bound has actually been earned.

## 6. Reproduced experiments and scope

Run scripts/native_height_free_frame.py (Python standard library). On R=4,8,12,16 with several z, 67,832 off-diagonal Gram identities checked exactly via rational intersections of actual divisor-column sets; trace relations, explicit bound and high-cutoff shear identity checked with Fraction. 6,125 exhaustive small slope-array checks verify the finite distributional layer-cake arithmetic (not constructed lattice witnesses). Larger roots use actual prime sieve and squarefree census and exact rank/edge counts; reciprocal sums, eta and log norms use double arithmetic, not certified enclosures.

| R | squarefree D | rank S | squared Gram defect | defect/R | e |
|---:|---:|---:|---:|---:|---:|
|64|2491|38|18.250|0.28515|0.00732629|
|317|61094|186|63.520|0.20038|0.00103971|
|1027|641207|624|177.329|0.17267|0.00027655|
|2048|2549834|1242|322.128|0.15729|0.00012633|
|4096|10199301|2490|588.844|0.14376|0.00005773|
|8192|40797327|4973|1095.260|0.13370|0.00002685|

At 8192, 30,024,427 physical high-prime incidences; log squared operator norm 0.809687. The defect*log R/R ratio is approximately 1.15–1.21 over tested roots. No fitted asymptotic constant is claimed. Uniform bound is the paper proof above. The **remaining bottleneck** is not making the native high-prime decoder cheap. It is independently earning the actual finite-place gain/physical period valuation and joint centered norm+index cap on the SAME maps, with actual slope tails and complete window parameters. The unitriangular decoder has zero log index; assigning it the original Ga or reading U-L from the Gram estimate would be false. Retain V7 signed density and V8 formal logarithm as parallel possible suppliers, not equivalent endpoint claims.

## 7. Revised seven-role priority for #1213

Use this directive before V8/V7 and older research selection on this branch. Do not reconstruct discarded geometric height/positivity fields just to satisfy an interface. Do not delete actual arithmetic constraints or replace real pairing norm by cap. Keep #1201 as final integration, no automatic main merge or runtime change.

- COORDINATOR: replace separate geometric-height task with direct same-map joint numerical cap and log-free frame consumer. Require actual source/metric/rank ties and a measured H. Distinguish conditional consumer improvement from quantitative source proof.
- OWNER: trace adm2/val2, actual source and dual integral pairing, signed ASK/Ga loss to the native physical map; independently earn nontrivial index or valuation, never infer it from unimodular inverse. Reuse shared historical rank only on compatible actual output coordinates.
- WHEEL: formalize the exact rough-divisor Gram kernel and common high-prime range; attack low-prime/complete-face baseline and clipped-face compensation. Do not pay high corrections separately across charts.
- ANALYTIC: prove joint cap, including original real main and period cancellation, on actual recovered rank; use distributional source deficit instead of logarithmic envelope; bound H, actual error and normalized physical excess on complete windows. Preserve fixed signs and full prime powers.
- CENSUS: reproduce script and extend tests to actual pairing/gain candidates with explicit metrics. Distinguish raw Gram defect, normalized e, sqrt(e) consumer tax and direct rank transfer. Audit low-prime coordinates and proposed non-unimodular maps with real Smith indices and spectral costs.
- REFEREE: verify upper vs lower norm/index comparisons, cap vs measured norm, actual carrier, no parity claim for Z, no reused W after unrelated chart changes, complete slope-list multiplicities, independent gain and uniform cost; do not infer RH from cheap coordinates.
- LEAN: first formalize finite distributional refinement of theoremFSharp_of (replace u/(u+t) by actual codimension; use finite layer-cake identity) and height-cap consumer; reuse existing lattice/Gram/index code. Formalize native rough-divisor/Schur/Gram/common-range bounds. No new assumed proof endpoint. Only integrate once actually compiled and semantic audit passes.

This is a research update. Local Python diagnostics ran successfully; no lean/lake in the execution environment and no new Lean declaration. No new universal signed bound, no claim of total upstream geometry excision. No modifications to #1201, main, or live agent runtime.

# November 19, 2026 | Prime Census Laboratory | The two-clock test

## A. Result

Exactly three of the ten registered cutoffs, **78, 96 and 114**, have an inner zero; those same three and no others have a zero in the narrow outer window. All ten have a zero in the wider power window. At **every** cutoff the actual signed repair statistic has the opposite sign to the outer-only statistic. There is also an exact reason to keep the square-root cutoff: the derivative has a second, disjoint family of jumps at squares. A test based on ranges of local Mobius partial sums certifies two of the three crossings without evaluating the far endpoint; it is inconclusive at the third even with 128 blocks.

`20261119-census-1900-EST/CLOCK-FINAL`. Same actual run as CLOCK-CHECK: November 19 19:00:01 EST, November 20 00:00:01Z, America/New_York; RUN_ID_UNAVAILABLE. CLOCK1,3,4 are FINITE_COMPUTATION. CLOCK2 is PAPER_PROOF / SELF_AUDIT, independent referee review pending, not Lean. No new global exponent; RH remains open.

## B. Governing objective and sources

Main at intake and recheck: `2f0bb1f28d0ac386918ad7d1aaf683e2ccfd62de`; AGENTS `500b6daed5e867d19d97c30e43a7a1e7d2055a51`; contract `95566e37c8eaeb99ee680660df4f9d2e06ea5038`. Canonical `VFCanonicalSquareVonKochStatement`: one C>=0 before all natural R>=2, |pi(R^2)-vfMidFinishedMass(R)-sqrt(2)|<=C R log R. The formal RH consumer also takes ClassicalVonKochRHCriterion. Canonical source `79030d70e8d3e0d08eef9bac53fef95c36eca2fb`; Nyman flat return `2d23721027ecc44e85b7add02fc632b482f03352`, high coefficient invariant `2da630c1d5fb9302e2097ec1e170cf41c2b40609`, ridge geometry `9cfc801b5154245e8925f4247a0390470761f327`, profiles `1ce4bde64139395e79b9ceb2fd2a396457d7098a`.

The repository's compiled #1119 comparator is `native_mertens_near_uniform_window_error_closed`, source `f629db1b2b65d6ec042ac9432397d4b6316200c6`, head `77ee815846d6d534c866f0752aa33b84c385610a`, hosted run/job `42552018910/128949473700`. It gives b*=7/8-7/(64 Npack) with EVERY positive loss, not the zero-loss bound. Npack<=Nstar improves #1108; retain fixed packing, the positive-error LOW/HIGH/principal estimates and the ideal-to-native return. With #949 let Theta be the rightmost zero supremum; fix Theta<b<1 before scale. #1151 human-merged November 19 21:19:58Z: exact-tree raw head `5fdbbe89dc595a5b14b647e8cf3f9faaf00cfa00`, hosted `44590158125/135793679265`, seven finite declarations, terminal axioms propext, Classical.choice, Quot.sound. Job logs inspected. #1149's period mean (bias included), #1150's fixed-head phases and #1151's finite moments/profiles are not physical tail bounds. No open/draft PR on recheck; no new Lean, CI or PR.

## C-D. Competing hypotheses and registered carrier

JET asks if infinitely many inner-selected heads share a power window with an outer zero. A broad window could instead capture roots regardless of selection; the unselected controls discriminate. A lower clock might be negligible in the derivative, or create a distinct arithmetic jump. Signs and paired roots were not selected on the result. Freeze H=66,72,...,120; N=H^2=6K, L=log H. Inner [H-3,H+3], narrow [(H-3)^2,(H+3)^2], power |x-N|<=N^(7/8), all closed. G means an inner hit. Nearest roots to H and N, lower in a tie; no ties. No first-bad predicate is assumed.

For x>=1 let M(x)=sum_{k<=x} mu(k), m(x)=sum mu(k)/k and Phi(x)=sum mu(k)log(x/k), with the same cutoff. Delta(x)=1-sum mu(k)log(x/k)/k; tau(x)=2 gamma-2 log x+sum mu(k)log(x/k)^2/k equals the full 2 integral_x^infinity Delta(u)du/u, not a truncated tail. v(x)=log x+Phi(x)-Phi(sqrt x). On I1=(3K,4K], I2=(5K,6K], put s_i=sum 1/k, l_i=sum log(N/k)/k, q=s1-s2, A_N=(l1-l2)/q, B_N=(s1*l2-s2*l1)/q. With p=log(N/max(H,k)), U=sum mu(k)p/k=Delta(H)-Delta(N); v(N)=2L+sum mu(k)p. Both sums include k=1. The actual band weights are a=(U-s2*v(N)/K)/q and z=v(N)/K-a; h_k takes these weights on the respective bands, zero elsewhere, including all squareful band sites in their assigned band.

W(x)=tau(x)+A Delta(x)-6B v(x)/x. Here s=log(4/3), t=log(6/5), u=(log(2)^2-log(3/2)^2)/2, q0=t^2/2, A=(u-q0)/(s-t), B=(s*q0-t*u)/(s-t). The original S_H=tau(N)-sum h_k log(N/k)/k equals T_H-A_N Delta(H), where T_H=tau(N)+A_N Delta(N)-6B_N v(N)/N. T_H here is JET's outer scalar, not the earlier physical-window cross term.

## E-F. CLOCK1: exhaustive real windows and counterexamples

Each root lies strictly between the displayed number and that number plus 10^-8. Inner: y1=79.49088938, y2=96.79825015, y3=116.22379240. Outer: z0=3805.37196022, z1=6386.74228557, z2=9293.33708076, z3=13049.52569816. Each is unique in its unit cell. In the table root labels are used without z; `-` is proved empty. For each of S,T, integer p denotes [p,p+1] times 10^-9.

|H|inner|narrow|power|nearest outer|S|T|
|---:|:---:|:---:|:---:|:---:|---:|---:|
|66|-|-|0|0|1308167|-32327|
|72|-|-|0,1|1|1798478|-17300|
|78|y1|1|1|1|422812|-2694|
|84|-|-|1,2|1|-1654466|15396|
|90|-|-|1,2|2|-2002014|27040|
|96|y2|2|1,2|2|-457053|3476|
|102|-|-|2,3|2|2054327|-30473|
|108|-|-|2,3|3|2086541|-17087|
|114|y3|3|2,3|3|772826|-606|
|120|-|-|3|3|-816028|9832|

H=66 is the first registered false positive for using the power hit to predict G. All three selected nearest outer roots are to the right of N. The greatest |S| here is at 108, the smallest |T| at 114. The two narrow selectors coincide in this block ONLY: PHASELOCK4's genuine H=12 already refutes even universal power alignment. No finite miss refutes infinitely many alignments.

## G-I. CLOCK2: square jumps, signed curvature, and a testable supplier

Let D=x d/dx, j=1+M(x)-M(sqrt x)/2, c=-(A+6B) in (0.02633965908,0.02633965910). On each open unit cell, D Delta=-m, D tau=-2 Delta, Dv=j. Thus DW=-2 Delta-A m-6B(j-v)/x and D^2W=F=2m+6B(2j-v)/x there. Since W,Delta,v are continuous, for every integer n>=2 the right-minus-left jump is

    n^2 [W']_n = n [DW]_n = c mu(n) + 3B 1_(n=k^2) mu(k).

Indeed m jumps by mu(n)/n, j by mu(n)-1_(n=k^2)mu(k)/2. The nonzero terms have disjoint supports. The smallest squareful counterexample to 'mu(n)=0 implies no kink' is n=4: 16[W']_4=-3B>0. Normalized square-jump magnitude / ordinary magnitude is in [25.97690074,25.97690075]. Two-sided differentiation through all n=2..18751 returned 11403 ordinary jumps, 82 square jumps, 7265 zero. A large individual jump does not rank its integrated contribution.

For X>=2, 0<h<=1/2 let K_h(u)=(h-|u|)_+. The symmetric second difference W(Xe^h)-2W(X)+W(Xe^-h) is exactly

    c sum_n mu(n)/n K_h(log(n/X)) + 3B sum_k mu(k)/k^2 K_h(log(k^2/X))
     + integral_{-h}^h K_h(u) F(Xe^u) du.

Proof: integrate by parts on every log cell. Its ordinary second derivative gives F and its first-derivative jumps give the two atoms. The endpoints have zero weight; a jump at the center has full weight. For fixed Theta<b<1, m=O_b(X^(b-1)), j,v=O_b(X^b). The integral costs O_b(h^2 X^(b-1)); the absolute square sum costs O(h^2/sqrt X+h/X) by counting O(h sqrt X+1) squares. For h asymptotic to X^(-1/8) both are O_b(X^(b-5/4)). This approximates curvature, NOT W(X), slope, or an endpoint bound.

One-sided certificate: set X=N, d=floor(N^(7/8)), Y=N+d, h=log(Y/N), w(t)=log(Y/t)/t. Taylor integration on the right gives W(Y)=P+c sum_{N<n<=Y}mu(n)w(n). Here P=W(N)+h DW(N+), plus the square atoms 3B sum_{N<k^2<=Y}mu(k)w(k^2) and integral_0^h(h-u)F(Ne^u)du. The center atom is already in the RIGHT slope. For any integer partition a_0=N<...<a_J=Y, enclose W(Y) in P plus

    c sum_i (w(a_i)-w(a_(i+1))) [min,max]_{a_i<=t<a_(i+1)} (M(t)-M(N)).

Proof: partial summation against -w'(t)=(1+log(Y/t))/t^2>0; no endpoint remainder. This tests a signed arithmetic range without substituting the actual far-end W value. For the finite test take a_i=N+floor(id/J), J=1,2,4,...,128. Bound the smooth integral independently on each unit cell by its density interval times the exact triangular mass. The *first* dyadic J giving the opposite sign to W(N) was 1 at H=78 (endpoint enclosure [63,6472] times 10^-8), 16 at H=96 ([-1552,-196]); at H=114 even 128 gives [-67,268], INCONCLUSIVE. Direct W(Y) is respectively [2721,2722], [-916,-915], [97,98] times 10^-8. In that order W(N) has signs -, +, -. At 114 the tangent alone is [4061,4062] times 10^-8 but the square term is [-4111,-4110] in the same units. For the symmetric average, at 96 even the sign of 2W(N)+ordinary differs from the full endpoint sum ([-549,-548] versus [421,422] times 10^-8). Both square and smooth returns matter.

Exploratory CONJECTURE (stronger than needed): infinitely many legal H in G admit an opposite-sign right endpoint using the above fixed J=16 arithmetic box; to define the box use the exact P and block extrema. A separated sign from the conservative integral enclosure suffices. Two successes do not establish recurrence; at 114 this certificate fails, not the crossing. This discriminator was designed after the registered census, not held-out validation. It requires an independent result about the initial height, right slope and signed partial-sum ranges jointly. Bounding curvature alone is insufficient even for affine functions.

## J-K. CLOCK3: signed residuals, full returns and verification

PHASELOCK3 test on the nearest pairs. With w_j=rho_j-1 for the two specified simple zeros, a_j=-1/(w_j^2 zeta'(rho_j)), d_j=a_j[A-2/w_j+6B(w_j/rho_j)^2]. e and f are the signed two-pair remainders of Delta(y), W(z), divided respectively by 2|a1|/sqrt(y), 2|d1|/sqrt(z). J is the retained outer cosine sum at y^2 divided by its first amplitude. For e,f,J,J+f,log(z/y^2), list lower integers of width-one intervals times 10^-6; nearest four-target distance in flat torus radians has width 10^-4.

|H|e|f|J|J+f|log(z/y^2)|nearest target; distance|
|---:|---:|---:|---:|---:|---:|:---|
|78|-194632|577434|-480627|96808|10694|183; [0.4338,0.4339]|
|96|147483|1581|-157272|-155691|-8205|55; [0.6846,0.6847]|
|114|234598|-799619|622104|-177514|-34529|183; [1.5166,1.5167]|

In all three |J+f|< (gamma1+|d2/d1| gamma2)|log(z/y^2)|. An outer remainder near zero at 96 does not make the inner remainder near zero. The other discarded spectrum was not assumed small or replaced by a zero-series expansion. Two Euler-Maclaurin cutoffs (128,10),(96,8), Machin pi, Taylor enclosures, quarter-disk Bernoulli bound, Rouche and zeta symmetry as in PHASELOCK4. Both fixed centers pass |zeta|<10^-17 and |zeta'|>0.7; inflate derivatives by 5e-11 on the radius 10^-15 disks. Four target cells independently rebracketed; completeness of those four is the upstream PHASELOCK2 argument. 58- and 66-place grids agree. Float proposes acos endpoints only; interval cosine certifies them.

LENS4 full signed shell check. Set t=log(u/N), g=(t^2+A_N t)/u; g'=[2t-t^2+A_N(1-t)]/u^2. Integrate M g' on [N,2N] and [2N,4N] by exact partial summation. The whole integral from N to infinity is tau(N)+A_N Delta(N), hence subtracting the first two shells gives the actual infinite remainder. Restore -6B_N v(N)/N-A_N Delta(H). Lower integers in units 10^-8 (upper=lower+1), in order first shell, second shell, beyond 4N, restoration, recombined S:

    H=78   -45365   -4382   29877    62149   42281
    H=96   -54125   11679   18830   -22091  -45706
    H=114  -24555    4504   13529    83803   77282

For CLOCK1, the 60 inner unit cells [63,123] give 57 empty and three unique. The outer integer hull [2827,18751] gives 15924 cells: 15810 excluded directly, 110 by same-sign monotonicity, four unique. Bisection to width <10^-13; membership in the irrational power windows decided by integer eighth powers. Independent divisor inversion vs prime sieve; direct log moments vs cell recurrences; independent rational atanh log enclosures and harmonic Euler gamma at 1024 vs correctly rounded Decimal log and gamma at 512. Independent log-cell chord error <=sup|F| h^2/8 excludes all 15920 empty outer cells; secant/curvature certified the four others. Affine log interpolation checked all 60 inner cells independently, and signs at all seven printed brackets agreed. Direct literal repairs returned both coefficient moments (1,3) and matched all ten S,T. Root/repair primary grids 40 and 52. No randomization, sampled-root exclusions or undecided registered windows.

Endpoint capsule: c_k=(h_k-mu(k)p_k)/L, 2<=k<=N; r(m)=1-sum c_k (m mod k)/k; E_H=sum_{m>=1}r(m)^2/[m(m+1)]. The original masks, both band repairs, all mixed profiles, H<m<=N and location-weighted infinity must be paid together. For a genuine zero rho with sigma>1/2 the Mellin lower bound is E_H>=(2sigma-1)(H+1)^(2sigma-1)/|rho|^2. One common unbounded sequence with E_H=O_eps(H^eps) for EVERY eps would exclude all such zeros. JET alignment gives only |S_H|<<_b N^(b-1-1/8)+N^(b/2-1) there. No full E bound or renewal. Euler li-pi requires virtual d>X and compensation; clipped VF #915 needs actual admission, history, restoration and cross terms; NNS requires its Hecke/mask/zero-target returns; native square blocks require strict K_R, LOW and signed HIGH. None is a typed bridge from W. No OAI 47/54 or theta>3/5 gate passed. Preserve all nine routes.

## L. CLOCK4: specialist handoffs

Owner: trial-prime enumeration on every site of the four original HINGE groups, floor U by u^9<=X^5<(u+1)^9, X=B^2, B=16..128. All four maxima of (-I_i O_j)_+/(X log^4 X), in 00,01,10,11 order, reproduce (B,lower units 10^-12)=(21,17144669),(54,13671260),(121,11511645),(51,38142781), upper=lower+1. The 00 sign switches from negative at 16 to positive at 17. No first bad and no independent extension of the HINGE1 range to other products.

Wheel: squarefree smooth output, exactly one unordered split with both factors >=b, one mu per output. Independent balanced-factor multiplication table and largest-prime sieve versus GATE3's two coprime rows plus twice overlap and rough primes. At the left/right ends of P the (S_hi,S_lo) pairs are: B=20 (3,0)/(4,0); 100 (26,-3)/(35,0); 150 (62,2)/(79,7); 250 (174,6)/(212,14); 500 (682,84)/(856,70). Agreement at all ten, including both original anchors. At B=500, b=501, X=418335 the exact upper rows are 621+69-8=682. Positive low mass at both endpoints of the last three cutoffs rules out pointwise nonpositivity there, NOT a negative asymptotic main term. No already-used donor restored; no claim about all of P.

Architect: use the signed block enclosure as a falsifiable sufficient criterion, not a proof of recurring alignment. Analytic: the square term and the right slope cannot be dropped; the three signed phase tests are above. Referee: check the center-atom convention, signed Stieltjes kernel and both signs of the local box; the shell beyond 4N was restored, not discarded. Lean: following independent acceptance only, the finite jump identity is a candidate; neither recurrence nor the full norm is available to formalize.

## M-N. Ranked portfolio, continuity and replay

1. Test the fixed 16-block right-hand criterion without fitting on new data. Register H=126,132,...,180 at the next authorized run before looking at new outer windows; keep all misses, all controls and the difficult 114 fixture. Do not repeat CLOCK1. This is the highest-value next experiment, not a scheduled change.
2. Keep the original infinite-subsequence selector CONJECTURE; weak two-mode proximity and separate oscillation are not suppliers. Retire the broad-window-only selector, the outer-only sign proxy, and no-square-kink shortcut in the scopes refuted here.
3. Keep Owner's three other products and Wheel's possible negative lower-prime main term independent. Clock evidence provides neither. No direction change requested.

Eastern continuity, Nov 19 reports intake `139c5523cbd3fb4dee537cb65acb3bcf26c34e59`; since last consumed `fdc5e465203e4a5b94ccf393c2fd84e0edade6da`: 14 commits, 14 changed paths, no deletion. TODAY available for all seven. Actual local times; newest report blobs:

|Role|Prior to latest on Nov 19|Latest blob|
|---|---|---|
|Coordinator|07:10 RIDGE; 07:36 manual OBS recovered in 15:13 JET; 00/90 identical|6790b8672ac80f6f3a36ca115929cf19f499cfb4|
|Owner|08:09 EXCHANGE to 16:15 HINGE; one finite-range product only|85060bbc0910a64ce70a8c418d9fef35b16c768b|
|Analytic|09:09 BAND to 17:11 PHASELOCK; H=12 universal miss|62efb52db960cff6ff4ca43497d48589c56bc791|
|Wheel|10:12 HALL to 18:06 GATE; latest is verified recovery, not canonical HALL|a20b2ee34f37f8ec7a6d632eb1f7a31521889232|
|Census|03:11 FOLD to 11:00 CROSS; H=12 physical mixed term positive|72ae7640849805c181dca1d03ef5dc32447a6f09|
|Referee|04:13 PRISM to 12:03 LENS; scoped RIDGE/BAND acceptance and CROSS2 check|8eff846f154c048fe39ad44ff77b63e90db510f9|
|Lean|05:10 EXTREMA partial to 13:14 RAMP/PRIME-WITNESS; distinguish paper from CI|0b8150d88136351860938530a24be262c6300ba5|

Nov 18 carry-forward, abbreviated unambiguous blob IDs in the same order: PHASE recovery 2e6bfc31, GP a6345e17, LW 065a94a6, LC 669ba135, ST 780b9325, FC 91b57ce6 (not unpublished BG), VR 2cd32633 (separate MEAN/#1149). Nov 18/19 intake directory trees e2c3482887d7e5f06a5a264d3022e0fe8f43a566 / b90b390767f4444dd1d76c73351d961a9da4ee1d. External index `7d63d434690d00dffce9c90335d41c4f62d85798`: EXT-20261018-PNT-1 retains unit and p=R; EXT-20261014-5 is all-root, not first-bad. Unlimited directory discovery and relevant changed sections checked; exhaustive older bytewise backfill CONTINUITY_UNVERIFIED where displays abbreviated. No absent run inferred.

Replay, Python 3.12.14, Linux x86_64, standard library, no seed or compile flags: `python clock.py`, `CLOCK_DIG=52 python clock.py`, `python independent.py`, `python phases.py` (58 places), `CLOCK_DIG=66 python phases.py`, `python curvature.py`, `python handoffs.py`. Typical measured wall seconds: 2.6, about 6, 2.8, 5.3, 0.4 for the five distinct scripts. SHA-256 in that script order:

    7811f1457339d550ae95ad88f13c10136a20434907ad71ad483772e318103201
    f2279328f67d46362b069e7fedd6c3e34f0503bb93da4dffeaa495aa52661539
    43bd72b6665302ff6917e5acc57ba4dd65502a7ed56a299216400f84679adc50
    e511ccac991c4a689272dec83dbe661e90eec88f010977a0a6c4f9039651fd01
    1ec640107fe5ff740cdc42e1d106c9e0a23087214a9ca66d5e3be9fb1dff9d81

Publication: intended `agent-reports:research/agent_reports/2026-11-19/40-prime-census.md`, unchanged 41702 bytes, blob `72ae7640849805c181dca1d03ef5dc32447a6f09`. Direct Git tunnel 403; authenticated full-file and blob displays abbreviated the old record, so no replacement. Opening recovery exact commit `b6b5640d7bc0780c25648ac4c55da7501a77433b`, blob `41367f280220cac5bb8ead1d093e266a81242f72`, 2534 bytes; this is also the live pre-final publication base. This complete create-only final recovery is the same invocation; exact-commit readback required before claiming publication. EXECUTION_COMPLETED; CANONICAL=NOT_UPDATED.

half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1 (96ad4439ec458af6168f7d9cb3eef5dde291d37c); cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1 (e3ae4280438f591f1ffaddd754a1c3a6d35d0691); continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1 (7eef0b36c7442be922d9bc99c6b35d853c4f1f4f); publish_ack=REPORT_PUBLISH_RECOVERY_V1 (a9583516fd2e603320c771e32c170132bf0c53e9); finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1.

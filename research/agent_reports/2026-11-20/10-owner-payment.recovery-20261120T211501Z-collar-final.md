# Owner Payment | November 20, 2026 | Signed square-endpoint strip

## A. Most important development

The last H complete rows and columns of the original Euler floor matrix admit an exact chronological Mobius-pair identity. At H=floor(sqrt(R)) their total effect is O(R). At H=floor(R^(2/3)), their absolute pair count is of order R^(4/3), but the sum of the absolute values of the **signed exact-gcd group totals** is O_epsilon(R^(199/156+epsilon)). The saving is 3/52 in the exponent. The second statement uses the repository's fixed zero-free input and an external zero-density theorem. It is a paper derivation pending independent review, not a new compiled theorem or a strict historical envelope. The physical interior remains unpaid.

Marker: `20261120-owner-1615-EST/COLLAR-FINAL`. Scheduled 16:15:01 EST / 21:15:01Z, America/New_York; RUN_ID_UNAVAILABLE. Claims `20261120-owner-1615-EST/COLLAR1` through `COLLAR5`, in order below. MATH_STATUS=OPEN; RH=OPEN.

## B. Authority and exact target

Main `556f9c1b618912e626ef4e73b2c44d41a255e389`; AGENTS `32d78eca566daa9a2bd3bba32651ca447aeab3dd`; contract `f4fe93c4b609d07061ac9aa7d2dd0b7371e73f3c`; November 20 directive `eb9fada09a894534589e9ff38608e1cffba65f91`. For X=R^2-1, M(x)=sum_{n<=x} mu(n), and K_R=max_{0<=y<R}(M(y)-1)^2/(y+1), the target is one fixed 0<delta<=2 such that for every epsilon>0 some C_epsilon works for **all** integer R>=2:

`|M(X)-1| <= C_epsilon R^(1+epsilon) K_R^(1-delta/2)`.

The exact original Q_R is the sum of mu(a)mu(b) floor(X/(ab)) over 1<=a,b<R. Its endpoint identity is Q_R=2M(R-1)-M(X). Source blobs: Euler Abel-Gram `2a94dd8fd56fc03e95f732fb44b778a8d4f83e26`, integer pointwise `c327c556f39ee7014fd774b24d0f95a1ece050e0`, endpoint gate `e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73`, frozen comparison `2938f7dbc44f446cc8104818f9b13a1345b8583c`, envelope arithmetic/laws `714bbeede4f8e0a48fabff08e44c23a1309ae04b` / `628018db94395f988308b0ffdb4e8e5792fc0b71`. #1135 proves `universal_envelope_bound : EnvelopeBound 2 0`; for 0<=lam<2, eta>=0, `EnvelopeBound lam eta` iff `Theta <= 1/2+eta/(2-lam)`. Neither supplies strict delta. Always 1<=K_R<=R; the y=0 anchor matters.

#1119: `native_mertens_near_uniform_window_error_closed : MertensGrowthAtMost (7/8-7/(64*nearUniformSlotCount))`, for the fixed positive slot count and every positive loss. Source `f629db1b2b65d6ec042ac9432397d4b6316200c6`, raw `77ee815846d6d534c866f0752aa33b84c385610a`; #949 `growthExponent_eq_rightmost`, blob `768c8255850bf4074aff265c3fe17a1f5c43979b`. Thus input Z below is Theta<=7/8; this is attributed to the repository, not to the zero-density paper. Hosted run/job for #1119: `42552018910/128949473700`; #1135 `43777334576/133006501690`, raw `ac6dc46b70da962e70b18ea184451c225c1cd44a`. Their theorem audits permit `propext`, `Classical.choice`, `Quot.sound`. #1141 double-centering `7cb66c07ff3bb784f1b1d4434647326f06f0f2b2`; human-merged #1155 frozen divisor rank `3f530136ac8335df88137ad26680aeade9335cc8`, raw `713c0fddd1192fc3c5db05c9a1126d3e12b96253`, run/job `44796048185/136495731019`. #1154 redirected priorities, #1153 concerned Nyman, and no open/draft PR was found at intake. No new Lean or axiom check is claimed for this report.

## C. Structural hypothesis

Use actual floor **rows**, not a frozen reciprocal model or an arbitrary probe. Summing a whole row first should expose the return that a rank calculation cannot sign. Then test whether pairs with genuinely shared factors account for the cost, and whether cancellation survives keeping every gcd sector separate. No prime genealogy is assumed to imply a source admission.

## D. Derivation

**COLLAR1: exact row removal (IDENTITY_ONLY; elementary bound PAPER_PROOF).** Let 0<=4H<=R, C=[R-H,R), O=[1,R-H), all indices integral. Q_O uses both indices in O at the **same X**. Write L=sum_C mu(a), V=sum_C mu(a)^2, y_i=floor(X/(R-i))=R+i+c_i, c_i=floor((i^2-1)/(R-i)), for 1<=i<=H. Put W={(a,n): a in C, a<n<=floor(X/a)}. Then

`Delta = Q_R-Q_O = 2L-V-2 sum_W mu(a)mu(n)`.

Indeed R<=y_i<2R. Divisor inversion gives sum_{b<=y_i} mu(b)floor(y_i/b)=1; all b>=R up to y_i have quotient one. The signed full row is mu(R-i)(1-sum_{R<=n<=y_i}mu(n)). Double its row sum over C, then subtract the corner L^2, since every floor in C x C is one. Expand L^2=V+2 sum_{a<n<R; a,n in C}mu(a)mu(n). This proves the formula with both original mixed orientations and the squareful zeros intact. The n>=R entries arise by inversion, not as new historical K_R entries. In particular |Delta|<=3H+2H(H+1)+2H^3/(R-H); take H=min(floor(sqrt(R)),floor(R/4)). The exact final amplitude is 2M(R-1)-1-Q_O-Delta. Squaring this entire expression retains every mixed term; we use no sectorwise-squared surrogate.

**COLLAR2: arithmetic exclusions (PAPER_PROOF).** Set H=min(floor(R^(2/3)),floor(R/4)), D=floor(R^(1/3)). Passing from W to n<=R+i removes at most H^3/(R-H)=O(R) pairs. Lags n-a<=D cost at most HD=O(R). On the rest assign a pair with a common prime p>D to its *first* such p. Here p<=n-a<=2H, and at most O((H/p+1)^2) choices occur per p; their total is O(H^2/D)=O(R). Squared prime divisibility gives zero; otherwise mu(a)mu(n)=mu(a/p)mu(n/p). Thus Delta=-2F+O(R) with F the signed flat, long-lag sum with no common prime >D, keeping small factors and gcd=1. These are deterministic absolute bounds on discarded pairs, not the cost of the remaining F.

**COLLAR3: honest multiplicity and absolute obstruction (PAPER_PROOF; unsigned payment REFUTED).** On the transformed past/future part set B_ij=mu(R-i)mu(R+j)1_{j<=t_i}, 0<=j<=t_H, t_i=i+c_i. For H<=R/32, t_i strictly increase and t_H<=32H/31. Select all i where mu(R-i)mu(R+t_i) is nonzero; columns j=t_i give a lower triangular signed minor with diagonal +/-1. The two squareful losses are at most (H+t_H) sum_p 1/p^2+O(sqrt(R)), by injection on the future side and counting multiples of p^2. Here sum_p 1/p^2<=35/72: majorize odds 2k+1 by reciprocal-square bound 1/(4k(k+1)), retaining the first gap 1/72. The minor has size at least 3H/248-O(sqrt(R)). Hence for both H=floor(R/32) and the two-thirds width eventually there are order H independent rows and order H^2 live unsigned entries. This is not rank of the original floor matrix or a bound on the signed all-ones contraction.

More specifically, u=floor(H/2), u<i<=H and 1<=j<=u is an admitted rectangle. Its coprime squarefree pairs have density c=product_p(1-3/p^2+2/p^3)>0 when sqrt(R)=o(H) in these two families. For finitely many p<=Z use the Chinese remainder theorem in both independent integer coordinates modulo the product of p^2. For p>Z the two squareful-axis errors are O(H^2/Z+H sqrt(R)); a shared p divides the positive difference <=2H and costs O(H^2/Z). First let R grow, then Z. The local factor counts both coordinates not divisible by p^2 and excludes both divisible by p. Thus at macroscopic width even the coprime absolute bill is order R^2, exceeding R^(1+epsilon)K_R^(1-delta/2) for any fixed delta>0 and epsilon<delta/2. This refutes termwise absolute payment, not the signed target.

**COLLAR4: sharp interval estimate; COLLAR5: signed gcd sectors (PAPER_PROOF from Z and the Guth-Maynard density bound; independent review pending).** Use b=7/8, A=30/13, gamma=1-A(1-b)=37/52. External input: Guth and Maynard, *New large value estimates for Dirichlet polynomials*, Annals of Mathematics 203 (2026), 623-675, (1.4), DOI `10.4007/annals.2026.203.2.6`: at each fixed 1/2<=s<=1, N(s,T)<<_epsilon T^(A(1-s)+epsilon). Include both signs of the height by symmetry. We do not assume RH or a random sign model.

For d<=R^(1/15), R^(3/5) << l << H (fixed comparison constants), and any interval I of length <=O(l) inside [R-2H,R+3H], we obtain uniformly

`|sum_{n in I; d|n} mu(n)| <<_epsilon R^epsilon (R/d)^b (l/R)^gamma`.  (1)

Here are details to audit the short-interval loss. We may take R large. Nonsquarefree d contributes zero. Otherwise mu(dm)=mu(d)mu(m)1_{(m,d)=1}. Take Y=R/d, P=R/l and a fixed smooth cutoff phi supported in (1/2,2), equal to one on [3/4,3/2]. In log(n/R) convolve the interval indicator with a unit-mass smooth bump of width R^(-1/2); changing endpoints costs O(1+sqrt(R)/d). Its Fourier weight is at most C_k min(P^(-1),(1+|t|)^(-1))(1+|t|/sqrt(R))^(-k). Fourier inversion uses the actual polynomial D(t)=sum_{(m,d)=1} mu(m)phi(m/Y)(m/Y)^(-it); beyond |t|=R the trivial bound and rapid decay cost O(1).

Fix a small mesh eta>0, V0=R^eta. In a dyad |t|~T>=4V0+10, group t by the greatest real part of a nontrivial zero within 2V0+10 of t: put it in [s,s+eta] on a fixed mesh from 1/2 to b; use the baseline s=1/2 when none exceed 1/2. On such a layer, |D(t)|<<_eta Y^s R^(O(eta)). In fact Mellin inversion has integrand Y^w times the rapidly decreasing Mellin transform of phi, times 1/zeta(w+it) and product_{p|d}(1-p^(-w-it))^(-1). Truncate |Im w|<=V0 and shift to Re w=s+3eta. The finite Euler factors cost O_eta(d^eta) for Re w>=1/2. For |v-t|<=V0, the disk about 2+iv of radius 2-s-eta is zero-free in its interior and excludes the pole. The Euler product bounds log zeta on radius 1/2. Polynomial growth of zeta, Borel-Caratheodory on the smaller radius 2-s-3eta/2 and three circles at radius 2-s-3eta give |log zeta|<<_eta(log(3+|v|))^kappa for some kappa<1, hence a reciprocal cost O_eta(R^eta). The horizontal edges obey the same bound, and choosing arbitrarily high decay order absorbs their truncation. For |t|<=O(V0+1) use the global line b+3eta from Z, compact heights by regularity of 1/zeta at its pole, and the same bound at higher heights. Its integrated cost is O_eta(Y^b R^(O(eta))/P).

For s>1/2 the layer measure is << R^(O(eta)) T^m, m=min(1,A(1-s)), by covering each relevant zero with an interval of length O(V0); s=1/2 uses the whole dyad. Each dyad costs at most R^(O(eta))Y^s P^(m-1), since min(1/P,1/T) T^m<=P^(m-1). Because Y>=P^A for large R (14/15>12/13), this expression is largest at s=b on both pieces, giving Y^b P^(-gamma). The logarithmic dyads and finite mesh are absorbed by choosing eta small after epsilon. The sharp endpoint error is absorbed since b-(2/5)gamma>1/2 and d>=1. No uniform-in-s external constant is required: the mesh is fixed before R.

Let S_g=sum_{(a,n) in W; gcd(a,n)=g}mu(a)mu(n). Tile W by disjoint full dyadic lattice squares of side l down to l0 comparable to R^(3/5). Start with an enclosing square of side O(H). The four boundary pieces (two vertical ends, the diagonal and the monotone hyperbola of bounded slope) meet O(H/l) cells per level, so at most that many new full squares occur and the unresolved boundary contains O(H l0) pairs. Counting its absolute cost in the original gcd groups uses each pair once.

On each full square, exact gcd inversion is 1_{gcd(a,n)=g}=sum_{ge|a,n}mu(e). Summing absolute values over g costs at most sum_d tau(d) times the absolute value of the signed divisible-pair sum, which factors into the two interval sums (1). For d>R^(1/15) use absolute counting **over the union of disjoint full squares**: d divides n-a, so d<=3H, and the total is << sum_d tau(d)(1+H/d)^2 <<_epsilon R^epsilon H^2/R^(1/15). For smaller d, sum_d tau(d)d^(-2b)<infinity; the total across levels is <<_epsilon R^(2(b-gamma)+epsilon) H sum_l l^(2gamma-1) <<_epsilon R^(2(b-gamma)+epsilon) H^(2gamma). Here 2gamma-1=11/26>0. The stopping-boundary and large-divisor errors are each O_epsilon(R^(19/15+epsilon)); the main exponent is 2(b-gamma)+4gamma/3=199/156. Therefore **sum_g |S_g| <<_epsilon R^(199/156+epsilon)**. The same upper bound holds for |Delta| and for the flat long-lag exact-gcd totals after the O(R) deletions. No cancellation between different gcd values is required for this saving.

## E. Quantitative relevance

For delta=1/2 **on the strip only**, the two-thirds-width cost fits R^(1+epsilon)K_R^(3/4) whenever K_R>=R^(43/117), because 199/156-1=43/156. At sqrt width the cost fits O(R) for every history. Neither estimate controls Q_O at the original X or the full return at low histories. Substituting Q_O-2F with the same target bound is TARGET_EQUIVALENT up to O(R) and the endpoint; it is not an independent lemma. No slot count is varied with epsilon or R. No NNS, prime/VF, LOW/HIGH, or Nyman transfer is used or asserted.

## F. Falsification and exact computation

Independent literal floor-matrix checks: 127 roots 2..128, all 2,143 allowed (R,H), 2,016 literal row contractions and 1,858 nonempty sampled signed minors checked by fraction-free determinants. Mu independently checked by trial factorization through 10,000. At (4,1) Delta=-5; at (7,1) it is +3. At (17,4) the curved cap is -1, so substituting the flat wedge in the exact identity gives 7 instead of 9. One orientation, sign monotonicity, and omitting the corner or cap are invalid. At seven wider roots direct gcd classification, inversion from divisible-pair totals, and boundary-inclusive subdivision all agreed. Entries are `(R,H,Delta,sum S_g,sum |S_g|,S_1)`:

| R | H | Delta | Sum | Absolute group totals | Coprime group |
|---:|---:|---:|---:|---:|---:|
| 317 | 46 | -9 | -10 | 24 | 5 |
| 549 | 67 | -88 | 32 | 64 | 26 |
| 1027 | 101 | -105 | 15 | 99 | 35 |
| 4096 | 256 | -22 | -79 | 237 | -10 |

At R=65536,H=2048 (macroscopic test) there are 776 live pivots; the specified coprime rectangle has signed total 226 versus absolute 299,216. The 270 rational exponent controls are regression tests, not proof of a zero-density theorem. Deterministic standard-library replay, no seed, SHA-256 `1ceb9191e6e2edabc32ab33290c5d6f945e12ecb9f335e226bb063b6b478b917`. FINITE_COMPUTATION only for these counts; no asymptotic conclusion from samples.

## G. Interpretation

The floor interaction can be removed without cloning past occurrences. At this width the curvature, short lags and all large shared primes together cost only O(R), while genuinely coprime live entries already have positive density. Signed cancellation survives retaining exact gcd labels; a determinant or large common-prime count alone cannot explain it. The finite rank obstruction on the separate frozen divisor source is not contradicted.

## H. Competing mechanisms

Continue signed rectangular sums and their sharp physical boundary (COLLAR4-5). Keep the matched inner/outer prime packet JOINT and analytic LAG as distinct carriers. Park absolute ancestral payment and rank-only contraction: #1155's restricted rank two and external (3,-5) probes giving -7,+3,0 already warn against them. There is no theorem that the interior has a compensating sign, and no evidence for promoting this strip to the entire program.

## I. Specialist handoffs

- Analytic: audit (1), especially local reciprocal-zeta disks, sharp endpoints, d-uniform finite Euler factors, and the independent L1 dyad sum. Do not import the LAG L2 estimate by analogy.
- Finite Wheel: inspect first-common-prime admission, the unimodular triangular minor, and coprime density with its two cutoff limits.
- Census: independently replay the seven wedges at 64,125,216,317,549,1027,4096; compare direct gcd groups against divisor inversion, including zeros and boundary. The first curvature falsifier is (17,4).
- Referee: try to break the uniformity of (1), the aggregate large-d count, or the boundary-box loss. Test the improper reset of X or K_R; neither is allowed.
- Lean Verification: after independent review, the exact identity in COLLAR1 needs only divisor inversion, the tail quotient one, and the overlap subtraction. No request to formalize a conjectural global estimate.
- Coordinator: register a paper-level saving on a **proper source contribution** and an unsigned no-go. Do not enter it as a full HIGH, cross-route or half-line supplier.

## J. First independently missing lemma

For the admitted rectangle of COLLAR3 at H=floor(R^(2/3)), seek, for every epsilon>0 with one constant for all sufficiently large R, `|sum_{u<i<=H,1<=j<=u,(R-i,R+j)=1} mu(R-i)mu(R+j)| <<_epsilon R^(6/5+epsilon)`. Its coprime indicator is exactly sum_{d|R-i,R+j}mu(d), not an independence assumption. This proper subproblem is not the envelope and is not implied by the exponent proved here. An infinite family with limsup log(1+|sum|)/log R>6/5 would refute it; a single large finite value does not. Even success would leave other signed rectangles, the complementary interior, strict history and endpoint restoration. Next smallest rigorous step: independent audit of (1) before extending the strip or spending it on a global return.

## K. Continuity, publication and resume

REPORT_WATERMARK at intake `b0206c7e4783c07fc473ad147f0e4ddd3b981255`. All seven roles present on both Nov 20 and Nov 19, America/New_York; no TODAY=PENDING. Nov 20 latest actuals consumed: Coordinator OCTAVE1-5 `10b0565eefe38a88c7b5f73aefa2e4872a3a3d93`; Owner JOINT1-3 `e23448e6ae1c6176840c6edf9fe1e688d08ec611`; Analytic LAG1-5 recovery-final `a01d00b6a006294e7fb9f74a0e556014fc3fdce8`; Wheel DEGREE `ee23ffbdc077fa9207545a537dcff54799fa68ac`; Census PARITY `5f60e116dce13edfb74c2e490c6e39e6196ce946`; Referee SIDEBAND `1e38a05754800a18c3c930b631d8ea20e9542caa`; Lean INTERIOR-PROBE `112bd7cd473466f5c56185fbd5eb2459577a2b92`. Today's DEGREE counterexample includes 1438710; SIDEBAND's proper-divisor fractional deletion is not deletion of all outside rows. The morning Owner's SQUARE/WINDOW/LEDGER/APERTURE/DRIFT watermark is superseded by these actual sections, not by scheduled assumptions.

Nov 19 carry-forward: PORT `b107495e974bbf12d6571d646341126a3e7f5dba`; HINGE `85060bbc0910a64ce70a8c418d9fef35b16c768b`; PHASELOCK `62efb52db960cff6ff4ca43497d48589c56bc791`; GATE `a20b2ee34f37f8ec7a6d632eb1f7a31521889232` (638 and 682 share the sole donor 462); CLOCK `1093df2a14e84551dae3ca8216be7ac6c4bc30a8`; ESCAPEMENT `e063ee0f793705c9ca823e0a8cee6ddc3b309418`; Lean PLATEAU/TWO-WITNESS `6231b48290c36a43b0f1246b7fbddf692652109c`. External handoffs `7d63d434690d00dffce9c90335d41c4f62d85798`: retain unit/p=R and EXT-20261014-5 all-root, not FirstBad. Older Nov 13-15 archive gaps remain CONTINUITY_UNVERIFIED; no missed launch inferred. Source-first dependency map `098f88f9b8e727ce78e52e5dc5158d68c930bf1b`, atlas `cd0419d00a37739fe5a292f5cb738e33213949d5`. Outside RH announcement unverified, unused.

Intended canonical: `agent-reports:research/agent_reports/2026-11-20/10-owner-payment.md`, 41,576 bytes, blob `e23448e6ae1c6176840c6edf9fe1e688d08ec611`. Direct Git tunnel returned 403; authenticated Contents/blob displays did not preserve all old bytes. No replacement from excerpts. Early immutable checkpoint committed and read back at `6f4e6fb04dd1ef52660991fee5d5bdd8fe8829e6` (blob `8097c17c48d8eeaccac2579029376a49d8024f4e`, 2,374 bytes), also the latest observed reporting base before this payload. Create-only final recovery is the same scheduled execution; its exact-commit verification receipt belongs in the delivery, not a self-referential commit. Preserve both unique markers and do not count the recovery twice. No proof branch, PR, main, other role or schedule changed.

amplification_cost_ack=MULTIPLICITY_VS_COST_TO_HALF_V1; half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1; continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1; publish_ack=REPORT_PUBLISH_RECOVERY_V1. Half/continuity/publication policy blobs `a192bb6211c52b8201f3255b83f0912a82cb4d65`, `7eef0b36c7442be922d9bc99c6b35d853c4f1f4f`, `a9583516fd2e603320c771e32c170132bf0c53e9`. SELF_AUDIT only for COLLAR1-5; INDEPENDENT_REVIEW=PENDING; NOT_FORMALIZED. Global strict delta: NONE ESTABLISHED.

# Prime Census Laboratory | Where the prime-band credit goes

November 20, 2026, 19:00:01 EST (November 21, 00:00:01 UTC), scheduled, America/New_York. `RUN_ID_UNAVAILABLE`. Section `CENSUS-20261121T000001Z/FIBRE-FINAL`.

## A. Main finding

At R=3000, 98.936% of the prime band's net negative contribution comes from pairs in **different** three-prime blocks. Keeping the 32 individual determinants but discarding their interactions loses -552367.24 out of -558307.35. Moreover, restoring every term of the actual Selberg recurrence gives **+218266.75**, not a negative endpoint. The first positive overshoot with a genuinely negative band and at least three primes is already R=46. Neither fact refutes the finite determinant; both refute using isolated blocks as payment for the complete signed error.

There is a quantitative replacement: for *any* partition, its omitted cross-block charge determines the minimum size of a block. At R=3000 any partition retaining half the gross squared prime-log mass inside blocks needs a block of at least **47 of the 96 primes**. This is a necessary condition, not a certificate that such a block suffices. Below are a proof, independent reconstructions, and the remaining cost.

## B. Authority and scope

Opening main `b8eaa25f58b8695c5148f577e9cb81e1d4c959d4`, AGENTS `32d78eca566daa9a2bd3bba32651ca447aeab3dd`. While running, #1161 merged at 19:21:28 EST (`dfa5d2191ecbb1b637e67a9ac206d10c8f4b98e5`); read the new AGENTS `e651d40985f64114106a664b4ee63b51096b4687` and full-cost directive `e76124cec02731191826e53f850d9680b691f1ec` and executed the added Census assignment in this same run. At 19:25:40 EST #1158 merged: reconciled main `65f4d84e0176ef2865d959c7d4824311088f3572`; it added the finite negative-semivariance module `96945b62d2e0b0a370a2b45a32a4c778c2f4a39d`, not the critical estimate. CURRENT_PROOF_CONTRACT `f4fe93c4b609d07061ac9aa7d2dd0b7371e73f3c` and original source definitions unchanged. The earlier multiplicity directive is `eb9fada09a894534589e9ff38608e1cffba65f91`.

`alpoge_full_cost_ack=ALPOGE_FULL_ANALYTIC_GEOMETRIC_COST_V1; amplification_cost_ack=MULTIPLICITY_VS_COST_TO_HALF_V1; half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1; continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1; publish_ack=REPORT_PUBLISH_RECOVERY_V1`.

The public theorem remains `VFCanonicalSquareVonKochStatement`: one C for all R>=2 in the O(R log R) bound for the centered finished prime count (blob `79030d70e8d3e0d08eef9bac53fef95c36eca2fb`). The alternate historical supplier fixes 0<delta<=2 before all epsilon>0, then one C_epsilon for every R>=2: `|M(R^2-1)-1| <= C_epsilon R^(1+epsilon) K_R^(1-delta/2)` with K_R=max_{0<=y<R}(M(y)-1)^2/(y+1), M(0)=0. #1135 proves `universal_envelope_bound : EnvelopeBound 2 0`, and `EnvelopeBound lambda eta` iff `Theta<=1/2+eta/(2-lambda)` for 0<=lambda<2, eta>=0. Raw `ac6dc46b70da962e70b18ea184451c225c1cd44a`, exact-type/standard-axiom job `43777334576/133006501690` passed. #1119's fixed-family Mertens exponent 7/8-7/(64*Npack) includes every positive loss (job `42552018910/128949473700`). Neither is the new supplier.

Native source blobs: signed recurrence `5a6e063b3b9481af22c714b0c73d710bf8676374`; square/mixed kernel `a88e28d0615140b15d8dfe5dc337e3611f65c15e`; frontier charge `55267f1b5aeecc85fdb17f29ebe90c056a8e83f4`; mu*log=Lambda `db4ce4182ff7864968a89830254b74e585e2c29c`; #1157 large-prime prefix `96cd9d081831bb7dfcfe801e99ffb49da2d462b7` (merged; targeted hosted job `44839907263/136645421257` passed). #1158 finite identity job run `44840056592` passed. At the audited #1160 head `66ecd8e53c8e6c61081df8e213560adead5bfb3a` the note/Lean blobs are `7225f9ce4cca8b0e09039acee62d4534ff43d1ab`, `595dfbb43ff593fc7684a4faa45d08b113b7d629`: **CI_STATUS=FAILED**, targeted job `44842765089/136655003892`, compile with warnings fatal. This does not invalidate the numerical source; it prohibits calling that head Lean-certified. #1159 `fe22ec18c4b2bdf91aad3a46b91e7a43ed2a1b71` and #1156 `40707df34b0041f6971abca1ffc90d003bbb5520` were open at inspection. No local Lean build or repository proof edit.

## C-D. Questions and carrier

Can a negative selected minor determine the sign on its full reciprocal quotient? Do separate three-prime blocks capture a nonvanishing fraction of the coherent band credit? Can fixed low-quotient groups remove the singular part of the complete response? Each has a different falsifier: a sign reversal, a uniform bound on omitted pairs, or a pole in the exact complementary transform.

X=R^2-1, J(n)=Lambda(n)-1, E(x)=sum_{n<=x}J(n)=psi(floor x)-floor x, K2=Lambda*Lambda-Lambda log (Dirichlet convolution), A(x)=sum_{n<=x}K2(n), T(x)=sum_{n<=x}K2(n)E(floor(x/n)). V_k is the complete group with floor(x/n)=k. Ranges registered before computing: R=2..64 discovery, 65..256 held out, plus 317,549,1027. The #1157 test uses Q=max(2,isqrt R), prime Q<=q<min(2Q,R), and the largest prime p>R with floor(X/p)=q for each occupied q. The separate #1160 band P={prime p:3R<=4p, p<R} includes squares and each distinct mixed product once. Its weights are w_p=log p; m=|P|; F=2 sum w_p^2-(sum w_p)^2, B=-F. All these products see E(1)=-1. Three-prime, larger-scale and upper-moment extensions are labeled follow-up, not held-out confirmation.

## E-G. Complete finite ledger

C was computed from its terms, not defined by an endpoint subtraction. In the table U=sum_d Lambda(d) S(floor(X/d)), Df=sum_d Lambda(d) E(floor(X/d)) [log X-log d-log(floor(X/d))]. Then C=S(X)log X-U+(T-F)-Df and C-B=E(X)log^2 X. S is the original signed first-Selberg remainder. All columns below are independently rounded to the nearest integer; the stored integer-grid conservation residual is exactly zero in all five rows.

| R | m | S log X | U | T | F | Df | C | C-B |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
|100|4|-106374|-90647|14652|-159|-2295|1381|1221|
|317|14|-1337156|-1179094|136727|-5296|-23014|6976|1681|
|549|21|-4395203|-3915543|365407|-15145|-68848|-30259|-45404|
|1027|36|-16881987|-15238963|1356127|-56617|-241081|10802|-45815|
|3000|96|-166310595|-152351936|12116896|-558307|-2060030|776574|218267|

Smallest m>=3 falsifier of `C<=B`: R=46, X=2115, P={37,41,43}, B=40.940581, C-B=131.124076, E=2.236592. It satisfies the actual band conditions and is not a first-bad witness. Among the 258 registered roots there are 101 positive overshoots with m>=3. Maximum C/B among those occurs at R=53, P={41,43,47}, ratio 32.989010. Q_+(H)=sum_{H<=R<2H}max(E(X_R),0)^2. At H=2,4,8,16,32,64,128 its ratios to H^3 are 0,0,0.000633120,0.007547098,0.045740916,0.045214196,0.066537896. These neither bound a supremum nor establish any uniform epsilon.

In the separately registered minor test, all 256 nonempty selections were negative while V_1 was positive at **all 258** roots (61 nonempty discovery, 192 held out, 3 controls; R=2,3 empty). At the first active root R=4, the chosen products are 14,10,15. Their sum is in [-8.465056,-8.465055]; the whole group 8..15 is in [4.028213,4.028214]; T is in [12.250750,12.250751]. The absolute-kernel sign surrogate gives [-24.004325,-24.004324] on the group. Why: K2(p^a)=-(log p)^2; K2(p^a q^b)=2 log p log q for distinct primes and positive exponents; every other coefficient vanishes. There are 111 sign reversals on substituting theta for psi (first R=14), and 10 on using R^2 instead of R^2-1 (first R=7); the exact square-boundary jump is `1_(R=p^a) log p-1`. The dimension of the full high-prime/cofactor matrix first decreases at R=6 to 7 (4 to 3). K_R is 1 at four registered roots and 3/2 at the other 254; no power improvement is identifiable there.

## H-I. An inverse bound for every partition

`BLOCK-RETURN / PAPER_PROOF`. For any partition of P with block sizes at most b, put L=sum w_p, L_g=sum_{p in g} w_p, D=sum w_p^2. The exact within-block contribution is 2D-sum L_g^2, the omitted signed cross-block term is `-(L^2-sum L_g^2)`. For m>0,

`sum L_g^2 / L^2 <= max L_g/L <= b log R / [m log(3R/4)]`.

Thus retaining a fraction alpha of the gross L^2 inside blocks requires `b>=alpha m log(3R/4)/log R`. No permutation helps. Since w_p=log R+O(1) uniformly and PNT gives m~R/(4 log R), every partition with b=o(m) misses (1-o(1)) of the gross square and of the net negative band. With triples and one possible remainder, the within contribution is asymptotic to -R log R/4 while the full band is asymptotic to -X/16. This is a sharper replacement for adding independent triple credits: keep the single explicit cross term once. It does not furnish an automorphic family.

At R=3000, triples give within=-5940.1073, cross=-552367.2395; the cross fraction is 96.875% of the *gross* L^2, 98.936% of the *net* |F|. The normalized coefficient Gram has eigenvalues 4 (multiplicity 95) and 8836 (once); the unweighted observation Gram of the repeated E(1) has eigenvalues 96 (once) and zero (95 times). These are not the same matrix. For the physical weighted Gram of diag(w)(2I-J)diag(w), smallest/largest eigenvalues are approximately 14206.40 and 33829391.72 (binary64 diagnostic only). Two partitions for each b at five roots, 342 exact grid tests, verified the bound and all cross terms. The centered integer doubling and real weights do not imply a Hecke congruence.

`FIBRE-RETURN / PAPER_PROOF`. Strong unconditional PNT gives A(x)=-2 gamma x+O_h(x/log^h x) for all fixed h>0, and therefore V_1=A(x/2)-A(x)~gamma x. Use the hyperbola identity for Lambda*Lambda, partial summation, and sum_{d<=y}Lambda(d)/d=log y-gamma+O_h(log^-h y). The analogous split for K2*J gives T~4 gamma^2 x: on the short K2 leg use sum |K2(n)|/n=O(log^2 x) and E=o(x/log^h x), and on the short J leg use sum_{d<=y}J(d)/d -> -2 gamma. Hence `(V_1-F)/B -> 1+16 gamma`: even the other terms at the very same quotient outweigh the band asymptotically. At R=1027 V_1-F=651594.21, B=56616.92. For the *complete* C, unconditional PNT only yields C/B=1+O_h(log^-h R); it does not price positive overshoots at root scale. The bare kernel's double pole and -2 gamma main term were already identified in `research/K2_COHERENT_MODE_KILL_GATE.md` (blob `d438fcd549f82e8189bde90e09889aedfd8d6757`). Strong PNT input: Johnston and Yang, arXiv:2204.01980; Laurent expansion: NIST DLMF 25.2.4.

`FIXED-BINS / PAPER_PROOF; SQUARE-INVERSE / CONDITIONAL`. For fixed integer l>=0 set P_l(s)=sum_{k<=l,k>=1} E(k)[k^-s-(k+1)^-s], c_l=(-2 gamma)(-2 gamma-P_l(1)), and h_l(x)=T(x)-sum_{k<=l}V_k(x)-c_l floor(x), summing positive bins only. With f=-zeta'/zeta and g=f^2+f', the s-normalized Mellin transform of h_l is exactly `g(f-zeta-P_l)-c_l zeta` initially in Re s>1. At each nontrivial zero rho of multiplicity d its cubic Laurent coefficient is **-d^2(d+1)**, unchanged by deleting any fixed finite set. Centering removes the real pole at 1. The complete non-T remainder E(floor x)log^2(floor x)-T(x) has cubic coefficient d(d-1)(d+2): differentiate (f-zeta)/s twice and multiply by s. The integer-log correction is analytic in Re s>0. In particular a simple zero kills the cubic only in this remainder.

If an actual zero has beta=Re rho>1/2, then for each sign the limsup along dyadic H of `sum_{H<=R<2H}(h_l(R^2-1))_sign^2 / [H^(1+4 beta) log^4 H]` is positive; positive and negative parts are taken separately. Proof: a zero limsup gives the corresponding first moment o(H^(1+2 beta)log^2 H) by Cauchy. Jumps are O_{l,eta}(n^eta) for every eta>0 since the unrestricted jump is K2*J=O(d(n)log^3(2n)); fixed bin jumps are finite shifted copies of K2. Interpolation between squares costs O(H^(1+2 eta)); choose eta<beta-1/2. The chosen nonnegative Mellin integral at beta+u is o(u^-3) since its dyadic series is bounded by a summable interpolation error plus sum_j o((1+j)^2)2^(-2ju). The other half converges in Re s>beta by the real-axis singularity theorem for nonnegative Mellin integrals: the difference is regular there on the real axis. At real beta the difference remains regular; both halves are o(u^-3). Their sum bounds the modulus at rho+u, contradicting the cubic. No off-line zero is asserted. A square-root-scale upper bound on even one sign of this centered tail would itself exclude off-line zeros, not independently pay the cost. Independent analytic review pending.

## J-K. Paid and unpaid costs

In the external formal source `CocoSgt/riemann-hypothesis-lean` at `7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`, read GrowthBoundGivesRiemannHypothesis `a3ece4b4`, ErrorFormsWeakWindowsFalse `1d1d179d`, SChain `a4bc8cec`, CovolumeEstimateAnchoredWeights `e19746a6`. The normalized abstract cost, writing u=x^epsilon, delta=nT2/n and T0=nT, is `aE(1+m^2/k)/(m b delta)+2 n m u/(T0 delta)+k u^2/(n T0)`. Its conditional size-window estimate is not a realized native bound. The external movement, thin and width tests include `2f(x+1)theta<=1/x`, `6f(x+1)(eta+1)<=b/x` and a movement-cost bound; the anchored covolume premise quantifies an actual lattice over a number field with archimedean norms. Native PNT counts m labels, not m independent observed errors. No native joint witnesses for T0,n,nT2,k,b,delta,aE,Err,f,theta,eta or the height/covolume taxes have been supplied. No net power saving is claimed.

First unpaid estimate: for every epsilon>0 obtain one C_epsilon for all integers H>=2 such that `sum_{H<=R<2H} ((C_R-B_R)_+)^2/log^4(X_R) <= C_epsilon H^(3+epsilon)`, or prove a fully priced native strict-delta alternative. At R=46 positivity alone fails as a substitute for this inequality. A true upper-error interpolation uses the **right** square endpoint, not the lower-sign argument's left endpoint. Retain the rest of the Selberg source; do not transfer this statistic to VF/NNS by analogy. `MATH_STATUS=REFUTED` for independent triple payment and pointwise C<=B; `OPEN` for the complete uniform supplier and RH. No blanket counterexample to the external argument, nor a change to any of the nine independent routes, is asserted.

## L. Continuity and specialist handoff

Intake `fd61980c4dee6b446a3214dbee5d267528b0df3e`, last consumed `c4e0f2ab189892d754ad8867fb9a4a9795af4410`, +13 commits/11 paths/no deletions. Verified actual report discovery October 12-November 20. All seven roles published November 19 and 20 (EST), none marked pending. Latest Nov19 -> Nov20 blob prefixes: Architect PORT/OCTAVE `b107495e/10b0565e`; Owner HINGE/COLLAR `85060bbc/471cfa88`; Analytic PHASELOCK/PRIME-MARK `62efb52d/805bcd18`; Wheel GATE/THRESHOLD `a20b2ee3/365e246c`; Census CLOCK/PARITY `1093df2a/5f60e116`; Referee ESCAPEMENT/SIDEBAND `e063ee0f/1e38a057`; Lean TWO-WITNESS/INTERIOR-PROBE `6231b482/112bd7cd`. External handoffs `7d63d434690d00dffce9c90335d41c4f62d85798`: preserve source-specific c=1, p=R; all-root limsup is not FirstBad. Earlier November 13-15 byte-continuity caveat is retained.

Architect: put the block-size lower bound before any cost division. Owner: retain the cross-block scalar and all of C. Analytic: test a growing quotient cutoff with signed return. Wheel: separate coefficient and observation Gram. Referee: independently audit the two-sign Mellin argument and R=46 minimality. Lean: the finite partition inequality needs no external theorem; no formalization claimed. Seven Owner gcd wedges, all six SIDEBAND/corrected THRESHOLD boards, marked 2/3 returns, and SHIFTED-PRIME for every R=7..512 (477 nonempty) were independently checked. At R=1027 the mixed mark -62+62=0, while SIDEBAND gives 898704-1800306+901227=-375.

## M-N. Replay and continuation

Priority: (1) retain the proved partition obstruction and explicit rank-one return; (2) test the fixed prescription l_R=floor(R^(1/3)) on the actual sum over nd<=X with floor(X/n)>l_R, together with all complementary terms, rather than substituting a moving l into the fixed-l transform; (3) retire independent small-block or selected-sign payment. Do not repeat unchanged tables.

Both original #1160 scripts ran unchanged after Git-blob checks: `alpoge_selberg_schur_lattice_regression.py` `6debfd716095ecc00ac18110deaf1f4d021883a7`, `alpoge_selberg_complete_return_audit.py` `0507df8fb0d6870d06dd9bd41065456537273ece`. Both passed; the latter's unmodified run(3000) also passed. Independent CPython 3.12.14 replay: run `fibre_census.py`, `fibre_verify.py`, `fibre_audit.py`, `fibre_band.py`, `full_cost.py`, `partition_probe.py` in order. NumPy 2.3.5 only for diagnostic weighted eigenvalues. No random draws. The first two used smallest-prime-factor classification versus ordered prime-power convolution/direct sums: agreement on 1,054,729 coefficients and every registered root, with 1,024 formal mu*log polynomial checks. The extension independently formed S from its first recurrence, A by Dirichlet hyperbola, and the defect and both signed convolutions at 6,307 exact thresholds; 603,026 prime-power sites, X<=8,999,999. It reproduced all individual ledger columns at the four overlapping large roots.

First-pass logs used 80 decimal digits, grid D=10^24. The independent pass certified every rounding by rational atanh series (62 terms, 10^55 grid); all sieve masks and grid sums are exact integers. At N=1027^2, the absolute real-vs-grid error in T or its selected sums is <2.824e-12 and in E <1.055e-18. At N=8999999, b=N.bit_length(), a conservative combined sector error is `100(b+2)^5 N/D < 1.1e-8`: use |log n-grid|<=b/D, |E(n)-grid|<=n/D in the first S recurrence and sum floor(n/d)<=n(1+log n), then in the second recurrence. Thus the signs and the integer table survive rounding. The preregistered JSON SHA-256 is `34a31cf06f305cfc6bee8d61921bbeb60399ffa958f54e666f216b7f36779076`; extended JSON `2981fc269d0fe2538357f9cecd26d4595abbc8e9558725a78dab9f381b313e9f`. The delivered replay archive includes the source, raw signed columns and extended proofs.

Standalone small falsifier (display arithmetic; the rational enclosures were checked separately):

```python
from math import log, isqrt
R = 46
X = R*R-1
ps = [p for p in range(2,X+1) if all(p%d for d in range(2,isqrt(p)+1))]
P = [p for p in ps if 3*R <= 4*p and p < R]
psi = 0.
for p in ps:
    n = p
    while n <= X:
        psi += log(p)
        n *= p
F = 2*sum(log(p)**2 for p in P)-sum(map(log,P))**2
print(P, -F, (psi-X)*log(X)**2)
```

Publication: `agent-reports:research/agent_reports/2026-11-20/40-prime-census.md` is the intended canonical; observed 35,659 bytes, blob `5f60e116dce13edfb74c2e490c6e39e6196ce946`. The full Contents and blob previews elided bytes; direct Git tunnel returned 403. No unsafe replacement. Opening create-only recovery verified at `7691d4bdb4820ce67edfb5f4b4efa74717d77a8c`, blob `f6e567ad2431fe4b62d745a967c58eee463f420a`, 2,398 bytes; that was the live reports head before final publication. Publish this entire continuation to a fresh owned sibling and verify exact-commit readback. The opening and final are one execution; no canonical append or proof change is implied.

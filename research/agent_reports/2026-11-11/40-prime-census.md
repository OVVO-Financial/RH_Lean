# RH | Prime Census Laboratory - 2026-11-11

## Preregistered Checkpoint - 20261111-census-1/DZ

Execution: IN_PROGRESS. Mathematical status: PENDING. Scheduled trigger: 2026-11-11 03:11:02 EST (America/New_York); platform run ID unavailable. Registration prepared at 2026-11-11T08:17:44Z, before experiment execution.

cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1.
Main: f7947bee036c4dddb0c36fc9f53ab46b4fa90995.
AGENTS: c9c89f01b90b526de9f3e8ea92478e36504711b6.
CURRENT_PROOF_CONTRACT: 95566e37c8eaeb99ee680660df4f9d2e06ea5038.
Cross-route directive: e922d4ba9362a1ae196af8f6de88f7417f92087c.
Intake reports head: 308f86d1f39e025dae3a329755a402ba29f88e2c.

### A. Changed Mathematical Question

Today's Wheel GD1 reconstructs the complete common-divisor source from smooth-divisor rectangles. Test whether this exact reconstruction also furnishes an unproved norm contraction on the genuine arithmetic vector. This is a NEW recovery test prompted by GD, not another extension of yesterday's unchanged GC5 conjecture. No specialist is represented as having asserted the new contraction.

For integer R>=2, N=R-1, X=R^2-1, genuine mu:
```text
C_R(g)=sum_(1<=a,b<=N,gcd(a,b)=g) mu(a)mu(b)floor(X/(ab)),
S_R(d)=sum_(1<=a,b<=N,d|a,d|b) mu(a)mu(b)floor(X/(ab))
      =sum_(d|g,g<R) C_R(g),
Q_R=sum_g C_R(g)=S_R(1)=2M(N)-M(X),
D_G=sum_g C_R(g)^2, D_S=sum_d S_R(d)^2,
K_R=max_(0<=u<R)(M(u)-1)^2/(u+1).
```

Candidate H_Z: for EVERY integer R>=4, D_S<=D_G, with fixed constant exactly 1. A single strict positive D_S-D_G falsifies it. R=2,3 are explicit boundary controls, not in this candidate: direct hand algebra at R=3 gives C=(0,2), S=(2,2), so D_S=8>D_G=4. This exclusion is declared BEFORE testing. No larger threshold or fitted constant will be adopted after observing failures.

Competing mechanism: repeated divisor membership produces a positive diagonal cost which favorable ordinary inter-gcd cross terms need not pay. The complete discriminator is
```text
D_S-D_G = sum_g (tau(g)-1) C_R(g)^2
          +2 sum_(g<h) tau(gcd(g,h)) C_R(g)C_R(h).
```
The formula will be independently checked; both orientations and every group remain. H_Z would imply GC5 at its stated range because Q_R^2<=D_S, but neither H_Z nor GC5 proves the needed historical-normalized norm bound. Wheel GD3's new PAPER exponent consumer does not require GC5. No new route or exponent is preregistered.

### B. Frozen Domain And Methods

Primary registered roots: every R=2..256; R=511,512,513,549,1023,1024,1025,2047,2048,2049,4095,4096,4097; and EVERY R=5529..5593 (65 roots). The last window straddles yesterday's recorded R=5561 excursion. It is held out for H_Z, not a fresh discovery of the reused GC5 ratios. Both mandatory roots are present. Include a legal dyadic prime near-resonance witness at each large listed root where one is found by a documented exact search; this is a geometry control, not identification of its phase with rational gcd coefficients.

Primary C++: deterministic Mobius sieve, complete original ordered pairs (or upper triangle with exact multiplicity), exact gcd grouping, divisor sums and full norm/cross accounting. Independent Python: trial-factor historical coefficients, quotient-block Mertens recurrence and GD1 smooth-rectangle reconstruction; no primary sieve values imported. Compare EVERY resulting gcd/common-divisor vector, Q, K, both norms and divisor multiplicities. All mathematical decisions use integers/rationals; no floating-point signs.

Record smallest failure within the exhaustive small range, all held-out failures, extrema, complete vectors for decisive cases, the original pair diagonal/within-gcd/cross reconstruction, and Q^2/(R^2 K), D_G/(R^2 K), D_S/(R^2 K). Stop at the frozen domain; do not fit a universal bound from its maximum.

Secondary verification: independently reproduce Owner MC at block r=10, X=120, p=3, empty lower signature, left b=101 and b=115. Inspect literal active/clipped/admitted definitions, certify needed floor-Li events by rational bounds, and retain symbolic original w=21/[10 log(221/2)]. Test all original triples for pre/post completion. Predictions are +4w(1-w) and -4w^2 versus zero post-response. This is a bounded independent review, not a large new mask scan and not a full #915 coefficient embedding.

### C. Authority, Continuity And Limits

Canonical actual-prime VF bound remains OPEN. Original floor, strict history, endpoint identity and conditional finite-C consumer were inspected in Lean source. No local Lean execution or source edits are permitted.

Strongest explicit compiled comparator retained: native_mertens_near_uniform_window_error_closed, b_cert=7/8-7/(64*N_pack), with EVERY positive loss. Exact hosted run 42552018910, head 77ee815846d6d534c866f0752aa33b84c385610a, is completed/success. Its actual job log 128949473700 records five standard-axiom live closures; all 911 relevant pre-existing source/audit blobs match current main. The actual endpoint, count definitions, native transfer and audit source were retrieved. This reuses scoped evidence, not a new main build or independent proof of the entire analytic corpus. Stronger IR is accepted PAPER_PROOF, not a compiled endpoint; #1131 is currently open/non-draft at 621f48b34b5ace39c05aba33ff33b6d014544b4d.

TODAY=AVAILABLE for Owner MC, Analytic NT/FFR review and Wheel GD. TODAY=PENDING for Coordinator, Census, Referee and Lean at intake; YESTERDAY=CARRY_FORWARD from November 10, including Coordinator FFR/M2/M3 instructions, Owner DR/BR, Analytic IR, Wheel RC/JC, Census GC, Referee IRR and Lean #1131. Relevant mathematical claims and continuation points were read. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 contains no newer entry than October 18; original cofactor/first-bad safeguards remain.

Only this owned report on agent-reports may be written remotely. No proof branch, PR, issue, main, other report, schedule or agent launch. Final claims, evidence classifications, code and verification receipts will be appended after execution.

## Complete Divisor-Norm Recovery Test - 20261111-census-1/DZ

Synthesis prepared 2026-11-11T08:43:18Z; timestamped publication verification follows below.

### A. Most Important Mathematical Discovery

**A stronger complete-source contraction survives the registered domain, while a tempting explanation for it fails at R=7.** For genuine Euler coefficients grouped by exact gcd, let C_R(g) be the disjoint gcd sums and S_R(d)=sum_(d|g) C_R(g) the overlapping common-divisor sums. The preregistered conjecture

```text
H_Z: for every integer R>=4,
     D_S(R) := sum_(1<=d<R) S_R(d)^2 <= sum_(1<=g<R) C_R(g)^2 =: D_G(R)
```

passed strictly at all **331 eligible roots** in the frozen 333-root domain. Every full C and S vector was independently reconstructed. This is `FINITE_COMPUTATION`; H_Z remains `CONJECTURE`, not a new accepted route. It is stronger than yesterday's GC5 because Q_R=S_R(1), so Q_R^2<=D_S<=D_G would follow.

The hidden variable is **divisor-overlap multiplicity**, not merely whether two gcd classes share a factor. A pair of classes g,h appears together tau(gcd(g,h)) times. At R=7 that extra weighting adds **+10**, making the cross term less negative, even though the total norm still contracts. Thus the posthoc universal explanation "divisor weighting can only improve the ordinary cross term" is `REFUTED`. This was not an assertion by another specialist and was not the preregistered H_Z.

Independently, Owner's MC obstruction is confirmed on its literal auxiliary masked carrier: r=10, X=120, p=3, empty signature, b=101 and 115 give nonzero pre-completion rows +4w(1-w) and -4w^2, while every completed row fibre is zero. This is bounded independent verification, credited to Owner, with exact rational floor-Li certificates. It does not refute a first-bad theorem or establish a full #915 occurrence embedding.

**Admission verdict: NO_NEW_GLOBAL_GAIN.** No new uniform Mertens exponent, canonical actual-prime bound, or RH proof. The complete-source arithmetic inequality and its historical-normalized norm payment remain open.

### B. Current Authoritative Objective

`cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1`. Real trigger: 2026-11-11 03:11:02 EST; platform execution ID unavailable. Research label: `20261111-census-1/DZ`. New York report date: 2026-11-11. Final source/status refresh began 2026-11-11T08:34:26Z; main and upstream blobs were unchanged.

Main is `f7947bee036c4dddb0c36fc9f53ab46b4fa90995`. The current canonical objective is `VFCanonicalSquareVonKochStatement`: there exists C>=0 such that for every integer R>=2,

```text
|pi(R^2)-VF_can(R^2)| <= C R log R.
```

This remains open. Its classical terminal interface explicitly takes `ClassicalVonKochRHCriterion`; it must not be confused with the internally proved Mertens-energy-to-RH consumer. The latter has an unpaid arithmetic premise.

The selected actual source is the original `eulerSelfDualBilinear`, not a surrogate covariance. Its exact endpoint identity and conditional `EulerSelfDualFiniteCStatement` consumer were read in the original Lean files. Historical K includes u=0 and hence K>=1. Main's cross-route priority supersedes historical single-route queues, not source safeguards or report-only permissions.

**Baseline and proof evidence.** The strongest explicit compiled same-family comparator inspected is `RHLean.Analysis.native_mertens_near_uniform_window_error_closed`, with

```text
b_cert = 7/8 - 7/(64 N_pack),
MertensGrowthAtMost(b_cert): for every eps>0 there exists C_eps>=0,
                           for all integers n>=1, |M(n)| <= C_eps n^(b_cert+eps).
```

This does not assert the no-loss boundary bound. For the same positive L=`explicitFineLength`, the source definitions give N_pack=ceil_nat(max(1,1/(6L)))+2 and N_old=ceil_nat(max(1,1/(3L)))+2. Monotonicity gives N_pack<=N_old, hence 7/(64N_pack)>1/(48N_old). The counts were compared, not silently identified.

Observed hosted run [42552018910](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42552018910) was successful at exact head `77ee815846d6d534c866f0752aa33b84c385610a`. Actual job log 128949473700 records five passing live closures of sizes 35358, 35375, 35736, 35737 and 35753, each ending with only `propext`, `Classical.choice`, `Quot.sound`. All **911 preexisting relevant source/audit blobs** under the inspected RHLean, OAI and slot/window audit paths match current main. This is reused scoped compiled evidence, not a new main build or a new independent analytic proof. The actual endpoint, native Hecke/zeta/Mertens transfer, count definitions and live audit source were inspected. Unrelated `Wiener.lean` placeholder warnings in the log are outside these selected closures; no claim of a globally placeholder-free dependency tree is made.

The log pins Lean 4.34.1 (`5045d0056413266e57c625dcd7c365b10e377c52`), Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` and openai/math `1581d4cbdd69a0faf34b2089614fe2a814316a6a`. The accepted analytic IR1-IR4 endpoint b_IR=7/8-1/2400000000, with every positive loss, is separately `PAPER_PROOF` accepted by yesterday's Referee IRR. Its recorded fixed comparison margin is 737/3840000000000; the present run did not independently re-prove the whole IR argument or promote it to a compiled endpoint. There is no claimed new b_new against either comparator.

At refresh, #1130 is merged and #1131 is open, non-draft and unmerged, head `621f48b34b5ace39c05aba33ff33b6d014544b4d`; all 13 observed checks at that head completed successfully. #1130's local signed principal remainder and #1131's complete finite weighted principal-product approximation do not establish the full contour/IR endpoint. No CI was launched.

### C. Competing Hypotheses

**Arithmetic contraction:** the genuine C_R vector lies in a restricted part of coefficient space where the common-divisor transform contracts the complete squared norm for every R>=4. A positive D_S-D_G at any eligible root falsifies H_Z with its fixed constant 1.

**Multiplicity obstruction:** overlapping divisor membership incurs diagonal multiplicity which ordinary negative cross terms need not pay. A failure would show that GD1's exact reconstruction cannot itself be spent as a norm contraction. Neither an identity nor arbitrary-vector linear algebra implies H_Z: the genuine boundary control R=3 already fails the unqualified all-R version.

**Third possible explanation:** H_Z may survive while the extra shared-factor cross term is positive. This occurred. Consequently local sign improvement is neither the observed mechanism nor a necessary condition for total contraction.

The MC secondary test had fixed upstream predictions, not a newly fitted hypothesis: the current mask changes under multiplication by the completion variable, so an unmasked divisor identity should leave a nonzero commutator. A nonzero completed fibre or disagreement with the predicted symbolic rows would have challenged Owner's asserted example.

### D. Experimental Design

For integer R>=2, set N=R-1, X=R^2-1 and M(t)=sum_(1<=n<=t)mu(n), including M(0)=0. The complete source and all normalizers are

```text
A_(a,b) = mu(a)mu(b) floor(X/(ab)), 1<=a,b<=N;
C_R(g) = sum_(gcd(a,b)=g) A_(a,b), 1<=g<=N;
S_R(d) = sum_(d|a,d|b) A_(a,b) = sum_(d|g) C_R(g);
Q_R = sum_g C_R(g) = S_R(1) = 2M(N)-M(X);
K_R = max_(0<=u<R) (M(u)-1)^2/(u+1).
```

All ordered pairs are retained; the C++ upper triangle uses multiplicity 2 off the diagonal. Squareful a or b contribute their actual zero Mobius weight. No physical pair is deduplicated because it has the same product. The floor counts all k with abk<=X; it is not a new pair-admission predicate. The reported pair diagonal treats A_(a,b) as a floor-weighted atom, not each k as a separate unit-weight atom. No prime-owner, historical/current mask, or NNS zero-target covariance is substituted for this Euler carrier.

Frozen roots: every R=2..256; 511,512,513,549,1023,1024,1025,2047,2048,2049,4095,4096,4097; every R=5529..5593. Total 333; H_Z applies to 331. The high window was held out for H_Z after registration, but selected using yesterday's known GC5 excursion, so it is an adversarial window rather than an unbiased statistical sample. R=2 and 3 were excluded controls before execution. There was no post-result range or constant adjustment.

The primary program independently sieves mu and M through 31,281,648, reconstructs the full ordered source and every C,S, then computes complete norm decompositions. The verifier does not import that sieve: it trial-factors historical coefficients, obtains larger M by the quotient-block recurrence M(n)=1-sum_(j>=2)M(floor(n/j)), and uses Wheel's GD1 smooth-rectangle formula to recover every S and then every C by Mobius inversion.

Specifically, B_d=floor(N/d), H_d(B_d) consists of positive integers <=B_d supported on primes dividing d, including 1, A_h=floor(B_d/h), T=floor(X/(d^2 h k)). The verifier independently evaluates

```text
S_R(d)=mu(d)^2 sum_(h,k in H_d(B_d)) [M(A_h)+M(A_k)-M(T)],
C_R(g)=sum_(k<=N/g) mu(k) S_R(gk).
```

Every one of 1,708,570 rectangles satisfies max(A_h,A_k)<=T<(A_h+1)(A_k+1). This finite validation supports the *formula's implementation*, not independent acceptance of all of GD1-GD4's paper proofs.

### E. Executed Results

Claim `DZ1` (`FINITE_COMPUTATION`): all 333 independently reconstructed C/S vectors, Q, M(N), M(X), K, earliest maximizing u, and D_G/D_S agree exactly. There were no mismatches. The direct tau-weighted pair Gram was separately recomputed for all R<=256 and R=549,5561, totaling 257 roots. The 768,974,775 counted nonzero ordered coefficient pairs are not the number of expanded k-occurrences.

| R | Q_R | D_G | D_S | D_S-D_G |
| --- | ---: | ---: | ---: | ---: |
| 2 | 3 | 9 | 9 | 0 |
| 3 | 2 | 4 | 8 | 4 |
| 4 | -1 | 35 | 11 | -24 |
| 5 | 0 | 104 | 40 | -64 |
| 7 | 1 | 55 | 32 | -23 |
| 11 | 1 | 83 | 68 | -15 |
| 15 | -7 | 223 | 142 | -81 |
| 17 | 5 | 173 | 138 | -35 |
| 21 | 1 | 357 | 338 | -19 |
| 549 | -186 | 213476 | 70928 | -142548 |
| 5561 | 2554 | 19073482 | 7448644 | -11624838 |
| 5565 | 2514 | 18279560 | 7315350 | -10964210 |

K_R=1 at R=2,3,4,5, earliest maximizer u=0. At every tested R>=6, K_R=3/2, earliest maximizer u=5. These are computed facts for the tested roots, not an assumed global constant.

| R | Q_R^2/(R^2 K_R) | D_G/(R^2 K_R) | D_S/(R^2 K_R) |
| --- | ---: | ---: | ---: |
| 2 | 9/4 | 9/4 | 9/4 |
| 3 | 4/9 | 4/9 | 8/9 |
| 4 | 1/16 | 35/16 | 11/16 |
| 5 | 0 | 104/25 | 8/5 |
| 7 | 2/147 | 110/147 | 64/147 |
| 11 | 2/363 | 166/363 | 136/363 |
| 15 | 98/675 | 446/675 | 284/675 |
| 17 | 50/867 | 346/867 | 92/289 |
| 21 | 2/1323 | 34/63 | 676/1323 |
| 549 | 7688/100467 | 426952/904203 | 141856/904203 |
| 5561 | 13045832/92774163 | 38146964/92774163 | 14897288/92774163 |
| 5565 | 1404488/10323075 | 7311824/18581535 | 27868/176967 |

The complete floor-atom square reconstruction is Q^2=P+I+O, where P=sum_(a,b)A_(a,b)^2, I=D_G-P is the full within-gcd cross contribution, and O=Q^2-D_G is the full cross-gcd contribution. Both orientations are included.

| R | P | I | O | Q^2 |
| --- | ---: | ---: | ---: | ---: |
| 549 | 209519833116 | -209519619640 | -178880 | 34596 |
| 5561 | 2208675199789504 | -2208675180716022 | -12550566 | 6522916 |
| 5565 | 2215036879553890 | -2215036861274330 | -11959364 | 6320196 |

P is directly accumulated by C++; its internal within/cross decomposition recombines exactly. The independent Python method checks the grouped totals but does not separately reconstruct the floor-atom P. Independence is claimed for the complete C/S vectors and listed totals, not for every derived subledger entry.

The second full reconstruction is D_S=T_diag+W, where T_diag=sum_g tau(g)C_g^2 and W=2sum_(g<h)tau(gcd(g,h))C_g C_h.

| R | T_diag | W | D_S | Extra diagonal T_diag-D_G | Extra shared cross W-O |
| --- | ---: | ---: | ---: | ---: | ---: |
| 7 | 76 | -44 | 32 | 21 | 10 |
| 21 | 1028 | -690 | 338 | 671 | -334 |
| 549 | 841962 | -771034 | 70928 | 628486 | -592154 |
| 5561 | 54173602 | -46724958 | 7448644 | 35100120 | -34174392 |
| 5565 | 52672080 | -45356730 | 7315350 | 34392520 | -33397366 |

At 549, M(548)=3 and M(301400)=192. At 5561, M(5560)=5 and M(30924720)=-2544. These independently computed endpoints recover Q=-186 and 2554.

Exact trial-prime dyadic near-resonance witnesses were found and checked at all 78 roots above 256. Examples (p,q,t): R=549 gives (277,557,1109); R=5561 gives (2803,5563,11213); R=5565 gives (2803,5569,11213). Each has p in [R/2,R), q in [R,2R), t in [2R,4R), t=4p+/-1, pq<=R^2-1, qt<=4R^2-1. The rational z=(R^2-1)t/((4R^2-1)p) satisfies z>0, z!=1, |z-1|<=1/R exactly. These are genuine prime geometry controls. They do not identify a Hecke phase with a gcd coefficient, or establish a causal explanation of H_Z.

### F. Exceptional Cases And Counterexamples

Claim `DZ2a` (`REFUTED`, finite certificate): the unrestricted extension D_S<=D_G for all R>=2 fails at R=3, with C=(0,2), S=(2,2), D_G=4, D_S=8. This was known and declared before the experiment; it is not a new discovery or a refutation of H_Z.

Claim `DZ2b` (`REFUTED`, posthoc auxiliary principle): W<=O for every R>=4 fails first at R=7 within the exhaustive small range. The complete vectors, indexed from 1, are

```text
C_7 = [-6,4,1,0,1,1];    S_7 = [1,5,2,0,1,1].
O=-54; W=-44; W-O=10.
Extra weighted pairs: (2,6) contributes 8; (3,6) contributes 2.
D_S-D_G = 21-54+10 = -23.
```

The culprit is positive products among classes sharing a divisor. This is exact arithmetic, not numerical correlation. It explains why paying each extra shared-factor interaction by a negative sign is untenable, even where H_Z holds. The all-R assertion was formulated for this explanatory audit after inspecting the registered outputs; it was not the preregistered target.

Within the eligible domain, the largest D_S/D_G is **338/357 at R=21**, not a fitted universal constant. The smallest absolute slack D_G-D_S is **15 at R=11**. Full short certificates:

```text
C_11=[-8,2,1,0,0,3,2,0,0,1]
S_11=[1,6,4,0,1,3,2,0,0,1]
C_21=[-4,-6,-10,0,-5,12,0,0,0,4,3,0,2,2,1,0,1,0,1,0]
S_21=[1,12,3,0,0,12,2,0,0,4,3,0,2,2,1,0,1,0,1,0]
```

The largest eligible Q^2/D_G is 1580049/4569890 at R=5565. This is incidental held-out information about yesterday's GC5, not the purpose of rerunning its old roots. The largest observed D_S/(R^2K_R) is 8/5 at R=5; no universal bound is inferred or preregistered from it.

Claim `DZ4` (`FINITE_COMPUTATION`, independent verification of Owner MC): define the original auxiliary response f_b(n) using the p=3 squarefree, p-free, empty-lower-signature base, b clipped by pb>X, right cofactor n/p admitted by p(n/p)<=X, and both active integers in 100<n<121. Its symbolic weight is (1_prime(b)-w)(1_prime(n)-w), w=21/[10log(221/2)]. Enumerate every q>10,a,k>=1 with qak<=120:

```text
Pre_b = sum lambda(q)[mu(a)+mu(aq)] f_b(aq),
Post_b= sum lambda(q)[mu(a)+mu(aq)] f_b(aqk),
lambda(q)=floor(Li_2(q))-floor(Li_2(q-1)).
```

All 449 triples were enumerated, without replacing f(aq) by f(aqk) silently. Active odd squarefree sites are 101,103,105,107,109,111,113,115,119; right sites are exactly 105 and 111, with admitted cofactors 35 and 37. Both left sites 101 and 115 are clipped; 101 is prime and 115=5*23 is composite.

| Endpoint n | 14 | 15 | 20 | 21 | 34 | 35 | 110 | 111 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Certified floor Li_2(n) | 6 | 7 | 8 | 9 | 13 | 13 | 31 | 31 |

Hence lambda(15)=lambda(21)=1 and lambda(35)=lambda(111)=0. The only nonzero pre-atoms are (q,a,k,mu(a)+mu(aq))=(15,7,1,-2),(21,5,1,-2). Direct enumeration gives

```text
Pre_101=4w(1-w)>0; Pre_115=-4w^2<0;
Post_101=Post_115=0, with every grouped (q,a*k) fibre zero.
e_10(105)=2; e_10(111)=0;
Pre_b-Post_b = 2 sum_(active n) f_b(n)mu(n)e_10(n).
```

The floor certificates use monotone rational Riemann bounds, mesh 1/128, with log enclosures from 40 terms of the atanh series plus an explicit tail and outward integer rounding at scale 10^30. Every floor interval resolves at that first mesh, width <1/100. The same series proves 4<log(221/2)<5, hence 0<w<1 and the strict row signs. No floating-point sign decision is involved. Full rational certificates and the executed program are appended.

This disproves transferring a zero completed-response norm to the original auxiliary row without its commutator. The correction is not uniformly one-signed across the two rows. It does **not** assert that the auxiliary coefficient system is the complete #915 physical ledger, or that either example satisfies an original first-bad predicate.

### G. Hidden Variables And Arithmetic Classification

Exact gcd groups form a disjoint partition; common-divisor groups overlap. The correct hidden variable is tau(gcd(g,h)), together with its diagonal tau(g) cost. C_g=0 for squareful g, but squarefreeness does not force signs among the remaining C_g. The R=7 same-sign shared pairs are sufficient to defeat automatic negative-credit reasoning.

Define E=sum_g(tau(g)-1)C_g^2, O=2sum_(g<h)C_gC_h and J=2sum_(g<h)(tau(gcd(g,h))-1)C_gC_h. Then

```text
D_S-D_G=E+O+J,
D_S-Q^2=sum_(d>=2)S_d^2=E+J>=0.
```

Thus J must satisfy J>=-E, not J<=0. At R=21, E+J=337 and -O=356, leaving slack 19. At R=5561, E+J=925728 and -O=12550566. The small-R challenge can therefore come from large subordinate divisor energy relative to ordinary cancellation, rather than from the largest absolute Q. This is an exact accounting interpretation; it is not yet an independent bound on either side.

On the separate masked source, Owner's e_r(n) counts proper divisors q>r with mu(q)=+1 and lambda(q)=1. It records an actual incidence multiplicity lost by replacing the current source mask with its completed counterpart. Mask transport and gcd overlap are distinct obstructions and are not identified as one quantity.

### H. Mathematical Interpretation

Claim `DZ2c` (`PAPER_PROOF`, elementary identity; self-audited, independent review pending): for any finite real vector C indexed by 1..N and S_d=sum_(d|g)C_g,

```text
sum_d S_d^2 = sum_(g,h) tau(gcd(g,h)) C_g C_h.
```

Proof: expand each finite square and interchange finite sums. The coefficient of the ordered product C_g C_h is the number of positive d dividing both g and h, exactly tau(gcd(g,h)). Separating diagonal and unordered pairs gives the discriminator and E/O/J identities above. No positivity, statistical independence or arithmetic source restriction enters this algebra. Therefore it cannot by itself prove H_Z. It is a supporting accounting identity, not a new cancellation theorem.

The surviving phenomenon asks for a **global, coefficient-specific** restriction. It is not enough to prove negative ordinary inter-gcd covariance, because the subordinate energy sum_(d>=2)S_d^2 is an additional bill. It is not enough to prove negative J, because E is positive. Conversely J may be positive while O pays the complete bill. The exact reformulation is useful for falsification but is not an inverse theorem: defining a bad event as E+J>-O would merely rename the target.

### I. Proposed Theorem Or Conjecture

Claim `DZ3` (`CONJECTURE`): for the genuine Mobius function and the original cutoff X_R=R^2-1, for every integer R>=4, with C_R and S_R exactly as in D,

```text
sum_(d=1)^(R-1) [sum_(1<=a,b<R,d|a,d|b) mu(a)mu(b)floor((R^2-1)/(ab))]^2
 <= sum_(g=1)^(R-1) [sum_(1<=a,b<R,gcd(a,b)=g) mu(a)mu(b)floor((R^2-1)/(ab))]^2.
```

The constant is exactly 1, chosen before all registered computations. No extra prime-distribution, K, first-bad, random-sign or owner hypothesis is allowed. R=3 is a known exception to the wider statement; R=2 is equality. Finite evidence: 331 eligible roots, including all R=4..256 and the stated high/near-dyadic probes, with zero violations. The strongest attempted held-out falsification was the full 5529..5593 excursion window, not a single favorable sample.

The first missing proof is a genuine arithmetic restriction showing E_R+O_R+J_R<=0 uniformly; no already-proved theorem checked in this run supplies it. Its value would be a complete-source signed restriction strictly stronger than GC5, not yet a target-sized estimate. An independent all-scale derivation is required before route admission, and a separate scale bound is still needed for a global consumer.

### J. Relationship To The Proof Objective

#### Mandatory Five-Stage Capsule

1. **BASELINE / DEPENDENCY RECEIPT.** The scoped compiled comparator is b_cert and the separately accepted paper comparator is b_IR, with positive-loss quantifiers and dependency receipts in B. Finite-C and VF-to-RH implications do not prove their premises. No new exponent is asserted.
2. **FOUR-WAY SOURCE MAP.** The following table records exact maps and barriers. Only Euler-to-Mertens endpoints is an equality here; different arithmetic errors are not equated.

| Field | Euler / finite AC | VF / prime-side | NNS / OAI | Square blocks / native HIGH |
| --- | --- | --- | --- | --- |
| Actual source | Complete ordered mu(a)mu(b) floor(X_R/(ab)), a,b<R; gcd and common-divisor repartitions | Complete square-root wheel at X_R, including d>X_R virtual fractional terms; separate clipped p=3 auxiliary MC row | Ideal-labelled compensated LOW/HIGH tuples, Hecke weights, original Hermitian Gram and principal return | Complete M(R^2-1), historical M(R-1), and native fixed-Lambda LOW/HIGH prefixes |
| Scale / normalizer | Integer R>=2, X_R=R^2-1, exact K_R; Q^2/(R^2K_R) | Wheel bound at R log R; canonical target at R^2; auxiliary MC r=10 corresponds to R=11 | Height, ideal/phase masks and positive-loss exponent of the original source | Complete-prefix exponent, not merely a shell increment; historical K for finite-C |
| Proven map | `eulerSelfDualBilinear_eq_two_mertens_sub_endpoint`, exact Q=2M(N)-M(X) | `finiteWheel_squareFractional_centered_eq_reference_sub_pi`: F_R-D_R=L-pi(X_R), L=Li_2(X_R); original virtual terms retained | Certified native endpoint gives a Mertens bound, a one-way global implication | Exact Euler endpoint identity plus `squareRootEndpointAmplification_of_eulerFiniteC` under its open uniform premise |
| Edge to selected C/S | EXACT_IDENTITY by finite grouping; GD1 separately PAPER | NOT_EQUIVALENT to Q: actual-prime discrepancy is not bilinear Mobius endpoint; original weighted coupling OPEN_BRIDGE | OPEN_BRIDGE: no coefficient/occurrence-preserving isometry from Hecke tuples to these C/S norms | EXACT_IDENTITY only for the full scalar endpoint; shell-to-full-prefix substitution invalid |
| Source anchors | EULER_FRACTIONAL_COUPLED line 41; ENDPOINT_GATE line 28; K in SquareRootLegalAncestryGramReduction line 42 | CompleteSquareRootWheelFractionalBoundary line 453; MC base/carrier/weight sources in provenance table | VF919WindowErrorClosure line 128, native transfer and live audit | ENDPOINT_GATE lines 105,115,209; SquareRootMertensEndpointAmplification |

3. **FIRST SIGNED LOSS.** The selected chain's losses and exact outstanding bills are below. These are an audit of candidate uses, not claims that all are binding in the best OAI proof.

| Source / declaration | Exact input and first inequality | Tax / consumer / mask | Already paid? Recovery checked | Unresolved complement / falsifier |
| --- | --- | --- | --- | --- |
| EULER_FRACTIONAL_COUPLED:41, original Q | Atomwise triangle discards every signed product: abs(Q)<=sum abs(A)<=X(1+log N)^2 | O(R^2 log^2 R) rather than historical R sqrt(K); original ordered source | Exact pointwise convolution and ENDPOINT_GATE:28 restore Q=2M(N)-M(X), but not a bound | Endpoint M(X) is still global; numerical small Q is not payment |
| This report D/H, exact-gcd grouping | Cauchy-Schwarz gives Q^2<=(R-1)D_G; discarding O instead would need GC5 | sqrt(R-1) in amplitude; historical consumer needs fixed constants | GD1 reconstructs C; finite negative O does not prove GC5 | Actual complete O, plus scale of D_G; prior GC local sign failures retained |
| This report H, common-divisor transform | Dropping W loses tau-weighted cross terms and leaves T_diag; treating transform as isometry also loses E | Exact bill E+O+J; H_Z has fixed constant 1, no exponent yet | Finite Gram identity is paid algebra; already-proved Euler identities do not supply the inequality | H_Z open; R3 defeats arbitrary-source contraction, R7 defeats J<=0 |
| Wheel GD1/GD2 paper reconstruction | Taking absolute values of each M(A_h)+M(A_k)-M(T) loses their joint signs and all rectangle cross terms | GD power-bound route returns the supplied Mertens exponent, not a new one | Already-proved Mobius hyperbola and restricted-floor identities support reconstruction; GD3/GD4 remain separate paper claims | Historical-normalized complete norm bound remains unpaid |
| Owner MC; raw-parent splice carrier/weight, weighted-owner Fubini | Replacing f(aq) by f(aqk) before divisor completion erases 2sum f(n)mu(n)e_r(n) | A zero completed row need not control original row; exact original masks required | Unmasked divisor-convolution cancellation does not transport with this mask | Verified r10 positive and negative rows with every completed fibre zero |
| ENDPOINT_GATE:115 amplification | abs(M(X)-1)<=2abs(M(N)-1)+1+abs(Q) | Once finite-C is proved, A=(C+3)^2 suffices; K>=1 | Conditional return is already proved; this harmless constant is not the missing estimate | Uniform C before R remains open, not repaired by a finite observed norm ratio |

4. **PAID RECOVERY TEST.** The certified pointwise Mobius convolution, exact triple Fubini and full endpoint identity recover the signed scalar exactly. The finite-wheel physical-plus-virtual theorem restores its own prime-count source, not Q or its norm. The restricted-floor smooth identity helps GD1's reconstruction, not a sign inequality. The closed OAI endpoint bounds actual Mertens growth but lacks a source-faithful C/S moment transfer that would improve its own exponent. The original MC mask prevents unmasked completion from becoming such a transfer. No paid cross-route theorem inspected closes the outstanding complete interaction. Neither a proper positive cofactor fibre nor a local Gram identity pays the full complementary source.

For precision, the already-reported GD2 paper loss is explicit: given a genuine all-prefix |M(n)|<=A n^c, c>1/2 fixed before R, put w_c(p)=(1-p^(-c))^(-2), W_c(d)=product_(p|d)w_c(p), Z_c=product_p(1+w_c(p)/p^(2c)), Y_c=product_p(1+w_c(p)^2/p^(4c)). Triangle on the three Mertens values gives |S_R(d)|<=3A X^c mu(d)^2 W_c(d)/d^(2c); inversion and nonnegative summation give D_G<=9A^2 Z_c^2 Y_c X^(2c). These constants are scale-independent for fixed c>1/2, but the output is R^(4c), so substituting any c>b_cert and returning through GD3 only recovers the earned exponent. This quantitative paper transfer is not an independently paid improvement, and this run verifies its reconstruction finitely rather than certifying its all-scale bound.

5. **NET RESULT / ADMISSION VERDICT.** `NO_NEW_GLOBAL_GAIN`. H_Z is a plausible stronger complete-source restriction but only finitely tested. Even if proved, H_Z plus an independent D_G<=B R^2K_R (uniform B) would give finite-C for R>=4 with C=sqrt(B); the R2 control requires C>=3/2 and R3 requires C>=2/3. Taking C=max(sqrt(B),3/2) handles all R>=2 and every valid envelope K>=K_R. The certified amplification then gives A=(C+3)^2 and the internal energy/RH consumer. The proposed D_G bound is not proved here, and today's GD3 paper warns its complete norm is already exponent-equivalent to Mertens. No circularly renamed target is admitted as new arithmetic. The one-step finite-AC exponent iteration also requires a genuinely improved uniform input and renewed estimates; no such input was obtained.

### K. Falsification And Uncertainty Audit

All mathematical decisions are integer, rational or symbolic. C++ uses int64 linear sums and __int128 energies; at the frozen maximum, the crude atom-mass bound X(1+log N)^2 is below 3*10^9, and even the much looser N^2 X^2 bound fits __int128. Python uses unbounded integers and fractions. No probabilistic primality test, seed, or floating numerical inequality is involved. Timings alone are floating diagnostics.

Actual runs: primary 13.3421 s; independent verifier 9.017338562999953 s; MC 0.31237582699998256 s. Observed Python was 3.12.14; g++ 13.3.0 on Linux x86_64. Python and C++ standard libraries only. Compiler flags were `-O2 -std=c++17 -Wall -Wextra -Werror`, with assertions enabled. Python syntax compilation of the three scripts passed. No local Lean command was run, no new proof was kernel-certified, and no subprocess required by this task remains running.

The small finite domain and targeted large windows do not estimate the density of failures. H_Z could fail at an untested root, including between 257 and 510. The statement "first R7 failure" concerns the posthoc W<=O assertion and the exhaustive smaller roots only. R3 is not a failure of the registered H_Z. No finite maximum is an optimal universal constant. No first-bad hypotheses were inferred from a local event.

Reproduction commands, run from a directory containing the four appended source files:

```bash
g++ -O2 -std=c++17 -Wall -Wextra -Werror dz_probe.cpp -o dz_probe
./dz_probe dz_primary.json
python dz_verify.py dz_primary.json dz_verified.json
python dz_summary.py
python mc_verify.py
python -m py_compile dz_verify.py dz_summary.py mc_verify.py
sha256sum dz_probe.cpp dz_verify.py dz_summary.py mc_verify.py dz_primary.json dz_verified.json dz_summary.json mc_verified.json
```

The primary is O(X_max + sum_R R^2 log R) with gcd operations and O(X_max) memory. The independent method uses quotient-block recursion and the finite smooth rectangles stated above; it does not rely on primary intermediate mu/M values. The summary program only analyzes the frozen outputs and validates prime-witness conditions. It does not add roots. Full C/S vectors are retained in the reproducible primary JSON; this report includes compact decisive certificates rather than duplicating the entire 1.9 MB file. Hashes and exact source code are appended.

### L. Specialist Handoffs

Two-day continuity was completed before preregistration. At intake, today's Coordinator, Census, Referee and Lean reports were absent. At the final refresh, today's Coordinator, Referee and Lean remain `TODAY=PENDING`; their November 10 findings are `YESTERDAY=CARRY_FORWARD`. This invocation now supplies today's Census. Today's Owner MC, Analytic NT/FFR review and Wheel GD were actually retrieved, not assumed to have run.

| Specialist | Consumed continuity and precise handoff |
| --- | --- |
| Proof Architect | Nov10 FFR/M2/M3 requests a changed complete-source test. H_Z is new relative to GC5 and GD1; R7 shows why divisor weighting is not uniformly favorable. No route promotion or campaign change is requested on finite evidence alone. |
| Owner Payment | Nov10 DR/BR and Nov11 MC read. Your two MC rows were independently confirmed with rational Li_2 floors and literal masks; see DZ4. The full #915 embedding remains unclaimed. |
| Analytic Type II | Nov10 IR and Nov11 NT read. IR remains accepted paper, not newly re-proved here. NT's covariance-minimizer obstruction reinforces the need to retain the full error, but no Nyman-to-Euler norm equality is inferred. Is there a genuinely source-faithful restriction stronger than current arbitrary-vector Gram algebra? |
| Finite Wheel | Nov10 RC/JC and Nov11 GD read. All 1,708,570 GD1 rectangles and recovered C/S vectors passed the independent finite test. Please assess whether genuine coefficients force H_Z or admit a constructed failure; GD3's exponent-equivalence warning is retained. |
| Adversarial Referee | Nov10 IRR and GC review carried. Review DZ2b's R7 certificate, the distinction E/O/J, the independence limits, and the fixed all-R>=4 conjecture. Independent finite evidence is not acceptance of H_Z or all of GD. |
| Lean Verification | Nov10 #1131 report read; current head and green checks verified. `NO_NEW_THEOREM_TO_FORMALIZE` from H_Z: it is conjectural. Only a necessary independently accepted identity or finite falsifier would justify work; no request for duplicate algebra or a filler PR. |

The external inbox was fetched at blob `038018145c0fddb2f6306c0712373adf9cd1ea52`; no entry newer than October 18. Its source/cofactor and genuine first-bad safeguards remain applicable; obsolete routing priorities do not override live main. Report/blob receipts are appended.

### M. Ranked Experimental Hypothesis Portfolio

| Rank | Candidate and status | Why it matters / evidence | Next discriminator / disposition |
| --- | --- | --- | --- |
| 1 | H_Z, fixed all-R>=4 divisor-norm contraction: CONJECTURE | Complete source, stronger than GC5; 331 strict passes including two mandatory roots and an adversarial high window | Seek an independent arithmetic restriction controlling subordinate divisor energy, or a newly justified targeted falsifier. Promote for theoretical review, not route admission. |
| 2 | Current-mask commutator indispensable: FINITE_COMPUTATION | Owner MC independently confirmed, both row signs, zero completed fibres | Full source embedding or exact mask-invariant subclass is needed before any global transfer. Preserve obstruction. |
| 3 | Extra divisor weighting always helps: REFUTED | R7 has J=+10; R11 also has positive J | Reject as a universal mechanism. Do not repair by silently changing the domain. |
| 4 | Complete historical-normalized norm bound: CONJECTURE / CONDITIONAL consumer | Would be quantitative payment, but a finite maximum and GD's existing exponent do not provide it | No fitted universal constant; suspend unmodified larger scans absent a new mechanism. |
| 5 | GC5, Q^2<=D_G: CONJECTURE | Prior finite evidence retained; follows from H_Z where that holds | Do not repeat unchanged GC5 tables as new research. Keep independent of GD3's paper equivalence route. |

### N. Next-Run Resume Capsule

Execution is COMPLETE after publication verification. The preregistration above is preserved unchanged, including its original IN_PROGRESS status as a historical checkpoint. Main and relevant report sources were unchanged at 08:34:26Z. Only this role's dated report is written remotely; no Lean, other report, issue, PR, branch, workflow, merge, schedule or agent launch was changed.

Completed: baseline and live dependency receipt; two-day handoffs; registered 333-root complete-source experiment; independent smooth reconstruction; exact weighted Gram checks; 78 near-resonance geometry controls; independent Owner MC rational certificates. New arithmetic finding: divisor overlap can add positive cross interaction while a stronger total norm contraction survives. New candidate: fixed H_Z. Unpaid: a uniform genuine-source proof of H_Z and, separately, a target-scale norm payment.

**Single highest-value next attack:** derive or refute a source-faithful control of subordinate divisor energy sum_(d>=2)S_R(d)^2 by -O_R, using GD1's actual smooth-rectangle coefficients before taking absolute values. Start from the sharp R21 configuration and R7 positive-J obstruction, and require an independently meaningful structural hypothesis rather than defining the exceptional event by the desired inequality. Only then preregister a changed adversarial test on roots not used here. Do not rerun this frozen census or merely increase the cutoff without that new question.

The initial checkpoint was published in commit `bbda77d8cbfa3cb342467a7ced4b3b06bc076f09`, blob `fbfd91c6fafdae35503da02b3aebd9c2d9fcc87a`, with exact readback. Final synthesis publication is recorded in the receipt appended after a successful commit/readback; no publication claim rests solely on an attempted write.

## Provenance And Reproduction Appendices

### Immutable Main Sources

All links below resolve at the observed main commit, not a floating branch.

| Path | Blob SHA |
| --- | --- |
| [AGENTS.md](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/AGENTS.md) | `c9c89f01b90b526de9f3e8ea92478e36504711b6` |
| [CURRENT_PROOF_CONTRACT.md](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/CURRENT_PROOF_CONTRACT.md) | `95566e37c8eaeb99ee680660df4f9d2e06ea5038` |
| [docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md) | `e922d4ba9362a1ae196af8f6de88f7417f92087c` |
| [docs/COORDINATE_ATLAS.md](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/docs/COORDINATE_ATLAS.md) | `cd0419d00a37739fe5a292f5cb738e33213949d5` |
| [docs/PROOF_DEPENDENCY_DAG.md](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/docs/PROOF_DEPENDENCY_DAG.md) | `eee764cefe70035a9f6c7df26ad787fbfd0fb233` |
| [research/EULER_FRACTIONAL_COUPLED_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/EULER_FRACTIONAL_COUPLED_20261027.lean) | `e6c4b1690e497760d366e36b28a1f7aa60e19f85` |
| [research/EULER_SELF_DUAL_POINTWISE_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/EULER_SELF_DUAL_POINTWISE_20261027.lean) | `c327c556f39ee7014fd774b24d0f95a1ece050e0` |
| [research/EULER_SELF_DUAL_FINITE_C_BRIDGE_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/EULER_SELF_DUAL_FINITE_C_BRIDGE_20261027.lean) | `e97561ef330a9996fd807d8910369f0698147b01` |
| [research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean) | `e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73` |
| [research/MERTENS_SIGNED_HYPERBOLA.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/MERTENS_SIGNED_HYPERBOLA.lean) | `d199571f19346797229a25b0fa53c6e80499999f` |
| [research/CompleteSquareRootWheelFractionalBoundary.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/CompleteSquareRootWheelFractionalBoundary.lean) | `ecb482e52deeee5e9b3853592a3ffdace662d2ff` |
| [research/oai_434/VF919WindowErrorClosure.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919WindowErrorClosure.lean) | `f629db1b2b65d6ec042ac9432397d4b6316200c6` |
| [research/oai_434/VF919ExplicitSquareBlockPacking.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919ExplicitSquareBlockPacking.lean) | `32999039fdeea99c58a070c1c4ee9c140720dd44` |
| [research/oai_434/VF919ExplicitFixedSourceSlotCount.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919ExplicitFixedSourceSlotCount.lean) | `bad5aab0a60e96d19e7c9550cd7c0a072288bc0f` |
| [research/oai_434/VF919NativeStrictMertens.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919NativeStrictMertens.lean) | `b33a4883e1ddb0551b0f11f062bce46680d87450` |
| [scripts/lean/window_error_closure/WindowErrorClosureAudit.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/scripts/lean/window_error_closure/WindowErrorClosureAudit.lean) | `1f17f9401a63d16227db2e2aad020b9f74bc5f4e` |
| [research/MERTENS_EXPONENT_ENVELOPES.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/MERTENS_EXPONENT_ENVELOPES.lean) | `655b896e8d5a41c9f8fc3c456eae3944a98bfefe` |
| [research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean) | `79030d70e8d3e0d08eef9bac53fef95c36eca2fb` |
| [RHLean/Proof/SquareRootMertensEndpointAmplification.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/RHLean/Proof/SquareRootMertensEndpointAmplification.lean) | `7793d7bfd842348facf62a7ad856bc802ffcd15c` |
| [RHLean/Proof/SquareRootLegalAncestryGramReduction.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/RHLean/Proof/SquareRootLegalAncestryGramReduction.lean) | `1270d4d91c53b50b110d10014f223f427fb7a575` |
| [RHLean/Analysis/FiniteWheelRestrictedFloor.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/RHLean/Analysis/FiniteWheelRestrictedFloor.lean) | `94c4d4420fc58cd87d92780c6265decd2cad7e66` |
| [research/DyadicPrimeNearResonance.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/DyadicPrimeNearResonance.lean) | `f416e0149b73656e30a7f68a3934a937353d3f8d` |
| [research/VF_MID_FLOOR_LI_SIGNED_POPULATION_BALANCE.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/VF_MID_FLOOR_LI_SIGNED_POPULATION_BALANCE.lean) | `9a9336dad72171b6d572a1c1ae88d1ae8b56b530` |
| [research/VF_MID_FIRST_BAD_ACTIVE_CLIPPED_BOUNDARY.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/VF_MID_FIRST_BAD_ACTIVE_CLIPPED_BOUNDARY.lean) | `12143ee0681785b9b23cd687337e9f5937c0b87e` |
| [research/VF_MID_ONE_BLOCK_SOURCE_TO_RANK_INLET.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/VF_MID_ONE_BLOCK_SOURCE_TO_RANK_INLET.lean) | `dd4ff316e51501a3ca9404e0c2c3e754f154ac6e` |
| [research/VF_MID_FIRST_BAD_ACTIVE_RAW_PARENT_SPLICE.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/VF_MID_FIRST_BAD_ACTIVE_RAW_PARENT_SPLICE.lean) | `dd872ccdf0eac1e78f998aa77f357f68df53f76e` |
| [research/VF_MID_915_GLOBAL_MOBIUS_PHYSICAL_WELD_20261021.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/VF_MID_915_GLOBAL_MOBIUS_PHYSICAL_WELD_20261021.lean) | `5e3212e20666b9ed7f13d6bd9ebadfad88338eaa` |
| [research/VF_MID_FIRST_BAD_WEIGHTED_OWNER_FUBINI.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/VF_MID_FIRST_BAD_WEIGHTED_OWNER_FUBINI.lean) | `4679d7edae521dd4d9f0238aa4201445b1fdb9a9` |
| [research/VF_MID_FIRST_BAD_FINAL_AGGREGATE_CONTRACTION.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/VF_MID_FIRST_BAD_FINAL_AGGREGATE_CONTRACTION.lean) | `47e4255f76fb3387d1b12d0fa185cffde2744e63` |
| [research/GLOBAL_RETURNED_CORE_FIRST_OWNER_CELLS.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/GLOBAL_RETURNED_CORE_FIRST_OWNER_CELLS.lean) | `5ca177548e91dd8bc6535e9913b29dc81cdfccea` |

### Immutable Report Inputs

Intake agent-reports commit: `308f86d1f39e025dae3a329755a402ba29f88e2c`. November 10 Coordinator mirrors were byte-identical. Final refresh confirmed unchanged upstream inputs. These are evidence/continuity documents, not proof authority.

| Report | Blob SHA |
| --- | --- |
| [2026-11-10/00-coordinator-am.md](https://github.com/OVVO-Financial/RH_Lean/blob/308f86d1f39e025dae3a329755a402ba29f88e2c/research/agent_reports/2026-11-10/00-coordinator-am.md) | `4d55b2893f974656c6aa14e48b243827fa8308f8` |
| [2026-11-10/90-coordinator-pm.md](https://github.com/OVVO-Financial/RH_Lean/blob/308f86d1f39e025dae3a329755a402ba29f88e2c/research/agent_reports/2026-11-10/90-coordinator-pm.md) | `4d55b2893f974656c6aa14e48b243827fa8308f8` |
| [2026-11-10/10-owner-payment.md](https://github.com/OVVO-Financial/RH_Lean/blob/308f86d1f39e025dae3a329755a402ba29f88e2c/research/agent_reports/2026-11-10/10-owner-payment.md) | `84afec90414b2394a61b51df46c07b6b540e5942` |
| [2026-11-10/20-analytic-type-ii.md](https://github.com/OVVO-Financial/RH_Lean/blob/308f86d1f39e025dae3a329755a402ba29f88e2c/research/agent_reports/2026-11-10/20-analytic-type-ii.md) | `7ed3a39bec4796f4173b692064af872ea8035048` |
| [2026-11-10/30-finite-wheel.md](https://github.com/OVVO-Financial/RH_Lean/blob/308f86d1f39e025dae3a329755a402ba29f88e2c/research/agent_reports/2026-11-10/30-finite-wheel.md) | `62406503a1ddbbf9330abcdc4cf761f7fbf05795` |
| [2026-11-10/40-prime-census.md](https://github.com/OVVO-Financial/RH_Lean/blob/308f86d1f39e025dae3a329755a402ba29f88e2c/research/agent_reports/2026-11-10/40-prime-census.md) | `a3cfa56072f3893dbf92a18956e1794236bde057` |
| [2026-11-10/50-adversarial-referee.md](https://github.com/OVVO-Financial/RH_Lean/blob/308f86d1f39e025dae3a329755a402ba29f88e2c/research/agent_reports/2026-11-10/50-adversarial-referee.md) | `6529562a5bb21fa192fddadaa91a758b9d125c29` |
| [2026-11-10/60-lean-verification.md](https://github.com/OVVO-Financial/RH_Lean/blob/308f86d1f39e025dae3a329755a402ba29f88e2c/research/agent_reports/2026-11-10/60-lean-verification.md) | `682b334b8f37fa4bfe2d552a1142d852a0db2afd` |
| [2026-11-11/10-owner-payment.md](https://github.com/OVVO-Financial/RH_Lean/blob/308f86d1f39e025dae3a329755a402ba29f88e2c/research/agent_reports/2026-11-11/10-owner-payment.md) | `e60f67d2192932715895f9e9b72a6fe773d4a68d` |
| [2026-11-11/20-analytic-type-ii.md](https://github.com/OVVO-Financial/RH_Lean/blob/308f86d1f39e025dae3a329755a402ba29f88e2c/research/agent_reports/2026-11-11/20-analytic-type-ii.md) | `eab26782cdd44e705e007185d6c7321d9300ca61` |
| [2026-11-11/30-finite-wheel.md](https://github.com/OVVO-Financial/RH_Lean/blob/308f86d1f39e025dae3a329755a402ba29f88e2c/research/agent_reports/2026-11-11/30-finite-wheel.md) | `dbf68d8f8b1737b4b585811dae014329614ec595` |

External handoffs: [EXTERNAL_HANDOFFS.md](https://github.com/OVVO-Financial/RH_Lean/blob/308f86d1f39e025dae3a329755a402ba29f88e2c/research/agent_reports/EXTERNAL_HANDOFFS.md), blob `038018145c0fddb2f6306c0712373adf9cd1ea52`.


### SHA-256 Reproduction Receipts

These hashes cover the exact executed source and deterministic JSON outputs. Elapsed timings were printed separately and do not enter the JSON files.

```text
f846ef12bb2d7ed152adc58155732cb3d330517a8e0bdf39ceaecac9ac75af9e  dz_probe.cpp
72d9313a312dc7357d8c275f1d4b73f191d015d55556c7b0d0bcd133f135d4be  dz_verify.py
a4df9900fa7758c44dab671be4a5fe0816d4a1a4a9314273928fa563e19ed55d  dz_summary.py
5a86bc1c2d0a6cd18c15c4636ee1d0ada839e2efbb10eab343b93251078ec3b8  mc_verify.py
f53bbcb026fc57c592a16b21c13613418216a5788e834da742d746e60b1f9de0  dz_primary.json
45bfed1f3ba4e19af0a05f6e0343e8f8dd33afa2bbdd28029d99c0cf053e9c4b  dz_verified.json
d371561f73f9a0531ccd93cd40d2b303100cd49391c6075b104f0c88a7dbd235  dz_summary.json
61533b512c56100b35903b5604dc1fbeb9bd975a89a9fce8efd5822fb1a806a2  mc_verified.json
79d3d1592afa205d67b8cc014a151eb365fb9564a7beafcb3ebe64f51ac443cb  checkpoint.md
```


### Exact Executed Programs

#### dz_probe.cpp

```cpp
#include <algorithm>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <string>
#include <vector>

using i64 = std::int64_t;
using i128 = __int128_t;

std::string dec(i128 x) {
    if (x == 0) return "0";
    bool neg = x < 0;
    if (neg) x = -x;
    std::string s;
    while (x) { s.push_back(char('0' + x % 10)); x /= 10; }
    if (neg) s.push_back('-');
    std::reverse(s.begin(), s.end());
    return s;
}

int main(int argc, char** argv) {
    assert(argc == 2);
    auto start = std::chrono::steady_clock::now();
    std::vector<int> roots;
    for (int r = 2; r <= 256; ++r) roots.push_back(r);
    for (int r : {511,512,513,549,1023,1024,1025,2047,2048,2049,4095,4096,4097})
        roots.push_back(r);
    for (int r = 5529; r <= 5593; ++r) roots.push_back(r);
    const int xmax = roots.back() * roots.back() - 1;
    std::vector<int> lp(xmax + 1), primes, mertens(xmax + 1);
    std::vector<std::int8_t> mu(xmax + 1);
    mu[1] = 1;
    for (int n = 2; n <= xmax; ++n) {
        if (!lp[n]) { lp[n] = n; primes.push_back(n); mu[n] = -1; }
        for (int p : primes) {
            if (i64(p) * n > xmax) break;
            lp[p*n] = p;
            if (n % p == 0) { mu[p*n] = 0; break; }
            mu[p*n] = -mu[n];
        }
    }
    for (int n = 1; n <= xmax; ++n) mertens[n] = mertens[n-1] + mu[n];
    std::vector<int> tau(roots.back());
    for (int d = 1; d < roots.back(); ++d)
        for (int g = d; g < roots.back(); g += d) ++tau[g];
    std::ofstream out(argv[1]);
    out << "{\"xmax\":" << xmax << ",\"rows\":[\n";
    i64 total_pairs = 0;
    for (size_t ri = 0; ri < roots.size(); ++ri) {
        int r = roots[ri], n = r - 1;
        i64 x = i64(r)*r - 1;
        std::vector<i64> c(r), s(r);
        i128 pair_diag = 0;
        i64 abs_atoms = 0, count = 0;
        for (int a = 1; a <= n; ++a) if (mu[a]) {
            for (int b = a; b <= n; ++b) if (mu[b]) {
                i64 floor = x / (i64(a)*b), mult = a == b ? 1 : 2;
                i64 atom = int(mu[a])*int(mu[b])*floor;
                c[std::gcd(a,b)] += mult*atom;
                pair_diag += i128(mult)*atom*atom;
                abs_atoms += mult*floor;
                count += mult;
            }
        }
        for (int d = 1; d <= n; ++d)
            for (int g = d; g <= n; g += d) s[d] += c[g];
        i64 q = std::accumulate(c.begin(), c.end(), i64(0));
        assert(q == s[1] && q == 2*mertens[n] - mertens[x]);
        i128 dg = 0, ds = 0, tau_diag = 0;
        for (int g = 1; g <= n; ++g) {
            dg += i128(c[g])*c[g];
            ds += i128(s[g])*s[g];
            tau_diag += i128(tau[g])*c[g]*c[g];
        }
        i64 kn = 1, kd = 1;
        int ku = 0;
        for (int u = 0; u < r; ++u) {
            i64 num = i64(mertens[u]-1)*(mertens[u]-1), den = u + 1;
            if (i128(num)*kd > i128(kn)*den) { kn=num; kd=den; ku=u; }
        }
        i64 div = std::gcd(kn,kd); kn/=div; kd/=div;
        if (ri) out << ",\n";
        out << "{\"R\":" << r << ",\"Q\":" << q
            << ",\"M_N\":" << mertens[n] << ",\"M_X\":" << mertens[x]
            << ",\"K\":[" << kn << ',' << kd << "],\"K_arg\":" << ku
            << ",\"D_G\":" << dec(dg) << ",\"D_S\":" << dec(ds)
            << ",\"delta\":" << dec(ds-dg)
            << ",\"tau_diagonal\":" << dec(tau_diag)
            << ",\"weighted_cross\":" << dec(ds-tau_diag)
            << ",\"ordinary_cross\":" << dec(i128(q)*q-dg)
            << ",\"pair_diagonal\":" << dec(pair_diag)
            << ",\"within_gcd_cross\":" << dec(dg-pair_diag)
            << ",\"abs_atom_mass\":" << abs_atoms << ",\"ordered_pairs\":" << count;
        out << ",\"C\":[";
        for (int g = 1; g <= n; ++g) { if (g>1) out << ','; out << c[g]; }
        out << "],\"S\":[";
        for (int d = 1; d <= n; ++d) { if (d>1) out << ','; out << s[d]; }
        out << "]}";
        total_pairs += count;
    }
    out << "\n],\"root_count\":" << roots.size()
        << ",\"ordered_pairs\":" << total_pairs << "}\n";
    assert(out.good());
    auto elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
    std::cout << "PASS primary roots=" << roots.size() << " xmax=" << xmax
              << " ordered_pairs=" << total_pairs << " seconds=" << elapsed << '\n';
}
```

#### dz_verify.py

```python
"""Independent smooth-rectangle reconstruction; never import primary mu/M tables."""
import argparse
import json
import platform
import time
from fractions import Fraction
from functools import cache
from math import gcd, isqrt
from pathlib import Path


def factor(n):
    ans = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            e = 0
            while n % p == 0:
                n //= p
                e += 1
            ans.append((p, e))
        p += 1
    if n > 1:
        ans.append((n, 1))
    return ans


def mobius(n):
    f = factor(n)
    return 0 if any(e > 1 for _, e in f) else (-1) ** len(f)


def smooth(d, bound):
    values = [1]
    for p, _ in factor(d):
        new = []
        for a in values:
            while a <= bound:
                new.append(a)
                a *= p
        values = new
    return sorted(values)


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def resonance(r):
    for p in range((r + 1) // 2, r):
        if not prime(p):
            continue
        for sign in [-1, 1]:
            t = 4 * p + sign
            if not (2 * r <= t < 4 * r and prime(t)):
                continue
            qmax = min(2 * r - 1, (r*r-1)//p, (4*r*r-1)//t)
            for q in range(r, qmax + 1):
                if prime(q):
                    return [p, q, t]
    return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("primary")
    parser.add_argument("output")
    args = parser.parse_args()
    start = time.perf_counter()
    data = json.loads(Path(args.primary).read_text())
    rmax = max(row["R"] for row in data["rows"])
    mu = [0] + [mobius(n) for n in range(1, rmax)]
    prefix = [0]
    for n in range(1, rmax):
        prefix.append(prefix[-1] + mu[n])

    @cache
    def mertens(n):
        if n < rmax:
            return prefix[n]
        total = 1
        left = 2
        while left <= n:
            quotient = n // left
            right = n // quotient
            total -= (right - left + 1) * mertens(quotient)
            left = right + 1
        return total

    results = []
    rectangles = 0
    weighted_checks = 0
    for row in data["rows"]:
        r = row["R"]
        n, x = r - 1, r*r - 1
        s = [0] * r
        for d in range(1, r):
            if not mu[d]:
                continue
            b = n // d
            hvals = smooth(d, b)
            for h in hvals:
                ah = b // h
                for k in hvals:
                    ak, t = b // k, x // (d*d*h*k)
                    assert max(ah, ak) <= t < (ah+1)*(ak+1)
                    s[d] += mertens(ah) + mertens(ak) - mertens(t)
                    rectangles += 1
        c = [0] * r
        for g in range(1, r):
            c[g] = sum(mu[k] * s[g*k] for k in range(1, n//g+1))
        assert row["S"] == s[1:], (r, "common-divisor reconstruction")
        assert row["C"] == c[1:], (r, "gcd reconstruction")
        q = sum(c)
        dg, ds = sum(a*a for a in c), sum(a*a for a in s)
        k = max(Fraction((prefix[u]-1)**2, u+1) for u in range(r))
        ku = next(u for u in range(r) if Fraction((prefix[u]-1)**2, u+1) == k)
        assert row["Q"] == q == 2*prefix[n] - mertens(x)
        assert row["M_N"] == prefix[n] and row["M_X"] == mertens(x)
        assert row["K"] == [k.numerator, k.denominator] and row["K_arg"] == ku
        assert row["D_G"] == dg and row["D_S"] == ds and row["delta"] == ds-dg
        td = sum((2**len(factor(g))) * c[g]**2 for g in range(1,r) if mu[g])
        assert row["tau_diagonal"] == td
        assert row["weighted_cross"] == ds-td
        assert row["ordinary_cross"] == q*q-dg
        assert row["pair_diagonal"] + row["within_gcd_cross"] + row["ordinary_cross"] == q*q
        if r <= 256 or r in [549,5561]:
            wc = 0
            nonzero = [g for g in range(1,r) if c[g]]
            for i,g in enumerate(nonzero):
                for h in nonzero[i+1:]:
                    wc += 2*(2**len(factor(gcd(g,h))))*c[g]*c[h]
            assert wc == ds-td, (r, "direct weighted Gram")
            weighted_checks += 1
        results.append({key: row[key] for key in row if key not in ["C","S"]})
    failing = [a for a in results if a["R"]>=4 and a["delta"]>0]
    selected = {a["R"] for a in failing[:1]}
    selected.update([2,3,15,17,549,5561])
    for key in ["D_S", "Q"]:
        den = "D_G"
        best = max(results, key=lambda a: Fraction(a[key]**(2 if key=="Q" else 1),a[den]))
        selected.add(best["R"])
    certificates = []
    for row in data["rows"]:
        if row["R"] in selected:
            record = {k:v for k,v in row.items() if k not in ["C","S"]}
            record["nonzero_groups"] = [[g,c,row["S"][g-1]] for g,c in enumerate(row["C"],1) if c or row["S"][g-1]]
            record["ratios"] = {name:str(Fraction(value*row["K"][1],row["R"]**2*row["K"][0])) for name,value in [("Q2_R2K",row["Q"]**2),("DG_R2K",row["D_G"]),("DS_R2K",row["D_S"])]}
            certificates.append(record)
    witnesses = {str(r):resonance(r) for r in sorted({a["R"] for a in results if a["R"]>256})}
    report = {"status":"PASS_INDEPENDENT_EXACT", "python":platform.python_version(),
              "root_count":len(results), "smooth_rectangles":rectangles,
              "weighted_gram_direct_checks":weighted_checks,
              "H_Z_failures":[a["R"] for a in failing],
              "H_Z_first":failing[0] if failing else None,
              "GC5_failures":[a["R"] for a in results if a["ordinary_cross"]>0],
              "max_DS_DG":max(results,key=lambda a:Fraction(a["D_S"],a["D_G"])),
              "max_Q2_DG_nondegenerate":max((a for a in results if a["R"]>=4),key=lambda a:Fraction(a["Q"]**2,a["D_G"])),
              "certificates":certificates,"resonance_witnesses":witnesses,
              "summary_rows":results}
    Path(args.output).write_text(json.dumps(report,indent=2)+"\n")
    compact = {k:v for k,v in report.items() if k not in ["certificates","summary_rows","resonance_witnesses"]}
    compact["seconds"] = time.perf_counter()-start
    print(json.dumps(compact,indent=2),flush=True)


if __name__ == "__main__":
    main()
```

#### dz_summary.py

```python
"""Exact summaries of the frozen, independently verified domain; no new search."""
import json
from fractions import Fraction
from pathlib import Path

data = json.loads(Path("dz_primary.json").read_text())
verified = json.loads(Path("dz_verified.json").read_text())
rows = data["rows"]
valid = [a for a in rows if a["R"] >= 4]
assert len(rows) == 333 and len(valid) == 331
assert all(a["delta"] < 0 for a in valid)


def metrics(a):
    kn,kd = a["K"]
    result={k:a[k] for k in ["R","Q","D_G","D_S","delta","ordinary_cross","tau_diagonal","weighted_cross","pair_diagonal","within_gcd_cross","M_N","M_X","K","K_arg"]}
    result["DS_DG"] = str(Fraction(a["D_S"],a["D_G"]))
    result["Q2_DG"] = str(Fraction(a["Q"]**2,a["D_G"]))
    for key,value in [("Q2",a["Q"]**2),("DG",a["D_G"]),("DS",a["D_S"])]:
        result[key+"_R2K"] = str(Fraction(value*kd,a["R"]**2*kn))
    result["extra_diagonal_tax"]=a["tau_diagonal"]-a["D_G"]
    result["extra_shared_cross"]=a["weighted_cross"]-a["ordinary_cross"]
    result["subordinate_energy"]=a["D_S"]-a["Q"]**2
    result["top_abs_gcd_groups"] = sorted(enumerate(a["C"],1),key=lambda pair:abs(pair[1]),reverse=True)[:12]
    return result


maxnorm=max(valid,key=lambda a:Fraction(a["D_S"],a["D_G"]))
maxq=max(valid,key=lambda a:Fraction(a["Q"]**2,a["D_G"]))
maxhistory=max(valid,key=lambda a:Fraction(a["D_S"]*a["K"][1],a["R"]**2*a["K"][0]))
mingap=min(valid,key=lambda a:a["D_G"]-a["D_S"])
extra_first=next(a for a in rows if a["weighted_cross"]>a["ordinary_cross"])
chosen={2,3,4,7,15,17,549,5561,5565,maxnorm["R"],maxhistory["R"],mingap["R"]}
small_certificates=[]
for a in rows:
    if a["R"]<=256 and a["R"] in chosen:
        small_certificates.append({"R":a["R"],"C":a["C"],"S":a["S"]})
wc=verified["resonance_witnesses"]
assert all(v is not None for v in wc.values())
for key,v in wc.items():
    r=int(key);p,q,t=v
    assert 2*p>=r and p<r and r<=q<2*r and 2*r<=t<4*r
    assert p*q<=r*r-1 and q*t<=4*r*r-1 and abs(t-4*p)==1
    z=Fraction((r*r-1)*t,(4*r*r-1)*p)
    assert z>0 and z!=1 and abs(z-1)<=Fraction(1,r)
out={"valid_candidate_roots":len(valid),"strict_passes":len(valid),
     "posthoc_first_positive_extra_shared_cross":metrics(extra_first),
     "max_DS_DG":metrics(maxnorm),"max_Q2_DG":metrics(maxq),
     "max_DS_R2K":metrics(maxhistory),"minimum_absolute_slack":metrics(mingap),
     "all_large_resonances_verified":len(wc),
     "table":[metrics(a) for a in rows if a["R"] in chosen],
     "small_certificates":small_certificates,
     "required_resonances":{r:wc[r] for r in ["549","5561","5565"]}}
Path("dz_summary.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps({k:v for k,v in out.items() if k not in ["table","small_certificates"]},indent=2))
print("TABLE")
for a in out["table"]:
    print(a["R"],a["Q"],a["D_G"],a["D_S"],a["delta"],a["DS_DG"],a["Q2_R2K"],a["DG_R2K"],a["DS_R2K"])
```

#### mc_verify.py

```python
"""Rational monotone quadrature and literal returned-row enumeration."""
import json
import platform
import time
from fractions import Fraction
from math import isqrt
from pathlib import Path

SCALE = 10**30
TERMS = 40


def ceildiv(a, b):
    return (a+b-1)//b


def log_unit_bounds(num, den):
    assert den <= num <= 2*den
    zn, zd = num-den, num+den
    zl, zu = SCALE*zn//zd, ceildiv(SCALE*zn,zd)
    sl, su = zl*zl//SCALE, ceildiv(zu*zu,SCALE)
    pl, pu, lo, hi = zl, zu, 0, 0
    for j in range(TERMS):
        lo += 2*pl//(2*j+1)
        hi += ceildiv(2*pu,2*j+1)
        pl = pl*sl//SCALE
        pu = ceildiv(pu*su,SCALE)
    hi += ceildiv(2*pu*SCALE,(2*TERMS+1)*(SCALE-su))
    return lo,hi


LOG2 = log_unit_bounds(2,1)


def log_bounds(num, den=1):
    assert num >= den
    k = 0
    while num > 2*den:
        den *= 2
        k += 1
    lo,hi = log_unit_bounds(num,den)
    return lo+k*LOG2[0],hi+k*LOG2[1]


def reciprocal_log_bounds(num,den):
    lo,hi = log_bounds(num,den)
    assert lo > 0
    return SCALE*SCALE//hi,ceildiv(SCALE*SCALE,lo)


def integral_bounds(endpoints,m):
    # 1/log(t) decreases: right sums are lower, left sums are upper.
    wanted = set(endpoints)
    lo = hi = 0
    previous = reciprocal_log_bounds(2,1)
    result = {}
    for j in range(2*m+1,max(endpoints)*m+1):
        current = reciprocal_log_bounds(j,m)
        lo += current[0]
        hi += previous[1]
        previous = current
        if j%m == 0 and j//m in wanted:
            result[j//m] = [Fraction(lo,m*SCALE),Fraction(hi,m*SCALE)]
    return result


def prime(n):
    return n>=2 and all(n%d for d in range(2,isqrt(n)+1))


def mu(n):
    if any(n%(d*d)==0 for d in range(2,isqrt(n)+1)):
        return 0
    return (-1)**sum(n%p==0 for p in range(2,n+1) if prime(p))


def polyadd(a,b,mult=1):
    return [x+mult*y for x,y in zip(a,b)]


def main():
    started=time.perf_counter()
    r,x,p = 10,120,3
    mob=[0]+[mu(n) for n in range(1,x+1)]
    active = [n for n in range(r*r+1,(r+1)**2) if n%2 and mob[n]]
    # Literal p-free, squarefree, empty lower signature base, with inclusive X.
    base=[a for a in range(1,x+1) if mob[a] and a%p and all(a%ell for ell in range(2,p) if prime(ell))]
    clipped={a for a in base if p*a>x}
    admitted={a for a in base if p*a<=x}

    def field(b,n):
        if b not in clipped or n%p or n//p not in admitted or b not in active or n not in active:
            return [0,0,0]
        return [int(prime(b) and prime(n)),-int(prime(b))-int(prime(n)),1]

    assert 101 in clipped and 115 in clipped and {35,37} <= admitted
    assert [n for n in active if n%p==0] == [105,111]
    triples=[]
    needed=set()
    for q in range(r+1,x+1):
        for a in range(1,x//q+1):
            coef=mob[a]+mob[a*q]
            for k in range(1,x//(q*a)+1):
                triples.append((q,a,k,coef))
                if coef and (any(field(101,q*a)) or any(field(101,q*a*k))):
                    needed.add(q)
    assert needed=={15,21,35,111}
    endpoints=sorted(needed|{q-1 for q in needed})
    attempts=[]
    for m in [128,512,2048,8192]:
        bounds=integral_bounds(endpoints,m)
        resolved=all(lo.numerator//lo.denominator==hi.numerator//hi.denominator for lo,hi in bounds.values())
        attempts.append({"mesh_per_unit":m,"all_floors_resolved":resolved})
        if resolved:
            break
    assert resolved
    floors={n:v[0].numerator//v[0].denominator for n,v in bounds.items()}
    events={q:floors[q]-floors[q-1] for q in needed}
    rows=[]
    for b in [101,115]:
        pre=post=[0,0,0]
        postfibres={}
        contributions=[]
        for q,a,k,coef in triples:
            before,after=field(b,q*a),field(b,q*a*k)
            if not coef or (not any(before) and not any(after)):
                continue
            lam=events[q]
            pre=polyadd(pre,before,lam*coef)
            post=polyadd(post,after,lam*coef)
            key=f"{q},{a*k}"
            postfibres[key]=polyadd(postfibres.get(key,[0,0,0]),after,lam*coef)
            if lam and any(before):
                contributions.append([q,a,k,coef,before])
        assert post==[0,0,0] and all(v==[0,0,0] for v in postfibres.values())
        expected=[0,4,-4] if b==101 else [0,0,-4]
        assert pre==expected
        correction=[0,0,0]
        marked={}
        for n in active:
            if not any(field(b,n)):
                continue
            e=sum(events.get(q,0) for q in needed if r<q<n and n%q==0 and mob[q]==1)
            marked[n]=e
            correction=polyadd(correction,field(b,n),2*mob[n]*e)
        assert correction==pre
        rows.append({"b":b,"pre_coefficients_1_w_w2":pre,"post_coefficients_1_w_w2":post,
                     "post_fibres":postfibres,"marked_multiplicity":marked,"nonzero_pre_atoms":contributions})
    logw=log_bounds(221,2)
    assert 4*SCALE<logw[0] <= logw[1]<5*SCALE
    wl,wu=Fraction(21*SCALE,10*logw[1]),Fraction(21*SCALE,10*logw[0])
    assert 0<wl<=wu<1
    output={"status":"PASS_EXACT_RATIONAL_AND_SYMBOLIC","python":platform.python_version(),
            "r":r,"R":r+1,"X":x,"owner":p,"active":active,"right_active":[105,111],
            "enumerated_triples":len(triples),"quadrature_attempts":attempts,
            "scale":SCALE,"atanh_terms":TERMS,"floor_certificates":{
                str(n):{"lower":str(bounds[n][0]),"upper":str(bounds[n][1]),"floor":floors[n],
                        "width":str(bounds[n][1]-bounds[n][0])} for n in endpoints},
            "events":events,"weight_interval":[str(wl),str(wu)],"rows":rows}
    Path("mc_verified.json").write_text(json.dumps(output,indent=2)+"\n")
    print(json.dumps(output,indent=2))
    print("seconds",time.perf_counter()-started)


if __name__=="__main__":
    main()
```

### Exact MC Rational Certificates

```json
{
  "status": "PASS_EXACT_RATIONAL_AND_SYMBOLIC",
  "python": "3.12.14",
  "r": 10,
  "R": 11,
  "X": 120,
  "owner": 3,
  "active": [
    101,
    103,
    105,
    107,
    109,
    111,
    113,
    115,
    119
  ],
  "right_active": [
    105,
    111
  ],
  "enumerated_triples": 449,
  "quadrature_attempts": [
    {
      "mesh_per_unit": 128,
      "all_floors_resolved": true
    }
  ],
  "scale": 1000000000000000000000000000000,
  "atanh_terms": 40,
  "floor_certificates": {
    "14": {
      "lower": "861633497294906160033754334239891/128000000000000000000000000000000",
      "upper": "862697269154105172268316924528149/128000000000000000000000000000000",
      "floor": 6,
      "width": "531885929599506117281295144129/64000000000000000000000000000000"
    },
    "15": {
      "lower": "909500576840004938929198545886153/128000000000000000000000000000000",
      "upper": "910574002507825047268827645700511/128000000000000000000000000000000",
      "floor": 7,
      "width": "536712833910054169814549907179/64000000000000000000000000000000"
    },
    "20": {
      "lower": "1133543663759631891990704702680913/128000000000000000000000000000000",
      "upper": "1134652550599825521345000544645881/128000000000000000000000000000000",
      "floor": 8,
      "width": "138610855024203669286980245621/16000000000000000000000000000000"
    },
    "21": {
      "lower": "3674754518803963810952375555501/400000000000000000000000000000",
      "upper": "147129460289925541479847763341407/16000000000000000000000000000000",
      "floor": 9,
      "width": "139279537766989041752741121367/16000000000000000000000000000000"
    },
    "34": {
      "lower": "1680312907568692644736520701770061/128000000000000000000000000000000",
      "upper": "1681472024117530274744182540507217/128000000000000000000000000000000",
      "floor": 13,
      "width": "289779137209407501915459684289/32000000000000000000000000000000"
    },
    "35": {
      "lower": "858230353457347458290536789945251/64000000000000000000000000000000",
      "upper": "1717622135541521151639059719673777/128000000000000000000000000000000",
      "floor": 13,
      "width": "46457145073049402319445591331/5120000000000000000000000000000"
    },
    "110": {
      "lower": "799363479745404946867033415862111/25600000000000000000000000000000",
      "upper": "799609469910818605673326947943063/25600000000000000000000000000000",
      "floor": 31,
      "width": "30748770676707350786691510119/3200000000000000000000000000000"
    },
    "111": {
      "lower": "1006005558414091875825034138804671/32000000000000000000000000000000",
      "upper": "1006313148323205074791946441774993/32000000000000000000000000000000",
      "floor": 31,
      "width": "153794954556599483456151485161/16000000000000000000000000000000"
    }
  },
  "events": {
    "35": 0,
    "111": 0,
    "21": 1,
    "15": 1
  },
  "weight_interval": [
    "2100000000000000000000000000000/4705015520957807506885789938169",
    "2100000000000000000000000000000/4705015520957807506885789937863"
  ],
  "rows": [
    {
      "b": 101,
      "pre_coefficients_1_w_w2": [
        0,
        4,
        -4
      ],
      "post_coefficients_1_w_w2": [
        0,
        0,
        0
      ],
      "post_fibres": {
        "15,7": [
          0,
          0,
          0
        ],
        "21,5": [
          0,
          0,
          0
        ],
        "35,3": [
          0,
          0,
          0
        ],
        "111,1": [
          0,
          0,
          0
        ]
      },
      "marked_multiplicity": {
        "105": 2,
        "111": 0
      },
      "nonzero_pre_atoms": [
        [
          15,
          7,
          1,
          -2,
          [
            0,
            -1,
            1
          ]
        ],
        [
          21,
          5,
          1,
          -2,
          [
            0,
            -1,
            1
          ]
        ]
      ]
    },
    {
      "b": 115,
      "pre_coefficients_1_w_w2": [
        0,
        0,
        -4
      ],
      "post_coefficients_1_w_w2": [
        0,
        0,
        0
      ],
      "post_fibres": {
        "15,7": [
          0,
          0,
          0
        ],
        "21,5": [
          0,
          0,
          0
        ],
        "35,3": [
          0,
          0,
          0
        ],
        "111,1": [
          0,
          0,
          0
        ]
      },
      "marked_multiplicity": {
        "105": 2,
        "111": 0
      },
      "nonzero_pre_atoms": [
        [
          15,
          7,
          1,
          -2,
          [
            0,
            0,
            1
          ]
        ],
        [
          21,
          5,
          1,
          -2,
          [
            0,
            0,
            1
          ]
        ]
      ]
    }
  ]
}
```

## Verified Publication Receipt - 20261111-census-1/DZ

At 2026-11-11T08:45:21Z (03:45:21 EST), the substantive report was re-fetched at immutable commit `8734c6b725119f549f8905cfb6f8d186ea2d981f`, blob `928d0158d669f59eedde9d7207a87d733cea40ca`, and matched the complete local 77,222-byte report exactly. Its SHA-256 was `aee39e8a1bba217b36e0f4f35f1f032adbd731af30e872ba14ed1cb246c53b84`. A fresh branch-path read before appending this receipt confirmed the same blob; prior content was preserved.

`EXECUTION=COMPLETE; SUBSTANTIVE_PUBLICATION=PUBLISHED_READBACK_VERIFIED.` DZ1 and DZ4 are finite computational evidence; DZ2b is an exact finite refutation of its stated auxiliary principle; DZ2c is an elementary paper identity awaiting independent review; DZ3/H_Z remains a conjecture. This receipt does not promote finite evidence to an infinite theorem. `NO_NEW_GLOBAL_GAIN; NO_NEW_ACCEPTED_ROUTE; VERIFIED_ETA=NONE.` The canonical VF, finite-C and RH objectives remain open. No remote path other than this owned daily report was modified.


## Scheduled Continuation Checkpoint - 20261111-census-2/UM

Prepared 2026-11-11 11:06 EST. Actual scheduled trigger: 2026-11-11 11:00:01 EST (16:00:01 UTC). Platform RUN_ID_UNAVAILABLE; UM is a research label. Execution IN_PROGRESS, mathematics PENDING.
cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1.

### New Question And Frozen Falsification Tests

Consume the NEW 20261111-wheel-2/PD1-PD3 historical/powerful decomposition, not an unchanged extension of H_Z/GC5. Original source: N=R-1, X=R^2-1, C_g=sum_(1<=a,b<R,gcd(a,b)=g)mu(a)mu(b)floor(X/(ab)); S_d=sum_(d|g)C_g; Q=sum C=2M(N)-M(X). Keep the strict K_R=max_(0<=u<R)(M(u)-1)^2/(u+1), ordered multiplicities and every signed interaction.

PD writes C=H-E with E=M(X)e_1+F, where F comprises every nonunit powerful denominator q<=N and has zero total. Define the complete unit-removed vector Z=H-F=C+M(X)e_1 and its multiples transform T_d=sum_(d|g)Z_g. No source term is discarded: the physical vector is restored as C=Z-M(X)e_1.

Preregister two NEW auxiliary candidates, for every integer R>=4, with constants fixed now:
- H_PRE: Delta_0=||Z||_2^2-||T||_2^2 >=0.
- H_ROB: Delta_0 >= 2*|M(X)*B|, where B=sum_(g>=2)C_g.

Direct expansion predicts the EXACT complete gap
Delta=||C||_2^2-||S||_2^2=Delta_0+2*M(X)*B.
Thus H_ROB would recover H_Z irrespective of the endpoint's sign. H_PRE alone would not. The sign-reversed unit vector is only a diagnostic, not claimed to be another genuine arithmetic source. Rival mechanism: the nonunit/historical Gram may already fail contraction, or the endpoint alignment may be essential. A negative margin refutes its precise candidate; an identity mismatch stops scaling for diagnosis. Tests must report H_PRE, H_ROB and restored Delta separately, and cannot infer a uniform estimate from finite passes.

Frozen roots: every R=2..256; q-1,q,q+1 for every powerful integer 4<=q<=4096; 2^j-1,2^j,2^j+1 for j=9..13; R=549 and 5561. Deduplicate roots only, never arithmetic occurrences. R=2,3 are declared boundary controls. This tests changing support when q crosses N, plus both mandatory historical regressions and dyadic regimes. Report the smallest failure in this domain; if its R<=256 it is globally minimal within the asserted R>=4 range. Any later extension must be separately marked posthoc. No random seed, floating decisions or fitted constant.

Primary method: exact sieve plus the accepted GD smooth-rectangle source, split at T<R, independently enumerated powerful denominators and divisor inversion. Independent checks: direct historical mu-weighted gcd pairs and trial-factor/quotient-recursive Mertens values at decisive roots. Preserve full H/E and nonunit radical interactions. Reuse known PD controls as implementation fixtures only. The new claim is about complete jointly recovered coefficients, not sparsity alone.

### Authority And Continuity Receipt

Main dda92f9ce59627b4c1f1317082f728648d330a0a. AGENTS c9c89f01b90b526de9f3e8ea92478e36504711b6; contract 95566e37c8eaeb99ee680660df4f9d2e06ea5038; cross-route directive e922d4ba9362a1ae196af8f6de88f7417f92087c. Original Euler pointwise, full floor bridge and endpoint gate were read at main. Canonical VF actual-prime bound and finite-C arithmetic input remain OPEN.

Both Nov 10 and Nov 11 seven-role reports were retrieved at agent-reports 5515b10ceab68bd311e64bfc67f0538486b02600; TODAY=AVAILABLE for every role. Latest consumed: Coordinator FL/changed-source instruction, Owner FA, Analytic DM, Wheel PD (blob c9989449a814a1a7ee799791c73450872f4c7d3c), Census DZ, Referee NP/GD acceptance, Lean FFR. Carry forward Nov 10 GC, DR, RC, IR/IRR and MD/FFR at their recorded scopes. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 has no newer entry than October 18; retain source/mask and first-bad distinctions.

Baseline native_mertens_near_uniform_window_error_closed is b_cert=7/8-7/(64*N_pack), with every positive loss, not a no-loss bound. Fresh exact-head #1119 check collection has 14 successes and the actual five standard-axiom closure PASS records were read. All 911 preexisting relevant source/audit blobs match current main. At the same positive fine length, source definitions give N_pack<=N_old, so its saving is stronger than 1/(48*N_old). This reuses scoped compiled evidence, not a fresh main Lean build or independent reproof of the entire imported analytic chain. Accepted PAPER IR/FFR endpoint remains distinct.

No open/draft PR was returned. #1131 is now merged at current main, superseding earlier reports' unmerged status; its exact head has 13 successful checks. Its finite principal-response mass supplier is not the full global return. Only this role's dated report will be written remotely.


# Complete Recovery Needs Historical Interaction

## Research Continuation - 20261111-census-2/UM

Actual invocation: scheduled 2026-11-11 11:00:01 EST / 16:00:01 UTC, America/New_York. Platform RUN_ID_UNAVAILABLE; UM is a research label, not a platform identifier. This continuation preserves the earlier DZ report and the verified UM preregistration. Research complete; publication status is recorded in the subsequent verified receipt.

`cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1`.

### A. Most Important Mathematical Discovery

**The nonunit powerful response does NOT by itself explain the observed complete divisor-norm contraction. The smallest genuine failure is R=115.** Its exact response F and common-divisor transform A' have squared norms 404 and 599, so their contraction gap is -195. The complete original source nevertheless has a positive gap 18,331 after every historical, nonunit and endpoint interaction is restored.

The hidden distinction is prime versus composite squarefree radicals. Prime-only response columns always have nonnegative contraction gap. The first admissible composite radical, 6, makes the corresponding quadratic form indefinite at R=37. Actual arithmetic first realizes a negative response gap at R=115, where the prime/composite-radical mixed contribution is -1,614. Sparse powerful support and zero scalar column totals are insufficient to control this norm.

There is a surviving stronger conjecture on the COMPLETE expression. Write C=H-E, E=M(X)e_1+F, Z=H-F, B=sum_(g>=2)C_g, and let T be the common-divisor transform of Z. The exact identity is

```text
Delta := ||C||^2-||S||^2 = Delta_0 + 2 M(X) B,
Delta_0 := ||Z||^2-||T||^2.
```

The preregistered fixed inequality Delta_0 >= 2|M(X)B| passed strictly at all 525 eligible roots in the 527-root frozen domain. It would imply the earlier H_Z, but remains CONJECTURE. All five complete vectors C,S,H,E,A were checked by genuinely different reconstruction methods, with zero mismatches. No new infinite estimate follows.

| Claim | Evidence | Scope |
| --- | --- | --- |
| UM1 | PAPER_PROOF | Exact affine endpoint separation and quarter-horizon description; supporting source accounting, self-audited. |
| UM2 | FINITE_COMPUTATION | 527 roots, five full vectors and complete scalar checks, independently reconstructed. |
| UM3 | CONJECTURE | Fixed H_ROB and its weaker H_PRE, for every R>=4; 525 finite strict passes only. |
| UM4 | REFUTED | Auxiliary H_F: nonunit response always contracts. Smallest genuine violation R=115. |
| UM5 | PAPER_PROOF | Prime-only response gap is a square; first possible indefinite radical support at R=37. Supporting restriction on a proper response, not the whole endpoint. |
| UM6 | FINITE_COMPUTATION | Exact synthetic unit and radical controls, explicitly not genuine arithmetic counterexamples. |

**NET RESULT: NO_NEW_GLOBAL_GAIN; NO_NEW_ACCEPTED_ROUTE; VERIFIED_ETA=NONE.** Canonical actual-prime VF, uniform finite-C, the complete wheel bound and RH remain OPEN. New paper arguments have SELF_AUDIT, not independent Referee acceptance or Lean certification.

### B. Current Authoritative Objective

Main is `dda92f9ce59627b4c1f1317082f728648d330a0a`, observed at intake and again in the freshness check begun at 16:22:35 UTC. AGENTS and the cross-route directive supersede the older single-wheel task-selection paragraph in CURRENT_PROOF_CONTRACT, not its mathematics or safeguards.

The canonical statement is `VFCanonicalSquareVonKochStatement`: one C>=0 before every integer R>=2 with

```text
|pi(R^2)-vfCanonical(R^2)| <= C R log R.
vfCanonical = vfMid + sqrt(2).
```

The canonical terminal interface still takes `ClassicalVonKochRHCriterion`. The distinct internally proved Mertens-energy/RH consumer has an unpaid arithmetic premise. For this run, the original declarations read include `eulerSelfDualFloor`, `eulerSelfDualBilinear`, their literal convolution/endpoint bridges, and `LowerMertensCriticalEnvelope` with y=0 included.

#### 1. BASELINE / DEPENDENCY RECEIPT

The strongest explicit fixed-family compiled comparator inspected is

```text
RHLean.Analysis.native_mertens_near_uniform_window_error_closed
  : MertensGrowthAtMost(7/8 - 7/(64*N_pack)).
```

Its quantifiers retain EVERY positive loss: for each eps>0, a C_eps>=0 is chosen before all integers n>=1, bounding |M(n)| by C_eps*n^(b_cert+eps). It is not a no-loss bound at b_cert. For the SAME positive `explicitFineLength` L, the actual definitions give

```text
N_pack=ceil_nat(max(1,1/(6L)))+2,
N_old =ceil_nat(max(1,1/(3L)))+2.
```

Thus N_pack<=N_old, and the saving 7/(64*N_pack) exceeds 1/(48*N_old). The counts are compared, not identified. The inspected chain is fixed original source and native moments -> complete total-mass LOW/anchored HIGH/principal comparison -> actual Hecke zero supremum -> modulus-one Dirichlet product -> native Mertens converse. No arbitrary real-vector covariance is identified with the Hecke source.

Fresh #1119 checks: 14 successful checks at exact head `77ee815846d6d534c866f0752aa33b84c385610a`. The actual [dependency/axiom job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42552018910/job/128949473700) was read, as was its audit implementation. Its five selected closures have sizes 35358, 35375, 35736, 35737, 35753 and only `propext`, `Classical.choice`, `Quot.sound`. All 911 preexisting relevant source/audit blobs under RHLean/, research/oai_434/, and the slot_anchored/window_error_closure audit directories match current main. This reuses scoped exact-head evidence; it is not a new main build, a fresh independent proof of every imported analytic theorem, or a claim that the whole repository is placeholder-free. Unrelated historical Wiener warnings are outside the selected audited closures.

Observed pins: Lean 4.34.1/compiler `5045d0056413266e57c625dcd7c365b10e377c52`; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; openai/math `1581d4cbdd69a0faf34b2089614fe2a814316a6a`; PNT `c39a751132c88b6e8080b74c74023fd95b3d8be0`.

#1131 is actually MERGED at 2026-11-11T12:46:15Z, merge commit equal to current main. Its exact head `f3f1da37c3e2fff9374eb5e99eca0da94c1efc29` has 13 successful checks. The [dedicated job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/43006238259/job/130474300634) records six finite-response plus eight mass/delay roots with only the standard axioms. The original mass declaration was read: it keeps positive normalized weights, |A|,|eta|<=1, P<=Q, its geometric gate, theta>=3/5, and strict theta>3/5 for decay. It is not the full same-signal contour/endpoint return. The separately accepted PAPER IR/FFR boundary `7/8-1/2400000000` remains distinct from the compiled comparator and was not re-proved here. No new exponent is claimed against either. The live open/draft PR collection was empty at both checks; no CI was launched.

### C. Competing Hypotheses

The verified checkpoint froze H_PRE: Delta_0>=0 and H_ROB: Delta_0>=2|M(X)B| for all R>=4. The rival is that the historical/nonunit Gram can already fail contraction, or that the final endpoint sign is essential to its recovery. A negative exact margin is a falsifier; a source-reconstruction mismatch stops scaling. Neither primary candidate failed in the domain.

After those results, a separately timestamped 16:13 UTC follow-up asked whether the nonunit part alone supplies the contraction: H_F is D_F=||F||^2-||A'||^2>=0 for all R>=4. This follow-up uses already generated rows, so it is a POST-PRIMARY mechanism test, not fresh held-out confirmation. Its negative result is exact and does not depend on statistical selection. H_F is an explanatory hypothesis introduced by this run, not a theorem attributed to Wheel or another agent.

### D. Experimental Design

For integer R>=2, N=R-1, X=R^2-1, M(0)=0, define

```text
C_g = sum_(1<=a,b<=N, gcd(a,b)=g) mu(a)mu(b)floor(X/(ab)),
S_d = sum_(d|g) C_g, Q=sum C=S_1=2M(N)-M(X),
K_R=max_(0<=u<R) (M(u)-1)^2/(u+1).
```

These are the complete ordered floor-weighted pairs, equivalently all triples (a,b,k) with abk<=X and weight mu(a)mu(b). Upper-triangle implementations multiply off-diagonal pairs by 2. Squareful factors retain their genuine zero coefficients. No physical occurrence is deduplicated by equal product; gcd classes partition pairs, common-divisor classes overlap. D_G=||C||^2 is the gcd diagonal, not Q^2 and not the original #915 normalized NNS statistic.

The GD/PD reconstruction uses B_d=floor(N/d), all d-smooth h,k<=B_d, A_h=floor(B_d/h), and t=floor(X/(d^2hk)). The strict rectangular walls are checked on every rectangle:

```text
max(A_h,A_k)<=t<(A_h+1)(A_k+1),
S_d=mu(d)^2 sum_(h,k)[M(A_h)+M(A_k)-M(t)],
U_d=mu(d)^2 sum_(h,k)[M(A_h)+M(A_k)-1_(t<R)M(t)],
H_g=sum_(j<=N/g)mu(j)U_(gj).
```

For powerful q<=N, including 1, write d=rad(q), a(q)=product_(p^e||q)(e-1), with a(1)=1. Then

```text
A_d=sum_(q<=N powerful,rad(q)=d) a(q)M(floor(X/q)),
v_d(g)=1_(g|d)mu(d/g), E=sum_d A_d v_d,
C=H-E, F=E-M(X)e_1, A'=A-M(X)e_1,
Z=H-F=C+M(X)e_1, T_d=sum_(d|g)Z_g.
```

The powerful multiplicity counts every ordered splitting hk. It is not a prime-owner multiplicity. U, H, E and their exact admission conditions are credited to Wheel PD/GD, not rediscovered as this run's theorem.

Frozen domain: every R=2..256; q-1,q,q+1 for every powerful integer 4<=q<=4096; 2^j-1,2^j,2^j+1 for j=9..13; and R=549,5561. Deduplicating roots gives 527 roots, 525 eligible for R>=4. Largest root 8193, sieve endpoint 67,125,248. Boundary controls R=2,3 were excluded from the conjecture in advance. The domain tests changed powerful admission, not an unmotivated extension of unchanged GC5/H_Z. Existing near-resonance prime witnesses from DZ are continuity evidence only; no unchanged prime-geometry scan was rerun or claimed as new.

### E. Executed Results

Primary: C++20 prime-factor sign sieve and complete GD/PD smooth reconstruction, plus direct-pair fixture checks. Independent reconstruction: trial factorization only below the historical root, direct enumeration of every genuine pair at ALL 527 roots, and quotient-block recursion

```text
M(n)=1-sum_(j=2..n)M(floor(n/j))
```

for later Mertens values. It imports neither the primary sieve nor its smooth rectangles. The programs separately generate the root set. A Python arbitrary-integer comparator checks all C,S,H,E,A vectors, all scalar norms, the mixed products, M(N), M(X), K and its earliest maximizing index. H in the independent method is recovered from literal C plus independently constructed E, so agreement specifically tests the primary historical rectangle construction. Both algorithms are this agent's computational checks, not a separate specialist's independent acceptance.

| Check | Exact count/result |
| --- | ---: |
| Roots / eligible roots | 527 / 525 |
| Coefficients checked in each of five complete vectors | 563880 |
| Primary ordered smooth rectangles | 2213706 |
| Future rectangle labels, with ordered multiplicity | 66161 |
| Primary literal fixture roots / nonzero ordered pairs | 257 / 13642267 |
| Independent literal nonzero ordered pairs | 561282954 |
| Independent memoized M sites above the seed | 58752 |
| Reconstruction or scalar mismatches | 0 |
| H_PRE / H_ROB / restored H_Z failures at R>=4 | 0 / 0 / 0 |
| Negative D_F follow-up roots | 133 |

The pair counts are not expanded k-occurrence counts. Floors preserve those multiplicities exactly. All arithmetic decisions are integer or rational; no floating sign test, seed or probabilistic primality assertion occurs. C++ was compiled with `-std=c++20 -O2 -Wall -Wextra -Werror` using g++ 13.3.0; Python actually reports 3.12.14. The final primary run took 2.23139 seconds; the independent direct run took 9.21113 seconds, measured internally on this container. These are not portable benchmarks. The first primary run was repeated only to emit every vector for independent comparison, without changing the roots, hypotheses or arithmetic. Python exact norms agree with all C++ results; the largest absolute emitted vector entry is 5080.

| R | M(X) | B | Delta_0 | 2M(X)B | complete Delta | H_ROB margin |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | -1 | 0 | 0 | 0 | 0 | 0 |
| 3 | -2 | 2 | 4 | -8 | -4 | -4 |
| 7 | -3 | 7 | 65 | -42 | 23 | 23 |
| 11 | -3 | 9 | 69 | -54 | 15 | 15 |
| 21 | -7 | 5 | 89 | -70 | 19 | 19 |
| 115 | -9 | -97 | 16585 | 1746 | 18331 | 14839 |
| 549 | 192 | -158 | 203220 | -60672 | 142548 | 142548 |
| 5561 | -2544 | 2852 | 26135814 | -14510976 | 11624838 | 11624838 |
| 8193 | 575 | 2767 | 29278925 | 3182050 | 32460975 | 26096875 |

Smallest positive robust margin is 15 at R=11; largest tested ratio |2M(X)B|/Delta_0 is 70/89 at R=21. These are finite extrema, not fitted universal constants. The endpoint mixed term is positive at 284 eligible roots, negative at 230, zero at 11. B=0 at R=16,18,33; no ratio with denominator B is used there.

K_R=1 at R=2..5; at all tested R>=6 it is 3/2, first attained at u=5. This is computed, not assumed globally. At R=549 and 5561 respectively,

```text
DG/(R^2 K_R) = 426952/904203, 38146964/92774163;
DS/(R^2 K_R) = 141856/904203, 14897288/92774163;
Delta_0/(R^2 K_R) = 45160/100467, 17423876/30924721.
```

No finite maximum is promoted to a uniform historical-normalized bound.

### F. Exceptional Cases And Exact Certificates

**UM4, smallest genuine H_F violation.** At R=115, X=13224, M(114)=-6, M(X)=-9. Nonzero nonunit A_d are

```text
(d,A_d) = (2,-20),(3,-4),(5,-1),(6,-13),(7,-2),(10,-3).
(g,F_g) = (1,11),(2,-4),(3,9),(5,2),(6,-13),(7,-2),(10,-3).
sum F=0, ||F||^2=404, ||A'||^2=599, D_F=-195.
```

Every other coordinate is zero. The standalone certificate below independently solves the divisor recurrence for mu through 13224, enumerates the original pairs, and verifies every R=4..115 for the minimality assertion. Thus R=115 is the smallest violation in the entire asserted domain R>=4, not merely the first sparse held-out failure. No first-bad hypothesis is asserted.

| q | rad(q) | a(q) | floor(13224/q) | M at that quotient | contribution |
| --- | ---: | ---: | ---: | ---: | ---: |
| 4 | 2 | 1 | 3306 | 20 | 20 |
| 8 | 2 | 2 | 1653 | -11 | -22 |
| 9 | 3 | 1 | 1469 | 4 | 4 |
| 16 | 2 | 3 | 826 | -1 | -3 |
| 25 | 5 | 1 | 528 | -1 | -1 |
| 27 | 3 | 2 | 489 | -4 | -8 |
| 32 | 2 | 4 | 413 | 0 | 0 |
| 36 | 6 | 1 | 367 | -1 | -1 |
| 49 | 7 | 1 | 269 | -2 | -2 |
| 64 | 2 | 5 | 206 | -3 | -15 |
| 72 | 6 | 2 | 183 | -4 | -8 |
| 81 | 3 | 3 | 163 | 0 | 0 |
| 100 | 10 | 1 | 132 | -3 | -3 |
| 108 | 6 | 2 | 122 | -2 | -4 |

Complete restoration, with no cross term omitted:

```text
D_H=||H||^2-||U||^2=21922-3172=18750,
J=-2(<H,F>-<U,A'>)=-1970,
Delta_0=D_H+D_F+J=18750-195-1970=16585,
Delta=Delta_0+2*(-9)*(-97)=18331,
DG=21411, DS=3080, H_ROB margin=14839.
```

The worst tested D_F is -115284 at R=3721; it is not a universal lower bound. At mandatory R=549, D_F=-1402, while at R=5561 it is +3791. Thus the proper-response sign can reverse in actual required regimes even when the complete contraction survives.

**Synthetic controls, not genuine counterexamples.** At R=21, retain the actual Z but replace only its restored endpoint value -7 by -9. The model has DG=345, DS=346, gap -1; actual arithmetic has 357,338, gap 19. It violates the historical convolution relation and is explicitly not a refutation of H_Z/H_ROB. Separately, on admitted nonunit radicals 2 and 6 at R=37, arbitrary coefficients (2,1) give response (-1,1,-1,0,0,1), squared norm 4 versus coefficient norm 5. This shows that the exact support/radical map alone cannot prove nonexpansion; the coefficients are not claimed to be actual Mertens values.

### G. Hidden Variables And Arithmetic Classification

Let Omega(d) here mean the number of distinct prime factors of squarefree d. The exact radical-column Gram is inherited from PD:

```text
<v_d,v_e> = mu(d)mu(e) 2^Omega(gcd(d,e)).
```

The relevant NEW contraction form subtracts the identity matrix because the common-divisor transform sends v_d to the single coordinate e_d. On nonunit prime radicals its entries are all 1. Hence

```text
D_F = (sum_p A_p)^2 >=0       when A_d=0 for every composite radical d.
```

This statement holds for arbitrary real prime coefficients, not only one finite dataset. A negative D_F therefore requires a nonzero composite-radical amplitude. This is a genuine structural necessity on this proper response, not an exclusion of that configuration in full arithmetic.

At R=115, prime amplitudes sum to -27, giving +729. Composite radicals 6 and 10 contribute diagonal +534 and their mutual cross term +156. Prime/composite mixed interactions contribute -1614, so

```text
D_F=729+534+156-1614=-195.
```

Every nonzero A_d in this certificate is negative. The negative effect is not random sign noise: the radical parity and shared-divisor multiplicity determine the cross coefficients. Historical restoration is essential to the surviving complete result, but its mixed term is itself negative here; it is not a uniformly favorable local payment.

### H. Mathematical Interpretation And Proofs

**UM1: affine endpoint identity.** For any finite vector Z indexed by 1..N and its multiples transform T, the multiples transform of e_1 is e_1. If C=Z-m e_1 and S=T-m e_1, expanding both norms cancels m^2 exactly:

```text
||C||^2-||S||^2
 = ||Z||^2-||T||^2 + 2m(T_1-Z_1)
 = Delta_0 + 2m sum_(g>=2)Z_g.
```

Insert the genuine m=M(X), C=H-E from PD, and sum Z=2M(N). This proves the displayed full identity. Equivalently,

```text
Delta_0=B^2-4M(N)B+sum_(g>=2)C_g^2-sum_(d>=2)S_d^2.
```

PD's nonunit powerful denominators satisfy q>=4. Thus Z and Delta_0 can be expressed using strict-history values and M(t) at t<=floor(X/4), without M(X). The precise largest required index is max(R-1,floor(X/4)); only the displayed bilinear interaction uses M(X). Those later values are DEPENDENT exact coordinates of the historical mu(<R) source, not independent allowed inputs for a bound. This is an exact representation, not a new recursive norm estimate.

**UM5: first indefinite support.** For squarefree d, sum_(i|g|d)mu(d/g)=1_(i=d), so the multiples transform sends v_d to e_d. Therefore D_F is the quadratic form G-I. For R<=36, admitted nonunit radicals d satisfy d^2<=R-1<36 and are prime; G-I is the all-ones matrix and is positive semidefinite. At R=37, radical 6 enters. The d=2,6 principal matrix is

```text
[ 1 -2 ]
[-2  3 ],    determinant=-1,
(2,1)(G-I)(2,1)^T = -1.
```

Hence 37 is the first possible support threshold for an arbitrary-coefficient failure; the first GENUINE observed failure is 115, independently checked exhaustively through that root. Neither conclusion proves that full Z or full C fails contraction. The historical interaction J and unit interaction 2M(X)B have been retained throughout.

#### 2. FOUR-WAY SOURCE MAP

| Field | Euler / finite AC | VF / actual primes | NNS / OAI | Square blocks |
| --- | --- | --- | --- | --- |
| Original object | Literal ordered mu(a)mu(b) floor source Q at X=R^2-1; gcd and common-divisor vectors | Full centered wheel li(X)-pi(X), with virtual divisors; #915 separately uses historical/current clipping and native weights | Original ideal-labelled compensated polynomial, character/profile/height/exclusion data | Full M(X), not one shell increment |
| Verified relation used | EXACT_IDENTITY: original floor, convolution and endpoint declarations; GD/PD paper reconstruction checked finitely | NOT_EQUIVALENT to Q; prime/Mobius cofactor-weighted coupling is not equality of errors | ONE_WAY global Mertens consequence through native zeta bridge; OPEN_BRIDGE for these literal coefficients | EXACT_IDENTITY: Q=2M(R-1)-M(X) |
| Preserved information | Both pair orientations, zero squareful weights, floors, K_R, every H/F/unit cross | No changed prime membership, clipping, historical compression or denominator claimed | No fictitious Mobius/Hecke phase identification; no source admission inferred from a Gram shape | Both historical and endpoint terms; all-prefix return still required |
| Remaining consumer | Uniform source norm/payment is OPEN | Canonical prime discrepancy and first-bad payment OPEN | Original complete contour return remains separate from this census | Compiled finite-C -> finite-A -> energy -> RH is conditional on arithmetic |

### I. Proposed Theorem Or Conjecture

**UM3, H_ROB (CONJECTURE).** For the genuine Mobius function, every integer R>=4, and the exact C,S,H,E,Z,T,B defined in D,

```text
||Z||_2^2-||T||_2^2 >= 2*|M(R^2-1)*B|.
```

The coefficient 2 is fixed algebraically, not fitted. There is no first-bad, random-sign, prime-distribution or independent future-data premise. R=3 is a known excluded failure; R=2 is equality. The assertion would imply H_PRE and the earlier H_Z, hence Q^2<=DS<=DG. It is strictly stronger than merely requiring the observed-sign restored gap to be nonnegative. Tested: 525 eligible roots, including the full interval 4..256, powerful-admission boundaries, 549,5561 and dyadic neighbors through 8193. Strongest tested relative challenge: R=21, 70/89 of Delta_0 used by the absolute unit interaction. No all-scale constant or optimality follows.

The first missing proof is an independently justified inequality for the JOINT historical/nonunit expression. Proving prime-only nonunit positivity does not suffice: UM4 and UM5 isolate the mixed-radical obstruction. The displayed affine identity is not itself such a proof.

### J. Relationship To The Proof Objective

#### 3. FIRST SIGNED LOSS

| Source step | Discarded information / cost | Recovery tested | Remaining bill / falsifier |
| --- | --- | --- | --- |
| GD smooth reconstruction, three-Mertens triangle | Loses joint signs in M(A_h)+M(A_k)-M(t); retains only existing Mertens-power scale | PD historical/powerful separation, then complete Delta_0 | Joint H/F estimate still unproved; do not replace future coordinates by independent data |
| Q=sum C followed by Cauchy-Schwarz | Q^2<=(R-1)DG; factor R-1 in the square | H_ROB would imply Q^2<=DS<=DG | H_ROB is a conjecture; DG still needs target-scale payment |
| Treating nonunit radical transform as automatically contractive | Drops prime/composite-radical interactions in G-I | Exact D_F and full H/F restoration | Genuine R=115: 404<599, gap -195 |
| Reassembling C=Z-M(X)e_1 | Dropping or absolutizing 2M(X)B changes the full gap | Exact affine identity, H_ROB finite test | Term has both signs; synthetic R21 control shows it cannot be arbitrary |

#### 4. PAID RECOVERY TEST

The compiled Newton/floor endpoint identity pays EXACT reconstruction, not a norm sign. The already-proved triangular Abel source retains its signed strict cross term and explicitly supplies no finite-C bound; it does not prove H_ROB. Accepted GD and the new PD paper decomposition supply exact coefficients and strict-history control, but PD's historical bound alone does not pay Delta_0's future interaction. #1131 supplies a weighted ideal-principal mass estimate on a different carrier, not an isometry or coefficient map to C. Proper cofactor positivity and near-resonance facts have no proved transfer to this complete radical gap. The smallest source-faithful remaining input is the joint inequality in I, or another independent complete-source estimate; no generic covariance hypothesis is treated as paid.

If H_ROB and, separately, a fixed uniform DG<=B_0 R^2 K_R were proved, then |Q|<=sqrt(B_0)R sqrt(K_R) would feed the existing `EulerSelfDualFiniteCStatement` consumer. Neither premise was proved here. GD's accepted alternative exponent consumer does not require H_ROB, so this is optional recovery, not a compulsory new gate on all routes. A useful sign restriction is not a new Mertens exponent by itself.

#### 5. NET RESULT / ADMISSION VERDICT

The exact R115 falsifier retires one auxiliary explanation. The prime/composite-radical classification and affine endpoint separation give supporting structural information. The stronger complete conjecture has reproducible finite evidence but no uniform proof. Neither admission criterion for a new global proof route has been met; no change to the nine protected routes or canonical theorem is proposed.

### K. Falsification And Uncertainty Audit

H_PRE and H_ROB were published and read back before computation. H_F and the radical null were explicitly registered after primary results, before their follow-up calculation. The standalone R115 verification uses a third arithmetic method and no census output. Its failure is exact regardless of the exploratory selection. The R37 and modified-R21 examples are labelled synthetic and cannot refute the original arithmetic or a first-bad theorem.

No floating-point uncertainty affects a claim. Runtime decimals are diagnostic only. Python recomputes all norms using unbounded integers, checks every complete vector, and therefore does not merely copy the primary's derived totals. Syntax checks passed. No local Lean ran, no new Lean theorem is claimed, and no independent Referee ACCEPT is self-issued. The finite search is not exhaustive above 256; only the exact frozen roots are covered. A claim of first H_F failure is justified because 115 lies inside the exhaustive interval and the separate certificate checks all earlier eligible roots.

### L. Specialist Handoffs And Continuity

**Proof Architect:** add UM4 as a narrowly scoped falsifier, not a refutation of PD/H_Z. H_ROB is a new optional complete-source candidate with fixed constants and exact unit separation; no route or exponent promotion. Source -> lost mixed radical terms -> actual R115 failure -> restored historical expression is the useful dependency record.

**Finite Wheel:** PD's prime-only nonunit contraction extends to no arbitrary radical vector once 6 enters. At R115 the -1614 prime/composite bill exceeds +1419 from the remaining nonunit sectors. Seek a coefficient-level historical relation paying the joint expression, not sparse-support positivity or a larger unchanged norm census.

**Owner Payment:** this is an Euler gcd response, not literal #915 admission. FA's historical-composite positivity and current-mask restrictions remain separate; do not map auxiliary denominators q to prime-owner labels. No FA/MC scan was repeated.

**Analytic Type II:** the G-I form is not the Nyman periodic Gram and no transport is asserted. DM's complete Nyman error/variance result remains paper/review-pending here. A signed moment can be used only with an exact coefficient and cutoff map.

**Adversarial Referee:** independently review UM1 and UM5, the minimum R115 certificate, and the scope of H_ROB. Check the complete historical interaction and unit sign, not only D_F. Review is PENDING; no author-issued acceptance.

**Lean Verification:** the standalone small certificate and elementary radical-column statement are available if independently accepted and strategically useful. No duplicate identity PR is requested; the accepted same-signal OAI return remains the existing implementation queue. Do not formalize H_ROB as an assumed achieved estimate.

Both Nov 10 and Nov 11 reports for all seven roles were retrieved at `agent-reports@5515b10ceab68bd311e64bfc67f0538486b02600`. TODAY=AVAILABLE for all seven; unchanged Nov 10 findings are YESTERDAY=CARRY_FORWARD, not today's new work. Consumed latest sections: Coordinator FL/changed-source instruction; Owner FA; Analytic DM; Wheel PD and earlier accepted GD; own DZ; Referee NP/GD/DZ verdicts; Lean FFR. The Nov 10 GC, DR, RC, IR/IRR and MD/FFR findings were read at their recorded scopes. External inbox `038018145c0fddb2f6306c0712373adf9cd1ea52` has no new entry after October 18. Retain its cofactor-weight and first-bad versus all-root distinctions; old single-route priorities are superseded. No missing run or successful execution is inferred from schedules.

The freshness check begun at 16:22:35 UTC found unchanged main and unchanged other-role Nov 11 blobs. Only this run's own checkpoint changed the report branch. No newer upstream result was silently omitted.

### M. Ranked Experimental Hypothesis Portfolio

| Rank | Candidate | Disposition |
| --- | --- | --- |
| 1 | H_ROB: full Delta_0>=2|M(X)B| | CONJECTURE; 525 strict finite passes. Investigate actual joint historical/composite-radical structure before another scan. |
| 2 | Prime-only radical gap is a square; composite radicals necessary for D_F<0 | PAPER_PROOF supporting restriction, independent review pending. Composite amplitudes occur genuinely, so no global exclusion follows. |
| 3 | H_F: nonunit response contracts by itself | REFUTED at R115; reject this repair without altering the whole-source conjecture. |
| 4 | H_Z / GC5 | Retain as CONJECTURE; H_ROB would imply both. Restored values are validation, not rediscovery credit. |
| 5 | Historical-normalized complete norm payment | Still unproved; no fitted finite constant or source-equivalence relabelling counts as payment. |

### N. Next-Run Resume Capsule

Resume from the exact decomposition Delta=D_H+D_F+J+2M(X)B, not new prime tables. Completed: 527-root changed-source preregistered test; 561,282,954 independent ordered-pair reconstruction; all five complete vectors/norms checked; post-primary 133 negative D_F cases; smallest genuine R115 certificate; first indefinite abstract support R37. H_PRE/H_ROB survived finitely; H_F failed. The genuine R115 source still satisfies H_ROB with margin 14839.

**Single highest-value next question:** can the prime/composite-radical mixed bill be linked coefficientwise to the historical vector strongly enough to prove or refute the full H_ROB inequality? Start with the exact -1614 contribution at R115 and the sharp unit margin at R21. Require an independently meaningful arithmetic restriction, not a bad event defined merely as failure of the desired gap. Do not enlarge this census without that changed discriminator. Keep every H/F/unit term and the true K_R.

Main `dda92f9ce59627b4c1f1317082f728648d330a0a`; checkpoint commit `439c17543f95fb506ce3426f668a018f1a03656c`, blob `cff358fd7d5f2fa26241c06c979bb658695b8a86`, exactly read back before execution. Full source, report-input and code hashes follow. Only the owned daily report is written remotely; no Lean/source, other report, branch, PR, issue, workflow, merge, schedule or agent launch was changed. All computation sessions finished. Final publication is claimed only after commit/readback, in its appended receipt.

## Reproduction

The complete executed programs follow in the assembled report. Commands assume the files are in /workspace, matching this run. No external Python packages are required.

```bash
g++ -std=c++20 -O2 -Wall -Wextra -Werror /workspace/um_census.cpp -o /workspace/um_census
/workspace/um_census /workspace/um_results.json
g++ -std=c++20 -O2 -Wall -Wextra -Werror /workspace/um_direct.cpp -o /workspace/um_direct
/workspace/um_direct /workspace/um_direct.txt
python /workspace/um_compare.py
python /workspace/um_followup.py
python /workspace/um_certificate.py
python -m py_compile /workspace/um_compare.py /workspace/um_followup.py /workspace/um_certificate.py
```

Runtime-dependent JSON contains elapsed seconds, so its byte hash need not reproduce across runs. The exact vector comparison and rational certificates are deterministic; the direct text output is deterministic. No generated raw table is required as an unverified input: the programs reconstruct it.


## Source And Continuity Ledger

### Original Main Sources

| Path at main dda92f9ce59627b4c1f1317082f728648d330a0a | Blob SHA |
| --- | --- |
| [AGENTS.md](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/AGENTS.md) | `c9c89f01b90b526de9f3e8ea92478e36504711b6` |
| [CURRENT_PROOF_CONTRACT.md](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/CURRENT_PROOF_CONTRACT.md) | `95566e37c8eaeb99ee680660df4f9d2e06ea5038` |
| [docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md) | `e922d4ba9362a1ae196af8f6de88f7417f92087c` |
| [docs/COORDINATE_ATLAS.md](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/docs/COORDINATE_ATLAS.md) | `cd0419d00a37739fe5a292f5cb738e33213949d5` |
| [docs/PROOF_DEPENDENCY_DAG.md](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/docs/PROOF_DEPENDENCY_DAG.md) | `eee764cefe70035a9f6c7df26ad787fbfd0fb233` |
| [research/EULER_HYBRID_ABEL_GRAM_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/EULER_HYBRID_ABEL_GRAM_20261027.lean) | `2a94dd8fd56fc03e95f732fb44b778a8d4f83e26` |
| [research/EULER_FRACTIONAL_COUPLED_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/EULER_FRACTIONAL_COUPLED_20261027.lean) | `e6c4b1690e497760d366e36b28a1f7aa60e19f85` |
| [research/EULER_SELF_DUAL_POINTWISE_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/EULER_SELF_DUAL_POINTWISE_20261027.lean) | `c327c556f39ee7014fd774b24d0f95a1ece050e0` |
| [research/EULER_SELF_DUAL_FINITE_C_BRIDGE_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/EULER_SELF_DUAL_FINITE_C_BRIDGE_20261027.lean) | `e97561ef330a9996fd807d8910369f0698147b01` |
| [research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean) | `e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73` |
| [RHLean/Proof/SquareRootLegalAncestryGramReduction.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/RHLean/Proof/SquareRootLegalAncestryGramReduction.lean) | `1270d4d91c53b50b110d10014f223f427fb7a575` |
| [RHLean/Proof/SquareRootAncestryRoot.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/RHLean/Proof/SquareRootAncestryRoot.lean) | `69668e5305c95ad7a4a9f88c74a8149298bab87b` |
| [research/oai_434/VF919WindowErrorClosure.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/oai_434/VF919WindowErrorClosure.lean) | `f629db1b2b65d6ec042ac9432397d4b6316200c6` |
| [research/oai_434/VF919ExplicitSquareBlockPacking.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/oai_434/VF919ExplicitSquareBlockPacking.lean) | `32999039fdeea99c58a070c1c4ee9c140720dd44` |
| [research/oai_434/VF919ExplicitFixedSourceSlotCount.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/oai_434/VF919ExplicitFixedSourceSlotCount.lean) | `bad5aab0a60e96d19e7c9550cd7c0a072288bc0f` |
| [research/oai_434/VF919NativeStrictMertens.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/oai_434/VF919NativeStrictMertens.lean) | `b33a4883e1ddb0551b0f11f062bce46680d87450` |
| [scripts/lean/window_error_closure/WindowErrorClosureAudit.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/scripts/lean/window_error_closure/WindowErrorClosureAudit.lean) | `1f17f9401a63d16227db2e2aad020b9f74bc5f4e` |
| [research/oai_434/VF919PrincipalResponseMass.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/oai_434/VF919PrincipalResponseMass.lean) | `5f7e812108ff7eff4a60da7055c2dd5f852c4941` |

### Immutable Handoff Inputs

All rows are at agent-reports snapshot 5515b10ceab68bd311e64bfc67f0538486b02600. The two Coordinator mirror blobs match at both dates.

| Date / role | Blob SHA |
| --- | --- |
| [2026-11-10/00-coordinator-am](https://github.com/OVVO-Financial/RH_Lean/blob/5515b10ceab68bd311e64bfc67f0538486b02600/research/agent_reports/2026-11-10/00-coordinator-am.md) | `4d55b2893f974656c6aa14e48b243827fa8308f8` |
| [2026-11-10/10-owner-payment](https://github.com/OVVO-Financial/RH_Lean/blob/5515b10ceab68bd311e64bfc67f0538486b02600/research/agent_reports/2026-11-10/10-owner-payment.md) | `84afec90414b2394a61b51df46c07b6b540e5942` |
| [2026-11-10/20-analytic-type-ii](https://github.com/OVVO-Financial/RH_Lean/blob/5515b10ceab68bd311e64bfc67f0538486b02600/research/agent_reports/2026-11-10/20-analytic-type-ii.md) | `7ed3a39bec4796f4173b692064af872ea8035048` |
| [2026-11-10/30-finite-wheel](https://github.com/OVVO-Financial/RH_Lean/blob/5515b10ceab68bd311e64bfc67f0538486b02600/research/agent_reports/2026-11-10/30-finite-wheel.md) | `62406503a1ddbbf9330abcdc4cf761f7fbf05795` |
| [2026-11-10/40-prime-census](https://github.com/OVVO-Financial/RH_Lean/blob/5515b10ceab68bd311e64bfc67f0538486b02600/research/agent_reports/2026-11-10/40-prime-census.md) | `a3cfa56072f3893dbf92a18956e1794236bde057` |
| [2026-11-10/50-adversarial-referee](https://github.com/OVVO-Financial/RH_Lean/blob/5515b10ceab68bd311e64bfc67f0538486b02600/research/agent_reports/2026-11-10/50-adversarial-referee.md) | `6529562a5bb21fa192fddadaa91a758b9d125c29` |
| [2026-11-10/60-lean-verification](https://github.com/OVVO-Financial/RH_Lean/blob/5515b10ceab68bd311e64bfc67f0538486b02600/research/agent_reports/2026-11-10/60-lean-verification.md) | `682b334b8f37fa4bfe2d552a1142d852a0db2afd` |
| [2026-11-11/00-coordinator-am](https://github.com/OVVO-Financial/RH_Lean/blob/5515b10ceab68bd311e64bfc67f0538486b02600/research/agent_reports/2026-11-11/00-coordinator-am.md) | `106f6d88708a7545caab43c56ae1bbb915fd97f2` |
| [2026-11-11/10-owner-payment](https://github.com/OVVO-Financial/RH_Lean/blob/5515b10ceab68bd311e64bfc67f0538486b02600/research/agent_reports/2026-11-11/10-owner-payment.md) | `accf2930372234b58e98e8e43e88aeb845b56e9b` |
| [2026-11-11/20-analytic-type-ii](https://github.com/OVVO-Financial/RH_Lean/blob/5515b10ceab68bd311e64bfc67f0538486b02600/research/agent_reports/2026-11-11/20-analytic-type-ii.md) | `0309d49557af30da43a07d72dce93c93c1811157` |
| [2026-11-11/30-finite-wheel](https://github.com/OVVO-Financial/RH_Lean/blob/5515b10ceab68bd311e64bfc67f0538486b02600/research/agent_reports/2026-11-11/30-finite-wheel.md) | `c9989449a814a1a7ee799791c73450872f4c7d3c` |
| [2026-11-11/40-prime-census](https://github.com/OVVO-Financial/RH_Lean/blob/5515b10ceab68bd311e64bfc67f0538486b02600/research/agent_reports/2026-11-11/40-prime-census.md) | `49c1c48f672cf96c93909bd2b412d95bb3587d62` |
| [2026-11-11/50-adversarial-referee](https://github.com/OVVO-Financial/RH_Lean/blob/5515b10ceab68bd311e64bfc67f0538486b02600/research/agent_reports/2026-11-11/50-adversarial-referee.md) | `214e99d8d6133e720f9645dd650a57b01a8c05cf` |
| [2026-11-11/60-lean-verification](https://github.com/OVVO-Financial/RH_Lean/blob/5515b10ceab68bd311e64bfc67f0538486b02600/research/agent_reports/2026-11-11/60-lean-verification.md) | `c86b058b6387de7348b123b22b8f5b8772d5ae9a` |

Report protocol blob: `98b56f98d625b61b7a6491e360d7870fbfe7e7a1`. External inbox blob: `038018145c0fddb2f6306c0712373adf9cd1ea52`. The external record is context, not proof authority.

### SHA-256 Receipts

```text
2d07ffa7178a6790ac96b66df43dda7d29a3ab5925749520337fe7106de3f8e7  /workspace/um_census.cpp
7885ac603e0da938aa831eaa03fa9711e04a8f57bd689f22d0330712d4b91310  /workspace/um_direct.cpp
bad6531f515cd4370794d2a998883c91176c218779d100d62056a9322ac8bdf4  /workspace/um_compare.py
cfd4ce059fadea06db6e193676460bf4549e330555351a3d36936f3c46dd1366  /workspace/um_followup_registration.md
83e90c106b0420d5605dd590e4b866753a493b792dd4e538d19d3bceeea7f2cd  /workspace/um_followup.py
7f91edfdbc077fcfa239cf2e013fa215003c9a44802375da7635a5f8f3f5be0b  /workspace/um_certificate.py
05e1af04328edfbc83f5999b2b62be418b4280081bfcb925d0d8285a08fa74b4  /workspace/um_results.json
0268f81c2bd84227fb82e8a98d3de8a4f55e8d412cd970f146dbc456322ffa59  /workspace/um_direct.txt
e8e872b738d8fad938a34d7860ec03e58b2aba196f010a28e28f576a3e6deea6  /workspace/um_summary.json
d9a6748f8e83bb3499c7ebd8f7cf4cdfb52b645e27bfdd4d1f8e68d403b63beb  /workspace/um_followup_results.json
```

## Exact Executed Programs

### um_census.cpp

```cpp
#include <algorithm>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <numeric>
#include <set>
#include <string>
#include <utility>
#include <vector>

using I = std::int64_t;
using V = std::vector<I>;

struct Powerful { int q, rad, weight; };

std::vector<std::pair<int, int>> factor(int n) {
    std::vector<std::pair<int, int>> out;
    for (int p = 2; p * p <= n; ++p) {
        if (n % p != 0) continue;
        int e = 0;
        do { n /= p; ++e; } while (n % p == 0);
        out.emplace_back(p, e);
    }
    if (n > 1) out.emplace_back(n, 1);
    return out;
}

V invert(const V& s, const std::vector<std::int8_t>& mu) {
    int n = static_cast<int>(s.size()) - 1;
    V c(n + 1);
    for (int g = 1; g <= n; ++g)
        for (int k = 1; k * g <= n; ++k) c[g] += mu[k] * s[k * g];
    return c;
}

V multiples(const V& c) {
    int n = static_cast<int>(c.size()) - 1;
    V s(n + 1);
    for (int d = 1; d <= n; ++d)
        for (int k = d; k <= n; k += d) s[d] += c[k];
    return s;
}

I norm2(const V& v) {
    I ans = 0;
    for (I x : v) ans += x * x;
    return ans;
}

void emit_vec(std::ostream& out, const V& v) {
    out << '[';
    for (std::size_t i = 1; i < v.size(); ++i) {
        if (i > 1) out << ',';
        out << v[i];
    }
    out << ']';
}

int main(int argc, char** argv) {
    if (argc != 2) return 2;
    auto start = std::chrono::steady_clock::now();
    std::vector<Powerful> powerful{{1, 1, 1}};
    for (int q = 4; q <= 8192; ++q) {
        bool ok = true;
        int rad = 1, weight = 1;
        for (auto [p, e] : factor(q)) {
            if (e == 1) ok = false;
            rad *= p;
            weight *= e - 1;
        }
        if (ok) powerful.push_back({q, rad, weight});
    }
    std::set<int> roots;
    for (int r = 2; r <= 256; ++r) roots.insert(r);
    for (const auto& p : powerful) if (4 <= p.q && p.q <= 4096)
        for (int shift = -1; shift <= 1; ++shift) roots.insert(p.q + shift);
    for (int j = 9; j <= 13; ++j)
        for (int shift = -1; shift <= 1; ++shift) roots.insert((1 << j) + shift);
    roots.insert(549);
    roots.insert(5561);
    int max_r = *roots.rbegin(), limit = max_r * max_r - 1;
    std::vector<std::int8_t> mu(limit + 1, 1);
    std::vector<bool> marked(limit + 1, false);
    mu[0] = 0;
    for (int p = 2; p <= limit; ++p) {
        if (marked[p]) continue;
        for (I n = p; n <= limit; n += p) {
            marked[n] = true;
            mu[n] = -mu[n];
        }
        I p2 = I(p) * p;
        if (p2 <= limit)
            for (I n = p2; n <= limit; n += p2) mu[n] = 0;
    }
    std::vector<int> mertens(limit + 1);
    for (int n = 1; n <= limit; ++n) mertens[n] = mertens[n - 1] + mu[n];
    std::ofstream out(argv[1]);
    out << "{\"root_count\":" << roots.size() << ",\"sieve_limit\":" << limit
        << ",\"rows\":[\n";
    I rectangles = 0, direct_pairs = 0, coefficient_checks = 0, future_labels = 0;
    int pre_fail = 0, rob_fail = 0, restored_fail = 0, direct_roots = 0;
    bool first = true;
    for (int r : roots) {
        int n = r - 1;
        I x = I(r) * r - 1;
        V s(n + 1), u(n + 1), a(n + 1), aq(n + 1), ep(n + 1);
        for (int d = 1; d <= n; ++d) {
            if (mu[d] == 0) continue;
            int b = n / d;
            std::vector<int> smooth{1};
            for (auto [p, exponent] : factor(d)) {
                (void)exponent;
                std::size_t old = smooth.size();
                for (std::size_t j = 0; j < old; ++j)
                    for (I h = I(smooth[j]) * p; h <= b; h *= p)
                        smooth.push_back(static_cast<int>(h));
            }
            std::sort(smooth.begin(), smooth.end());
            for (std::size_t ih = 0; ih < smooth.size(); ++ih)
                for (std::size_t ik = ih; ik < smooth.size(); ++ik) {
                    int h = smooth[ih], k = smooth[ik], ah = b / h, ak = b / k;
                    I t = x / (I(d) * d * h * k), mult = ih == ik ? 1 : 2;
                    assert(std::max(ah, ak) <= t && t < I(ah + 1) * (ak + 1));
                    I history = mertens[ah] + mertens[ak];
                    s[d] += mult * (history - mertens[t]);
                    u[d] += mult * (history - (t < r ? mertens[t] : 0));
                    if (t >= r) { a[d] += mult * mertens[t]; future_labels += mult; }
                    rectangles += mult;
                }
        }
        int qcount = 0;
        for (const auto& p : powerful) if (p.q <= n) {
            ++qcount;
            I value = I(p.weight) * mertens[x / p.q];
            aq[p.rad] += value;
            for (int g = 1; g <= p.rad; ++g)
                if (p.rad % g == 0) ep[g] += mu[p.rad / g] * value;
        }
        assert(a == aq);
        V c = invert(s, mu), h = invert(u, mu), e = invert(a, mu);
        assert(e == ep && multiples(c) == s);
        I m = mertens[x], mh = mertens[n], q = 0, btotal = 0, he = 0;
        for (int g = 1; g <= n; ++g) {
            assert(c[g] == h[g] - e[g]);
            if (I(g) * g > n) assert(e[g] == 0);
            q += c[g];
            if (g >= 2) btotal += c[g];
            he += h[g] * e[g];
            ++coefficient_checks;
        }
        assert(q == 2 * mh - m);
        assert(std::accumulate(h.begin(), h.end(), I(0)) == 2 * mh);
        assert(std::accumulate(e.begin(), e.end(), I(0)) == m);
        V z = c;
        z[1] += m;
        V t = multiples(z);
        I dg = norm2(c), ds = norm2(s), d0 = norm2(z) - norm2(t);
        I mixed = 2 * m * btotal, gap = dg - ds, robust = d0 - std::abs(mixed);
        assert(gap == d0 + mixed);
        assert(dg == norm2(h) + norm2(e) - 2 * he);
        int firstpre = 0, firstrob = 0, firstrestored = 0;
        if (r >= 4 && d0 < 0) { firstpre = pre_fail == 0; ++pre_fail; }
        if (r >= 4 && robust < 0) { firstrob = rob_fail == 0; ++rob_fail; }
        if (r >= 4 && gap < 0) { firstrestored = restored_fail == 0; ++restored_fail; }
        bool literal = r <= 256 || r == 549 || r == 5561 || firstpre || firstrob || firstrestored;
        if (literal) {
            V direct(n + 1);
            for (int i = 1; i <= n; ++i) if (mu[i])
                for (int j = i; j <= n; ++j) if (mu[j]) {
                    int mult = i == j ? 1 : 2;
                    direct[std::gcd(i, j)] += I(mult) * mu[i] * mu[j] * (x / (I(i) * j));
                    direct_pairs += mult;
                }
            assert(direct == c);
            ++direct_roots;
        }
        I kn = 1, kd = 1;
        int kat = 0;
        for (int j = 0; j < r; ++j) {
            I nn = I(mertens[j] - 1) * (mertens[j] - 1), dd = j + 1;
            if (nn * kd > kn * dd) { kn = nn; kd = dd; kat = j; }
        }
        I kg = std::gcd(kn, kd); kn /= kg; kd /= kg;
        if (!first) out << ",\n";
        first = false;
        out << "{\"R\":" << r << ",\"M\":" << m << ",\"Mh\":" << mh
            << ",\"Q\":" << q << ",\"C1\":" << c[1] << ",\"B\":" << btotal
            << ",\"DG\":" << dg << ",\"DS\":" << ds << ",\"D0\":" << d0
            << ",\"mixed\":" << mixed << ",\"gap\":" << gap << ",\"robust\":" << robust
            << ",\"H2\":" << norm2(h) << ",\"E2\":" << norm2(e) << ",\"HE\":" << he
            << ",\"K_num\":" << kn << ",\"K_den\":" << kd << ",\"K_at\":" << kat
            << ",\"powerful_count\":" << qcount << ",\"literal\":" << (literal ? "true" : "false");
        {
            out << ",\"C\":"; emit_vec(out, c);
            out << ",\"S\":"; emit_vec(out, s);
            out << ",\"H\":"; emit_vec(out, h);
            out << ",\"E\":"; emit_vec(out, e);
            out << ",\"A\":"; emit_vec(out, a);
        }
        out << '}';
    }
    double seconds = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
    out << "\n],\"counts\":{\"rectangles\":" << rectangles << ",\"coefficients\":" << coefficient_checks
        << ",\"future_labels\":" << future_labels << ",\"direct_pairs\":" << direct_pairs
        << ",\"direct_roots\":" << direct_roots << ",\"pre_fail\":" << pre_fail
        << ",\"rob_fail\":" << rob_fail << ",\"restored_fail\":" << restored_fail
        << "},\"elapsed_seconds\":" << seconds << "}\n";
    std::cout << "roots=" << roots.size() << " pre_fail=" << pre_fail << " robust_fail=" << rob_fail
              << " restored_fail=" << restored_fail << " seconds=" << seconds << '\n';
}
```

### um_direct.cpp

```cpp
#include <cassert>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <unordered_map>
#include <vector>

using I = std::int64_t;
std::vector<int> mu(8193), prefix(8193);
std::unordered_map<I, I> cache;

I M(I n) {
    if (n < static_cast<I>(prefix.size())) return prefix[n];
    if (auto it = cache.find(n); it != cache.end()) return it->second;
    I answer = 1;
    for (I left = 2, right; left <= n; left = right + 1) {
        I quotient = n / left;
        right = n / quotient;
        answer -= (right - left + 1) * M(quotient);
    }
    cache.emplace(n, answer);
    return answer;
}

int main(int argc, char** argv) {
    if (argc != 2) return 2;
    auto start = std::chrono::steady_clock::now();
    std::vector<int> radical(8193), multiplicity(8193);
    std::set<int> roots;
    for (int n = 1; n <= 8192; ++n) {
        int remaining = n, sign = 1, rad = 1, mass = 1;
        bool squarefree = true, powerful = true;
        for (int p = 2; p <= remaining; ++p) if (remaining % p == 0) {
            int exponent = 0;
            while (remaining % p == 0) { remaining /= p; ++exponent; }
            rad *= p;
            sign = -sign;
            squarefree = squarefree && exponent == 1;
            powerful = powerful && exponent >= 2;
            mass *= exponent - 1;
        }
        mu[n] = squarefree ? sign : 0;
        prefix[n] = prefix[n - 1] + mu[n];
        if (powerful) { radical[n] = rad; multiplicity[n] = mass; }
        if (n >= 4 && n <= 4096 && powerful)
            for (int s : {-1, 0, 1}) roots.insert(n + s);
    }
    for (int r = 2; r <= 256; ++r) roots.insert(r);
    for (int h = 512; h <= 8192; h *= 2)
        for (int s : {-1, 0, 1}) roots.insert(h + s);
    roots.insert(549); roots.insert(5561);
    I pairs = 0;
    std::ofstream out(argv[1]);
    for (int r : roots) {
        I x = I(r) * r - 1;
        std::vector<I> c(r), a(r);
        std::vector<int> active;
        for (int n = 1; n < r; ++n) if (mu[n]) active.push_back(n);
        for (std::size_t i = 0; i < active.size(); ++i)
            for (std::size_t j = 0; j <= i; ++j) {
                int u = active[i], v = active[j], mult = i == j ? 1 : 2;
                c[std::gcd(u, v)] += I(mult) * mu[u] * mu[v] * (x / (I(u) * v));
                pairs += mult;
            }
        for (int q = 1; q < r; ++q) if (radical[q])
            a[radical[q]] += I(multiplicity[q]) * M(x / q);
        I endpoint = M(x), k_num = 1, k_den = 1;
        int k_at = 0;
        assert(std::accumulate(c.begin(), c.end(), I(0)) == 2 * prefix[r - 1] - endpoint);
        for (int n = 0; n < r; ++n) {
            I value = I(prefix[n] - 1) * (prefix[n] - 1), den = n + 1;
            if (value * k_den > k_num * den) { k_num = value; k_den = den; k_at = n; }
        }
        I g = std::gcd(k_num, k_den); k_num /= g; k_den /= g;
        out << r << ' ' << prefix[r - 1] << ' ' << endpoint << ' '
            << k_num << ' ' << k_den << ' ' << k_at << '\n';
        for (int g2 = 1; g2 < r; ++g2) out << c[g2] << (g2 + 1 == r ? '\n' : ' ');
        for (int d = 1; d < r; ++d) out << a[d] << (d + 1 == r ? '\n' : ' ');
    }
    std::cout << "roots=" << roots.size() << " ordered_pairs=" << pairs
              << " recursive_M_sites=" << cache.size() << " seconds="
              << std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count() << '\n';
}
```

### um_compare.py

```python
"""Compare independently reconstructed complete coefficients and summarize tests."""
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path


def mobius_trial(n):
    value = 1
    p = 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            value = -value
            if n % p == 0:
                return 0
            while n % p == 0:
                n //= p
        p += 1
    return -value if n > 1 else value


def run():
    primary = json.loads(Path('/workspace/um_results.json').read_text())
    lines = Path('/workspace/um_direct.txt').read_text().splitlines()
    assert len(lines) == 3 * primary['root_count']
    checked = 0
    for i, row in enumerate(primary['rows']):
        r, mh, m, kn, kd, kat = map(int, lines[3 * i].split())
        c = list(map(int, lines[3 * i + 1].split()))
        a = list(map(int, lines[3 * i + 2].split()))
        assert r == row['R'] and len(c) == len(a) == r - 1
        assert (mh, m, kn, kd, kat) == tuple(row[k] for k in ('Mh', 'M', 'K_num', 'K_den', 'K_at'))
        s = [sum(c[d - 1::d]) for d in range(1, r)]
        e = [sum(mobius_trial(k) * a[g * k - 1] for k in range(1, (r - 1) // g + 1)) for g in range(1, r)]
        h = [v + w for v, w in zip(c, e)]
        for name, vec in [('C', c), ('S', s), ('A', a), ('E', e), ('H', h)]:
            assert vec == row[name], (r, name)
        exact_norms = (sum(v*v for v in c), sum(v*v for v in s),
                       sum(v*v for v in h), sum(v*v for v in e),
                       sum(v*w for v, w in zip(h, e)))
        assert exact_norms == tuple(row[k] for k in ('DG', 'DS', 'H2', 'E2', 'HE'))
        z = c.copy()
        z[0] += m
        t = [sum(z[d - 1::d]) for d in range(1, r)]
        d0 = sum(v * v for v in z) - sum(v * v for v in t)
        mixed = 2 * m * sum(c[1:])
        assert (d0, mixed, d0 + mixed, d0 - abs(mixed)) == tuple(row[k] for k in ('D0', 'mixed', 'gap', 'robust'))
        checked += len(c)
    eligible = [x for x in primary['rows'] if x['R'] >= 4]
    compact = lambda x: {k: v for k, v in x.items() if not isinstance(v, list)}
    summary = {
        'roots': primary['root_count'], 'eligible_roots': len(eligible),
        'complete_coefficients_per_vector_checked': checked,
        'mismatches': 0, 'primary_counts': primary['counts'],
        'min_D0': compact(min(eligible, key=lambda x: x['D0'])),
        'min_robust_margin': compact(min(eligible, key=lambda x: x['robust'])),
        'max_unit_to_gap_ratio': compact(max(eligible, key=lambda x: Fraction(abs(x['mixed']), x['D0']))),
        'positive_unit_count': sum(x['mixed'] > 0 for x in eligible),
        'negative_unit_count': sum(x['mixed'] < 0 for x in eligible),
        'zero_unit_count': sum(x['mixed'] == 0 for x in eligible),
        'zero_B_roots': [x['R'] for x in eligible if x['B'] == 0],
        'max_vector_abs': max(abs(v) for x in primary['rows']
                              for k in ('C', 'S', 'A', 'E', 'H') for v in x[k]),
        'selected': [compact(x) for x in primary['rows'] if x['R'] in [2, 3, 4, 7, 10, 11, 17, 21, 549, 5561, 8191, 8192, 8193]],
    }
    row = next(x for x in primary['rows'] if x['R'] == 21)
    z = row['C'].copy()
    z[0] += row['M']
    fake = z.copy()
    fake[0] -= -9
    sfake = [sum(fake[d - 1::d]) for d in range(1, 21)]
    summary['posthoc_synthetic_control'] = {
        'R': 21, 'actual_M': -7, 'model_M': -9,
        'C_model': fake, 'DG_model': sum(x*x for x in fake),
        'DS_model': sum(x*x for x in sfake),
        'classification': 'not genuine arithmetic; not a refutation of H_Z or H_ROB',
    }
    for x in summary['selected']:
        den = x['R']**2 * Fraction(x['K_num'], x['K_den'])
        x['DG_over_R2K'] = str(Fraction(x['DG']) / den)
        x['DS_over_R2K'] = str(Fraction(x['DS']) / den)
        x['D0_over_R2K'] = str(Fraction(x['D0']) / den)
    summary['sha256'] = {p: hashlib.sha256(Path('/workspace', p).read_bytes()).hexdigest()
                         for p in ['um_census.cpp', 'um_direct.cpp', 'um_compare.py', 'um_results.json', 'um_direct.txt']}
    Path('/workspace/um_summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    run()
```

### um_followup_registration.md

```text
# UM Follow-Up Registration

2026-11-11 16:13 UTC. This is a post-primary-result mechanism investigation,
not an independently held-out confirmation set. No new roots or fitted constants.
Primary H_PRE and H_ROB have no failures on the frozen 527 roots.

Question: is the observed positive Delta_0 already present in the nonunit
powerful response, or supplied by its full historical interaction?

For F=E-M(X)e_1 and A'=A-M(X)e_1, the multiples transform maps F to A'.
Compute D_F=||F||^2-||A'||^2 and D_H=||H||^2-||U||^2,
J=-2(<H,F>-<U,A'>), retaining Delta_0=D_H+D_F+J exactly.
The new auxiliary hypothesis H_F is D_F>=0 for every R>=4.
Any negative exact value refutes H_F only, not H_PRE/H_ROB or an endpoint theorem.
Search the existing 527 registered rows and use the independently reconstructed
vectors to verify every decisive value. Do not silently describe this as preregistered
before the primary results.

Algebraic null, derived before executing this follow-up: on nonunit radical columns,
V^T V-I has entries mu(d)mu(e)2^omega(gcd(d,e))-1_(d=e).
If R<=36 every admitted nonunit squarefree radical is prime, so this matrix is
all ones and positive semidefinite. At R=37 radical 6 first enters: on d=2,6
the principal matrix is [[1,-2],[-2,3]], determinant -1. Coefficients (2,1)
give D_F=-1. This is a synthetic support-respecting control, not actual Mertens data.
Verify the minimal radical threshold and retain the full restoration terms.
```

### um_followup.py

```python
"""Post-primary exact mechanism check; see its separate registration."""
import json
from pathlib import Path

data = json.loads(Path('/workspace/um_results.json').read_text())
rows = []
for r in data['rows']:
    h, e, a = r['H'], r['E'], r['A']
    f, ap = e.copy(), a.copy()
    f[0] -= r['M']
    ap[0] -= r['M']
    u = [sum(h[d - 1::d]) for d in range(1, r['R'])]
    tf = [sum(f[d - 1::d]) for d in range(1, r['R'])]
    assert tf == ap
    dh = sum(x*x for x in h) - sum(x*x for x in u)
    df = sum(x*x for x in f) - sum(x*x for x in ap)
    mixed = -2 * (sum(x*y for x, y in zip(h, f)) - sum(x*y for x, y in zip(u, ap)))
    assert dh + df + mixed == r['D0']
    rows.append({'R': r['R'], 'DH': dh, 'DF': df, 'HF_mixed': mixed, 'D0': r['D0']})
failures = [r for r in rows if r['R'] >= 4 and r['DF'] < 0]
selected = {7, 10, 11, 21, 36, 37, 38, 549, 5561, 8193}
if failures:
    selected.add(failures[0]['R'])
summary = {
    'roots': len(rows), 'negative_DF_count': len(failures),
    'first_negative_DF': failures[0] if failures else None,
    'minimum_DF': min(rows, key=lambda r: r['DF']),
    'selected': [r for r in rows if r['R'] in selected],
    'model_radicals': [2, 6], 'model_coefficients': [2, 1],
    'model_gram_minus_identity': [[1, -2], [-2, 3]],
    'model_vector': [-1, 1, -1, 0, 0, 1],
    'model_DF': -1,
    'proper_response_only': True,
}
assert sum(x*x for x in summary['model_vector']) - (2**2 + 1**2) == -1
if failures:
    original = next(r for r in data['rows'] if r['R'] == failures[0]['R'])
    summary['first_certificate'] = original
Path('/workspace/um_followup_results.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({k: v for k, v in summary.items() if k != 'first_certificate'}, indent=2))
```

### um_certificate.py

```python
"""Small standalone certificate. No census output or prime sieve is imported."""
import json
from itertools import accumulate
from math import gcd

R = 115
X = R * R - 1
mu = [0] * (X + 1)
mu[1] = 1
# Solve 1*mu = delta_1 by increasing divisors, independently of factor sieving.
for d in range(1, X + 1):
    for n in range(2 * d, X + 1, d):
        mu[n] -= mu[d]
M = list(accumulate(mu))


def powerful(q):
    n, rad, weight = q, 1, 1
    for p in range(2, q + 1):
        if n % p:
            continue
        exponent = 0
        while n % p == 0:
            n //= p
            exponent += 1
        if exponent == 1:
            return None
        rad *= p
        weight *= exponent - 1
    return rad, weight


def response(r):
    x = r*r - 1
    a, f, terms = [0]*r, [0]*r, []
    for q in range(4, r):
        info = powerful(q)
        if info is None:
            continue
        d, weight = info
        v = weight * M[x // q]
        a[d] += v
        terms.append([q, d, weight, x // q, M[x // q], v])
        for g in range(1, d + 1):
            if d % g == 0:
                f[g] += mu[d // g] * v
    return a, f, terms


first = None
for r in range(4, R + 1):
    a, f, _ = response(r)
    if sum(v*v for v in f) < sum(v*v for v in a):
        first = r
        break
assert first == 115
a, f, terms = response(R)
c = [0] * R
for i in range(1, R):
    for j in range(1, R):
        c[gcd(i, j)] += mu[i] * mu[j] * (X // (i*j))
s = [0] + [sum(c[d::d]) for d in range(1, R)]
e = f.copy()
e[1] += M[X]
h = [v+w for v, w in zip(c, e)]
u = [0] + [sum(h[d::d]) for d in range(1, R)]
z = c.copy()
z[1] += M[X]
t = [0] + [sum(z[d::d]) for d in range(1, R)]
norm = lambda v: sum(x*x for x in v)
df = norm(f) - norm(a)
dh = norm(h) - norm(u)
j = -2*(sum(v*w for v, w in zip(h, f))-sum(v*w for v, w in zip(u, a)))
assert (M[114], M[X], sum(c), norm(c), norm(s)) == (-6, -9, -3, 21411, 3080)
assert (norm(f), norm(a), df, dh, j) == (404, 599, -195, 18750, -1970)
assert norm(z) - norm(t) == dh + df + j == 16585
assert norm(c) - norm(s) == 16585 + 2*(-9)*(-97) == 18331
print(json.dumps({
    'first_genuine_HF_failure': first, 'R': R, 'X': X,
    'powerful_terms_q_rad_weight_quotient_M_contribution': terms,
    'A_nonzero': [[i, a[i]] for i in range(1, R) if a[i]],
    'F_nonzero': [[i, f[i]] for i in range(1, R) if f[i]],
    'F2': norm(f), 'A2': norm(a), 'DF': df,
    'H2': norm(h), 'U2': norm(u), 'DH': dh, 'HF_mixed': j,
    'Z2': norm(z), 'T2': norm(t), 'D0': 16585,
    'DG': norm(c), 'DS': norm(s), 'gap': 18331, 'robust_margin': 14839,
}, indent=2))
```

# RH_Lean agent daily report - 2026-10-31 / RH | Prime Census Laboratory

**Status:** COMPLETED  
**Invocation:** scheduled run begun 2026-10-31 03:11 America/New_York  
**Final authority refresh:** 2026-10-31 03:32 America/New_York  
**Pinned live main:** `6b2a869750b92fcdbebff78a591e7722b4f2c747`  
**Authority blobs:** `AGENTS.md` `d30a5c4320bec77a510932e72ce7f17d98a68e51`; `CURRENT_PROOF_CONTRACT.md` `7a067ec0423a998e1079e37494061346d8ee02b0`; stable selector `497c59885bf1da401bfc755e6980d1548ce167f0`; all-vector directive `a2892b6641268e1ac1ce08622bbe53445fe2e8eb`; role prompts `010af4bb369d11a61eaf1842d1c119c1e3730e56`.  
**Material source blobs:** `research/EULER_FRACTIONAL_COUPLED_20261027.lean` `e6c4b1690e497760d366e36b28a1f7aa60e19f85`; `research/EULER_PHYSICAL_COMPLETE_PACKET_20261030.lean` `8084af7fa50fb5b8361a64f05eb658f08b529ca7`.  
**Open proof PR:** #1060, head `80ee69a861398007046e35b79f7040e923078942`, unmerged; its uniform coefficient pairing is PR-head evidence, not main authority.  
**New claim:** `20261031-census-1`.  
**Evidence classes:** `PAPER_PROOF / EXACT SQUAREFREE DEPTH LAW`, `FINITE_COMPUTATION / EXACT RATIONAL CENSUS`, `NO_COMPLETE SOURCE BOUND`, `NO_FIXED_ETA GAIN`, `NO_RH`.

## A. Mathematical mystery and competing hypotheses

Analytic claim `20261031-analytic-1` pays the exact first moving-band wedge
[
1le klesqrt R,qquad d=R+k,
]
at (O(H^2log^2 H)) energy. The unpaid complement is
[
V_R=2sum_{sqrt R<k<R}eta_R(R+k)
 rac{R^2-1mod(R+k)}{R+k},
]
where (eta_R(d)) is the literal moving unordered coefficient from
`eulerFractionOffQ`.

Two mechanisms were preregistered.

1. **Sparse phase hypothesis:** (V_R) is driven by a small order-one-remainder family near the far edge, such as the Analytic witness (R=2m+1, k=R-1).
2. **Arithmetic-depth hypothesis:** large positive and negative populations are broad, and cancellation is governed primarily by the factor pattern of (d=R+k), especially squarefree Möbius depth.

The discriminators were exact far-band signed mass, absolute mass, dyadic energy, near/far mixed energy, phase quartiles, squarefree factor depth, the largest individual terms, and pointwise coherence (|V_R|/sum|{m term}|).

## B. Exact hidden-variable law

For every (Rge2) and (1le k<R), (d=R+k<2R). The completed pair ((1,d)) is not admitted, while every other strict factor pair (a<b), (ab=d), has (ble d/2<R). Hence
[
eta_R(R+k)=alpha(R+k)-mu(R+k),                 	ag{1}
]
where
[
alpha(d)=sum_{1le a<b, ab=d}mu(a)mu(b).
]

If (d) is squarefree with (r=omega(d)ge1), it is nonsquare and
[
2alpha(d)=(mu*mu)(d)=(-2)^r.
]
Therefore
[
oxed{eta_R(d)=(-1)^r(2^{r-1}-1).}              	ag{2}
]

Thus every squarefree far-band term has sign determined by Möbius parity and coefficient magnitude increasing with depth:
[
r=1,2,3,4,5:qquad 0, +1, -3, +7, -15.
]
This is an exact original-carrier statement, not a fitted correlation. It explains why prime columns vanish after the missing ((1,d)) activation correction and why high-depth squarefree columns can dominate individual terms.

Equation (2) identifies a previously concealed variable in the moving high-product source: **squarefree factor depth, with exponentially weighted parity**. Any far-band estimate that groups only by displacement (k/R), phase, or product size loses this sign structure.

## C. Exact experiment

### Carrier and endpoints

For every integer (R) in each complete dyadic interval
[
[16,32),[32,64),ldots,[2048,4096),
]
the census used
[
X_R=R^2-1,quad
f_d(R)=rac{X_Rmod d}{d},quad
eta_R(d)=sum_{substack{1le a<b<R\ab=d}}mu(a)mu(b).
]
The near/far split was (klelfloorsqrt Rfloor) versus (k>lfloorsqrt Rfloor). All sums and energies used exact Python `Fraction` arithmetic. No centering, randomization, floating sign decision, PNT input, imported 7/8 bound, or omitted activation term was used.

### Independent checks

The full sweep precomputed (mu) by a sieve and (alpha) by an unordered divisor convolution. At (R=15,16,317,549,1027,2053), every coefficient was independently reconstructed by direct admitted factor-pair enumeration, with each factor's Möbius value recomputed by trial factorization. All comparisons were exact and agreed.

The full-sweep script SHA-256 was
`3e740a48cafd292ed2b5f52a231610f8e3d87a22c48c2404e2046832478fbf40`.
A verification-only revision adding trial-factorization coefficient checks had SHA-256
`4a30d0f60ca424fe948df5194afdda336ba612e78b743771072616f91817ebb7`.
Command: `python first_band_census.py 2048`. Python 3.12.13. The exact result JSON was 136,618 bytes.

## D. Dyadic results

Here (E_{m near}=sum W_R^2), (E_{m far}=sum V_R^2), and
(E_{m mix}=2sum W_RV_R). Decimal values display exact rationals.

| H | E_near | E_far | E_full | E_mix | E_far/H^(5/2) | max pointwise coherence |
|---:|---:|---:|---:|---:|---:|---:|
| 16 | 68.245 | 120.477 | 152.927 | -35.795 | 0.1177 | 0.5440 |
| 32 | 191.112 | 1,691.471 | 1,986.736 | 104.153 | 0.2920 | 0.4802 |
| 64 | 699.764 | 6,959.492 | 8,589.603 | 930.347 | 0.2124 | 0.3217 |
| 128 | 3,352.631 | 41,181.963 | 45,397.627 | 863.033 | 0.2222 | 0.2479 |
| 256 | 11,961.504 | 201,856.033 | 213,226.088 | -591.448 | 0.1925 | 0.1924 |
| 512 | 36,566.912 | 1,058,133.949 | 1,056,253.360 | -38,447.501 | 0.1784 | 0.1715 |
| 1024 | 95,318.368 | 6,087,337.627 | 6,093,162.213 | -89,493.782 | 0.1814 | 0.1060 |
| 2048 | 389,731.773 | 29,549,676.195 | 29,620,553.915 | -318,854.053 | 0.1557 | 0.1108 |

This is finite evidence only. It neither proves a bounded normalized energy nor identifies a positive (eta). It does show that the far band is not becoming pointwise coherent over the tested range: the worst (|V_R|/sum|{m term}|) drops from 0.5440 to 0.1108 between the first and last dyadic blocks.

The near/far mixed term changes sign and is not uniformly favorable. Any proof that discards it or assumes nonpositive covariance is false to the data.

## E. Exceptional and held-out behavior

Exact anchor summaries:

| R | W_R near | V_R far | full | far absolute mass | coherence |
|---:|---:|---:|---:|---:|---:|
| 15 | -8/9 | 5422/2145 | 1.638850 | 3.327739 | 0.7596 |
| 16 | -11/6 | -263/2002 | -1.964702 | 6.297203 | 0.0209 |
| 317 | 7.430585 | -21.042446 | -13.611861 | 313.983902 | 0.0670 |
| 549 | 17.605175 | -74.674414 | -57.069239 | 642.854768 | 0.1162 |
| 1027 | -5.988393 | 48.162482 | 42.174089 | 1,339.201060 | 0.0360 |
| 2053 | -13.724407 | -51.958480 | -65.682887 | 3,090.713680 | 0.0168 |

The permanent BLOCK regression (R=549) was retained. No inference about the false universal capture statement was drawn from this different carrier.

At held-out (R=2053), the squarefree depth contributions to (V_R) were
[
r=2: +518.502,quad
r=3: -1094.140,quad
r=4: +586.835,quad
r=5: -73.178.
]
The final (V_R=-51.958) appears only after these broad, individually much larger depth classes and the squareful classes are restored. The largest term was not a sparse endpoint witness but
[
k=677, d=2730, omega(d)=5, eta_R(d)=-15, 
f_d(R)=31/35, {m term}=-186/7.
]

Phase quartiles at (R=2053) contributed approximately
[
-15.928,quad +3.359,quad -53.514,quad +14.124.
]
No single phase quartile explains the total. Across the complete dyadic block (H=2048), phase-quartile signed totals were approximately
[
+53.9, -7488.3, -3375.0, -9086.5,
]
whereas squarefree depth totals had magnitudes in the millions and canceled strongly. This supports the arithmetic-depth mechanism over the sparse-phase mechanism on the tested domain.

## F. Falsification and limitations

1. **Sparse-family sufficiency is disfavored, not universally refuted.** Order-one endpoint phases exist, but the tested far energy is broad and its largest terms occur at several depths and displacements.
2. **No uniform sign:** (V_R) is positive at (R=15,1027) and negative at (R=16,317,549,2053).
3. **No favorable mixed sign:** dyadic near/far mixed energy is positive for (H=32,64,128) and negative for several later blocks.
4. **No exponent claim:** the observed (E_{m far}/H^{5/2}) range (0.1177) to (0.2920) is selection-range evidence, not an all-scale bound.
5. **Only first band:** later (jR+k) bands, Wheel's corrected root-dependent resonance (delta(R,j,k)=gcd(j^2,jR+k)), reciprocal square, diagonal, restoration, and cross-band energy remain unpaid.
6. **Squareful classes retained numerically:** equation (2) describes squarefree (d) only; the census did not delete squareful terms.
7. **No completed-coefficient freezing:** equation (1) explicitly includes the missing ((1,d)) activation correction.
8. **No global source conclusion:** the exact original complete shell and all other packet families remain outside this result.

## G. Conjecture and proof consequence

Define the squarefree far first-band source
[
V_R^{m sf}
=2sum_{substack{sqrt R<k<R\R+k {m squarefree}}}
(-1)^{omega(R+k)}
(2^{omega(R+k)-1}-1)f_{R+k}(R).
]

**Conjecture `CENSUS-FAR-DEPTH-1`.** There exists a fixed (eta>0) such that, after adding the exact squareful correction on the same first-band carrier,
[
sum_{Hle R<2H}|V_R|^2
ll_{arepsilon}H^{5/2-eta+arepsilon}.
]
The evidence-generating range is (16le Hle2048); the strongest attempted falsifiers are the full exact dyadic census, (R=549), the order-one phase family, and high-depth columns through (omega=5). Status: `CONJECTURE`.

The new mathematical information is not the conjectured bound itself but the exact reduction (2): the relevant signed coefficient is a parity-alternating factor-depth weight. A theoretical proof must exploit cancellation of these weighted depth classes jointly with the rational square-clock phase. A phase-only incomplete-correlation estimate or an unsigned divisor bound cannot see this mechanism.

The smallest plausible analytic lemma is a bilinear or Selberg-Delange-style estimate for the moving interval
[
R+sqrt R<d<2R
]
with coefficient
[
1_{m sf}(d)(-1)^{omega(d)}(2^{omega(d)-1}-1)
]
against (f_d(R)), uniform in all (Rin[H,2H)), followed by an exact squareful correction. It must deliver an (L^2_R) estimate and preserve the near/far mixed term when recombined.

## H. Continuity and route impact

Consumed today's Owner report blob `3ebb890e1f1dec6a16cd68a9a4ae391559df700f`, Analytic blob `c6d51381488052aec63081a23b44f0bf9ef5b65c`, and Wheel blob `ab2a2be76ed633d560ef332340796e1ff13fe3ab`. Today's Coordinator, Referee, and Lean reports were unavailable at finalization and are `TODAY=PENDING`.

Yesterday's verified reports were carried forward from the upstream continuity ledger: Coordinator `f50176f5b1091a528f73147f9f9e74e69f3a5b82`, Analytic `bae5e244f4bafdb42071263e72d502d50f3ce31e`, Wheel `c732ac930234989d702ca9f6954a050febd5965b`, Census `dbcc43c3a64d0065743bebf7194c6bf82762ca88`, Referee `4903fd6e4c4594f301fe9bc88d9b3d3ec152583c`, and Lean `3bc9f808fb733f45e650978ef1bc8d6799f4b87c`. No 2026-10-30 Owner report existed; it remains `YESTERDAY=PENDING`. External inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52` has no newer handoff than 2026-10-18.

Route impact: this is S1/CODIV source evidence for the first moving high-product band. It does not change any registry status. VF-LOW, SAT, JOH, FINITE-AC, CORR4, MU-LIFT, OAI-NNS, NYMAN, the complete shell bound, a fixed (eta), the canonical VF estimate, and RH remain OPEN.

## I. Specialist handoffs

**Analytic Type II.** Replace a displacement-only model of the far first band by the exact depth weight (2). Test whether the squarefree generating coefficient can be handled by a uniform short-interval Dirichlet-series or bilinear method against the square-clock phase. Keep the squareful correction and mixed energy explicit.

**Finite Wheel.** Extend the depth classification to later bands (d=jR+k) while using the corrected root-dependent lift multiplicity (gcd(j^2,jR+k)). Determine whether high factor depth correlates with maximal resonance.

**Owner Payment.** Do not infer complete-return reciprocal decay from the small pointwise coherence here. This census is pre-return first-band arithmetic and does not bypass `20261031-owner-1`.

**Adversarial Referee.** Check (1)-(2), the direct-factor cross-check design, and whether the conjecture is genuinely narrower than the full shell target. Reject any promotion of the finite normalized table to a uniform exponent.

**Lean Verification.** After review, the smallest structural formal target is (1), then the squarefree specialization (2). No analytic (L^2) bound is ready for formalization.

## J. Evidence status and continuation checkpoint

**Evidence status:** `FINITE_COMPUTATION` for the exact census on all roots in the stated dyadic ranges, plus `PAPER_PROOF` for equations (1)-(2). No all-scale inequality is claimed.

**Next run:** hold the coefficient formula fixed before examining new data. Extend the exact census to at least (H=8192), preregister the statistic (E_{m far}/H^{5/2}), and separately record the squarefree-depth and squareful energies rather than only signed totals. Independently test the proposed depth-weighted (L^2) lemma on a withheld range and on roots satisfying Wheel's maximal later-band resonance congruences. Do not repeat the (Hle2048) table unless the source definition changes.


## Additional scheduled continuation - 2026-10-31 11:04 America/New_York

**Status:** COMPLETED  
**Authority correction:** current live main is \`05c3fcfc2ad699f09d7d473f17ac63a918a3aad3\`, not the earlier pinned \`6b2a869...\`. Main now includes merged #1060 and merged #1061. The current stable selector is blob \`bcdfe8df1bb4d7e8ed7696b560f3fc4916af245a\`; the broad-search policy is \`46d27ef877325c391377d7cba6629f69316588b9\`; all-vector directive \`a2892b6641268e1ac1ce08622bbe53445fe2e8eb\`; Census role prompt \`adbcf73ef6e58fbc477ae6c16675682e08ec03d6\`. The original source remains \`research/EULER_FRACTIONAL_COUPLED_20261027.lean\` blob \`e6c4b1690e497760d366e36b28a1f7aa60e19f85\`; physical moving rows are in \`EULER_PHYSICAL_COMPLETE_PACKET_20261030.lean\` blob \`8084af7fa50fb5b8361a64f05eb658f08b529ca7\`; uniform completed coefficients are now on main at blob \`c39fde58586c2df55fb5be0166d1908db5aa3aba\`.

**New claim:** \`20261031-census-2\`.  
**Evidence classes:** \`PAPER_PROOF / EXACT CUBEFREE-RESONANCE SUPPORT\`, \`FINITE_COMPUTATION / EXACT RATIONAL GRAM CERTIFICATE\`, \`NO_COMPLETE SOURCE BOUND\`, \`NO_FIXED_ETA GAIN\`, \`NO_RH\`.

### A. Mystery, competing hypotheses, and discriminator

Coordinator claim \`20261031-coordinator-1\` pays the coefficient-weighted resonance diagonal
\[
  \sum_{H\le R<2H}\delta(R,j,k)|\beta_R(jR+k)|^2,
  \qquad \delta(R,j,k)=\gcd(j^2,jR+k),
\]
but not cross-column cancellation. Two possibilities were fixed before the experiment:

1. cross-column centered coherence defeats the sum of individual resonance budgets;
2. the actual moving Mobius support suppresses the worst resonance branches and the finite centered Gram remains below that diagonal budget.

For columns \(c=(j,k)\), \(1\le j\le J\), \(0\le k\le j\), define
\[
 n_c(R)=jR+k,\quad
 \beta_R(n)=\sum_{\substack{1\le a<b<R\\ab=n}}\mu(a)\mu(b),
\]
\[
 m_n={1\over n}\sum_{r=1}^n{(r^2-1)\bmod n\over n},\qquad
 x_c(R)=2\beta_R(n_c(R))\left({(R^2-1)\bmod n_c(R)\over n_c(R)}-m_{n_c(R)}\right).
\]
Thus \(m_n\) is the literal \`eulerPacketRootPrincipal\`, not an empirical block mean. Put
\[
 G_{cd}=\sum_{H\le R<2H}x_c(R)x_d(R),\qquad
 D_c=4\sum_{H\le R<2H}\delta(R,j,k)\beta_R(n_c(R))^2.
\]
Since the centered fractional column has absolute value below one and \(\delta\ge1\), \(G_{cc}\le D_c\). The discriminator was whether \(D-G\) stayed positive definite on complete residue periods or the normalized Gram developed an eigenvalue above one.

### B. Exact hidden support law

For every root \(R\) and product \(n\),
\[
 \boxed{\beta_R(n)\ne0\Longrightarrow n\text{ is cubefree}.} \tag{7}
\]
Indeed, if \(p^3\mid n=ab\), then one of \(a,b\) is divisible by \(p^2\), so its Mobius coefficient is zero. This uses the actual moving subset and needs no completed-coefficient substitution.

For the maximal Wheel family \(k=j\), \(R\equiv-1\pmod j\),
\[
 n=j(R+1)=Lj^2,\qquad \delta(R,j,j)=j^2.
\]
If \(j\) is not squarefree, then \(p^2\mid j\) for some prime \(p\), hence \(p^4\mid n\), and (7) gives
\[
 \boxed{\beta_R(jR+j)=0.} \tag{8}
\]
Thus every maximal root-phase spike with nonsquarefree band index is removed exactly by genuine Mobius support. This does not remove maximal spikes for squarefree \(j\), and it does not bound their joint signed contribution.

### C. Exact finite Gram results

The intervals were chosen so their length is divisible by every tested \(j\): \((H,J)=(12,4),(60,6),(420,7)\). Every coefficient was reconstructed in two independent ways inside the reference program:

- direct enumeration of admitted pairs \(1\le a<b<R\);
- completed enumeration minus the exact owner frontier \(a\le j\).

They agreed for every cell. All phases, principals, Gram entries, and the matrices \(D-G\) used exact Python \`Fraction\` arithmetic. Exact rational LDL decomposition gave strictly positive pivots in every case, certifying \(D-G\) positive definite without floating-point sign decisions.

| H | J | columns | exact Gram SHA-256 | top eigenvalue of \(D^{-1/2}GD^{-1/2}\) | max \(G_{cc}/D_c\) | exact \(D-G\succ0\) |
|---:|---:|---:|---|---:|---:|:---:|
| 12 | 4 | 14 | \`9a08be8956efb61ee6b0f4146ea3a3fc8eaed71cdf2f9c845fdb3d3c4a983698\` | 0.3344413728 | 0.2975613508 | yes |
| 60 | 6 | 27 | \`63f2a9726abe5a74ea4aaa20b836cde0b463869742ea46349985722257a4d556\` | 0.3316774342 | 0.2869813429 | yes |
| 420 | 7 | 35 | \`945e20dcf52f4c63d527d791e2f87e5206b5e836fe0d6badd2fae1d5830e6a2a\` | 0.2872723077 | 0.2688363956 | yes |

The displayed eigenvalues are diagnostics. NumPy symmetric eigensolvers and an independent 70-digit Decimal power iteration agreed: \(0.33167743420382256\) versus \(0.33167743420382261838\) at \((60,6)\), and \(0.28727230769692735\) versus \(0.28727230769692753451\) at \((420,7)\). The rigorous finite conclusion is the rational LDL certificate, not those decimals.

No earliest cross-column spectral excess was found through \(J=7\). The top mode was dominated by the primitive columns \((1,0)\), \((1,1)\), not by a maximal resonant column. At \(H=420\), maximal-family survival counts were:

| j | maximal roots | nonzero \(\beta_R\) | \(\sum\delta\beta_R^2\) |
|---:|---:|---:|---:|
| 2 | 210 | 61 | 512 |
| 3 | 140 | 53 | 1,035 |
| 4 | 105 | 0 | 0 |
| 5 | 84 | 39 | 2,000 |
| 6 | 70 | 7 | 252 |
| 7 | 60 | 28 | 3,479 |

The \(j=4\) row is the exact nonsquarefree exclusion (8). The \(j=6\) row shows why no broader claim is valid: squarefree band indices can survive maximal resonance.

### D. Secondary withheld first-band check

Before the Coordinator blob became retrievable by SHA, the prior Census resume capsule was executed on held-out blocks. An optimized C++ pair-sieve and an independently structured trial-factor Python reference reproduced the old exact \(H=64\) energy \(6959.49218545907\). The withheld long-double diagnostics were:

| H | \(E_{\rm far}/H^{5/2}\) | \(E_{\rm sf}/H^{5/2}\) | \(E_{\rm squareful}/H^{5/2}\) | sf-squareful mixed energy |
|---:|---:|---:|---:|---:|
| 4096 | 0.1057433 | 0.0693352 | 0.0171169 | +20,713,794.5 |
| 8192 | 0.0994340 | 0.0705966 | 0.0127794 | +97,536,542.5 |

These are uncertified floating diagnostics, not the primary result and not an exponent fit. Exact rational anchor reconstruction at \(R=4099,8209,16381\) verified total = squarefree + squareful and showed alternating depth contributions far larger than the final total. The positive squarefree-squareful mixed term on both withheld blocks refutes any extrapolation that squareful correction is uniformly favorable.

Reproducer hashes: \`moving_band_centered_gram.py\` \`670da82c518c64b416911ca678c8973ae7c2e98f086fe7546668668ef667710e\`; \`first_band_withheld.cpp\` \`067efd349914b149a5d53e022387a4696bda653bb2a299357b0162e2bff6b297\`; \`first_band_reference.py\` \`674dd4b03ccaa3a3d4aa112618eac92dabce88c7819b69b5b7dd3f488dfc4e7f\`. Environment: Python 3.12.14, NumPy, GCC 13.3.0, \`-O3 -std=c++17\`.

### E. Scope, route impact, and routing check

The exact support law (7)-(8) is a same-source interaction between Wheel resonance and the genuine moving Euler coefficient. It removes an infinite maximal-resonance subclass before any norm. It is not a power saving: squarefree \(j\), primitive columns, \(k>j\), larger \(J\), principal reconstruction, original fractional diagonal, reciprocal square, high products, mixed bands, endpoint restoration, and the complete shell remain unpaid.

The finite positive-definiteness certificates support continued investigation of “average \(\delta\) before Cauchy,” but do not prove a uniform large sieve. The next mathematical lemma is a uniform finite-column/operator inequality with explicit growth in \(J\), followed by the omitted principal and partial-period costs. A fixed-\(J\) Gram cannot pass the eta gate.

\`eta_gate: SEARCH_BROAD\`  
\`primary_route_and_original_carrier: CODIV/S1 centered moving-band eulerFractionOffQ with actual beta_R and eulerPacketRootPrincipal\`  
\`actual_new_lemma_or_first_unresolved_inequality: exact cubefree support and nonsquarefree maximal-resonance exclusion; uniform J-growing centered operator bound remains open\`  
\`independent_reviewer_and_formal_evidence: pending; equations (7)-(8) paper proof, Gram finite rational certificate only\`  
\`net_endpoint_gain_after_complete_return: UNKNOWN\`  
\`next_distinct_route_due: FINITE-AC/CORR4 or NYMAN census; do not spend the next allocation on another Euler range extension\`

The literal BLOCK claim remains refuted at \(R=549\). Claims \`20261031-owner-2\`, \`20261031-analytic-2\`, Wheel/Referee/Lean current reports, Coordinator blob \`d725323b...\`, the Oct 30 carry-forward set, and external inbox blob \`038018145...\` were consumed. No proof-obligation status changes. Fixed positive eta, strict exponent below \(7/8\), the canonical VF theorem, and RH remain OPEN.

### F. Continuation checkpoint

1. Ask Referee to audit (7)-(8) and the exact centered-Gram carrier, especially whether \(D_c\) is the correct post-completion diagonal for the proposed analytic operator.
2. On the next Census allocation, rotate away from Euler: test one preregistered FINITE-AC/CORR4 or NYMAN claim with its original carrier and retained regression suite.
3. If this Gram is revisited later, increase \(J\) with a declared \(J(H)\), include \(k>j\) and partial periods, and search for the first exact failure of \(D-G\succeq0\); do not merely enlarge \(H\) at fixed \(J\).


## Scheduled continuation - 2026-10-31 19:05 America/New_York

**New claim:** \`20261031-census-3\`.  
**Evidence classes:** \`FINITE_COMPUTATION / EXACT INTEGER-RATIONAL CENSUS\`, \`COUNTEREXAMPLE TO SMALL-OWNER SIGN COMPENSATION\`, \`CONJECTURE / SMALL-OWNER DEFECT CONCENTRATION\`, \`NO_NEW INDEPENDENT INEQUALITY\`, \`NO_FIXED_ETA GAIN\`, \`NO_RH\`.

### A. Route rotation and mathematical question

This continuation follows the prior Census checkpoint and rotates away from a third Euler packet/resonance experiment to the protected CORR4 carrier \`COORD-CORR4-DAUGHTERS\`. It uses the literal main definitions behind \`OPEN-CORR4-MIXED-TAIL-POWER\`:

\[
X_R=R^2-1,\quad Q_R=\{q\ge3:q\ {\rm prime},\ q^2<R\},\quad
d_q=M(\lfloor X_R/q^2\rfloor),
\]
\[
C_R=M(R-1)-M(X_R),\quad E_R=\sum_{q\in Q_R}d_q^2,\quad
s_R=\sum_{q\in Q_R}q^{-2},\quad U_R=\sum_{q\in Q_R}d_q/q,
\]
\[
\Delta_R=s_RE_R-U_R^2
=\sum_{q<r\in Q_R}(d_r/q-d_q/r)^2.
\]

For \(S=\{3,5,7,11,13,17\}\), let
\[
T_{17}(R)=\sum_{\substack{q<r\\q\in S\ {\rm or}\ r\in S}}
(d_r/q-d_q/r)^2.
\]
The exact record-energy predicate is
\[
900E_R\le211C_R^2.
\]

The prior claim \`20261026-census-1\` suggested that low daughter dispersion is anchored by small owners rather than being a tail-wide collinear mode. Before reading the new range, the falsifiable test was frozen as:

> For every record-energy root in the fresh range with
> \(\Delta_R/E_R\le1/20\), one has \(T_{17}(R)/\Delta_R\ge1/2\).

A single legal root violating either exact premise and the conclusion would refute it. A competing signed-compensation hypothesis was also tested: low-dispersion record roots should have \(C_Rd_3<0\).

### B. Exact results

The held-out ranges were \(10001\le R\le12000\) and \(12001\le R\le20000\). The earlier control range \(290\le R\le10000\) was rerun only to locate the smallest counterexample to the new sign hypothesis and to preserve continuity with claim \`20261026-census-1\`.

| roots | record-energy roots | \(\Delta/E\le0.05\) | concentration violations |
|---|---:|---:|---:|
| 290--10000 | 4109 | 55 | 0 |
| 10001--12000 | 920 | 0 | 0 |
| 12001--20000 | 3427 | 2 | 0 |
| total | 8456 | 57 | 0 |

The two genuinely held-out low-dispersion roots are:

| \(R\) | \(C_R\) | \(E_R\) | \(\Delta_R/E_R\) | \(T_{17}/\Delta_R\) |
|---:|---:|---:|---:|---:|
| 13532 | 2540 | 1465781 | 0.04954040321188526996 | 0.99151576600941637718 |
| 14288 | -1179 | 280616 | 0.04959191927730220717 | 0.98142763852663750246 |

Their exact small-owner daughter vectors are respectively
\[
(d_3,d_5,d_7,d_{11},d_{13},d_{17})
=(-812,-738,-180,-305,242,-13)
\]
and
\[
(320,237,215,174,-15,151).
\]

Across all 1174 record-energy roots with \(\Delta/E\le0.1\), the smallest observed touch share was
\[
T_{17}/\Delta=0.97684124733264887652
\quad\text{at }R=3304.
\]
Thus the preregistered half-share conjecture survived by a large finite margin. This remains finite evidence: no universal positive lower bound is inferred.

### C. Decisive counterexample to the stronger sign rule

The proposed deterministic sign compensation \(C_Rd_3<0\) is **REFUTED**. The smallest observed counterexample satisfying the stricter \(\Delta/E\le0.05\) predicate is
\[
R=2002,\quad C_R=-208,\quad d_3=-52,\quad E_R=8367,
\]
so \(C_Rd_3=10816>0\), while the record predicate holds and
\[
\frac{\Delta_R}{E_R}
=\frac{333980624271685170836648439763538}
 {7306552932969761761929417608576175}
=0.04570973855053400009\ldots.
\]
Its concentration share is nevertheless
\[
\frac{T_{17}}{\Delta}
=\frac{165079891399798136748316610555944}
 {166990312135842585418324219881769}
=0.98855969120837161590\ldots.
\]

This separates the mechanisms: small-owner concentration of the Lagrange defect does not force the endpoint excursion to oppose the \(q=3\) daughter.

### D. Independent reconstruction and numerical control

Implementation 1 was C++17. It used an Eratosthenes prime-multiple Möbius sign flip plus square-multiple zeroing, retained only the required Mertens query points, and used the exact integer record comparison \(900E_R\le211C_R^2\). SHA-256:
\`1e993cc451eae6b731ecea120f1a35ad616cddca43dc248b42eb1e5f1573e7a5\`.

Implementation 2 was Python 3.12.14. It used a linear least-prime Möbius base table and an independent quotient-grouped recurrence
\[
M(n)=1-\sum_{l=2}^{n}(r(l)-l+1)M(\lfloor n/l\rfloor),
\quad r(l)=\lfloor n/\lfloor n/l\rfloor\rfloor,
\]
then reconstructed \(\Delta/E\) and \(T_{17}/\Delta\) with \`fractions.Fraction\`. SHA-256:
\`75ddd0ef4bcb1f668242735855e73c95d3ffe2271eb7ffd1bb27385f85708a96\`.

The independent implementation agreed at \(R=56,317,1027,2002,3304,13532,14288\) on \(C_R,E_R\), every displayed small daughter, and the exact rational ratios. The third-smallest held-out ratio was \(0.0500885682\ldots\), leaving a margin above the frozen \(0.05\) threshold far larger than long-double rounding. Discrete claims and displayed rational certificates are exact; other decimals are rounded diagnostics.

Environment: \`g++ 13.3.0 -O3 -std=c++17 -Wall -Wextra -pedantic\`; Python 3.12.14. Commands:

\`\`\`text
./corr4_small_owner_scan 290 10000
./corr4_small_owner_scan 10001 12000
./corr4_small_owner_scan 12001 20000
python corr4_small_owner_verify.py
\`\`\`

The permanent BLOCK regression was also rerun from main source blob
\`9e2c26a182743d44b79b94720d719bd5e671d529\`: at \(R=549\),
\(\pi(R^2)=26112\), \(\pi((R+1)^2)=26193\),
\(\lfloor F_R\rfloor=26194\), and
\(\lfloor F_R+\sqrt2\rfloor=26196\). Literal one-block capture remains refuted.

### E. Proof impact and honest scope

The concentration statistic is a restriction on the exact CORR4 daughter vector, but it does not yet bound the signed physical mixed tail
\`lowOwnerPrefixTailMixedRawCellMass\`. In particular:

1. it supplies no inequality relating \(T_{17}\) to the endpoint gap \(C_R\);
2. it supplies no sign for the endpoint/daughter cross term;
3. the proposed simplest sign relation is already false at \(R=2002\);
4. it does not pay the physical diagonal, returned source, or mixed-tail complement;
5. it gives no fixed \(\eta>0\) and no strict exponent improvement.

The surviving theorem candidate is deliberately conditional and falsifiable:

> **Small-owner inverse candidate.** There exist absolute \(c_0,c_1>0\) such that every record-energy root with \(\Delta_R/E_R\le c_0\) satisfies \(T_{17}(R)\ge c_1\Delta_R\).

The tested values are \(c_0=1/20,c_1=1/2\) for \(290\le R\le20000\). Status: \`CONJECTURE\`. Even if proved, it advances \`OPEN-CORR4-MIXED-TAIL-POWER\` only after an independent source-faithful lemma connects the fixed small-owner defect to the complete signed mixed-tail bill.

### F. Authority, continuity, and routing check

Final refresh: \`main@05c3fcfc2ad699f09d7d473f17ac63a918a3aad3\`; \`AGENTS.md\` blob
\`d30a5c4320bec77a510932e72ce7f17d98a68e51\`; proof contract blob
\`7a067ec0423a998e1079e37494061346d8ee02b0\`; broad-search policy blob
\`46d27ef877325c391377d7cba6629f69316588b9\`. Original carrier sources:
\`GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_SIGNED_CELL_SPLIT.lean\` blob
\`29bb263ddd07b12a2dd5ccf6a12aecaf627134d8\`;
\`CORR4_OAI_POWER_MIXED_TAIL_GATE_20261025.lean\` blob
\`bb0ee1252e7ba10c44ae5b8d827573d6c581b73a\`;
\`CORR4_MIXED_TAIL_RECORD_PLATEAU_20261026.lean\` blob
\`a4abeb13653076bedd8e1173c933ee3324bfea26\`.

Current-day Coordinator, Owner, Analytic, Wheel, Referee, and Lean blobs consumed:
\`8e901e46877ff28bd8eb7c46cb3a46ade5ef32a6\`,
\`fdb9413fdd49588e1ad1c2348b4fabf4cff55b9c\`,
\`574c544048e225475569c57f95ca1e47237ab733\`,
\`5e62d4c536061564ceca0444a844f51b8886a7fd\`,
\`2c6b45c346617010d2d8b82eaf27b8bbc8f38465\`,
\`9786950ba58b9c8c3ddaccc00926417d4b3bb945\`.
The 2026-10-30 Owner file remains \`YESTERDAY=PENDING\`; the other preceding-day reports were consumed at the blobs already listed above. External inbox blob
\`038018145c0fddb2f6306c0712373adf9cd1ea52\` has no handoff newer than 2026-10-18.

PR #1062 remains the sole open PR at head
\`4309335c62ddcf41d7d3a17df2589de007291eff\`; its root-dependent resonance theorem is structural only.

\`eta_gate: SEARCH_BROAD\`  
\`primary_route_and_original_carrier: CORR4 / genuine q^2 daughters and exact Lagrange defect\`  
\`actual_new_lemma_or_first_unresolved_inequality: finite small-owner inverse candidate; unresolved deterministic T17-to-complete-mixed-tail bridge\`  
\`independent_reviewer_and_formal_evidence: PENDING; no Lean theorem claimed\`  
\`net_endpoint_gain_after_complete_return: UNKNOWN\`  
\`next_distinct_route_due: FINITE-AC or NYMAN; do not extend this CORR4 scan before an analytic small-owner bridge is proposed\`

### G. Evidence status and continuation checkpoint

**Evidence status:** \`FINITE_COMPUTATION\` on every root \(290\le R\le20000\), with exact rational independent verification of the extrema and counterexample. The sign hypothesis is \`REFUTED\`; the small-owner inverse statement is \`CONJECTURE\`; no open proof node changes status.

**Continuation:** do not rerun \(R\le20000\) or enlarge the CORR4 census merely to collect more supportive roots. The next Census allocation should test a preregistered FINITE-AC or NYMAN claim on its original carrier. Return to CORR4 only if an analyst supplies a precise lemma converting \(T_{17}\) into a bound for the full signed mixed-tail expression with diagonal and return terms retained.

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

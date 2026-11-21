# Lean Verification | 2026-11-21 (America/New_York)

## 05:10 EST / 10:10 UTC | LV-20261121T101000Z | PARTIAL

Actual scheduled invocation. `main=65fa3abb6ddf2f29786fe976c8e5ca4d8c6d9056`; `AGENTS=e651d40985f64114106a664b4ee63b51096b4687`; `CURRENT_PROOF_CONTRACT=f4fe93c4b609d07061ac9aa7d2dd0b7371e73f3c`; full-cost directive `1321c6e8e0f4d5b5248cecf651e69da873eb7463`. `alpoge_full_cost_ack=ALPOGE_FULL_ANALYTIC_GEOMETRIC_COST_V1`; `amplification_cost_ack=MULTIPLICITY_VS_COST_TO_HALF_V1`; `publish_ack=REPORT_PUBLISH_RECOVERY_V1`.

Initial report watermark `76a81f3f09f1b1c8f55d6fff273d8781d77ac089`: five specialist files present today; Coordinator TODAY=PENDING. Last own work #1167 has a human merge at this main. #1166 is a separate open research PR at `0a7f65b0c320422b759ed849c6bcf228426483d5`, not main. Checking previous actual sections, source signatures, exact-head CI and the moving square companion/local-divisibility handoff. No new mathematical or CI success claimed in this checkpoint. The same-source complete signed geometric cost and strict-history supplier remain OPEN.

## 05:38 EST / 10:38 UTC | LV-20261121T101000Z-PR | CI_PENDING

Draft [PR #1168](https://github.com/OVVO-Financial/RH_Lean/pull/1168) implements the finite part of `COORD-20261121T040901Z-LOCALITY2`, including a sharp positive weight example at the distinguished d-site. The exact cyclotomic replay checks 9,024 ramified coefficients, 1,464 unramified controls and 160 equality cases; this is finite computation, not a certificate. The first two hosted builds found warning-fatal proof-script diagnostics, not a counterexample. Repaired head `c49ab8f43052ff1a16f083c4b9979d7f78198533` is running [raw-head verification](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44895299919). No accepted axiom certificate or full geometric estimate is claimed at this checkpoint.

## Final | LV-20261121T101000Z-FINAL

### A. Result and scope

`PROVED_IN_LEAN` at `921e8d111c0e376fbe27ffe795c458cabc00c52c`; `CI_STATUS=GREEN_EXACT_HEAD`; #1168 `REVIEW_READY`, open and unmerged. All 12 attached workflows passed. The separate moving-square estimate in D is `PAPER_PROOF` only.

`LV-20261121T101000Z/LOCAL-FIBRES`. For the three specified inertia cosets, the nonprincipal character return is minus the full site mean at both 2 and q. At d it is the weight at one specified site minus that same mean. A strictly positive two-level weight attains the exact width factor `(N-1)/N` on N sites. In particular, a uniform `width/N` rule already fails at N=4: the deviation is 3/4, not at most 1/4. This refutes the rule for arbitrary profiles; it neither identifies which profiles genuine geometric lifts produce nor refutes a bound on that narrower class.

### B. Statement, proof and original carrier

Let H be any finite abelian group, U=(Z/2) x H, G=(Z/2) x U, N=|U|. Sum all additive complex characters of G except the literal trivial character. Finite dual orthogonality gives `|G| 1[x=g]-1`; the removed character has value 1, including at all bad sites. Average over the entire listed inertia coset, then average with arbitrary complex weights v(s) over every site g=(1,s). For natural i, the 2-coset `(0,i mod 2,h)` and q-coset `(0,b,iQ)` miss g; the d-coset `(b,i mod 2,iD)` hits it exactly for b=1 and s=z=(i mod 2,iD). No equal-weight, equidistribution, or positivity hypothesis is used for these identities.

In `RHLean.Analysis.locality_primePower`, e,q,d,i are natural, q and d prime and coprime to `2^(e+2)`, i>0, and H is the finite dyadic unit group modulo sign, written additively with a Fintype instance. Q,D are the actual unit classes of q,d. Three separate weight functions are allowed. With `vbar` the full U-mean, the sum weighted by the original `Lambda(2^i), Lambda(q^i), Lambda(d^i)` is `-log(2)*vbar2-log(q)*vbarq+log(d)*(vd(z)-vbard)`. The theorem is about specified cosets, not a universal identification with primitive Dirichlet coefficients. On the intended physical hosts (q=3 mod 8, d=7 mod 16, (-d/q)=1) CRT and quadratic reciprocity identify the inertia/Frobenius coordinates on paper; the conductor-to-coset bridge is not a Lean conclusion of this PR. No imported terminal theorem, no RH hypothesis and no infinite series.

`locality_width` sums the N-1 differences from z, whose absolute values are at most w. `locality_dSpike` evaluates `v=1+1_z` exactly: deviation `1-1/N`. At n=1 there are still two parity sites; the factor is 1/2, not zero. Classification: structural identity, sharp finite inequality and obstruction; no full-source exponent saving.

### C. Formalization queue and source pins

The prior owned PR #1167 was merged by a human; its matched-face source `94e298ab264fb8437cab08a0228c589bce710769` is on main. Reused tested head `dd5ca2ec3002ef6ea7a316052a085ff2b1268e24`, [11-root certificate](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44855720633/job/136697343765), artifact SHA-256 `d318dcd037551d0412eeb255a76e24c1c27d4ed89cec9927d0ad72c303d4d42e`. No duplicate build. #1166 is separate (four scalar characters, not these full fibres); its hosted build and source audits passed, but one attached run was cancelled and I do not certify its new declarations. #1165 closed unmerged. Selected the Coordinator's finite LOCALITY2 with Referee concurrence; retain the primitive-character bridge and the full height bound as distinct candidates.

Main tree `ddd766a3e0cb3b0cc25dc58e991689dfe6a45116`; multiplicity policy `eb9fada09a894534589e9ff38608e1cffba65f91`. #1159 and #1160 are merged. #1160 tested head `001efd2a357e950fdce7a8293fcfe9b7462b383c`, Schur source `5d7fdb70c53fd55b32a990d3a1103d3280a15ebf`; regression/audit blobs `6debfd716095ecc00ac18110deaf1f4d021883a7`, `0507df8fb0d6870d06dd9bd41065456537273ece`. Native signed recurrence `5a6e063b3b9481af22c714b0c73d710bf8676374`; native error `6779156e0fd49eee0c04d7a05825d6af8d5abed0`. Original external cost files read at `CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`, not imported. Canonical VF still asks for one C>=0 bounding `|pi(R^2)-vfMidFinishedMass(R)-sqrt(2)|` by `C R log R` for all natural R>=2; its published bridge explicitly takes `ClassicalVonKochRHCriterion`.

### D. Independent moving-square result (paper only)

`LV-20261121T101000Z/SQUARE-LINEAR`, strengthened to all Taylor orders. For integer R>=4 set X=R^2-1. For any subset of primes with `j=floor(X/p^2)>=J>=1`, let `u=(X mod p^2)/p^2`, `y=u/j`, `E(j)=psi(j)-j`. The actual floor-defect summand from Owner SR1 is `d_p=log(p) E(j) log(1+y)`. For integer k>=1 let `P_k(y)=sum_{r=1}^k (-1)^(r-1)y^r/r`. Uniformly in the submask,

```
sum_p |d_p - log(p) E(j) P_k(y)|
  <= sum_p log(p) u^(k+1) / ((k+1)j^k)
  <= log(4) sqrt(X) / ((k+1) J^(k+1/2)).
```

Proof: the exact remainder is `(-1)^k integral_0^y t^k/(1+t) dt`. Also `|E(j)|<=j`: psi is nonnegative and `psi(j)<=2j log(2)<2j`, by the binomial-coefficient induction in Owner SR2. Primes here satisfy `p<=sqrt(X/J)`; apply `Chebyshev.theta_le_log4_mul_x` to their positive log weights. For k=1 the remainder has sign opposite E(j) when y>0. The linear term itself is at most `log(4) sqrt(X/J)` in absolute sum. This is not an independent estimate for the signed bare matched face.

In the actual moving shell `J=floor(L/2)+1`, `L=floor(R^(1/3))`, `J<=j<=L`, the linear, quadratic and cubic approximation errors are respectively `O(R^(1/2))`, `O(R^(1/6))`, `O(R^(-1/6))`. Thus the cubic residual tends to zero even after summing absolute errors; the linearized term is `O(R^(5/6))`. The linearization error's normalized squared dyadic sum is `O(H^2/log(2H)^4)`. Exact zero remainders from divisibility cannot occur on this shell: `p^2>X/(L+1)>=R+1`, p is odd, and an odd prime cannot divide both R-1 and R+1. If its square divided X it would divide one factor, both smaller than p^2. None of this prices `-2 sum log(p)^2 E(j)`, the complete floor on all prime powers, or any missing mixed return.

Finite check: 80-digit decimal calculations at R=4..256 and 317,549,1027,1537,3000,6859; 259 roots, 1,293 actual sites, 1,287 negative and 6 positive child errors, zero exact divisions. Replay uses `log(lcm(1,...,j))-j`, compares the original log difference independently with each polynomial, and checks both the individual and summed bounds; script SHA-256 `55d97975a55058cd45942b65b40f9fd61248ce8a56300b773b8ce8c405c3726a`. These diagnostics are not a proof of a sign law. `PAPER_PROOF`; not Lean-certified.

### E. Latest actual handoffs and next actions

Intake `c62bb4d70edf5196e3ce503551f0e2b6ce04cf1a` to `76a81f3f09f1b1c8f55d6fff273d8781d77ac089`: 14 commits, 10 changed paths, zero deletions. Times below are EST; mirrors and checkpoints are not separate runs. Deeper inherited November 13-15 exhaustive continuity remains unverified. External inbox `7d63d434690d00dffce9c90335d41c4f62d85798`: retain c=1 and p=R where required (EXT-20261018-PNT-1), q=R (EXT-20261017-XCOORD-1), and all roots rather than hypothetical FirstBad (EXT-20261014-5).

| Role / last actual | Input, disposition, and handoff |
|---|---|
| Coordinator, Nov 20 23:09, `cb32802c` | `COORD-20261121T040901Z-LOCALITY1-5`, recovered mirror counted once; TODAY=PENDING, YESTERDAY=CARRY_FORWARD. Use finite LOCALITY2 only; leave conductor transport and total cost open. |
| Owner, Nov 21 00:09, `f20f2967` | `OP-20261121T050900Z-SQUARE-RETURN` SR1-5. Matched and lower logarithms reinforce. Use the cubic approximation only for the stated floor face, once, with its original sign. |
| Analytic, 01:04, `96fd489c` | `ATII-20261121T060401Z-THIN`. Good character pairs exist in the stated sampled measure; identify one such pair with actual height control rather than charging probability as a geometric gain. |
| Wheel, 02:05, `7f2a0590` | `FW-20261121T070510Z-INCIDENCE` INDEX1-5. A local scalar index or coefficient determinant is not a high-rank geometric minor. Check height on the same anchored object. |
| Census, 03:11, `a9409717` | `CENSUS-20261121T081100Z-ORBIT`. Equal histograms can differ by `(265/1104)log(23)` at n=4. Retain translates; test whether geometric weights can realize the positive spike. |
| Referee, 04:13, `38457576` | `REF-20261121T091300Z-CHAR-FINAL`. Accepts the finite source scope. CHAR2's one-sign critical continuous companion is already RH-equivalent, not the physical sampling discrepancy alone. Audit the conductor bridge and the new paper remainder separately. |
| Lean, Nov 20 21:08, `beb65f24` | `LV-20261121T020800Z/MATCHED-FACE` and `/RAMIFIED-COST`. Reuse merged face; positive raw ramified cost is not the signed nonprincipal conversion. |

### F. The first unpaid estimate

For the native signed recurrence put `F_R=2 sum_P log(p)^2-(sum_P log(p))^2`, `B_R=-F_R` on genuine `3R<=4p`, `p<R`. `C_R` contains `S log X-Lambda*S`, all `K2*E` returns off the selected face, and `-floorDefect`. Cross-triple and rank-one terms remain; `E(1)=-1` is one observation, not m independent ones. `2I-J` doubles centered coefficients and has mean eigenvalue 2-m; it is not a p-adic index on log weights. The alternative bound `sum_{H<=R<2H} ((C_R-B_R)_+)^2/log(X_R)^4 <<_eps H^(3+eps)` for every eps>0 remains OPEN.

On the SAME growing family: prove actual independent multiplicity `m>=x^(1/2-eps)`, window `xm<=k<=n^2 x^(1/2-eps)`, and `topExcess<=Err` after all costs. With `delta=nT2/n`, the normalized bill already includes `aE(1+m^2/k)/(m b delta)+2 n m x^eps/(T delta)+k x^(2eps)/(n T)`. Exhibit the finite-place index and archimedean height on the same lifts and pay the f,theta,eta movement, thin, width, principal and signed complement costs. No free `1/m`. There is no fixed `0<d0<=2` proved before every eps>0 giving `|M(R^2-1)-1|<=C_eps R^(1+eps) K_R^(1-d0/2)` with strict `K_R=max_{y<R}(M(y)-1)^2/(y+1)`. #1135's dictionary (source `628018db94395f988308b0ffdb4e8e5792fc0b71`) supplies the implication, not that hypothesis. No new RH, VF or half-exponent conclusion.

### G. Hosted verification and resume capsule

Branch `agent/lean-verification/20261121-local-prime-fibres` from the pinned main. [Proof source](https://github.com/OVVO-Financial/RH_Lean/blob/921e8d111c0e376fbe27ffe795c458cabc00c52c/research/ALPOGE_LOCAL_PRIME_FIBRES.lean) blob `a95aee9a11ed6ffbd3546e77daa4cb9abac602a3`; exact types `f08889ef8d64c8905b86fbd5376828b77356c395`, audit `57c9ea36b6a9faaba46205bde9392411b771fb77`, regression `2bcc2110f5e4cd174b9643136c651a9749368e10`, scoped read-only workflow `89abb37edf35fcad1892c27ab5cfa6bff8c7aea5`. Lean 4.34.1 (toolchain blob `ba8ebf2dbaf6a668cd2a0e086186d6d569b69ff5`); Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` (manifest `a34d142c3d75a602a8b0f8241a4fb504d5c7c5a4`). No local Lean run, central policy change, merge or auto-merge.

The [raw-head proof/audit](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44895754344/job/136820926359) forced the module (`compiled=1 cached=0`). Five independent type examples passed, including n=1 odd and even, and the physical prime-power specialization. All 12 public declarations gave exactly `propext, Classical.choice, Quot.sound`. Dependency walks reached orthogonality, native von Mangoldt on powers, and unit-of-coprime; 345 names for `locality_primePower`, 292 for `locality_dSpike`. [Evidence ZIP](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44895754344/artifacts/14704375223) downloaded, inspected and SHA-256 verified: `39c3f06eb7fe1d11b23774aedbd750ebd061c46d9f103f39c5db5bb348937d40`.

Other green gates: [targeted compile](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44895754478/job/136820926887), [hosted build/declaration graph](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44895754422/job/136820927175), [proof holes/root imports](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44895754422/job/136820926837), [inventory](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44895754378/job/136820926543), [public exports](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44895754472/job/136820926549). The exact cyclotomic replay used n=1,2,4,8,32; (q,d)=(3,23),(11,7),(211,439),(227,599); i=1..8. It uses primitive conductors and integer coefficient reductions, independently of the Lean character sum. Raw-head values: 9,024 bad-prime coefficients, 1,464 good-prime controls, 160 spikes. Finite evidence is not the all-host conductor theorem.

Repair history: `41b06ae8ff33b4930f942ddddeb0928f82ec6359` (job `44894213748/136816281439`), deprecated simplifier, proof-local instance style, surplus tactic. `5529eb7a232f8adc34ce12928dda08af67b02863` (`44894752792/136817912125`), redundant tactic focus and obsolete unused simplifier. `c49ab8f43052ff1a16f083c4b9979d7f78198533` (`44895299919/136819545630`), proof compiled; separate even-parity test needed a literal cast rewrite. The final head fixed that test without changing the theorem or weakening a gate.

Resume: check for human review or merge first; reuse this certificate if the source and dependencies are unchanged. Next small formal target: identify primitive-conductor character coefficients with the explicit CRT inertia averages for every admissible host, including n=1, before any infinite summation. The first quantitative target remains the same-family height/multiplicity estimate in F. `MATH_STATUS=PROVED` (finite fibres), `REFUTED` (unrestricted width/N), `OPEN` (full cost). `RUN_ID_UNAVAILABLE`; `continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1`.

Publication history: 1,092-byte opening at `81a5378682fb3f9820a57ab1452ba9c0ed21a358`, blob `19eb974d067372bcb1e5bf785993f2929cec660e`; 1,870-byte milestone at `8d4accff9ad0e32138343fa1bb509dbe854f892f`, blob `59331d7bf80db974b3522cb1dd302b0350a68223`. Both read back in full. This final append preserves those bytes through authenticated GitHub Contents, under publication policy `a9583516fd2e603320c771e32c170132bf0c53e9`. The final publication receipt is determined by immutable-commit readback, not by this text.

## LV-20261121T181401Z-OPEN | IN_PROGRESS

Scheduled invocation November 21, 2026 at 13:14:01 EST (18:14:01 UTC), America/New_York. RUN_ID_UNAVAILABLE. Intended canonical: research/agent_reports/2026-11-21/60-lean-verification.md on agent-reports. Opening branch snapshot 96221297b092abe3360768fbce4c401bcfd9e33b; existing canonical e0d842c4ae8b61488e5bb0de24a92593551472df, 15,966 bytes per GitHub. Direct Git returned HTTP 403 at CONNECT. The prior report is accessible in excerpts, not yet locally verified as a byte-for-byte replacement. Preserve it; use a create-only opening continuation if needed.

Main 17b4efc3181bbfadd94af19e9e1fd8fea87c11f3; AGENTS af75601305b535d0c11ba67bee9a447ba04ec043; contract f4fe93c4b609d07061ac9aa7d2dd0b7371e73f3c; full-cost directive 1321c6e8e0f4d5b5248cecf651e69da873eb7463. Hosted Lean source audits failed at the observed heads of #1169 (44930912630), #1170 (44930775561), and #1171 (44932392197). Inspect the failed jobs, exact original arithmetic and any changes of head before repair. The three-prime finite fibre result is previous work, not today's new result. No new Lean certificate or full-source bound claimed. The first unpaid quantity is the complete signed upper moment, or a paid height and multiplicity estimate on the same growing geometric family.

alpoge_full_cost_ack=ALPOGE_FULL_ANALYTIC_GEOMETRIC_COST_V1; amplification_cost_ack=MULTIPLICITY_VS_COST_TO_HALF_V1; publish_ack=REPORT_PUBLISH_RECOVERY_V1. Resume at the three exact-head job logs and latest specialist handoffs. Publication receipt requires independent immutable-commit readback.

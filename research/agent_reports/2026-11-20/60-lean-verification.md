# Lean Verification | 2026-11-20

## PARTIAL | LV-20261120T101000Z-checkpoint

Scheduled invocation: 2026-11-20 05:10:00 EST (10:10:00 UTC), America/New_York. RUN_ID_UNAVAILABLE. This is a checkpoint, not a mathematical certification.

Main `6338941bb9d10387e9361ca3ca55468d4c710e4c`; AGENTS `500b6daed5e867d19d97c30e43a7a1e7d2055a51`; contract `95566e37c8eaeb99ee680660df4f9d2e06ea5038`. Intake reports head `076f7161fcc13f9c1695b15d96914dd84c33a741`. No own canonical file in the November 20 listing; five specialist reports present. November 20 Coordinator pending at intake. #1152 is merged into this main; no open PR returned. Exact CI and new source audit pending.

half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1; cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1; continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1; publish_ack=REPORT_PUBLISH_RECOVERY_V1. Publication policy `a9583516fd2e603320c771e32c170132bf0c53e9`. Direct Git tunnel HTTP 403; using authenticated GitHub API. Never replace an unverified prefix, count a mirror twice, or infer a green job. Resume: inspect last actual reports and recovery siblings, extract the independently reviewed next source step, and verify or explicitly bound its mathematical scope.

## CI_PENDING | LV-20261120T101000Z-implementation

Same invocation, not a second launch. Implemented the reviewed TWO-WITNESS obstruction plus the exact joint-count fibres and two-point zero set on the original signed residual. Draft [PR #1153](https://github.com/OVVO-Financial/RH_Lean/pull/1153), base `6338941bb9d10387e9361ca3ca55468d4c710e4c`. The first hosted build at `9f0a9dcebafc006be1170a7637181c5edd1ab9ed` reported `dsimp made no progress` at `NYMAN_WITNESS_RANK.lean:76:4`. Removed the redundant step; no statement changed. Repaired head `e05f68039373d3df16bd1c033b9277178a7eb43d`: [witness](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44719772066/job/136232250227), [targeted](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44719772064/job/136232249941). No certificate claimed at this checkpoint. Independent exact arithmetic: 87 heads, 13,374 outputs, 5,029 joint count pairs aggregated across heads. No genuine energy bound or RH gain. Original canonical checkpoint `a901ede4c447ba7b371303e4fc928270096daa80`, blob `e60f01e642dce1c3b93513d4d57fdef8f9d6244a`, 1,220 bytes verified.

## Final | LV-20261120T101000Z-FINAL

### A. What Lean proved

Under two explicit prime witnesses, the original two-band Nyman residual agrees with the clipped formula **exactly at the two outputs `6K` and `6K+1`**. More precisely, two outputs have equal clipping error if and only if both of their integer floor counts agree. This excludes every later accidental cancellation, not just the first doubled floor found in #1152. It does not estimate the size of a nonzero error or the energy of the true residual. `PROVED_IN_LEAN` at `e05f68039373d3df16bd1c033b9277178a7eb43d`; all 12 attached workflows passed.

### B-D. Authority, queue and selection

At intake main was `6338941bb9d10387e9361ca3ca55468d4c710e4c`, tree `726dae6ed74c212a69923255f77ef36952494810`. The canonical target is one C>=0 for all natural R>=2 with `|pi(R^2)-vfMidFinishedMass(R)-sqrt(2)| <= C R log R`. Its public RH bridge explicitly takes `ClassicalVonKochRHCriterion` (source `79030d70e8d3e0d08eef9bac53fef95c36eca2fb`). The November 16 half directive `96ad4439ec458af6168f7d9cb3eef5dde291d37c` prioritizes direct or renewable progress to one half; signed-recovery directive `e3ae4280438f591f1ffaddd754a1c3a6d35d0691` and continuity rule `7eef0b36c7442be922d9bc99c6b35d853c4f1f4f` apply. `finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1; high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1; chain_ack=CANCELLATION_CHAIN_REUSE_V1`.

No open proof PR needed repair at intake. #1151 supplied finite moment and floor profiles. #1152 was human-merged at 03:04:26Z (Nov 19, 22:04:26 EST); its tested head `907105ddda130ef046fbbaab1fc63076cb886b03` has exactly the intake-main tree. Rechecked its [seven-root certificate](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44664507110/job/136050421713). Neither PR classified all output pairs. Selected `20261119-lean-2108-EST/TWO-WITNESS`, reviewed by Coordinator PORT and Referee APERTURE. LEDGER2 is a separate, scoped incidence candidate. Common-clock existence and full energy are not ready for implementation.

### E-G. Statement, carrier and proof

Let K,H be natural, H>0, and p,q distinct primes with `max(3K,H)<p,q<6K`; these imply K>0 and H<N=6K. Write `L=log(N/H)`, `F(k)=mu(k) log(N/max(H,k))`, `U=sum F(k)/k`, `V=2L+sum F(k)` on `1<=k<=N`, including the unit. The repair bands are `I1=(3K,4K]`, `I2=(5K,6K]`; their reciprocal masses are s,t and `d=s-t>=1/12`. Set `a=(U-tV/K)/d`, `z=(sV/K-U)/d`. Physical coefficients are `c_k=(a 1_I1+z 1_I2-F(k))/L` for `2<=k<=N`, including squareful repair sites. The true residual is `r(m)=1-sum c_k (m mod k)/k`. With `Qi(m)=sum_{k in Ii} floor(m/k)`, replacing both counts by K gives the clipped formula; `e(m)=r(m)-clipped(m)=[a(Q1(m)-K)+z(Q2(m)-K)]/L`. Below N this compares formulas only; distinct-site clipping applies from saturation onward.

A rational relation `xU+yV=0` implies `x+p*y=0` from the literal prime row `(1/p,1)`; no postulated independence of logarithms. The p,q rows of the solved amplitudes have determinant `(1/p-1/q)/(K*d)`, nonzero. Thus `(x*a+y*z=0) iff (x=y=0)` over the rationals. Subtract the error formulas at any natural m,n: the two integer count differences must vanish separately. At N both counts are K. Up to N+1 the first-layer counts are `min(b,m)-a0` in natural subtraction for a band `(a0,b]`; both reach K together exactly at N and N+1 in that range. At N+2 the first count is K+1 and is nondecreasing thereafter. No endpoint, sign, scale, or multiplicity assumption is suppressed. Lean does not assert the two-prime supply for every head; the prior paper supply and K=1 controls are separate.

### H-J. Implementation and hosted verification

[PR #1153](https://github.com/OVVO-Financial/RH_Lean/pull/1153), branch `agent/lean-verification/20261120-nyman-two-witness`, base as above, tree `64b45dc56544b43f88a9a64e3f8fe1b9a01fa568`. Seven changed paths. Pinned Lean `v4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` (toolchain `ba8ebf2dbaf6a668cd2a0e086186d6d569b69ff5`; manifest `a34d142c3d75a602a8b0f8241a4fb504d5c7c5a4`). Inputs: original residual `2da630c1d5fb9302e2097ec1e170cf41c2b40609`, taper `2d23721027ecc44e85b7add02fc632b482f03352`, geometry `9cfc801b5154245e8925f4247a0390470761f327`, profiles `1ce4bde64139395e79b9ceb2fd2a396457d7098a`. The five additional public checks, all in `RHLean.Analysis`, are:

| File in `research/` at tested head | Declaration | Dependencies visited |
|---|---|---:|
| `NYMAN_WITNESS_PRIME.lean` (`ec5d4b6badb30f367c742b68e639ff6a7c1a9bbc`) | `nyman_witness_relation_coordinate` | 558 |
| `NYMAN_WITNESS_CLIP.lean` (`a9728bb6cdbc54a92fc45e546acbf780d4b1b234`) | `nyman_witness_error_counts` (existing proof, made public) | 514 |
| `NYMAN_WITNESS_RANK.lean` (`a60a037c44d62f780a67fc524dc3a41cc1eb7935`) | `nyman_witness_two_amplitudes` | 705 |
| same | `nyman_witness_clip_fibres` | 770 |
| same | `nyman_witness_clip_zero_iff` | 836 |

The [first compiler run](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44718695707/job/136228550847) stopped at `dsimp made no progress`; the second commit removed this redundant step and applied the same rational independence theorem directly to count differences. No statement was weakened. The [raw-head job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44719772066/job/136232250227) checked the exact checkout, pins, rational regressions, warning-fatal original-source closure, both exact-type harnesses and all 12 dependency/axiom roots. The five rows above each used exactly `propext`, `Classical.choice`, `Quot.sound`, not five new axioms. [Audit artifact](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44719772066/artifacts/14620449270), SHA-256 `2b30d90e504b4ee2deab749fedea30764f3dc5e2391275e7ce5f856533fb5909`.

Other evidence: [independent targeted build](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44719772064/job/136232249941), [root build and elaborated graph](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44719772281/job/136232251618), [holes, axioms and root imports](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44719772281/job/136232251224), [proof inventory](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44719772065/job/136232249956), [public export](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44719772365/job/136232251128). No local Lean or no-op rerun. The PR was marked ready for human review at 10:34:07Z, not merged by this agent.

### K-M. Independent checks and a new paper result

The independently constructed [exact-rational checker](https://github.com/OVVO-Financial/RH_Lean/blob/e05f68039373d3df16bd1c033b9277178a7eb43d/scripts/lean/nyman_witness/two_witness_check.py) recomputed original and clipped residuals separately, from prime valuations of the signed taper, before comparing to the floor formula. It checked 13,374 outputs over 87 heads and 5,029 distinct joint counts aggregated across heads. Of these heads 84 have two eligible primes; three K=1 controls used 5 and 2, not two upper primes. Tests included m=0, both zeros, N+2 and large common-period shifts. Finite evidence, not the universal proof.

**`LV-20261120T101000Z/DRIFT`: PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING, not in #1153.** For fixed natural K>=1 and `0<H<6K`, no prime assumption is needed for this asymptotic as integer M tends to infinity:

`sum_{m=1}^M e(m)^2/[m(m+1)] = (U/L)^2 M - (3 U V/L^2) log M + C_{K,H} + O_{K,H}(1/M)`.

Indeed `Gi(m)=sum_{k in Ii}(m mod k)/k` is periodic with period dividing `lcm(2,...,N)` and mean `(K-s_i)/2`. Thus `e(m)=A m+b_m`, `A=U/L`, `b_m=-[a(G1(m)+K)+z(G2(m)+K)]/L`. Since `as+zt=U` and `K(a+z)=V`, its mean is `(U-3V)/(2L)`. The weighted summand equals `A^2+(2A b_m-A^2)/(m+1)+b_m^2/[m(m+1)]`. The centered periodic term has bounded partial sums, so its harmonic tail is O(1/M) by summation by parts; the last term has the same tail bound. The harmonic coefficient is `-3UV/L^2`. One eligible prime already forces U!=0 by the single-coordinate theorem (x=1,y=0), so the clipping-error energy diverges linearly at that fixed head. In contrast r is periodic and bounded for fixed K,H, and has period mean `1-(3-1)/2=0` by #1151; its weighted energy is finite. These bounds are not uniform as H grows. Independent control: K=1,2, H=1 or 3K, valuation rows 2,3,5,7,11; 20 full-period means and 100 polarized logarithmic coefficients checked exactly. Checker SHA-256 `6428b4f4e188627053bca1b4e1972b24e6ea41a93fe80949cd877fe7d0a2d2eb`.

### N. Continuity and specialist handoffs

Last own final `86b067fa8626fd58d3245fe8b4486634b28f135c` (Nov 19 PLATEAU/TWO-WITNESS, blob `6231b48290c36a43b0f1246b7fbddf692652109c`) to intake: 12 report commits, nine paths, no deletions. Dated listings and owned recovery siblings were included; a checkpoint and final for one run count once. `CONTINUITY_COMPLETE` for this delta; `CONTINUITY_UNVERIFIED` only for the inherited exhaustive Nov 13-15 archive gaps, not evidence of a missing launch. External handoffs unchanged `7d63d434690d00dffce9c90335d41c4f62d85798`: EXT-20261018-PNT-1 retains c=1 and p=R; EXT-20261014-5 is all-root, not first-bad.

| Role | Nov 19 -> last available at Nov 20 intake | Decision or requested check |
|---|---|---|
| Coordinator | PORT 23:09 EST; canonicals both `6790b8672ac80f6f3a36ca115929cf19f499cfb4`, final recovery twins `b107495e974bbf12d6571d646341126a3e7f5dba` | TODAY=PENDING; YESTERDAY=CARRY_FORWARD. One mirrored run. PORT1-4 reviewed on paper, PORT5 finite. Record the exact two-output obstruction, not a new exponent. |
| Owner | HINGE `85060bbc0910a64ce70a8c418d9fef35b16c768b` -> SLICE `4efb6209fe5bafdd68b3308d6fd3bf65706b2dff` | The exceptional 5/9+eps estimate is not all-square; restore the other products, masks and lower-height return. |
| Analytic | PHASELOCK `62efb52db960cff6ff4ca43497d48589c56bc791` -> SQUARE `ac32607e1561406f104e2d0255675ef1bfb8d442` | Keep the old-pair term, its square-root cutoff and the two-new error. H=12 rules out the universal clock shortcut, not an unbounded common subsequence. |
| Wheel | GATE `a20b2ee34f37f8ec7a6d632eb1f7a31521889232` -> WINDOW `5e9b51ec08580329940bdeb3c30a0603444b95d3` | The two-shape logarithmic estimate leaves other shapes, signs and strict chronology unpaid. No transport of the clipping bound. |
| Census | CLOCK `1093df2a14e84551dae3ca8216be7ac6c4bc30a8` -> LEDGER `b7a4cf1c9c6da6d6a2e0c2231ab92f47f1db1fae` | Retain degrees and coprimality; six endpoints are finite evidence. Reproduce DRIFT on different complete band periods. |
| Referee | ESCAPEMENT `e063ee0f793705c9ca823e0a8cee6ddc3b309418` -> APERTURE `29070a23c0dc5d7d296dd2f7032f07b26d384a5b` | Accepted TWO-WITNESS with its prime conditions, not an energy bound. Independently check the sign, all mixed terms and head dependence in DRIFT. APERTURE's displaced-zero expansion is still a paper claim. |

### O-P. First open theorem and resume capsule

Keep the predetermined `G={H>=6: 6 divides H and delta(y)=0 for some |y-H|<=3}`, `delta(y)=1-sum_{k<=y}mu(k)log(y/k)/k`, N=H^2=6K. Need **one unbounded subfamily of G** on which, for every eps>0, one scale-independent C_eps gives `E_H=sum_{m>=1} r_H(m)^2/[m(m+1)] <= C_eps H^eps`. The RIDGE4/PHASE3 paper Mellin consumer gives `E_H >= (2 sigma-1)(H+1)^(2 sigma-1)/|rho|^2` for each zeta zero rho with real part sigma>1/2. Thus this is a direct endpoint, not a finite exponent iteration. The common-subfamily full estimate is target-equivalent on the reported paper route, not an independently proved input. Restore the middle, both repair bands, their mixed products, growing head and location-weighted infinite tail together; a fixed-head estimate or a single well-chosen output does not do so.

Rechecked the [#1119 terminal certificate](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42552018910/job/128949473700), tested `77ee815846d6d534c866f0752aa33b84c385610a`, and [#949 underlying source](https://github.com/OVVO-Financial/RH_Lean/actions/runs/38741634035/job/116444547917), tested `982500b01f0f008b1164a172d06d28d14f8171d0`. `native_mertens_near_uniform_window_error_closed` (blob `f629db1b2b65d6ec042ac9432397d4b6316200c6`) transfers the genuine native growth theorem by boundary monotonicity: `b*=7/8-7/(64 Npack)` with every positive loss, not zero loss. No improvement here. Finite-AC's signed Mobius floors at `X=R^2-1`, Euler/VF's physical and virtual compensation, NNS's masked Hermitian terms and the native signed LOW/HIGH are different carriers; no typed norm bridge from these clipping errors was found. Preserve the nine independent routes. `STATUS=ACTIVE_SUPPORT; NO_NEW_GLOBAL_UPPER_GAIN; VERIFIED_ETA=NONE; RH=OPEN`.

Next: reuse the tested head; human review/merge only. Referee to review DRIFT before any new proof PR. Analytic/Coordinator to find an independent growing-head estimate on the complete signed residual on the same selected heads. Publication: early checkpoint and CAS milestone are one invocation; the latter's exact-commit readback `6280779e33ddc3608bd55f20f5a1de993d72300f` matched 2,338 bytes, Git blob `1dbc89709404c3e659a20a5ec1624f3ac9116e89`. Final canonical append preserves that entire prefix; its authenticating commit is recorded in the delivery receipt.

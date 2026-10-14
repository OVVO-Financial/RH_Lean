# External direct-research handoff — 2026-10-14 seven-function cycle

**Origin:** user-directed direct ChatGPT research session, NOT a scheduled RH Workspace Agent run.  
**Storage:** `agent-reports` branch only. This file must NOT overwrite any agent's eight assigned daily reports.  
**Main checked after PR #937 merge:** `fcccdb32559d762dc5296dc519929f053f0fdf95`.  
**Main authority blobs:** `AGENTS.md` `709ad61bf4555fe4f2c92af3fd42f3994798c8bf`; `CURRENT_PROOF_CONTRACT.md` `f6e8dc6813ec63974489c26b0c383e34203f0aa9`.  
**Original research baseline:** `52babf6eb87a7c6f80316ceb952667ad65cb2aa3`.  
**Proof PR:** [#937](https://github.com/OVVO-Financial/RH_Lean/pull/937), **MERGED** at `fcccdb32559d762dc5296dc519929f053f0fdf95`; verified proof head `59221ae46b2fa9b61cce2330ba965ea99bbce715`.  
**Important:** this is a *research submission*. Paper derivations and experiment results below are NOT to be relabeled `PROVED_IN_LEAN` until separately formalized, nor are the direct session's self-checks independent scheduled-referee acceptance.

## How to consume this handoff

At your next scheduled run: refresh current `main:AGENTS.md`, `main:CURRENT_PROOF_CONTRACT.md`, actual `main` SHA, original source declarations, and today's **and yesterday's** existing upstream reports at `ref=agent-reports` as normal. Also read this external handoff, checking its claim IDs and code against the live source. Only the merged #937 theorem declarations are `PROVED_IN_LEAN`. The three proposed estimates below are `PAPER_PROOF` and independent review/formalization candidates. Do not treat an external handoff as a completed scheduled stage or a change to the canonical objective.

## Canonical still-open objective

With `F_R=vfMidFinishedMass R`, public phase `sqrt(2)`, and genuine prime counting, prove

```text
VFCanonicalSquareVonKochStatement:
  exists C >= 0, forall R >= 2,
    |primeCounting(R^2) - F_R - sqrt(2)| <= C R log R.
```

The direct signed source target `VFMid915FirstBadSourcePaymentStatement` is **OPEN**. So is the native `VFMidDyadicSignedLateCorrectionStatement`. Finite A/C and CORR-4 are open sufficient alternatives. Raw original VF weights MUST NOT be replaced by phase-shifted covariance: `D_can=D_raw-sqrt(2)`; the quadratic correction is `-2 sqrt(2) D_raw + 2`.

## Claim EXT-20261014-1 — exact sharp quotient wheel-2310 capacity

**Status: PAPER_PROOF; FINITE_COMPUTATION results separately below.** Not yet compiled into Lean.  
**Original carrier:** `5 <= A <= R < 2A`; `p` is an actual prime late least-factor owner `A < p <= R`. Its fibre is the set of physical composites `n` in strict band `R^2 < n < (R+1)^2` with `minFac(n)=p`. Existing genuine-prime child theorem on the subdoubling run gives `n=p*q` with actual prime `q >= p`. There is a bijective/cardinality-preserving quotient map `n |-> q`, not a population proxy.

For `A >= 11`, define exact endpoints
```text
t = floor(R^2/p)
u = floor(((R+1)^2 - 1)/p)
C_m(R,p) = #{ q in Z : t < q <= u, gcd(q,m)=1 }
m = 30, 210 or 2310
W30(t) = #{j in {1,2,3,4} : gcd(t+j,30)=1}.
```
Then **for every genuine late fibre**, without a distribution hypothesis:
```text
card(F(A,R,p)) <= C_2310(R,p) <= C_210(R,p)
                 <= C_30(R,p) <= W30(t) <= 2.
```
**Proof:** A genuine quotient child is prime, `q >= p > A >= 11`. Therefore none of primes `2,3,5,7,11` divides `q`; it is coprime to 2310. The exact strict band gives `t<q<=u`. Existing Lean four-slot theorem gives `u<=t+4`. Injectivity of `n->q` implies the cardinality inclusion. The remaining inequalities are elementary set inclusions under nested moduli and the established parity-two wheel. No sieve error, independence, PNT, covariance assumption, or RH premise.

**Summed run consequence:** for any `11 <= A <= B <= 2A`, defining
`W_2310(A,B) = sum_(A<=r<B) sum_(p in LateOwners(A,r)) C_2310(r,p)`,
```text
LateRemoval(A,A,B) <= W_2310(A,B)
PrefixSupply(A,A,B) - W_2310(A,B) <= PrimeSupply(A,B).
```
These are **unsigned** starting-prefix population inequalities. They do NOT bound the centered cutoff-two signed correction `LateRemoval(2,A,B)-LateReference(2,A,B)`, nor the original historical VF source payment.

**Sharpness/counterexample:** `(A,R,p)=(12,22,17)`, `q=29,31` gives `n=493,527`, both strictly between `22^2` and `23^2`. Hence universal one-child capacity is **REFUTED** even on the genuine 2310-wheel.

**Computed exact totals, using the attached reproducer** `sharp_wheel_2310.py`:

| Run [A,B) | Owner slots | Actual late composites | Four-slot W30 | Sharp C30 | Sharp C210 | Sharp C2310 |
|---|---:|---:|---:|---:|---:|---:|
| [50,100) | 268 | 131 | 282 | 177 | 145 | 133 |
| [100,200) | 1,033 | 463 | 1,091 | 704 | 603 | 532 |
| [500,1000) | 18,409 | 6,587 | 19,573 | 12,442 | 10,662 | 9,735 |
| [2634,5267) | 426,984 | 125,272 | 454,679 | 290,946 | 249,372 | 226,691 |
| [5000,10000) | 1,411,740 | 385,553 | 1,504,048 | 959,418 | 822,307 | 747,547 |

The 2310 sum saves `227,988` vs W30 over [2634,5267) and `756,501` over [5000,10000). These values were **rerun successfully in the posting session**, but remain finite results; they do not imply any all-R residue-dispersion estimate or signed payment.

**Next checks:** Finite Wheel should verify sharp quotient upper endpoint `((r+1)^2-1)/p` against existing Lean, and Agent #7 can formalize on a NEW scoped PR after Referee accepts the statement. The highest-value proof problem remains elsewhere: the physical weighted source splice.

## Claim EXT-20261014-2 — strict signed original-weight owner-3 ancestry

**Status: PAPER_PROOF; not Lean-formalized.** For actual prime `q>3`, current physical composite `n=3q`, integer root `R>=2048` with `R^2 < 3q < (R+1)^2`, put `r=floor(sqrt(q))` and original odd-seat weight
```text
w(t) = (2t+1)/(t * log(t^2+t+1/2)).
x = w(R), y = 1-w(r).
```
The literal signed current/historical pair is `+x` on composite `3q`, `-y` on prime `q`, with distinct original block weights. The map `3q -> q` is injective **within this matched owner-3 subcarrier**, but this does not authorize spending `q` again under another owner.

**Proposed bound:**
```text
x - y = w(R) + w(r) - 1 < -451/640.
```
**Paper proof:** `vfMid915TripleCurrentParent_in_halfRun` (compiled for `R>=16`) places `q >= (R/2+1)^2` with natural integer division, so `r >= R/2+1 >=1024`. For every `t>=16`,
`0 < w(t) < 33/(32 log t)`: the logarithm denominator is `>2 log t` and `1+1/(2t)<=33/32`. Since `log2>2/3`, `R>=2^11` implies `w(R)<9/64=90/640`; `r>=2^10` implies `w(r)<99/640`. Add and subtract 1:
`x-y < 90/640+99/640-640/640=-451/640`.
This is a strictly **local signed** pairing, not the global UPM/LPM zero-target payment.

Relevant exact Lean source:
- [Original signed seat charges](https://github.com/OVVO-Financial/RH_Lean/blob/fcccdb32559d762dc5296dc519929f053f0fdf95/research/VF_MID_SIGNED_SEAT_CHARGE.lean), blob `13dda0d2c6cc59580959a2d59fad60126b1c6b0b`.
- [Triple-parent half-run membership](https://github.com/OVVO-Financial/RH_Lean/blob/fcccdb32559d762dc5296dc519929f053f0fdf95/research/VF_MID_915_LATE_PREFIX_WEIGHTED_DYADIC.lean), blob `3d12fe937cc7de03fb307417a7156d194bab45db`.

## Claim EXT-20261014-3 — negative isolated NNS payment; global covariance NOT decided

**Status: PAPER_PROOF, not Lean-formalized.** For every eligible original `3q` pair in Claim 2, the isolated two-seat zero-target NNS slack obeys
```text
6*x*y - x^2 - y^2 < -541/409600 < 0.
```
**Proof:** Claim 2 gives `0<x<90/640`, `y>541/640>0`; hence `y-6x>1/640`. Algebra:
`6xy-x^2-y^2= -x^2 - y(y-6x) < -(541/640)(1/640)=-541/409600`.

**Crucial warning:** this REJECTS the proposed *pairwise standalone payment method*; it does NOT refute original global source payment. For the whole residual source, let `M0` be total absolute mass and `S0` the signed sum. Adding literal charges `(+x,-y)` gives `a=x+y`, `d=x-y`, and
```text
G(M,S)=M^2 - 2*S^2
G(M0+a,S0+d)-G(M0,S0)
  = 2*M0*a - 4*S0*d + (a^2 - 2*d^2).
```
The cross terms couple the pair to the *entire* ledger. Compiled `vfMid915ActualHistoricalSquaredNormRestoration` also imposes exact historical norm restoration `4UL+2C(U+L-|U-L|)`. No pair can be declared globally paid or deleted from the NNS denominator until this complete accounting is preserved.

**Numerical reproducer:** `nns_pair_slack.py` using genuine prime trial division, integer square roots, and 55-digit decimal logs. Selected observed maximum isolated slack:
```text
R=1010: +0.000031458273832282995  (54 pairs)
R=1011: -0.000067449052755200863  (57 pairs)
R=1024: -0.001618362818899407292  (51 pairs)
R=2048: -0.078610716445253926918  (106 pairs)
R=4096: -0.144986831672762669977  (180 pairs)
R=5000: -0.162407201673252884591  (210 pairs).
```
Exact genuine witness `R=1011, n=1022127=3*340709`, `r=583` disproves the universal individually nonnegative isolated payment claim. The numerical results are `FINITE_COMPUTATION` and were reproduced in the posting session; the all-scale `R>=2048` inequality rests on the paper derivation above.

Relevant Lean source:
[original historical NNS norm restoration](https://github.com/OVVO-Financial/RH_Lean/blob/fcccdb32559d762dc5296dc519929f053f0fdf95/research/VF_MID_915_EXACT_HISTORICAL_NNS_COMPRESSION.lean), blob `190bd8024bcda99eb3b3349729466903db4e4c39`.

## Claim EXT-20261014-4 — existing merged, compiled W30 infrastructure (NOT new research)

**Status: PROVED_IN_LEAN at PR #937's exact verified head; now merged into `main`.** The following declarations were compiled in `research/VF_MID_LATE_OWNER_WHEEL_THIRTY_BUDGET.lean` (main blob `3701895c3e3af16b6f6b0506ed69f7b5c3d55800`):
1. `vfMidSquareBandLateOwner_roughChildren_subset_wheelThirty`
2. `vfMidSquareBandLateOwner_card_le_wheelThirty`
3. `vfMidDyadicLateRemoval_start_le_wheelThirtyBudget`
4. `vfMidDyadicPrimeSupply_ge_startPrefix_sub_wheelThirtyBudget`

PR #937 proof head `59221ae46b2fa9b61cce2330ba965ea99bbce715` passed:
- [Targeted Lean iteration](https://github.com/OVVO-Financial/RH_Lean/actions/runs/38548372917), `success`, warning-fatal new module and standard axioms only (`propext, Classical.choice, Quot.sound`).
- [Lean source audits](https://github.com/OVVO-Financial/RH_Lean/actions/runs/38548373792), `success`.
- [Proof inventory](https://github.com/OVVO-Financial/RH_Lean/actions/runs/38548372797), `success`.
- [Public export verification](https://github.com/OVVO-Financial/RH_Lean/actions/runs/38548372748), `success`.

The W30 theorems do not imply the stronger C2310 bound **without the separate paper proof**; neither one establishes signed historical source payment. Do not reopen #937 or redo its compilation on unchanged declarations.

## Current first missing lemma: SOURCE-SPLICE-1

The genuinely first open direct-VF structural requirement is an EXACT occurrence-, sign-, coefficient-, source-tag-, time-, clipped-boundary-, survivor-mask-, historical-anchor-, cross-term- and multiplicity-preserving equality from the true cutoff-two first-bad historical/current source onto the already-cancelled safe/sector-six ledger, followed by descent of **complete lower-child runs**. The source-payment inequality and global NNS positive slack remain unpaid. The sharper C2310 bound helps only one unsigned auxiliary capacity leg.

Falsify candidate mappings before estimating: ensure occurrence `27` at `(A=5,B=9)` is retained once with its actual early owner; test repeated owner `p=7` (77,91) and repeated historical partner `q=13` (91,143); conserve raw signed sum and complete original absolute mass separately, then check global `M^2-2S^2`, including restoration. No hidden covariance, factor-independence, all-scale residue dispersion, or fixed-phase crossing premise.

### Specialist routing for the next actual scheduled runs

- **Coordinator:** read and cite this handoff in the next stage; route EXT-1 to Wheel/Referee, EXT-2/3 to Owner/Analytic/Referee, and SOURCE-SPLICE-1 as the primary proof task. Do not report these as independent scheduled-agent outputs.
- **Owner Payment:** focus on the literal original-weight `3q` pairing, its unmatched historical siblings, masks, anchor, and cross terms. Propose an exact residual-to-Sector-Six identity; *not* a pairwise nonnegative NNS theorem.
- **Analytic Type II:** test the global coupled NNS balance only after the exact residual carrier is defined. Do not mistake a separate sum-of-squares or a conventional unsigned sieve bound for physical signed payment.
- **Finite Wheel:** audit C2310 exact endpoint and genuine child inclusion; avoid assuming adaptive prime residues are equidistributed.
- **Prime Census:** reuse existing numeric aggregates, reproduce the two small scripts if needed after checking hashes, and prioritize counterexamples to *new weighted ledger equality*.
- **Adversarial Referee:** independently ACCEPT/REVISE/REJECT each EXT claim, especially the inequalities involving `w_R,w_r`, repeated historical occurrences, and global NNS cross terms. Self-audited paper results are not independent referee certification.
- **Lean Verification:** no need to reprove merged W30. After referee acceptance, consider concise Lean formalization of EXT-1 and the owner-3 scalar bounds if useful. Do not create a closure PR with SOURCE-SPLICE-1 as an unproved premise.

## Reproducibility and provenance

Scripts committed next to this handoff on `agent-reports`:
- [sharp_wheel_2310.py](sharp_wheel_2310.py): SHA256 `f519ab2bb2d9bc843c6be69bbbb81350d0c1c2dce9a66c3e64d4c560599a6faa`. Run `python3 sharp_wheel_2310.py`.
- [nns_pair_slack.py](nns_pair_slack.py): SHA256 `21e7bcab9cb10af0d1c5bc7bd0ce1dd9bc4afcbeb2bba533264737a3c1473e3a`. Run `python3 nns_pair_slack.py`.

These scripts were executed in this direct session and their tables verified. The earlier October 14 scheduled Wheel/Census/Referee reports remain unmodified; do not backfill absent `00/10/20` reports as if they ran. The larger direct-session narrative artifact is archived outside GitHub; this self-contained handoff and scripts are the durable GitHub submission.

**No RH proof. No universal finite A/C. No original signed source-payment closure. No changes to `main` or any scheduled agent report.**

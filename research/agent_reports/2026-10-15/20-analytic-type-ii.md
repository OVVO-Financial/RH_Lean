# RH_Lean agent daily report — 2026-10-15 / RH | Analytic Type II

**Status:** PARTIAL / IN_PROGRESS  
**Run ID:** RH-ANALYTIC-20261015T222600-0400  
**Checkpoint:** 2026-10-15T22:28:37-04:00 (America/New_York)

## A. Most important analytic development

Research is in progress. The selected question is whether the newly merged Nyman–Beurling positive-residue geometry admits a general, explicit inverse theorem forcing every squarefree modulus coefficient toward its Möbius value. No all-scale decay, canonical endpoint bound, zero-free half-plane, or RH claim is made at this checkpoint.

## B. Authority and continuity

- Live `main` HEAD: `68bc4aaae65c9f505202a22df446c0fb40e4d040` (merge of PR #957).
- `main:AGENTS.md` blob: `cbc234051834f971929d82972ba6a157b2129d32`.
- `main:CURRENT_PROOF_CONTRACT.md` blob: `dc73babe5eb7b8f9fb83272a27cd2468dbdcb7f2`.
- Factor-depth brief blob: `1a5f94bb81aa7d50b7c118f823a14c9ec644f947`.
- Mertens amplification budget blob: `3beff1f789646d59237744379ff8e578bb1042a0`.
- Nyman–Beurling research note blob: `b2775c892edffe920a101651eef6f3581c73c9d4`.
- Current-day reports read: Coordinator `0f9e254738e1bc3d01cfd0a3b114d99b7478b08a`; Owner `01fb928be14c1004b3124fb25101f369ad7e8611`; Wheel `6d451c35eef4021fcff78253bed609d193c249c1`; Census `2e3c1cf95cd11669d57d2ce1f7216916736ff095`; Referee `cf0db85f6b04c56527bc9a26a1b6741ae196435a`; Lean `a11eddb6f78c927b8ec838426f94d72e63cda123`.
- This Analytic report was absent before this write: `TODAY=PENDING`. The 2026-10-14 Analytic report blob `3a6932d9c5e1474adf1f34374310c7b73eb71fc2` is `YESTERDAY=CARRY_FORWARD`.
- External inbox blob `c1d1aad9872d1760d2e4e34b30bbc0ed4fa3d33c` was consumed. Its 2026-10-14 claims retain their recorded scopes.
- PR #957 is merged; no open pull request was found at refresh. The merge adds a paper-level positive-residue note and exact finite computation, not a Lean proof of convergence.

## C. Exact research target

For `a_k(m)=(m mod k)/k`, `F(m)=sum_k c_k a_k(m)`, residual `r_m=1-F(m)`, and
`D(F)^2=sum_(m>=1) r_m^2/[m(m+1)]`, derive and falsify a completely explicit squarefree-`q` coefficient-rigidity inequality. The starting identity in the merged note is
`L_q(F)=sum_(d|q) mu(q/d)(F(d)-F(d-1))=-c_q`.
The missing work is the exact dual norm, quantitative constant, uniformity, and interpretation.

## D. Publication state

This is an early durable checkpoint only. Substantive derivation, falsification, claim classification, and the next-run capsule will be appended after completion.

---

## Completed analytic update — 2026-10-15T22:30:31-04:00

**Final status:** COMPLETED  
**Result classes:** PAPER_PROOF; exact inverse/rigidity theorem; no new decay estimate and NO_NEW_RESULT on the canonical endpoint bound.

## E. Claim 20261015-analytic-1 — exact coefficient extractor and weighted dual bound

Fix a real `alpha >= 1/2`. Put

```text
w_alpha(m) = (m^(-2 alpha) - (m+1)^(-2 alpha))/(2 alpha) > 0,
a_k(m) = (m mod k)/k      (k>=2, m>=0),
F(m) = sum_(k in finite K) c_k a_k(m),
t(0)=0, t(m)=1 for m>=1,
r_m=t(m)-F(m),
D_alpha(F)^2=sum_(m>=1) w_alpha(m) r_m^2.
```

For every integer `q>=2`, define

```text
Lambda_q(f)=sum_(d|q) mu(q/d) [f(d)-f(d-1)],
lambda_q(m)=1_(m|q) mu(q/m) - 1_(m+1|q) mu(q/(m+1)),
C_(q,alpha)=sum_(m=1)^q lambda_q(m)^2 / w_alpha(m).
```

Here an absent coefficient is defined as `c_q=0). Then

```text
Lambda_q(a_k) = -1_(k=q),
Lambda_q(t)=mu(q),
Lambda_q(r)=mu(q)+c_q,
|mu(q)+c_q|^2 <= C_(q,alpha) D_alpha(F)^2.       (A)
```

**Status: PAPER_PROOF.** All quantifiers are explicit: the coefficient set is any finite subset of integers at least two; coefficients are real; `q>=2`; and `alpha>=1/2`. The constant is finite, positive, and depends only on `q,alpha`.

**Proof.** Since
`a_k(d)-a_k(d-1)=1/k-1_(k|d)`, the constant `1/k` term vanishes under the divisor Möbius sum. The remaining sum is

```text
-sum_(d|q,k|d) mu(q/d)
 = -1_(k|q) sum_(e|(q/k)) mu((q/k)/e)
 = -1_(k=q).
```

Only the jump `t(1)-t(0)=1` contributes to `Lambda_q(t)`, giving `mu(q)`. Collecting the coefficient of each `r_m` gives the displayed `lambda_q(m)). Weighted Cauchy–Schwarz gives (A), with no convergence exchange because `Lambda_q` has finite support.

This is stronger than the merged note's qualitative squarefree omission remark: it extracts every coefficient, including squareful indices, with its exact continuous-functional norm.

## F. Claim 20261015-analytic-2 — classical-norm constants, omission floors, and coefficient rigidity

At `alpha=1/2`, `w(m)=1/[m(m+1)]), hence

```text
C_q = sum_(m=1)^q m(m+1) lambda_q(m)^2,
C_q <= 4 sigma_2(q) <= 4 zeta(2) q^2 = (2 pi^2/3) q^2.       (B)
```

The first inequality follows from `(u-v)^2<=2u^2+2v^2` and the two divisor-coordinate contributions:
`2 sum_(d|q)[d(d+1)+(d-1)d]=4 sigma_2(q)`. The second is
`sigma_2(q)/q^2=sum_(d|q)d^(-2)<=zeta(2)`.

Consequences for every finite residue combination are:

1. `|c_q+mu(q)| <= 2 sqrt(sigma_2(q)) D(F) <= (2 pi/sqrt(6)) q D(F)`.
2. If squarefree `q` is omitted, then
   `D(F)^2 >= 1/C_q >= 1/[4 sigma_2(q)] >= 3/(2 pi^2 q^2)`.
3. If `D(F_j)->0`, then for every fixed `q>=2`,
   `c_(j,q)->-mu(q)`. Thus squarefree coefficients converge to their signed Möbius values, while every fixed squareful coefficient converges to zero.
4. The assertion does not prove that the squarefree-only span is dense. It proves a necessary pointwise coefficient law for any successful sequence.

For `q=6`, the only nonzero coefficients of the dual functional are
`lambda_6(1)=2, lambda_6(3)=-1, lambda_6(5)=-1, lambda_6(6)=1`; therefore
`C_6=8+12+30+42=92). The merged omission-of-6 floor `D^2>=1/92` is exactly the `q=6` instance, not a separate phenomenon.

**Status: PAPER_PROOF.** No zeta-zero hypothesis, PNT, random-sign assumption, or asymptotic interchange is used.

## G. Claim 20261015-analytic-3 — quantitative forced support and coefficient complexity

Let `D=D(F)>0`. If

```text
2 <= Q <= sqrt(6)/(4 pi D),
```

then every squarefree `q<=Q` must occur in the support and has
`|c_q|>=1/2`. Indeed Claim 2 gives
`|c_q+mu(q)|<=1/2`, while `|mu(q)|=1`. Consequently

```text
sum_k |c_k| >= (1/2) #{q: 2<=q<=Q, q squarefree}.             (C)
```

Using the classical squarefree counting asymptotic, (C) says that along any sequence with `D->0), the coefficient `l1` norm is at least of order `1/D`. This is an inverse concentration theorem: small positive Hilbert error forces a growing block of genuine Möbius-signed directions. It also explains why a tail certificate based only on
`|r_m|<=1+sum|c_k|` becomes increasingly expensive; this is a limitation of that absolute tail method, not an obstruction to approximation itself.

As a weaker self-contained distance consequence, Bertrand's theorem supplies a prime `N<q<2N` omitted by the basis `2<=k<=N`. Claims 1–2 give, for every integer `N>=2`,

```text
d_N^2 >= 3/(8 pi^2 N^2).
```

This elementary bound is far weaker than Burnol's logarithmic lower obstruction and is not presented as competitive with it.

**Status: PAPER_PROOF.** The exact finite inequality (C) needs no asymptotic. The order-`1/D` interpretation uses the standard squarefree counting asymptotic; the final `d_N` corollary uses Bertrand.

## H. Independent validation and falsification

An exact rational script checked simultaneously for every `2<=q<=100` and `2<=k<=150` that
`Lambda_q(a_k)=-1_(q=k)`, and checked `C_q<=4 sigma_2(q)`. Output:

```text
PASS q<=100, k<=150: extractor identity and C_q <= 4 sigma_2(q)
```

This is only finite regression evidence; the proof above is all-scale.

Strongest attempted overclaims rejected:

- The theorem does **not** prove `D(F_N)->0), a contraction, a subpower Mertens gain, or RH.
- Pointwise decay of squareful coefficients does not prove the squarefree-only basis is dense; infinitely many collectively small squareful coefficients could still matter.
- Coefficient rigidity is necessary, not a sufficient approximation construction.
- The exact dual lower bound need not be sharp for general `q`, because the minimizing residual for the abstract finite functional need not lie in the residue-span residual set.
- No raw-seat, first-bad returned-cell, #915, or canonical-VF source bridge is inferred.

The primary literature context was checked at the cited original sources: Báez-Duarte's integer-dilation strengthening (arXiv:math/0202141) and Burnol's lower-bound paper (arXiv:math/0103058). The new Claims 1–3 are elementary derivations from the merged discrete model and do not depend on importing either external theorem.

## I. Relevance and mechanism decision

**Independent fact learned:** the positive residue geometry contains a continuous family of exact Möbius coefficient extractors. Small Hilbert error cannot arise from arbitrary positive-basis cancellation: it forces the low squarefree coefficient block toward `-mu` and suppresses each fixed squareful coefficient.

**What this changes:** the merged omission-of-6 obstruction generalizes quantitatively to every squarefree modulus, and the full route now has an inverse theorem identifying the only possible pointwise coefficient profile. This is a genuine structural restriction, not merely another equality for the endpoint defect.

**What it does not change:** the missing theorem remains an independently proved upper bound or decay law for the full positive approximation. At `alpha=1/2`, such convergence is RH-strength by the external Báez-Duarte criterion. The present inverse theorem supplies no rate and no new value of the Mertens growth exponent.

**Decision:** `CONTINUE / REVISE` the positive-geometry alternative as a distinct analytic program; seek a constructive estimate exploiting the forced Möbius profile. Do not replace the live factor-depth or MU-LIFT portfolios without Coordinator/human approval. Reject prime-only and any basis omitting a fixed squarefree direction. Treat squarefree-only density as open, not as a conclusion of coefficient rigidity.

## J. Specialist handoffs

- **Coordinator:** Claims `20261015-analytic-1..3` are new `PAPER_PROOF` structural/inverse results on the merged positive-residue carrier. They do not close the endpoint bound. Consider the route as an eligible alternative, not a replacement campaign.
- **Adversarial Referee:** audit the sign `Lambda_q(a_k)=-delta_(qk)`, the residual identity `Lambda_q(r)=mu(q)+c_q`, exact dual norm, and the distinction between pointwise squareful suppression and squarefree-only density.
- **Lean Verification:** Claims 1–2 are finite-sum arithmetic plus weighted Cauchy–Schwarz and are plausible scoped formalization candidates only after Referee acceptance. No proof PR is requested by this scheduled non-Lean agent.
- **Prime Census:** no large computation is requested. If numerical work is later authorized, inspect optimized coefficient deviations `c_q+mu(q)` against `sqrt(C_q)d_N` and distinguish fixed-`q` convergence from growing-`q` behavior.
- **MU-LIFT researchers:** this theorem is on a distinct positive Hilbert carrier and does not supply the required signed floor-kernel inequality with final budget exponent `r<k`.

## K. Source, PR, and CI state

Final refresh kept `main@68bc4aaae65c9f505202a22df446c0fb40e4d040`. Material blobs:
canonical theorem `43e160ac7ad51f7646771297f43a9b95395ce709`;
Mertens converse `c15bdfcb0b050b26e3f0ea54775d8fd61d8af8bb`;
Nyman note `b2775c892edffe920a101651eef6f3581c73c9d4`.

PR #957 is merged at `68bc4aaa...` from head `a5fc4e8acc8198af57fb6206d90553194ae4c013`. Connector queries returned no workflow runs and no legacy combined statuses attached to that head. This is consistent with the PR's documentation/experiment scope but is not Lean CI evidence. No new Lean theorem or axiom audit is claimed here.

## L. Next-run resume capsule

- Resume from `main@68bc4aaa...`, authority blobs `cbc23405...` and `dc73babe...`.
- Reuse Claims `20261015-analytic-1..3`: exact coefficient extraction, weighted dual inequality, explicit `C_q`, squarefree omission floor, pointwise Möbius rigidity, and forced-support lower bound.
- Preserve the regression `q=6, C_6=92` and the exact PR #957 finite separation.
- First unresolved analytic question: can a constructive full- or squarefree-basis approximant exploit the forced coefficient profile to prove any new uniform upper bound without simply assuming Nyman–Beurling density?
- Strong falsification target: determine whether truncating at `c_q=-mu(q)` produces a tail whose exact Hilbert norm can be bounded independently, with all residue correlations retained.
- Avoid: interpreting coefficient necessity as convergence, inferring squarefree-only density, claiming a fixed contraction forbidden by Burnol, or transferring this Hilbert result to the VF carrier without a proved bridge.
- Canonical endpoint bound, MU-LIFT amplitude gain, finite A/C, CORR-4, #915 payment, and RH remain open.


## M. Publication verification

- Early checkpoint commit: `133a56c80cc9b8a25239e28aa495784334988989`; verified checkpoint blob `9093a2c160d99fb5ca8eafc1051f7c215dc4d804`.
- Substantive completion commit: `54970e21548735062ce97483b6960fa37eabb935`; verified completion blob `8c2d99fea902024b4e8694479ad63647fb209c61`.
- Readback verified all three claim IDs, complete proofs and constants, falsification limits, handoffs, source/CI state, and the resume capsule.
- Publication status: `COMPLETED`.

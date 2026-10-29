# RH_Lean agent daily report - 2026-10-29 / RH | Adversarial Referee

**Status:** COMPLETED  
**Invocation:** scheduled run begun 2026-10-29 03:34 America/New_York  
**Pinned main:** `a59d351aa33c3cc071ab7b9221f765dc89a2012c`  
**Main tree:** `ca27a57919b217ae7875df8fe092dd7fe0724136`  
**Authority blobs:** `AGENTS.md` `4bc5e5bacd333be41ca9334fa6eaf8e29b9bd1c8`; `CURRENT_PROOF_CONTRACT.md` `24bd727096001b68c76b28fe70c99b8d548d7bfe`  
**Primary reviews:** PR #1051 at `3d687adfbfd080167e6eedbd5c0185640428f39f`; PR #1050 at `8930575b88813094ae44cfa87b4ff8c3faf20d1f`; `20261028-coordinator-1`  
**New claims:** `20261029-referee-1..3`  
**Result classes:** `ACCEPT_WITH_SCOPE`, `COUNTEREXAMPLE_TO_STRENGTHENING / INFINITE FAMILY`, `TARGET_EQUIVALENT`, `PROVED_IN_LEAN_PR_GREEN_UNMERGED`, `NO_NEW_GLOBAL_QUANTITATIVE_BOUND`, `NO_RH`

## A. Bottom line

1. **PR #1051 centered first-prime theorem: ACCEPT WITH SCOPE.** The paper proof of

   `sum_(H<=R<2H) F_Q(R)^2 <= 4(HQ+Q^4) <= 8HQ`

   for `H,Q>=2`, `Q^3<=H`, is correct. It uses the literal `a=1,b=p` column of the original Euler off-diagonal, exact centering, coprime CRT, and a valid incomplete-period remainder. I independently reproduced held-out cases. A sharper bound follows from the same proof:

   `E_Q <= 4[H*pi(Q) + (sum_(p<=Q)p)^2 - sum_(p<=Q)p^2]`.

2. **The same estimate is false for the uncentered physical row.** Claim `20261029-referee-2` gives an infinite primorial-period family. The principal residue mean is not a bookkeeping nuisance: it eventually contributes more than `8HQ` by a factor of order `Q/log^2 Q`. Thus #1051 proves cancellation only for the centered residual `F_Q`, not an `8HQ` moment for the actual row `U_Q`. Principal and mixed terms remain unpaid.

3. **Coordinator anti-saturation audit: ACCEPT / TARGET_EQUIVALENT.** The square-completion inverse statements in `20261028-coordinator-1` are correct. PR #1050's later scalar defect lower-bound proposal is equivalent, under the historical envelope and above the computed threshold, to excluding the high root itself. It is not an independent bootstrap. The exact owner-tail, boundary, Abel, and square-completion declarations remain valid structural reductions at a green unmerged head.

4. The canonical `VFCanonicalSquareVonKochStatement`, complete signed source payment, strict improvement below `7/8`, finite A/C, full CORR-4 mixed-tail power, MU-LIFT gain, and RH remain open.

## B. Authoritative objective and source

The canonical public objective remains

```text
exists C >= 0, forall R >= 2,
  |pi(R^2)-VF_can(R^2)| <= C*R*log R.
```

The exact source used by #1051 is on main in `research/EULER_FRACTIONAL_COUPLED_20261027.lean`, blob `e6c4b1690e497760d366e36b28a1f7aa60e19f85`. Its strict original off-diagonal is

```text
eulerFractionOffQ(R)
 = sum_(1<=b<R) mu(b) sum_(1<=a<b) mu(a)
     ((R^2-1 mod ab)/(ab)).
```

For `a=1,b=p`, symmetry supplies coefficient `2*mu(1)*mu(p)=-2`. If

```text
f_p(R)=((R^2-1) mod p)/p,
m_p=p^(-1) sum_(r mod p) f_p(r),
U_Q(R)=-2 sum_(p<=Q) f_p(R),
F_Q(R)=U_Q(R)+2 sum_(p<=Q)m_p,
```

then `F_Q` is the centered residual reviewed below. The condition `Q^3<=H` ensures every `p<=Q` is genuinely admitted by `b<R` throughout `H<=R<2H`.

## C. Claim `20261029-referee-1`: centered theorem accepted and sharpened

Put `g_p=f_p-m_p`. For distinct primes `p,q`, CRT identifies one complete `pq`-orbit with the product of the separate residue orbits, hence

```text
sum_(R mod pq) g_p(R)g_q(R)=0.
```

Every consecutive interval of length `H` is a union of complete `pq` blocks starting at its own left endpoint plus fewer than `pq` remaining sites. Since `|g_p g_q|<=1`,

```text
|sum_(H<=R<2H) g_p(R)g_q(R)| <= pq.
```

The diagonal is at most `H` per prime. Expanding before absolute values gives the sharper exact bookkeeping bound

```text
sum F_Q(R)^2
 <= 4[H*pi(Q) + sum_(p!=q<=Q) pq]
 = 4[H*pi(Q) + (sum_(p<=Q)p)^2 - sum_(p<=Q)p^2].       (1)
```

Since `pi(Q)<=Q` and `sum_(p<=Q)p<=Q^2`, (1) implies the submitted `4(HQ+Q^4)`, and `Q^3<=H` implies `Q^4<=HQ`.

Independent exact-rational held-out checks, not present in #1051's regression, gave:

| H | Q | exact energy | sharper bound (1) | submitted bound |
|---:|---:|---:|---:|---:|
| 343 | 7 | `27623857/56700` | 6296 | 19208 |
| 2197 | 13 | `2994784222921/624323700` | 57944 | 228488 |
| 6859 | 19 | `902524732816853017/44566098677100` | 239096 | 1042568 |

All satisfy (1). The advertised factor-`Q` saving is relative to the coarse pointwise estimate `4HQ^2`; it is genuine for the centered subsector but does not estimate the complete source.

**Verdict:** `PAPER_PROOF / ACCEPT_WITH_SCOPE`. The bound itself is not a named Lean theorem. The complete-orbit covariance supporting it is kernel-certified at the stated PR head.

## D. Claim `20261029-referee-2`: primorial obstruction to the uncentered strengthening

The strengthening obtained by replacing `F_Q` with the actual uncentered row `U_Q` in `8HQ` is false for infinitely many `(H,Q)` satisfying every size condition.

Let

```text
P_Q = product_(p<=Q, p prime) p,
H=P_Q.
```

For all sufficiently large `Q`, `Q^3<=P_Q`. The interval `[H,2H)` is one complete period for every column and hence for `U_Q`. Its period mean is

```text
mean(U_Q) = -2 sum_(p<=Q)m_p.
```

Jensen, or Cauchy-Schwarz on the complete period, gives

```text
sum_(H<=R<2H) U_Q(R)^2
 >= 4H (sum_(p<=Q)m_p)^2.                              (2)
```

It remains to lower-bound the genuine principal means without assuming equidistribution. For an odd prime `p`, put `y_r=(r^2-1) mod p` in `[0,p)`. There are `ceil(p/4)` possible integers with `y<p/4`, and each congruence `r^2=y+1 mod p` has at most two solutions. Therefore at least `(p-3)/2` residues have `y_r>=p/4`, and

```text
m_p = p^(-2) sum_(r mod p)y_r >= (p-3)/(8p).
```

In particular `m_p>=1/16` for every prime `p>=7`. Thus

```text
sum_(p<=Q)m_p >= (pi(Q)-3)/16,
sum U_Q(R)^2 >= H (pi(Q)-3)^2/64.                       (3)
```

By the prime number theorem, `(pi(Q)-3)^2/Q -> infinity`. Consequently (3) exceeds `8HQ` whenever `(pi(Q)-3)^2>512Q`, which holds for all sufficiently large `Q`. This supplies an unconditional infinite family of failures of the uncentered extension.

**Classification:** `COUNTEREXAMPLE_TO_STRENGTHENING`, not a refutation of #1051's stated centered theorem. It proves that any transfer to the physical row must explicitly pay the principal energy and its mixed interaction with the remaining Euler source. Merely calling `F_Q` an actual subsector does not remove this bill.

## E. Claim `20261029-referee-3`: #1050 anti-saturation and no-circularity audit

At PR #1050 head `8930575b88813094ae44cfa87b4ff8c3faf20d1f`, set

```text
x=M(R^2-1)-M(R-1),
s=sum_(q^2<R) M(floor((R^2-1)/q^2))/q,
E=sum_(q^2<R) M(floor((R^2-1)/q^2))^2,
lambda=211/1814.
```

The formal square-completion algebra yields

```text
Def=lambda*x^2-2*x*s-s^2+(9/4)E.
```

Under the historical envelope and a high root, `|s/x|<=u_a`, `E/x^2<=e_a`. For `u_a<=1`, the maximum of `-2t-t^2` on `|t|<=u_a` is `2u_a-u_a^2`, attained at `t=-u_a`. Hence

```text
Def/x^2 <= lambda + 2u_a-u_a^2+(9/4)e_a.
```

Therefore an all-high-root lower bound with a larger defect excludes every high root; conversely, absence of high roots makes that universal conditional assertion vacuous. Within this scalar envelope the proposed statement is target-equivalent, not an independent contraction. The witness `s=-u_a*x`, `E=e_a*x^2` is sharp for the coarse scalar constraints, though it is not asserted to be an admissible arithmetic configuration.

This does not invalidate #1050's exact original-owner bridge, `3R` boundary payment, conditional large-owner tail, Abel recombination, or square-completion identities. It blocks only promotion of the scalar non-saturation hypothesis as new arithmetic input. The original OAI adapter remains outside the native-only kernel validation, exactly as the PR states.

## F. Formal and CI audit

### PR #1051

- State: open draft, mergeable; exact head `3d687adfbfd080167e6eedbd5c0185640428f39f`.
- Paper blob: `research/NATIVE_SQUARE_CLOCK_FIRST_PRIME_MOMENT_20261028.md` `17fd5a56e16f8f9d8fd14a64acbebdfc6bce832d`.
- Centered covariance Lean blob: `83c83502e815d15c06d2eda8c1890022adbca119`.
- Targeted Lean run `40798727612`: success. It compiled both changed Lean modules warning-fatally; printed axioms are only `[propext, Classical.choice, Quot.sound]` (the elementary difference theorem omits `Classical.choice`).
- Exact-rational run `40798727572`: success. It verifies the submitted fixtures and shared-factor negative controls.
- Scope: the all-`H` moment is paper-proved and regression-tested, not kernel-formalized as a named inequality.

### PR #1050

- State: open non-draft, mergeable; exact head `8930575b88813094ae44cfa87b4ff8c3faf20d1f`.
- All 12 attached PR-triggered workflows succeeded, including targeted run `40785345238` and dedicated paid-estimate run `40785345159`.
- Scope: named native declarations are `PROVED_IN_LEAN_PR_GREEN_UNMERGED`; no strict exponent gain, anti-saturation theorem, or RH result is certified.

Green CI is evidence for declarations at these exact heads only. Neither PR is merged on main.

## G. Continuity and handoffs

No `2026-10-29` upstream report existed at intake or final pre-publication refresh. Record all upstream roles as `TODAY=PENDING`.

The complete relevant October 28 set was consumed as `YESTERDAY=CARRY_FORWARD`:

- Coordinator blob `162f82242e8eb84f4ed21c1e59342edf3400b6cd`, claim `20261028-coordinator-1`;
- Owner blob `af67eace39fb00261953a92de1f7067489be7546`, claim `20261028-owner-1`;
- Wheel blob `27dd840bb424d551f2dce0beebd7b0d2f66622f0`, claim `20261028-wheel-1`;
- Census blob `dca77bca7ed46d5d9fccbd05a565ed10c000a6c8`, claim `20261028-census-1`;
- Referee blob `fabec6a00f43ded6139256072d228024d62a015c`, claims `20261028-referee-1..2`;
- Lean blob `9698f817e44105033409f90d98b2e018cf727ac8`, claim `20261028-lean-1`.

The October 28 Analytic report was absent, so Analytic blob `0ab3dbac7df59b6fb4c1f35a29c010160cc42f3e`, claim `20261027-analytic-1`, is the explicit older carry-forward. `EXTERNAL_HANDOFFS.md` remains blob `038018145c0fddb2f6306c0712373adf9cd1ea52`, with no entry newer than 2026-10-18; its identities and no-gos do not pay the current principal or mixed source.

## H. Mechanism decisions and handoff

- **ACCEPT:** centered coprime CRT cancellation and the first-prime residual moment.
- **REVISE LANGUAGE:** call it a centered residual-subsector theorem, not an `8HQ` theorem for the actual uncentered physical row.
- **REJECT:** discarding the principal mean before global reassembly. Claim `20261029-referee-2` proves that omission can dominate the advertised scale.
- **RETAIN:** #1050's exact paid native reductions and source-faithful square-completion reserves.
- **REJECT AS NEW DAG INPUT:** scalar anti-saturation lower bounds stated only after the historical envelope and high-root normalization.

The next useful theorem must control the principal-centered mixed block jointly with shared-gcd and large-modulus columns. For a proposed extension, require an exact decomposition

```text
full Euler source = principal low-prime block
                  + centered low-prime block
                  + remaining source,
```

followed by all three squares and cross terms. Coprime complete-period cancellation alone cannot pay the two mixed terms or shared-factor covariance.

No source, proof branch, PR, issue, workflow, schedule, permission, or another role's report was modified. The only authorized write is this daily report.

**Independent structural progress:** YES.  
**Independent global quantitative progress:** NONE.  
**Canonical theorem:** OPEN.  
**RH:** OPEN.

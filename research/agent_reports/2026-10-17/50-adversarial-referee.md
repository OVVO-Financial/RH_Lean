# RH_Lean agent daily report - 2026-10-17 / RH | Adversarial Referee

**Status:** COMPLETED  
**Run ID:** 2026-10-17T03:34:01-04:00, scheduled invocation  
**Result classes:** `PAPER_PROOF` (two sharpened elementary bounds), `INDEPENDENT_REVIEW`, `FINITE_COMPUTATION`, scope correction, `NO_NEW_RESULT` on the canonical bound

## A. Executive verdict

The merged Hecke cutoff package is mathematically sound at its stated identity/sufficient-condition scope. I found no counterexample to the local Euler factors, large-square decomposition, seven-layer completeness, exact zero-BAD root cutoff, two-layer identity, prime-extension recurrence, or signed Abel variation bound.

Two constants can be improved by the same elementary proofs:

```text
20261017-referee-1:
|BAD_floor(X^(1/8))(X)|
  <= 3 X^(7/8) (1+log X),                    X>=256.

20261017-referee-2:
0 <= H_R^(large square)
  <= (51/8) R^(7/4)/log R,                   integer R>=2.
```

Thus the advertised constants `4` and `10` are accepted but nonsharp. These sharpenings do not control the unpaid signed Hecke core or the complete VF ledger.

The quotient-variation inlet is accepted as an independently meaningful **normed sufficient condition**. The phrase “strictly stronger” must be read at the representation level: `V)-control implies core control by Abel and triangle inequality. No strict asymptotic separation theorem has been proved for the one fixed genuine arithmetic bucket family, so I classify that wording `REVISE`, not a refutation of the sufficient route.

The rank-3 witness is accepted only at its literal scope: one unmasked occurrencewise difference of two separable products for the native AMP weight. It does not obstruct masked or multi-row Hecke sources, regrouping over factorizations, or the root-cutoff `P0-2P1` identity itself.

No uniform signed saving, Mertens exponent improvement, canonical VF estimate, or RH proof is established.

## B. Authority, continuity and live state

Fresh final authority was:

- `main@fef979286efa91b23bfced46f0a8a0143b000df0`, merge of PR #964 at 2026-10-17T04:32:01Z.
- `AGENTS.md` blob `6e07fe3c550cd371cdd2121768757839b1f9a3f4`.
- `CURRENT_PROOF_CONTRACT.md` blob `a71c0abbb43ec996ccc7ec8385dfde558e438c0c`.
- Hecke cutoff note blob `e32cdf37f62a79dd68806a1b3cb1d960234f3a47`.
- Square-shell note blob `8c881169efccd3eaf129af4321a1c4becb3833bf`.
- Compiled #919 coefficient source `research/VF_MID_919_OAI_PRINCIPAL_COEFFICIENT_MAP.lean`, blob `c06f8828962fabff89668a142a8b09809afcae01`.
- Compiled quotient return `research/VF_MID_919_QUOTIENT_SIGNED_RETURN.lean`, blob `c6f7d8fe126a1821744f916f449c4214898c84d3`.
- Rank witness `research/VF_MID_919_OAI_RECTANGLE_RANK_OBSTRUCTION.lean`, blob `067a90227fa6118f0e09c729cffd7b0da6ee500e`.
- Merged structural sources: `OddResidualCofactorSupport.lean` blob `356eefadaa7d798177da54017873021c4b8e0eae`; `RootWallCompleteFibre.lean` blob `054694c0aa125e6f542a3208d85d30c2d79fb320`.
- Canonical objective remains `VFCanonicalSquareVonKochStatement`, OPEN.

PR #964 is merged and no PR is open. Its body and several merged documents still say “draft/not live”; live PR metadata supersedes that stale prose. This is a documentation-state correction, not a mathematical inconsistency.

PR #919 is merged at `a9801975d32960841560d7cdda090f066e1a20fb`; all seven attached workflows on proof head `78edbb0df604c7b81b717cde1517f40c6d4efb7d` succeeded, including “VF principal coefficient map and signed sixth-power inlet,” the excluded-six kernel, Lean source audits and proof inventory. PR #961 is merged and all eleven attached workflows on `dd066a06d752f5ee76017c687799c8b440c71609` succeeded. PR #964's four attached workflows on `4706d2bae42edbc4962e457502f6b206c1de4aea` succeeded; they certify repository checks, not the new paper inequalities.

Continuity:

- Today Wheel is complete, blob `dbaefd4005c2cc93b894f9bb97c7a74c5f28dc49`.
- Today Census is complete despite its stale opening line “PARTIAL,” blob `9efa34cd7a2d3c021b20779889eaaf6a556020d3`.
- Today Coordinator/Owner/Analytic/Referee/Lean were absent at intake: `TODAY=PENDING`.
- The complete October 16 set is `YESTERDAY=CARRY_FORWARD`: Coordinator `fc5c5b46a0ec56f606444bb5dbfe400d4a444d18`, Owner `cb42efd7a6aa0e782c353803e604684b9500cdb2`, Analytic `2b93e7c237c09439746a93356c20cd15e4671028`, Wheel `134eb9eb0558a622b6f042baa20f3feb847ed6f4`, Census `26510606eea9f43450e5bb092c4542ab23fcb729`, Referee `e4c0a92301f032eb732a51f7bd997f4a19ac8b48`, Lean `180cf24f8444852a5b69bf2581f0c6d160f3a16e`.
- External inbox blob `008a2c7e2d8b0821a23c4580d0a5120813360c54` and handoff `EXT-20261017-HECKE-1..3`, blob `de13ba37bf86f32d64923ddf5ebf96382aa6d006`, were consumed. Their old “PR pending” metadata is superseded by the merge.

## C. Claim `20261017-referee-1` - sharpened Hecke BAD bound

Let `y=floor(X^(1/8))`, `X>=256`, and use the exact paper definition of `BAD_y`. The submitted proof correctly gives, for every integer `y>=2`,

```text
|BAD_y(X)| <= 2 X (1+log X)/y.                 (C1)
```

The factor 2 is exactly `|K|<=2`; the union bound permits repeated counting; `|a6(p^2u)|<=tau(u)`; `sum_(u<=Z)tau(u)<=Z(1+log Z)`; and `sum_(p>y)p^(-2)<=1/y`. No signed-core term is discarded.

Put `z=X^(1/8)>=2`. Since `y=floor z>=2`,

```text
z/y < (y+1)/y <= 3/2.
```

Substitution in (C1) gives

```text
|BAD_y(X)|
 <= 2(z/y) X^(7/8)(1+log X)
 <= 3 X^(7/8)(1+log X).
```

**Verdict:** `ACCEPT_WITH_SHARPENING / PAPER_PROOF`. Constant `4` remains valid. Constant `3` is the strongest consequence of the submitted floor comparison alone; no claim of optimal arithmetic constant is made.

Carrier audit: this is the #919 excluded-six norm coefficient paired with `K(floor(X/m))). It is not the original VF physical seat sector and does not bound `CORE_y).

## D. Claim `20261017-referee-2` - sharpened original VF large-square sector

The submitted proof of `10 R^(7/4)/log R` is correct on the literal odd, strict open-square physical carrier. It improves without changing an input.

For `R>=16`, the submitted counting gives

```text
H_R^(large square)
 < (6 R^(7/4) + 3R)/log R.
```

Since `R^(-3/4)<=1/8),

```text
6 + 3R^(-3/4) <= 6 + 3/8 = 51/8.
```

For integer `2<=R<16`, the submitted small-range estimate gives `H<R^2`. Moreover

```text
R^(1/4) log R < 2 log 16 < 51/8,
```

so again `H<(51/8)R^(7/4)/log R`.

The intermediate weight inequality `w_r<=3/log n` was checked at `r=2` and `r>=3); the odd-multiple count is an overcount, not an equality; and each physical seat is summed once even if several large prime squares divide it.

**Verdict:** `ACCEPT_WITH_SHARPENING / PAPER_PROOF`. The stronger constant is `51/8`. This is still only a positive squareful subpopulation; it supplies no estimate for lower-tag charges, semiprime charges, mixed covariance, returned-cell admission or the total VF defect.

## E. EXT-20261017-HECKE-2 - Euler factors, layers and root cutoff

Exact restatement reviewed:

```text
a6(p)=-2, a6(p^2)=1                 split p=1 mod 3,
a6(p)=0,  a6(p^2)=-1                inert p=2 mod 3,
a6(p^e)=0                            e>=3,
```

with `p=2,3` removed by the mask. After excluding `p^2` for `p>y`, each remaining large prime is split and occurs once, so its factor is `-2`. If `y=floor(X^alpha)`, then every integer prime `p>y` satisfies `p>X^alpha`; hence `k` such factors force `X>product p_i>X^(alpha k)`, so `k<1/alpha`. At `alpha=1/8`, depths are exactly `0..7`.

At `y=floor(sqrt X)`, `p>y` implies `p>sqrt X`, so `p^2>X` and `BAD=0`. A surviving norm has at most one such prime and uniquely factors as `s q`, giving exactly

```text
M(X)=P0(X;y)-2P1(X;y),  s<=floor(X/q)<sqrt X.
```

For split primes adjoined once, commuting integer-floor operators give

```text
C_q(t)=C_(q^-)(t)-2C_(q^-)(floor(t/q)).
```

If `X/2<q<=X`, then `floor(X/q)=1` and every earlier prime operator vanishes at argument one, leaving injection `-2`.

**Verdict:** `ACCEPT / IDENTITY_ONLY`. These are exact rearrangements on the genuine #919 coefficient carrier. The root cutoff deletes a tail and lowers large-prime depth, but it transfers all unresolved cancellation to `P0-2P1`; it is not a quantitative reduction by itself. The fixed `chi_-3=+1` on every surviving first-power split prime supplies support selection, not oscillatory phase.

The separate root-wall Lean theorems describe greatest-prime incidence, not equality with original VF weights, the #915 clipped returned source, or the #919 Hecke coefficient. All proposed bridges remain explicit obligations.

## F. EXT-20261017-HECKE-3 - signed quotient variation

The generic compiled Abel identity applies to the square-excluded coefficients `b_y` as well as to `a6`. With every quotient bucket retained, including buckets where `K(t)=0`,

```text
CORE_y(X)=sum_t F(t)(B(t)-B(t+1)),
|CORE_y(X)|<=4 sum_t |B(t)-B(t+1)|.
```

The endpoint is correct because `B(X+1)=0). At the root cutoff `b_y=a6` for every `m<=X`, so this is the native full #919 quotient variation.

**Verdict on implication:** `ACCEPT / PROVED_IN_LEAN` for the full-`a6` Abel inequality and `PAPER_PROOF` for applying the generic identity to the explicitly defined cutoff buckets. A uniform `V=O_epsilon(X^(7/8+epsilon))` is a genuine sufficient theorem and remains OPEN.

**Scope correction:** write “stronger normed sufficient condition,” not an established strict asymptotic strengthening on the fixed arithmetic carrier. For arbitrary bucket sequences the reverse implication is false: one can place alternating values on zero-`K` positions, making the paired core vanish while adjacent variation grows. That model proves the triangle-inequality loss is real in the ambient sequence space, but it is not an admissible arithmetic counterexample. No theorem currently shows that a 7/8 core bound fails to imply a 7/8 variation bound for the genuine `a6` buckets.

Mean-zero over a 36-period quotient, bounded `F`, and the finite values `V(10^7)=25547` do not prove a uniform exponent.

## G. Rank obstruction verdict

The exact Lean theorem uses the literal matrix

```text
[230456 230456 470696
 470696 470696 451061
 470696 451061 427856]
```

at `R=317`, with determinant `-2309174383131000`. Since every matrix `f_i g_j-u_i v_j` has rank at most two and zero determinant, no single centered separable rectangle matches these nine native AMP coefficients occurrence by occurrence.

**Verdict:** `ACCEPT / PROVED_IN_LEAN_ON_MAIN` for the displayed obstruction. **Unaffected approaches:** sums of rectangles, coupled masks, regrouping over factorizations, changing the coefficient carrier with an exact bridge, and admissible multi-row Hecke moments. The witness is not a no-go theorem for the root-cutoff Hecke representation and says nothing quantitative about `V).

## H. Independent computation

I used a fresh literal Dirichlet-convolution implementation, not the merged local-Euler recurrence, to construct

```text
a6(n)=1_(gcd(n,6)=1) sum_(d|n) mu(d) chi_-3(n/d) mu(n/d)
```

through `n=200000`. It agreed coefficient-by-coefficient with the split/inert local table. On 1,001 boundary-stressed values (every `12<=X<=1000` plus neighborhoods of powers/squares and values through `200000`):

- root-cutoff `BAD=0`;
- `CORE=M(X)`;
- only depths 0 and 1 occurred;
- all quotient buckets, including zero-`K` buckets, were retained in `V`.

Examples `(P0,P1 contribution; M; V)`:

```text
X=256:    (-3,+2; -1; 31)
X=4096:   (-59,+40; -19; 201)
X=10000:  (-123,+100; -23; 358)
X=100000: (-888,+840; -48; 1525)
X=200000: (-1577,+1576; -1; 3140).
```

For eighth-root cutoffs on the same stress set, the largest observed ratio
`|BAD|/[4X^(7/8)(1+log X)]` was about `0.00076912` at `X=490`; this is diagnostic only. An independent exact-seat enumeration for `2<=R<448` found maximum `H log R/R^(7/4)` about `0.3902602` at `R=14`; logarithms affect this diagnostic only, not Claim referee-2.

Today's Census independently reproduced the full `X=10^7` values and added held-out controls. I therefore did not duplicate its large scan.

## I. No-circularity and strategy decision

- Bounding the recombined root core `|P0-2P1|` at 7/8 is the desired Mertens estimate in new coordinates: `TARGET_EQUIVALENT / REFORMULATION`.
- Bounding complete quotient variation at 7/8 is independently stronger at the Abel-norm level and sufficient, but OPEN.
- The square-shell `H^(5/2+epsilon)` second moment is a different stronger sufficient input. Its full covariance contains every diagonal and off-diagonal shell pair; it is not the original #915 returned-source statistic.
- The top-half split-prime cohort has coherent mass of order `X/log X`; local insertion or termwise absolute values cannot pay it at 7/8. Any credible proof must retain nonlocal earlier-prime/`P0` response before norming.
- The rank witness blocks one source shape only.
- Hecke BAD and the VF physical large-square sector are distinct carriers and may not be combined as though they were one paid tail.

**Decision:** `CONTINUE / REVISE` the root-cutoff and quotient-variation lanes. The smallest useful new theorem is a uniform arithmetic restriction on adjacent genuine signed quotient buckets or a nonlocal prime/cofactor moment after extracting the coherent upper-half mode. Reject any claim that fewer layers, kernel mean zero, or finite small variation is itself a saving.

## J. Resume capsule

Reusable new claims:

- `20261017-referee-1`: constant `3` eighth-root Hecke BAD bound.
- `20261017-referee-2`: constant `51/8` original VF large-square bound.
- `20261017-referee-3`: quotient variation is accepted as a stronger normed sufficient inlet; “strictly stronger on the genuine sequence” is unproved.
- `20261017-referee-4`: rank witness accepted only for one unmasked centered rectangle.

Next adversarial test: require any proposed `V) or multi-row theorem to state its complete bucket/source definition, conductor/profile uniformity, top-half principal-mode extraction, zero-`K` bucket retention and exact consumer. Search first for a lower-bound family or a source-admissibility failure before attempting a large computation.

No RH proof claim.

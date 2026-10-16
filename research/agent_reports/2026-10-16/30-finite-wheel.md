# RH_Lean agent daily report - 2026-10-16 / RH | Finite Wheel & Incidence

**Status:** COMPLETED  
**Run ID:** 2026-10-16T00:09:01-04:00, scheduled invocation  
**Completed:** 2026-10-16T00:14:00-04:00  
**Result classes:** `PAPER_PROOF`, exact structural restriction, decisive mechanism falsification, `NO_NEW_RESULT` on the canonical bound

## A. Most important mathematical development

The positive raw residual `H_R` is confined to a sharply separated greatest-prime sector.

### Claim `20261016-wheel-1` - exact composite-cofactor representation

Fix `R >= 3`. For every physical occurrence `n` contributing to `H_R`, let `q=P+(n)` be its greatest prime factor and put `a=n/q`. Then:

```text
n = a*q,
a is odd and composite,
a >= 9,
q = P+(n),
n < R^2.
```

Conversely, every odd nonsquare `n=a*q<R^2` with `a` composite, `q` prime, and `q=P+(n)` is an `H_R` occurrence. Thus the map `n |-> (a,q)` is an exact bijective incidence representation of the squareful/depth-at-least-three residual. It preserves one physical occurrence and its native coefficient `w_floor(sqrt n)`; it neither duplicates a prime tag nor changes a weight.

**Status:** `PAPER_PROOF`.

### Claim `20261016-wheel-2` - sharp one-ninth greatest-tag support

Every `H_R` occurrence satisfies

```text
q < R^2 / 9.
```

Equivalently, `H_R` has zero incidence on greatest-prime tags `q >= R^2/9`. The constant 9 is asymptotically sharp: for every prime `q>3`, `n=9q` is a nonsquare squareful/higher-factor occurrence, and with `R=floor(sqrt(9q))+1) it lies in the strict last block while `q/R^2 -> 1/9` along growing primes.

**Status:** `PAPER_PROOF`.

### Claim `20261016-wheel-3` - forced cross-tag compensation and transport no-go

The Coordinator's macro tail

```text
A_R = sum_(prime q, R^2/3 < q < R^2) G_R(q)
```

and the entire positive residual `H_R` have disjoint greatest-prime tag support, separated by a factor of three:

```text
support(A_R) subset {q > R^2/3},
support(H_R) subset {q < R^2/9}.
```

Therefore any occurrence pairing, flow, or depth transport required to pair the macro negative tail with positive `H_R` mass is necessarily cross-tag. A transport that preserves the greatest-prime tag has zero `A_R`-to-`H_R` edges and cannot explain the proved PNT-scale compensation.

This is an independently proved mechanism obstruction, not a bound on
`A_R+B_R=L_R`. The complete square remains

```text
L_R^2 = T_R^2 + H_R^2 + 2*T_R*H_R.
```

No cross term is deleted, and no raw claim is transferred to the masked/clipped returned-cell carrier or the compressed #915 norm.

**Status:** `PAPER_PROOF`; `REJECT` greatest-tag-preserving transport as a complete coupling mechanism.

## B. Proof

The raw carrier is

```text
C_R = {(r,n): 2<=r<R, r^2<n<(r+1)^2, n odd}.
```

Hence every represented integer is odd, is strictly below `R^2`, and is not a perfect square. An `H_R` occurrence is composite but is not a distinct semiprime `p*q` with primes `p<q`.

Let `q=P+(n)` and `a=n/q`. Unique factorization makes this representation unique. Since `n` is odd, `a` is odd.

- `a=1` would make `n=q` prime.
- If `a` were prime, then `a<=q`. If `a<q), `n=a*q` would be a distinct semiprime and belong to the tag ledger `T_R`, not `H_R`. If `a=q`, then `n=q^2`, a perfect square excluded by the strict block endpoints.
- Therefore `a` is an odd composite, so `a>=9`.

It follows that `9q<=aq=n<R^2`, proving `q<R^2/9`. The converse follows directly from the accepted exact raw partition: a composite nonsquare with composite cofactor after removal of its greatest prime is neither a prime nor a distinct semiprime, so it belongs to the residual.

The sharp family `n=9q` also shows why the strict-square convention matters. If perfect squares were silently added, the prime-cofactor case `n=q^2` would invalidate the proof; those integers are not in `C_R`.

## C. Assigned inverse-observable outcome

The assigned campaign was `RENORMALIZED-INVERSE-OBSERVABLE-1`. The most natural candidate - concentration of positive higher-depth mass on the same high greatest-prime tags as the macro negative tail - is decisively falsified: that incidence count is identically zero.

The surviving non-tautological configuration is:

```text
positive H_R compensation must be carried by composite cofactors a>=9
on tags q<R^2/9, while A_R uses q>R^2/3.
```

This differs from the endpoint sum and is independently forced by FTA and strict square geometry. It narrows any future inverse theorem to a genuine cross-tag/cofactor transport. It does not independently limit the size of that transport. Naming the remaining cross-tag mismatch as small would be target-equivalent and is not done here.

The result is compatible with Owner Claim `20261015-owner-transport-1`: the boundary descendants `3q` are distinct semiprimes and therefore remain in `T_R`; they are not `H_R` mass. The next useful transport must connect those tagged packets to composite-cofactor classes without losing their literal coefficients.

## D. Falsification and finite regression

An independent exact-integer enumerator checked every `H_R` occurrence for roots `3<=R<=200`:

```text
H occurrences checked: 517,602
violations of odd-composite cofactor or 9q<R^2: 0
largest observed 9q/R^2:
  0.9997932419659735 at (R,n,q,a)=(184,33849,3761,9)
```

This computation is `FINITE_COMPUTATION` supporting the proof, not its basis. The near-boundary `a=9` witness stress-tests strict versus nonstrict inequalities and demonstrates sharpness. Small roots and square cases were included; no exception is hidden at `R<9`.

Repository novelty searches for the one-ninth support law, composite greatest-prime cofactor representation, and `H_R` support found no equivalent theorem. Existing high-prime/cofactor modules concern different Mobius or first-bad carriers. The accepted raw partition and tail monotonicity are dependencies/context, not this support theorem.

## E. Authority, continuity, and source verification

- Final live `main`: `68bc4aaae65c9f505202a22df446c0fb40e4d040`, merge of PR #957.
- `AGENTS.md` blob: `cbc234051834f971929d82972ba6a157b2129d32`.
- `CURRENT_PROOF_CONTRACT.md` blob: `dc73babe5eb7b8f9fb83272a27cd2468dbdcb7f2`.
- Factor-depth brief blob: `1a5f94bb81aa7d50b7c118f823a14c9ec644f947`.
- Dynamic protocol blob: `61f7e4dd90200c2f3426fce1e96f9779f40238dc`.
- Canonical definition blob: `b504704070b193cea835713d697ba0d980704c7a`.
- Canonical theorem blob: `43e160ac7ad51f7646771297f43a9b95395ce709`.
- Original signed-seat source blob: `13dda0d2c6cc59580959a2d59fad60126b1c6b0b`. It formally defines the physical charge `w_R-1_Prime(n)`, proves its block sum, and supplies the FTA least-owner decomposition. The raw greatest-tag partition remains paper-level, as the live contract states.
- All 2026-10-16 upstream stage paths were absent at initial and final refresh: `TODAY=PENDING`.
- 2026-10-15 reports consumed: Coordinator `0f9e254738e1bc3d01cfd0a3b114d99b7478b08a`; Owner `01fb928be14c1004b3124fb25101f369ad7e8611`; Analytic `fda92df0cd94cb997f213eddf4e6a5427b6dd03f`; Wheel `6d451c35eef4021fcff78253bed609d193c249c1`; Census `2e3c1cf95cd11669d57d2ce1f7216916736ff095`; Referee `cf0db85f6b04c56527bc9a26a1b6741ae196435a`; Lean `a11eddb6f78c927b8ec838426f94d72e63cda123`. These are `YESTERDAY=CARRY_FORWARD`.
- External inbox blob `c1d1aad9872d1760d2e4e34b30bbc0ed4fa3d33c` consumed. `EXT-20261014-1..5` and `CL-20261014-1..11` retain their recorded scopes; none supplies or contradicts the one-ninth raw support theorem.
- Live PR search returned no open pull requests. PR #957 is merged. No branch, Lean source, issue, PR, or central policy was changed by this scheduled specialist.

The authoritative theorem remains `VFCanonicalSquareVonKochStatement`. The compiled definition confirms the canonical defect and its unaltered actual-prime recurrence. Claims 1-3 do not prove a new endpoint estimate, source payment, finite A/C, CORR-4, or RH.

## F. Mechanism decisions and handoff

- **Greatest-tag-preserving FD transport:** `REJECT` as an explanation of macro `A_R` versus `H_R` compensation. The required incidence graph has no edges.
- **Cross-tag composite-cofactor transport:** `CONTINUE / REVISE`. The exact pair carrier `(a,q)` with `a>=9` is the next structurally faithful representation.
- **Unsigned wheel enlargement / fixed-capacity allocation:** remains `REJECT` as a complete route.
- **Inverse configuration:** `CONTINUE` only if it bounds a specified cross-tag/cofactor observable independently; the endpoint mismatch itself is not such an observable.

Handoffs:

- **Owner:** refine `N_R` in Claim `20261015-owner-transport-1` by the exact composite-cofactor classes; preserve `3q` in `T_R` and all weight-change/boundary terms.
- **Census:** no larger undirected scan is requested. If needed, directly classify the `a=9,15,21,...` cofactor layers and test a predeclared cross-tag transport law.
- **Referee:** audit Claims `20261016-wheel-1..3`, especially the converse, the exclusion of `q^2` by strict endpoints, and the distinction between raw and returned-cell carriers.
- **Lean Verification:** after Referee acceptance, the composite-cofactor bijection and `9q<R^2` support lemma are small exact formalization candidates. No closure PR is requested.

## G. Resume capsule

- Reuse Claims `20261016-wheel-1..3`: exact composite-cofactor representation, sharp one-ninth support, and forced cross-tag compensation.
- Reuse the exact regression above; do not rerun it without a changed definition or new hypothesis.
- First missing structural lemma: an exact native-weight transition from the owner-3/other distinct-semiprime packets into specified composite-cofactor classes, with a separately proved restriction on its residual.
- First quantitative blocker: no independent bound on the resulting cross-tag transport or on `T_R+H_R`.
- Avoid greatest-tag-preserving matching, cloned historical tags, added perfect squares, raw-to-returned source transfer, separate absolute sector estimates, and omission of `2*T_R*H_R`.
- No RH proof claim.

## H. Publication verification

Early checkpoint commit: `d0ac594430f4c61d95765990cea4e36ea2e16966`; verified checkpoint blob `84facd494d32853f89a8e52762ea46139fce5d72`.

The completion commit and final readback blob are recorded by the transport/readback operation outside this self-hashing body.


---

# Manual continuation — unified manual AI research cycle, pass 4 of 7 (2026-10-16)

**Status of this section:** COMPLETED
**Invocation:** explicitly owner-requested manual run, performed by one AI session (Claude) executing the seven functions sequentially. This section is **appended**; the scheduled 00:09 run above is preserved unchanged and remains that run's record.
**Run ID:** `RH-UNIFIED-MANUAL-20261016T0806-0400` · section written 2026-10-16T09:07-04:00
**Authority:** `main@69e44d7cc8a63ebc1160639c264cbda4210339e1` (after #958/#959 merged; #960 merged on `agent-reports`). `AGENTS.md` `c40e9bc1…`, contract `b945dec4…`, brief `80b865bf…`, protocol `03d07880…`. Upstream this cycle: Owner `20261016-owner-1..6`, Analytic `20261016-analytic-1..4`.
**Result classes:** `PAPER_PROOF` (incidence walls, inverse theorem), `FINITE_COMPUTATION` (strata), `NO_NEW_RESULT` on the canonical bound.

## M-A. What changed

The greatest-prime incidence geometry of the raw carrier now has **two exact walls**: the merged one-ninth wall (`H_R` tags `q < R^2/9`) and the **square-root wall** `q = R`, above which every fibre is complete (owner-1; Lean core on draft PR #961). The scheduled run's inverse campaign falsified same-tag concentration; this pass supplies a non-circular inverse theorem whose configuration is independently restricted — and shows its restriction has exactly classical strength.

## M-B. Claim `20261016-wheel-4` — fibre staircase and the square-root wall

For `x = R^2`, `R >= 5`, prime `q`:

```text
x/(2k+1) < q < x/(2k-1),  q >= R  ==>  fibre(q) = {q, 3q, ..., (2k-1)q}       (k >= 1)
H-part of fibre(q) nonempty            <=>  some odd composite a < x/q  <=>  q < x/9
q >= R                                 ==>  no smoothness or square condition is active
5 <= q <= R/sqrt(2)                    ==>  the smoothness condition P+(a) <= q is active
```

**Proof.** First three lines: owner-1 (complete fibre: all odd `a < x/q`), and the least odd composite is `9`. Last line: Bertrand gives a prime `p in (q, 2q)`; `2q <= x/q` iff `q <= R/sqrt 2`, so `a = p < x/q` is an odd cofactor with `P+(a) > q`, excluded from the fibre of `q`. Between `R/sqrt 2` and `R` activity depends on whether `(q, x/q)` contains a prime and is not claimed. **Status:** `PAPER_PROOF`; incidence core (`largestPrimeFactor_eq_iff_exists_mul_of_root_le`, `isOddFactorDepthResidual_mul_iff_of_lt`, `nine_mul_le_of_odd_composite_cofactor`) compiled on PR #961 at head `dd066a06…`.

**Consequence.** The `A_R` sector (`q > x/3`) is the `k = 1` step of the staircase; the one-ninth wall is the `k = 5` step where the first composite cofactor `9` enters. Between `R` and `x/9` the `H` part of each fibre is the set of odd composites below `x/q` — a cofactor range that grows to `R` as `q` approaches the wall, consistent with census-2 (no fixed backbone).

## M-C. Claim `20261016-wheel-5` — inverse configuration with an independent restriction

**(i) Imbalance ⇒ configuration (two-sided, explicit).** For the band `[R, 2R)`, owner-3 gives

```text
| (T_R - M_R) - F_R (E(2R-1) - E(R-1)) |  <=  sum_{R<=q<2R} max(|lo(q)|, |lo(q) + wtilde(q)|)  =  O(R/log^2 R).
```

So a band imbalance `V` forces the Mertens increment `|E(2R-1) - E(R-1)| >= (V - O(R/log^2 R))/F_R`, and conversely. The configuration is a prime statistic at scale `R`, defined independently of `L_R` (scale `R^2`), so the template is **not circular**.

**(ii) Independent restriction of the configuration.** Unconditionally (PNT with classical error term) `E(y) = O(exp(-c sqrt(log y)))`, hence

```text
|T_R - M_R| = O(R^2 exp(-c sqrt(log R)))         (explicit uniform estimate for a growing-cofactor cross band of complete B)
```

— weaker than the target by `R exp(-c sqrt(log R))/log R`. Under RH it is `O(R^(3/2))`; by Lemma M it is not `O(R^(3/2 - delta))`.

**Status:** `PAPER_PROOF`. **Decision:** INV-CONFIGURATION is *realised* here, but the restriction it produces is exactly our knowledge of primes at scale `sqrt(x)`; it cannot reach the target scale on any intermediate band (analytic-4). Merge INV-CONFIGURATION into the cut-mode picture; do not run it as an independent lane to the endpoint.

## M-D. Finite strata (`FINITE_COMPUTATION`, directly recomputed per seat, matching the Fenwick totals)

At held-out `R = 4999` (`x = 24,990,001`): `S1 (q<R) = 463,865.15`, `S2 ([R,2R)) = 121,694.82`, `S3 ([2R, x/3]) = 298,366.96`, `S4 = A_R = -883,575.00`. Inside `S2`, 81.2% of the mass sits at cofactor exponent `log a/log x in [3/8, 1/2)`; `Omega = 2, 3, 4, >=5` carry `34,614 / 49,056 / 26,564 / 11,895`. The complete complement `B_R = S1 + S2 + S3` puts 52.5% of its mass below the wall (`S1`), where fibres are smooth-restricted.

## M-E. Handoffs and capsule

- **Census:** test the band law and the cut mode with pre-registered criteria (done in pass 5).
- **Referee:** audit wheel-4's Bertrand step and wheel-5's two-sided bound.
- **Lean:** wheel-4's incidence core is on PR #961; the analytic parts are out of scope.
- **Capsule:** reuse wheel-4/5; avoid intermediate-cut band estimates, same-tag transport, fixed backbones, unsigned wheel growth. No RH proof claim.

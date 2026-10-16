# RH_Lean agent daily report - 2026-10-16 / RH | Adversarial Referee

**Status:** COMPLETED  
**Run ID:** 2026-10-16T03:34:01-04:00, scheduled invocation  
**Result classes:** `PAPER_PROOF`, independent asymptotic refinement, exact finite reproduction, scope correction, `NO_NEW_RESULT` on the canonical bound

## A. Executive verdict

The new raw cofactor geometry is sound. I prove the stronger refinement

```text
H_R(a) ~ 2 R^2 / (a log^2(R^2))
```

for every fixed odd composite cofactor `a>=9`. Thus every fixed finite cofactor family is smaller by a full logarithm than the macro `R^2/log R` mode. Any complete factor-depth transport must change greatest-prime tag and use cofactors growing with `R`.

Scope correction: the proved PNT-scale compensation is between the upper tag sector `A_R` and the **entire complement** `B_R`, not specifically between `A_R` and `H_R`. The one-ninth theorem only proves that a direct `A_R`-to-`H_R` occurrence transport is cross-tag.

The merged Nyman coefficient extractor and rigidity inequalities are correct at paper level. I independently reproduced the exact N=96 certificate below `1/92`. They remain on a distinct positive Hilbert carrier and supply no all-scale decay.

## B. Authority and continuity

- Final `main`: `68bc4aaae65c9f505202a22df446c0fb40e4d040`; target remains `VFCanonicalSquareVonKochStatement`.
- Authority blobs: `AGENTS.md` `cbc234051834f971929d82972ba6a157b2129d32`; contract `dc73babe5eb7b8f9fb83272a27cd2468dbdcb7f2`; brief `1a5f94bb81aa7d50b7c118f823a14c9ec644f947`; protocol `61f7e4dd90200c2f3426fce1e96f9779f40238dc`; amplification budget `3beff1f789646d59237744379ff8e578bb1042a0`.
- Canonical source blobs: `b504704070b193cea835713d697ba0d980704c7a`, `43e160ac7ad51f7646771297f43a9b95395ce709`. Signed-seat source: `13dda0d2c6cc59580959a2d59fad60126b1c6b0b`.
- Nyman note: `b2775c892edffe920a101651eef6f3581c73c9d4`; N=96 code/coefficients: `e25e5dc6e230ddcaf1b112176c0be3cb40508b48`, `bbd6341a91bafd4699a278d37410f01df581c458`.
- Today Wheel `9af028f5ce10cf9a06280d47ae6b0795c5974b8b` and Census `7e7033b2f5c7c780efb6e9ff4ce347b8a879296f` were consumed. Coordinator, Owner, Analytic and Lean remained `TODAY=PENDING`.
- Yesterday Coordinator `0f9e254738e1bc3d01cfd0a3b114d99b7478b08a`, Owner `01fb928be14c1004b3124fb25101f369ad7e8611`, Analytic `fda92df0cd94cb997f213eddf4e6a5427b6dd03f`, Wheel `6d451c35eef4021fcff78253bed609d193c249c1`, Census `2e3c1cf95cd11669d57d2ce1f7216916736ff095`, Referee `cf0db85f6b04c56527bc9a26a1b6741ae196435a`, and Lean `a11eddb6f78c927b8ec838426f94d72e63cda123` are `YESTERDAY=CARRY_FORWARD`.
- External inbox `c1d1aad9872d1760d2e4e34b30bbc0ed4fa3d33c` was read; its qualified claim scopes are unchanged.

## C. Wheel verdicts

**`20261016-wheel-1`: ACCEPT / PAPER_PROOF.** For `n in H_R`, `q=P+(n)`, `a=n/q). If `a=1`, `n` is prime. If `a` is prime, `a<q` gives a distinct semiprime and `a=q` gives the excluded square `q^2`. Hence `a` is odd composite and `a>=9`. Conversely, an odd nonsquare `aq<R^2` with composite `a` and `q=P+(aq)` lies in `H_R`. Equivalently `q>=P+(a)`, excluding the finite square case `a=q b^2`.

**`20261016-wheel-2`: ACCEPT / PAPER_PROOF.** From `a>=9`, every `H_R` tag has `q<R^2/9`. The family `n=9q`, `R=floor(sqrt(9q))+1`, proves asymptotic sharpness.

**`20261016-wheel-3`: ACCEPT WITH SCOPE CORRECTION.** `A_R` uses `q>R^2/3`, while `H_R` uses `q<R^2/9`; any direct edge changes tag. But the accepted macro theorem is `A_R+B_R=o(R^2/log R)`, with `B_R=L_R-A_R` containing lower tag terms and `H_R`. There is no `A_R+H_R` cancellation theorem. Preserve `L_R^2=T_R^2+H_R^2+2T_RH_R`.

## D. Census verdicts and new theorem

**`20261016-census-1`: ACCEPT / PAPER_PROOF.** If `k=Omega(n)`, the `k-1` prime factors of `a` are at most `q), so

`a^k <= (aq)^(k-1)=n^(k-1)<R^(2(k-1))`.

Thus `a^(j+1)>=R^(2j)` forces `Omega(n)>=j+2`. The reported odd/even prime-power families make the exponent sharp.

**`20261016-census-2`: ACCEPT.** Odd nonsquare multiples of 9 in `[R^2/2,R^2)` give `H_R >> R^2/log R`. For fixed `a`, Chebyshev and the native weight give `H_R(a)=O_a(R^2/log^2 R+R)`, hence every fixed finite backbone has vanishing relative mass.

**`20261016-referee-1`: PAPER_PROOF.** Put `X=R^2`. For fixed odd composite `a`, apart from finitely many initial/square cases, the exact layer is primes `q<X/a`, `q>=P+(a)`. Uniformly,

```text
w_floor(sqrt(aq)) = 2/log(aq) + O_a(q^(-1/2)/log q).
```

PNT plus partial summation gives

```text
H_R(a) ~ 2X/(a log^2 X);
H_R(A) ~ [2 sum_(a in A)1/a] X/log^2 X
```

for fixed finite `A`. This is an explicit logarithmic deficiency, not a signed cancellation theorem or a bound for growing cofactor unions.

The unchanged large finite tables were not rerun; no theorem above depends on their floating totals.

## E. Coordinator tail audit

Claims `20261015-coordinator-1/-2` are ACCEPTED at `PAPER_PROOF` scope. For `R^2/3<q<R^2`, no odd prime descendant fits, so `G_R(q)=-(1-w_floor(sqrt q))`. Fixed-ratio PNT yields

`A_R=-(1/3+o(1))R^2/log R`.

The compiled all-real VF-Li `O(1)` bridge plus PNT gives `L_R=o(R^2/log R)`, hence the opposite main term for `B_R`. Therefore `|A_R|+|B_R|` is supertarget: separate absolute sectorization is rejected, while signed cross-sector analysis remains open.

## F. Nyman rigidity audit

**`20261015-analytic-1/-2`: ACCEPT / PAPER_PROOF.** Since

`a_k(d)-a_k(d-1)=1/k-1_(k|d)`,

Möbius inversion gives `Lambda_q(a_k)=-1_(k=q)`. For `r=t-F),

```text
Lambda_q(r)=mu(q)+c_q,
lambda_q(m)=1_(m|q)mu(q/m)-1_(m+1|q)mu(q/(m+1)).
```

Weighted Cauchy-Schwarz gives the exact dual bound. At `alpha=1/2`, `C_q<=4 sigma_2(q)<=(2pi^2/3)q^2`. For `q=6`, the coefficients `2,-1,-1,1` at `m=1,3,5,6` give `C_6=92`.

I independently verified the extractor for all `2<=q<=200`, `2<=k<=250`, and the `C_q` bound. Small error forces each fixed squarefree coefficient to `-mu(q)` and each fixed squareful coefficient to zero. This is pointwise necessity, not squarefree-only density.

**`20261015-analytic-3`: ACCEPT / PAPER_PROOF.** If `q<=sqrt(6)/(4pi D)`, every squarefree `q` is present with `|c_q|>=1/2`. The finite forced-support inequality is exact; its order-`1/D` reading uses squarefree counting. Bertrand gives the stated weak `d_N^2>=3/(8pi^2N^2)` consequence.

No claim proves Hilbert decay, a Mertens gain, a VF bridge, or RH.

## G. Exact certificate and CI

PR #957 is merged: head `a5fc4e8acc8198af57fb6206d90553194ae4c013`, merge `68bc4aaae65c9f505202a22df446c0fb40e4d040`. My independent rebuild reproduced:

```text
partial=2933093216945
tail=71511969227
total=3004605186172
l1=27900192
92*total<SCALE: PASS
```

Verdict: `ACCEPT / FINITE_COMPUTATION`. It strictly separates the full N=96 witness from every omission-of-6 model; it does not prove convergence.

Exact-head workflows:

- Documentation `38827065583`, job `116736868964`: successful.
- Proof inventory `38827065612`, job `116737220349`: successful.

The combined legacy status endpoint is empty; no PR-triggered run is attached to the merge commit. These workflows did not compile a new Lean theorem or kernel-certify the C++ result. No open PRs existed at final refresh.

## H. Decisions and next step

- Greatest-tag-preserving direct `A_R`-to-`H_R` transport: **REJECT**.
- Fixed finite cofactor backbone: **REJECT**.
- Growing-cofactor cross-tag transport: **CONTINUE / REVISE**; necessary shape, no quantitative signed theorem.
- Cofactor-depth staircase: **CONTINUE** as an inverse classifier.
- Separate absolute macro sectors: **REJECT**.
- Nyman full positive basis: **CONTINUE** as a distinct alternative; rigidity is necessary, decay remains open.
- Prime-only or any basis omitting a fixed squarefree modulus: **REJECT** for convergence.
- Canonical endpoint, complete-source covariance, finite A/C, CORR-4, MU-LIFT gain and RH: **OPEN / NO_NEW_RESULT**.

Smallest decisive factor-depth step: obtain a uniform theorem for dyadic cofactor bands `A<=a<2A` with growing `A=A(X)`, then identify and retain the actual negative partner before taking norms. A positive histogram cannot prove cancellation.

Smallest decisive Nyman step: test whether the forced truncated profile `c_q=-mu(q)` has an independently provable uniform Hilbert upper bound after all residue correlations are restored.

## I. Resume capsule

Reuse `wheel-1/-2`, `census-1`, new `20261016-referee-1`, the `A_R+B_R` scope correction, `analytic-1..3`, and the reproduced N=96 separation. PR #957 has documentation/inventory CI only and no new Lean theorem.

Do not treat `H_R` as the proved sole compensator, omit lower tags or `2T_RH_R`, transfer raw results to returned cells, infer squarefree-only density, or upgrade finite Hilbert separation to decay.

No RH proof claim.


---

# Manual continuation — unified manual AI research cycle, pass 6 of 7 (2026-10-16)

**Status of this section:** COMPLETED
**Nature of review:** this is a **self-audit** by the same AI session that produced passes 2–5. It is not independent review by another agent and does not replace the scheduled Referee run above, which is preserved unchanged.
**Run ID:** `RH-UNIFIED-MANUAL-20261016T0806-0400` · section written 2026-10-16T09:07-04:00
**Authority:** `main@69e44d7c…`; `AGENTS.md` `c40e9bc1…`, contract `b945dec4…`, brief `80b865bf…`, protocol `03d07880…`, amplification budget `3beff1f7…`.

## R-A. Verdict summary

| Claim | Verdict | Strongest correct version / note |
| --- | --- | --- |
| owner-1 complete fibre | **ACCEPT / PAPER_PROOF** | Needs `R >= 5` (at `R = 3`, `q = 3` gives the non-seat `3`). Lean core green on PR #961. |
| owner-2 sampling bracket | **ACCEPT** | Monotone comparison is valid because `wtilde` is nonincreasing on `[4, x)` and extended by `0` beyond `x`; when `q = R` is prime, `x/q = R` is an integer and the last sample is `(R-2)q`, still covered. |
| owner-3 band identity | **ACCEPT** | Exact; bracket tested with 0 violations. |
| owner-4 / Lemma M | **ACCEPT / PAPER_PROOF** | Audit points below. Scope: "band-local" means against a prime-free main term within `O(R^(3/2-delta))` of `M_R`; cross-band relations are not excluded. |
| owner-5 cut identity | **ACCEPT** | Exact bookkeeping to `2e-9`. |
| owner-5 B ⇔ RH | **ACCEPT / PAPER_PROOF** | Bootstrap checked below. |
| owner-6 wall decomposition | **ACCEPT WITH SCOPE** | Exact identity; telescoping only for `y_m <= x^(2/3-delta)`; the `eta`-sum over `[R, x)` is `O(x/log^2 x)` and not claimed small. |
| analytic-1 anatomy | **ACCEPT / IDENTITY_ONLY** | Verified exactly at 15 `(N, X)` pairs. |
| analytic-2 controls | **ACCEPT** | `|Psi_a| <= (1/2)(sum|a|)^2` since `|psi| <= 1/2`. |
| analytic-3 calibration | **ACCEPT** | Recurrence handles `r < 1` via the `max`; conclusion is conditional, not a gain. |
| analytic-4 spectrum | **ACCEPT WITH RANGE** | `1/2 <= theta < 2/3`; the sparse set `y = R^(2 theta)` is dense enough for Lemma M because consecutive values move `E` by `O(y^(-1/(2theta)))`, `o(y^(-1/2-delta))` for `delta < 1/4`. |
| wheel-4 staircase / wall | **ACCEPT** | Bertrand step correct; activity on `(R/sqrt 2, R)` deliberately unclaimed. |
| wheel-5 inverse theorem | **ACCEPT** | Non-circular (scale `R` statistic vs scale `R^2` endpoint); its restriction is classical-strength only. |
| census N-C/N-D | **ACCEPT / FINITE_COMPUTATION** | Pre-registration written after generation but before inspection — disclosed; development range `R <= 600` disclosed. |

No claim is promoted to an endpoint bound, and none is target-equivalent in disguise: owner-5's equivalence is proved in both directions and is presented as an obstruction.

## R-B. Audit of Lemma M (Mertens-increment oscillation)

1. *Domain.* `E(y) = O(1/log y)` (Mertens) makes `Ehat(s)` holomorphic on `Re s > 0`. ✔
2. *Continuation.* Under the contrary hypothesis, `D(s)` converges absolutely on `Re s > -1/2 - delta`; `D = (2^s - 1) Ehat - 2^s J`, `J` entire (substitution `u = 2y`, checked). Poles only at `2^s = 1`, i.e. `Re s = 0`. ✔
3. *Link to primes.* `P(s+1) = s int_2^inf S(y) y^(-s-1) dy` with `S = log log + M + E`; the `log log` part gives `-log s + entire` (exponential integral). Sign checked: `s Ehat = P(s+1) + log s + entire`. ✔
4. *Holomorphy of `P_2` at the boundary point.* `2 rho_0` has real part exactly `1`; `zeta` is finite and nonzero at `1 + 28.27i` (no zero on `Re = 1`, no pole off `1`), so `log zeta(2w)` is holomorphic near `rho_0`; `k >= 3` terms are uniformly small. ✔
5. *Path.* From `s = 1` to `s_0 = -1/2 + 14.13i` in the upper half-plane, crossing `Re s = 0` at a non-pole and avoiding `s = 0` (so `log s` and `log zeta(s+1)` follow the principal continuation). ✔
6. *Contradiction.* The continued branch of `log zeta` is holomorphic on a disk around `rho_0`, so `zeta(rho_0) != 0` — false. Only the classical, rigorously verified zero `rho_0` is used; no RH. ✔
7. *Integer sampling.* `E` changes by `O(1/R)` on `[R, R+1]`. ✔

**Falsification attempt.** Could a cleverer main term absorb the band mode? Its non-oscillating part (the positive bias of `E` from prime squares, visible as 80–88% negative `Pred` in census N-D) is explicit and absorbable; the lower bound, however, comes from the singularity at `rho_0`, i.e. from oscillation that no prime-free function can track. Survives.

## R-C. Audit of the B ⇔ RH bootstrap (owner-5)

From the identity, `(1 - w) epsilon(y) = -(B - B*) - wtilde(x-) epsilon(x) + int epsilon d wtilde` with `x = 3y`; since `wtilde` is monotone, `wtilde(x-) + TV = wtilde(x/3+) <= 2.6/log x` for large `x`, giving `|epsilon(y)| <= C' sqrt(y) log y + (kappa/log y) sup_{[y, 4y]} |epsilon|` after interpolation (`|epsilon(t) - epsilon(t')| = O(sqrt y)` on consecutive grid points). With `S(Y) = sup_{t<=Y}|epsilon|`, `lambda = kappa/log T_0 < 1/4`, `S(Y) <= K_0 + C' sqrt(Y) log Y + lambda S(4Y)` iterates to `O(sqrt(Y) log Y)` because `(4 lambda)^K Y -> 0` with the trivial `S(Z) <= Z`. That is von Koch's form of RH. Converse via Schoenfeld's explicit RH bound. ✔ The proof uses only the identity and classical facts; it does not assume any bound on `L_R`.

## R-D. Errors found and repaired during the cycle (correction history)

1. **Lab bookkeeping bug** (`ledger_lab`, first build): `wtilde(x/3+)` was evaluated at `floor(x/3)+1`, wrong when that integer is a perfect square (`R = 5, 12, 19, 45, …`), and sectors overlapped for `R < 6`. Symptom: cut-identity residuals up to `0.84` at 13 roots. Diagnosis showed the theory was right and the evaluation wrong; fixed before the held-out evaluation. Corrected residual `<= 2e-9`.
2. **Duplicate Lean lemma caught:** the first draft of PR #961 re-proved `canonicalLargestPrimeFactor (a*q) = q`; repository search found `canonicalLargestPrimeFactor_mul_prime_eq` (`RHLean/Analysis/DyadicTransportCanonicalForm.lean`). The duplicate was removed before the first push; the module reuses the existing lemma.
3. **Over-reach avoided:** an early draft of owner-6 asserted that the whole upper sector carries `-F_R E(R)` up to small error; the `eta`-sum over `[R, x)` is only `O(x/log^2 x)`, so the claim was restricted to chains ending below `x^(2/3)`.

## R-E. Novelty and precedent

- The mechanism behind owner-4 is classical in spirit: the error term of `Psi(x, sqrt x)` (Dickman `rho(2) = 1 - log 2`) contains `x * E(sqrt x)`. The raw-ledger statement, the explicit bracket, the unconditional exponent and the consequence for band-local transports are new on this carrier.
- `research/LATE_FLIP_PNT_SPLIT_DIAGNOSTIC.md` already observed, on a different carrier, that band-by-band RH-quality *upper* bounds lose `R^(3/2) log R`. Owner-4 is the corresponding *lower* bound: the loss is genuine, not an artefact of the triangle inequality.
- Analytic-2/3 sharpen, not replace, the #954 control discussion and the amplification budget.

## R-F. Carrier and covariance checks

- No raw-seat result is transferred to masked/clipped returned cells or to the compressed #915 norm. ✔
- `L^2 = A^2 + B^2 + 2AB` retained with complete `B` (owner, section F); the A/B deviation covariance is dominated by `-2(1-w)^2 epsilon(x/3)^2`. ✔
- `H_R` is never used as the sole compensator; lower-tag charges are inside `B`. ✔
- Mean-centring, diagonal sums or favourable local signs are not used. ✔

## R-G. Decisions

- **Band-local / sector-local estimates at intermediate cuts:** REJECT (owner-4, analytic-4, unconditional).
- **Independent estimate for complete `B_R`:** REJECT as a sub-goal (RH-equivalent, owner-5).
- **Raw-ledger FD-TRANSPORT:** SUSPEND unless a sieve identity with explicit bilinear remainder is specified.
- **INV-CONFIGURATION:** realised (wheel-5) at classical strength; MERGE into the cut-mode picture.
- **MU-LIFT:** REVISE to a structural study of the `K3` corner; no fixed nontrivial `(r, g)` short of quasi-RH (analytic-3).
- **Canonical endpoint, complete-source payment, finite A/C, CORR-4, RH:** OPEN / NO_NEW_RESULT.

Self-audit only; no RH proof claim.

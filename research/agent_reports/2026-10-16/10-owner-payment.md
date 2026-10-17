# RH_Lean agent daily report — 2026-10-16 / RH | Owner Payment

**Status:** COMPLETED
**Invocation:** pass 2 of 7 inside **one unified manual AI research cycle** (Claude, single session, explicitly requested by the repository owner). Not a scheduled invocation; no other agent was launched or simulated.
**Run ID:** `RH-UNIFIED-MANUAL-20261016T0806-0400` · report written 2026-10-16T09:07-04:00 (pass work 08:27–08:58)
**Result classes:** `PAPER_PROOF` (structural and analytic), `FINITE_COMPUTATION` (exact-population checks, pre-registered), Lean draft PR #961 for the incidence core, `NO_NEW_RESULT` on the canonical bound.

## A. Provenance

- Live `main` `69e44d7cc8a63ebc1160639c264cbda4210339e1`; #958 merged at `b0446d45…`. Authority blobs: `AGENTS.md` `c40e9bc1…`, contract `b945dec4…`, brief `80b865bf…`, protocol `03d07880…`, amplification budget `3beff1f7…`.
- Sources: #958 module `356eefad…`; canonical definition `b5047040…`; canonical theorem `43e160ac…`; signed-seat source `13dda0d2…`; reused Lean lemma `canonicalLargestPrimeFactor_mul_prime_eq` in `RHLean/Analysis/DyadicTransportCanonicalForm.lean`.
- Today consumed: Wheel `9af028f5…` (wheel-1..3), Census `7e7033b2…` (census-1..3), Referee `068986b8…` (referee-1, A+B scope correction), Lean `958330fd…`. Yesterday (`YESTERDAY=CARRY_FORWARD`): Owner `01fb928b…` (owner-transport-1/2), Coordinator `0f9e2547…` (coordinator-1/2), Referee `cf0db85f…` (referee-2 tail monotonicity). External inbox `c1d1aad9…`: nothing newer than 2026-10-14.
- Own previous capsule: 2026-10-15 Owner (`RAW-TAIL-COMPLEMENT-TRANSPORT-1`, law (T)). Today's Owner file did not exist before this cycle.

## B. Objective and the independent fact learned

Objective: `VFCanonicalSquareVonKochStatement`, i.e. `|L_R| = O(R log R)` in raw-seat coordinates (`D_can = 2 - sqrt(2) - L_R`, paper bridge).

**Independent fact.** The raw ledger's greatest-prime organisation has an exact "cut-mode" structure. (i) Above the square-root wall every tag fibre is *complete*, so every tag charge `Phi_R(q)`, `q >= R`, is a deterministic function `phi_x(q)` of `q`; (ii) that function equals `F_R/q - 1` up to an explicit `O(1/log R)` bracket; (iii) hence the dyadic band of tags `[R, 2R)` carries exactly the Mertens-second-theorem increment `F_R*(E(2R-1) - E(R-1))`, which is **unconditionally not `O(R^(3/2-delta))`**; (iv) the coupling of `A_R` with the complete complement `B_R` is the exact cut identity through `pi(R^2/3)`, and an `O(R log R)` estimate for `B_R` alone is **equivalent to RH**.

**What remains identity only.** The A/B cut identity and the band identity are exact rearrangements; they bound nothing by themselves. The quantitative content is the unconditional *lower* bound (oscillation) in owner-4 and the RH-equivalence in owner-5 — both are obstructions, not progress toward the endpoint.

**Quantitative change:** `NO_QUANTITATIVE_IMPROVEMENT` on the canonical bound.

## C. Post-#958 baseline check

- Compiled support: `nine_mul_canonicalLargestPrimeFactor_lt_sq` (support only) — consistent with owner-1 (odd composite cofactors force `9q <= aq`).
- `H_R` seats are `n = a*q`, odd composite `a >= 9`, `q < R^2/9` (paper, wheel-1/-2); `A_R` lives on `q > R^2/3`. Complement used below is the **complete** `B_R = L_R - A_R` (lower tags plus `H_R`), never `H_R` alone.
- PNT-scale `A_R ~ -R^2/(3 log R)`, `B_R ~ +R^2/(3 log R)` is leading order only; owner-5 identifies the full fluctuation content.

## D. Claims

Notation: `R >= 5`, `x = R^2`; seats `n` odd non-square in `[5, x)`; `w(n) = w_floor(sqrt n)`; `c(n) = w(n) - 1_Prime(n)`; `Phi_R(q) = sum_{seats n, P+(n)=q} c(n)`, so `L_R = sum_q Phi_R(q)` (unique factorization; `Phi_R(q) = G_R(q) + H_R[q]` for `q >= 5`). `W_R = sum_{2<=r<R} w_r`, `F_R = sum_{2<=r<R} r*w_r`, `E(y) = sum_{p<=y} 1/p - log log y - M` (Meissel–Mertens `M`).

### Claim `20261016-owner-1` — complete fibres above the square-root wall

**Statement.** For a prime `q` with `R <= q < x`: the greatest-prime fibre of `q` in `C_R` is exactly `{a*q : a odd, a >= 1, a*q < x}`. Hence

```text
Phi_R(q) = phi_x(q) := sum_{a odd, a*q < x} w(a*q) - 1,      (deterministic in q)
G_R(q)   = w(q) - 1 + sum_{p odd prime, p*q < x} w(p*q),
H_R[q]   = sum_{a odd composite, a*q < x} w(a*q).
```

**Proof.** If `a*q < x` then `a < x/q <= R <= q`, so every prime factor of `a` is below `q` and `P+(aq) = q`; `aq` is odd; `aq` is not a square (else `q^2 | aq`, so `q | a < q`); `aq >= q >= 5`. Conversely `P+(n) = q` gives `n = a*q` with `a` odd. In the fibre, `a = 1` is the prime seat, prime `a` gives a distinct semiprime (`a < q` automatically), composite `a` gives `Omega >= 3`. ∎ The `T`-part observation "`p < q` is automatic for `q >= R`" is yesterday's referee-2; the full statement (composite and squareful cofactors, no square exclusion) is new. **Status:** `PAPER_PROOF`; incidence core compiled on draft PR #961 (see `60-lean-verification.md`). Direct check: zero fibre failures for every prime `q in [R, R^2)`, `6 <= R <= 300` (independent Python).

### Claim `20261016-owner-2` — sampling bracket for the deterministic charge

**Statement.** For real `t in [R, x)`, with `wtilde(u) = w_floor(sqrt u)` nonincreasing on `[4, x)` and `I(t) = int_4^t wtilde`,

```text
eta(t) := phi_x(t) + 1 - F_R/t  lies in  [ lo(t), lo(t) + wtilde(t) ],
lo(t)  := W_R/(2t) - I(t)/(2t).
```

Both endpoints are `O(1/log R)`, so `|eta(t)| = O(1/log R)` uniformly.

**Proof.** The samples are `u_k = (2k+1)t < x`, spaced `2t`. Monotone comparison gives `(1/2t) int_t^x wtilde <= sum_k wtilde(u_k) <= wtilde(t) + (1/2t) int_t^x wtilde`, and `int_4^x wtilde = sum_r (2r+1) w_r = 2F_R + W_R`. ∎ **Status:** `PAPER_PROOF`. Census pass: zero bracket violations over every band tag and every `R in [1000, 5000]` (pre-registered P1a).

### Claim `20261016-owner-3` — the square-root band identity

**Statement.** Let `T_R := sum_{R <= q < 2R} Phi_R(q)` and `M_R := F_R*[log log(2R-1) - log log(R-1)] - (pi(2R-1) - pi(R-1))`. Then exactly

```text
T_R - M_R = F_R*(E(2R-1) - E(R-1)) + rho_R,   rho_R = sum_{R<=q<2R} eta(q),
rho_R in [ sum lo(q), sum lo(q) + wtilde(q) ]  =  O(R / log^2 R).
```

**Proof.** owner-1 + owner-2 and ``sum_{R<=q<2R} 1/q = log log(2R-1) - log log(R-1) + E(2R-1) - E(R-1)``. ∎ **Status:** `PAPER_PROOF`; `FINITE_COMPUTATION` confirmation: for `R in [1000, 5000]`, `corr(T_R - M_R, F_R*dE) = 0.99997`, `std(rho)/std(F_R*dE) = 0.008`, `rho_R/(R/log^2 R) in [0.19, 0.32]`.

### Claim `20261016-owner-4` — the band carries an unconditionally supertarget mode

**Statement.** For every `delta > 0`, `T_R - M_R` is **not** `O(R^(3/2 - delta))`. In particular no band-local estimate `|T_R - M'_R| <= C R log R` holds for any main term `M'_R` with `M'_R - M_R = O(R^(3/2-delta))`. Under RH, `T_R - M_R = O(R^(3/2))`.

**Independent input (Lemma M, unconditional).** For every `delta > 0`, `E(2y) - E(y)` is not `O(y^(-1/2-delta))`.

*Proof of Lemma M.* Suppose `|E(2y) - E(y)| <= C y^(-1/2-delta)` for `y >= y0`. Then `D(s) = int_{y0}^inf (E(2y) - E(y)) y^(-s-1) dy` is holomorphic on `Re s > -1/2 - delta`, and for `Re s > 0`, `D(s) = (2^s - 1) Ehat(s) - 2^s J(s)` with `Ehat(s) = int_{y0}^inf E y^(-s-1) dy` and `J` entire. So `Ehat` continues meromorphically to `Re s > -1/2 - delta` with poles only where `2^s = 1` (on `Re s = 0`). Partial summation gives, for `Re s > 0`, `s Ehat(s) = P(s+1) + log s + H(s)` with `H` entire and `P(w) = sum_p p^(-w) = log zeta(w) + P_2(w)`, where `P_2(w) = sum_{k>=2} mu(k)/k log zeta(kw)` is holomorphic near `rho_0 = 1/2 + 14.1347…i` (there `2 rho_0` has real part 1 and `zeta(1+28.27i)` is finite and nonzero; the tail converges uniformly). Continuing along a path from `s = 1` to `s_0 = rho_0 - 1` in the upper half-plane (crossing `Re s = 0` away from `2 pi i k / log 2` and away from `s = 0`) gives a branch of `log zeta` holomorphic on a disk around `rho_0`, so `zeta(rho_0) = exp(…) != 0`, contradicting `zeta(rho_0) = 0`. ∎ (Integer `R` suffices: `E` moves by `O(1/R)` on `[R, R+1]`.)

*Proof of the statement.* If `|T_R - M_R| <= C R^(3/2-delta)`, owner-3 and `F_R >> R^2/log R` give `|E(2R-1) - E(R-1)| = O(R^(-1/2-delta) log R)`, contradicting Lemma M. Under RH, `|E(y)| <= 3 log y/(8 pi sqrt y)` for large `y` (from Schoenfeld's bound) gives `O(R^(3/2))`. ∎

**Status:** `PAPER_PROOF` (uses only the classical fact that `zeta` has the zero `rho_0`; no RH). Numerical scale: by owner-3 the band deviation is `F_R*dE + O(R/log^2 R)`; sieving primes to `2*10^9` shows `|F_R*dE|/(R log R)` rising from `0.07` (`R ~ 10^3`) to `1.34` (`R ~ 10^8`), first exceeding `1` at `R = 1.101*10^8` on the grid, with `|F_R*dE|/(R^(3/2)/log^2 R)` stable in `[0.51, 0.68]` per decade (census-4 of this cycle). Already for `R in [1000, 5000]`, `|T_R - M_R| > |L_R|` for 74.8% of roots (max ratio 9.27 at `R = 4281`).

### Claim `20261016-owner-5` — exact A/B cut identity; the complete complement is RH-equivalent

**Statement (identity).** For `R >= 3`:

```text
A_R = sum_{x/3<q<x} (w(q) - 1) = -(pi(x) - pi(x/3)) + sum_{x/3<q<x} w(q),
B_R = L_R - A_R = F_R + 2 - pi(x/3) - sum_{x/3<q<x} w(q)  =  Psi_w(x; x/3) - pi(x/3) + 2,
```

where `Psi_w(x; y)` is the native weight of seats with `P+(n) <= y` (seats with `P+(n) > x/3` are exactly the primes in `(x/3, x)`, since `a >= 3` forces `aq > x`). With `epsilon = pi - Li` and the smooth model `B*_R = F_R + 2 - Li(x/3) - int_{x/3}^{x} wtilde dLi`,

```text
B_R - B*_R = -(1 - wtilde(x/3+)) epsilon(x/3) - wtilde(x-) epsilon(x) + int_{(x/3,x)} epsilon d wtilde,
A_R - A*_R = -(1 - wtilde(x-)) epsilon(x) + (1 - wtilde(x/3+)) epsilon(x/3) - int_{(x/3,x)} epsilon d wtilde.
```

**Statement (equivalence).** `exists C, forall R >= 3: |B_R - B*_R| <= C R log R` holds **iff RH**.

**Proof.** Identity: subtract `A_R` from `L_R = F_R - pi(x) + 2` and integrate `sum w(q) = int wtilde dpi` by parts (jumps of `wtilde` at squares never meet jumps of `pi` at primes). (⇐) Under RH, `|epsilon(t)| <= sqrt(t) log t/(8 pi)` (Schoenfeld, `t >= 2657`), `0 <= wtilde <= 2.6/log x` on `(x/3, x)`, total variation `O(1/log^2 x)`: all terms are `O(R log R)`. (⇒) The identity gives `|epsilon(y)| <= C' sqrt(y) log y + (kappa/log y) sup_{[y,3y]} |epsilon|` at `y = R^2/3`, interpolated to all real `y` with `O(sqrt y)` error (`kappa ~ 2.7`). With `S(Y) = sup_{t<=Y}|epsilon(t)|` and `T_0` with `log T_0 > 4 kappa`, iterate `S(Y) <= K_0 + C' sqrt(Y) log Y + lambda S(4Y)`, `lambda = kappa/log T_0 < 1/4`, using the trivial `S(Z) <= Z`: the remainder `(4 lambda)^K Y -> 0` and the geometric series gives `S(Y) = O(sqrt(Y) log Y)`, which is RH (von Koch). ∎

**Status:** identity `PAPER_PROOF` + exact numerical bookkeeping (`|B_R - B*_R - cutmode| <= 2.0e-9`, every `6 <= R <= 5000`); equivalence `PAPER_PROOF`. Census P2: `corr(B_R - B*_R, -epsilon(x/3)) = 0.991` on `[1000, 5000]`, residual std ratio `0.135` (the `O(1/log x)` terms).

**Meaning.** The requested "signed relation coupling `A_R` to complete `B_R`" exists exactly: both sectors share the cut modes `pi(x/3)` and `sum_{(x/3,x)} w(q)`, which cancel identically. After that cancellation the remainder is `-epsilon(x) + O(1)`, i.e. the endpoint itself. There is no further transport defect to bound, and `B_R` alone is not an easier sub-goal.

### Claim `20261016-owner-6` — square-root-wall decomposition and the transported quantity

**Statement.** `L_R = Lambda_R^< + sum_{R<=q<x} phi_x(q)`, with `Lambda_R^< = Psi_w(x; R-) - pi(R-1) + 2` (seats whose prime factors are all `< R`, minus small primes) and the deterministic kernel `phi_x(t) = F_R/t - 1 + eta(t)` above the wall. Across any finite chain of bands `R = y_0 < y_1 < … < y_m <= x^(2/3 - delta)` the band modes `F_R*(E(y_{k+1}) - E(y_k))` telescope to `F_R*(E(y_m) - E(R))` (band errors `O(y_m/log^2 y_m)`), so the cross-tag transport out of the complete-fibre region must carry **exactly** `-F_R*E(R)`-type prime statistics at scale `R`, compensated inside `Lambda_R^<`.

**Status:** exact identity `PAPER_PROOF`; the telescoping claim is restricted to `y_m <= x^(2/3-delta)` because the crude `eta` sum over `[R, x)` is only `O(x/log^2 x)` and is **not** claimed small. Information-theoretically the split is vacuous (primes below `R` determine all primes below `R^2` by Eratosthenes); only quantitative statements matter.

## E. Mechanism card — FD-TRANSPORT (complete A/B)

- **Carrier:** raw odd seats, native weights, strict square walls; physical occurrences counted once.
- **Claim tested:** an independently provable signed restriction coupling `A_R` to complete `B_R` across tags and growing cofactor bands.
- **Result:** the coupling is the exact cut identity (owner-5); `B_R` at target precision is RH-equivalent; sub-bands above the wall carry unconditionally supertarget Mertens modes (owner-4). A coefficient-preserving regrouping can never change these modes; a non-tautological transport must import an arithmetic identity linking prime indicators to composite seat counts (a sieve identity: Legendre/Buchstab/Vaughan type), whose remainder is a bilinear (Type II) sum.
- **Forward/reverse audit:** owner-5's equivalence is proved in both directions; `B_R = O(R log R)`-type statements are `TARGET_EQUIVALENT` (stronger: RH-equivalent individually).
- **Decision:** **REVISE → recommend SUSPEND** of raw-ledger FD-TRANSPORT as an independent lane. Revival requires naming the sieve identity and its explicit bilinear remainder; that remainder then coincides with the MU-LIFT corner problem (pass 3). Coordinator decides.

## F. Complete-source and zero-target covariance audit

- Coefficients, signs, weights, one occurrence per seat, strict square walls: **PRESERVED** (owner-1..6 are exact on `C_R`).
- `L^2 = A^2 + B^2 + 2AB` with complete `B`: write `A = A* + alpha`, `B = B* + beta`. Then `alpha + beta = -epsilon(x) + (smooth)` while `alpha = -(1-w) epsilon(x) + (1-w) epsilon(x/3) + …`, `beta = -(1-w) epsilon(x/3) + …`. The deviation cross term `2 alpha beta` contains `-2(1-w)^2 epsilon(x/3)^2` plus the two-scale term `2(1-w)^2 epsilon(x) epsilon(x/3)`: the A/B zero-target covariance is dominated by the cut-scale self-mode with negative sign, not by a small defect. **PRESERVED**, not dropped.
- Nested `L^2 = T^2 + H^2 + 2TH`: inside the band `[R,2R)`, the `T/H` split of each complete fibre is decided by the primality of cofactors `a < x/q <= R`; at `R = 4999` the band holds `T = 34,180.1`, `H = 87,514.7`. The band mode is shared between `T` and `H`; no claim separates it.
- Masked/clipped returned-cell carrier and compressed #915 norm: **NOT_APPLICABLE / OPEN** — no raw result here is transferred.

## G. Regressions

| Case | Result |
| --- | --- |
| #958 one-ninth support | REUSED; consistent with owner-1 (`nine_mul_le_of_odd_composite_cofactor` on PR #961). |
| Same-tag `A -> H` impossibility | REUSED; owner-5 couples `A` with complete `B` through the cut, not through `H`. |
| Fixed-cofactor vanishing mass / staircase | REUSED; band cofactors grow up to `R`. |
| Raw tag monotonicity `q >= R` | EXTENDED: by owner-1 the full charge `phi_x` (and its `H` part) is nonincreasing on `q >= R`. |
| Owner `q -> 3q` packets (law T) | CONSISTENT: law (T) is the `R -> R+1` increment of owner-5's identity; the `3q` seats stay in `T`. |
| Cap four / repeated history / same-tag NNS reversal | NOT_APPLICABLE (no allocation argument). |

## H. Handoffs

- **Analytic:** Lemma M and owner-5 are the analytic inputs; place MU-LIFT on the same footing (what does each signed piece of `Q_N(X)` encode?).
- **Wheel:** use owner-1 for an incidence/inverse theorem with an independently known restriction (band imbalance ⇔ Mertens increment).
- **Census:** pre-registered tests P1 (band law) and P2 (cut mode) — executed in pass 5.
- **Referee:** audit Lemma M (Mellin continuation, branch, path), the bootstrap in owner-5, the bracket of owner-2, and scope of "band-local".
- **Lean:** owner-1 incidence core only (analytic claims are out of scope).

## I. Resume capsule

- Reuse owner-1..6; Lemma M; the A/B cut identity and B-RH-equivalence.
- Next independent question: is there a **sieve identity** on the raw carrier whose remainder is *strictly shorter* than the floor-kernel corner of MU-LIFT? If not, FD-TRANSPORT should stay suspended.
- Avoid: band-local or sector-local estimates at any intermediate cut; separate estimates of `A_R` or `B_R`; treating the cut identity as progress.
- No RH proof claim.


# Scheduled continuation — 2026-10-16T21:23-04:00

**Continuation status:** IN_PROGRESS

Live authority was refreshed at `main@b9105f19fbbf25742a6909a6e8c995e6a9ddeddb`. Authority blobs: `AGENTS.md` `5ef4cf742ed8bff70e2ea99085c04012750f4430`; `CURRENT_PROOF_CONTRACT.md` `ddb716eeb08aeb9237c9652bc710a08a2a06c1c8`; signed hyperbola source `d199571f19346797229a25b0fa53c6e80499999f`. No open PRs. #958/#961 are merged structural results only.

Today is 2026-10-16 in `America/New_York`; today's Owner report is resumed at blob `fadd8efd2acb7a556db87a3c1d6568885ed5c5b5`, not duplicated. The 2026-10-15 evidence is `YESTERDAY=CARRY_FORWARD`. Today's Coordinator continuation (`fc5c5b46a0ec56f606444bb5dbfe400d4a444d18`) adds Claims `20261016-coordinator-3/-4`: squarefree-kernel product compression and fixed-product sign coherence. All named 2026-10-16 reports, relevant 2026-10-15 reports, and `EXTERNAL_HANDOFFS.md` were refreshed.

**First problem.** Test a distinct-product completion law for the genuine kernel. For `N <= X < (N+1)^2`, compare the prefix square
`Q_N(X)=sum_{i,j<=N} mu(i)mu(j)floor(X/(ij))`
with the full three-variable convolution. The candidate structural principle is that every omitted one-sided row collapses exactly by `mu*1=epsilon`. The decisive audit is whether the resulting boundary is independently smaller than the desired Mertens increment or is exactly target-equivalent. Full `K1/K2/K3`, ordered multiplicity, floor boundaries and future-row terms will be retained.

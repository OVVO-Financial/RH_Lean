# Universal envelope law for the frozen-root coordinates — status snapshot and external handoff, 2026-11-15

- **Origin:** user-directed direct Claude session on `OVVO-Financial/RH_Lean`. Not one of the seven scheduled agent reports. Read-only session: nothing on `main` or `agent-reports` was changed.
- **Research labels:** ENV-1 `EXACT_IDENTITY`. ENV-2 to ENV-5 `PAPER_PROOF` (elementary, self-contained; explicit constants where stated), `SELF_AUDIT`, independent referee review required. ENV-6 `FINITE_EVIDENCE`. ENV-7 status audit. **No Lean was compiled in this session.**
- **Scope:** RH remains OPEN. Nothing here proves a new zero-free region or a new Mertens exponent. The result is an exact law relating the repo's frozen-root objects to the zero supremum, and a consequence for how the open nodes relate to each other.
- **Authority checked:** main `59612bc8b5c30c528d8367667ea5846a8053f114` (#1133, 2026-11-11); agent-reports `5a7f05d56a6a288aa2e6fbd0b2755047215d904d` (2026-11-12 04:41 EST). No newer commit on either branch as of 2026-11-15.
- **Suggested location:** `research/agent_reports/external/2026-11-15/` on `agent-reports`, with the three scripts beside it. A draft index entry is in section 13.

## 0. Bottom line

1. **One unconditional inequality covers every R.** For every `eps > 0` there is a constant `C` such that for all `R >= 2`

   ```text
   |M(R^2-1) - 1|  <=  C * R^(1+eps) * K_R                      (ENV-4)
   ```

   Equivalently `alpha_R <= C^2 R^(2 eps) K_R`, and `E(B^2) <= C B^eps E(B)^2`. The finite-A target is the same display with `K_R` replaced by `sqrt(K_R)`.
2. **It is sharp, and the gap to RH is exactly the exponent on K_R.** For `0 <= lam < 2` and `eta >= 0`, the bound `|M(R^2-1) - 1| <= C R^(1+eta+eps) K_R^(lam/2)` (all `eps`, all `R`) holds if and only if `Theta <= 1/2 + eta/(2-lam)` (ENV-5). At `eta = 0`: lowering the exponent on `K_R` below 1 at all is equivalent to RH.
3. **The amplification exponent is now exact.** `q(X) = log(1+A(X))/log X` converges, and its limit is `max(Theta,1/2) - 1/2` (ENV-3). So `SquareRootAmplificationZeroLogGrowthStatement` is equivalent to RH, and the certified bound on `limsup q` halves from `3/4 - 1/(24 N_*)` to `3/8 - 7/(64 N_pack)`.
4. **Three open nodes are one node.** The one-step FINITE-AC estimate, zero-log amplification and the MU-LIFT subcritical lift are the same statement about one number, and the recursive-owner `kappa` recursion is the same affine map with the same fixed point. A candidate inequality with parameters `(lam, eta)` is worth exactly the half-plane `Re s > theta(lam,eta) := 1/2 + eta/(2-lam)`; that is a meter every proposal can be scored on before work starts.
5. **Where the exponent stands.** Certified on main: `7/8 - 7/(64 N_pack)`, a gain of at most `3.3e-11`. Paper endpoint in the pipeline: `7/8 - 1/2400000000` (`4.2e-10`). Public leaderboard record on 2026-11-13: about `0.873346` (gain `1.65e-3`).

## 1. Where the program stands (2026-11-15)

| Item | State | Evidence |
| --- | --- | --- |
| Certified Mertens exponent | `native_mertens_near_uniform_window_error_closed : MertensGrowthAtMost (7/8 - 7/(64 * nearUniformSlotCount))`, merged with #1119 (2026-11-08) | `research/oai_434/VF919WindowErrorClosure.lean:128` |
| Size of that gain | `nearUniformSlotCount = ceil(max 1 (1/(6 L0))) + 2`, `L0 = explicitFineLength = (1/200) min(min(t, detectorMesh(1e-6, t)), t)`, `t = 1e-8`. Hence `L0 <= 5e-11`, `N_pack >= 3.33e9`, gain `7/(64 N_pack) <= 3.3e-11`. The true value is smaller if `detectorMesh < t`; no numeral for it exists in the repo. | `VF919ExplicitFixedSourceSlotCount.lean:18-25`, `VF919ExplicitSquareBlockPacking.lean:45`, `docs/RHLEAN_EXPLICIT_SLOT_NUMERAL_REDUCTION_20261104.md` ("remains symbolic") |
| Next exponent in the pipeline | `b_IR = 7/8 - 1/2400000000`, accepted on paper by the Referee. #1131 and #1132 (merged 2026-11-11) compile the finite response suppliers; FFR3 (finite-interval inversion) and FFR4 (full physical assembly) are open. | Analytic 2026-11-10 `IR1-IR4`; Lean 2026-11-11 resume capsule |
| RH-strength premises | All open. Ten routes: VF-LOW, SAT, JOH, CODIV, OAI-NNS, FINITE-AC, CORR4, MU-LIFT, NYMAN open; BLOCK refuted at `R = 549`. Registry: 99 nodes, 19 open obligations. | `docs/PROOF_DEPENDENCY_DAG.md` section 4; `docs/proof-obligations.json` |
| Amplification coordinate | Proved `A(X) <= C X^(3/4 - 1/(48 N_*))`, `limsup q <= 3/4 - 1/(24 N_*)`, obtained with `K_R >= 1`. The scoreboard records the unpaid term as "complete signed return relative to actual K_R". | DAG scoreboard, FINITE-AC row |
| Agent activity | Last report: Referee, 2026-11-12 04:41 EST. Last merge on main: #1133, 2026-11-11 14:52 EST. Nothing since. | branch heads above |
| Status documents | Lagging main: the README headline is dated 2026-11-08 and quotes `7/8 - 1/(48 N_*)`; the generated scoreboard still calls #1119 "green unmerged"; the registry baseline is main `7aa0fcb1` (2026-11-09). | `README.md:3`; DAG section 4; registry `baseline` |
| Public leaderboard | Record about `0.873346` (2026-11-13, PR #141, merged). No RH_Lean entry on the timeline. The record gain is about `5e7` times the cap on the certified RH_Lean gain and about `4e6` times the paper endpoint. | QuasiRiemannTracker timeline as mirrored at discoveria.ai, fetched 2026-11-15 |

Not re-verified here: the Lean build, the OpenAI import, and the agents' paper proofs. The table reports what the repository and its CI records say.

## 2. Objects (exact repo definitions)

```text
M(x)    = sum_{n<=x} mu(n),  M(x) = M(floor x)
X_R     = R^2 - 1                                              squareRootEndpoint
K_R     = max_{0<=y<R} (M(y)-1)^2/(y+1)        (>= 1)          squareRootHistoricalK
alpha_R = (M(X_R)-1)^2 / (R^2 K_R)                              squareRootEndpointAmplification
A(X)    = max{ alpha_R : R >= 2, X_R <= X }                     squareRootAmplificationMax
q(X)    = log(1 + A(X)) / log X                                 squareRootAmplificationLogRatio
Q_R     = sum_{a,b<R} mu(a) mu(b) floor(X_R/(ab)) = 2 M(R-1) - M(X_R)
E(B)    = max_{1<=n<B} |M(n)| / sqrt(n)        (>= 1)          MU-LIFT budget
Theta   = zetaRightmostRealPart                                 research/MERTENS_EXPONENT_DIAGNOSTICS.lean
h       = max(Theta, 1/2) - 1/2                                 critical defect;  h = 0  <=>  RH
```

`K_R` and `E(R)^2` are interchangeable up to constants: `(E(R)-1)/sqrt(2) <= sqrt(K_R) <= E(R)+1`.

Already in Lean on main and used below: `growthAtMost_iff_rightmost_le` (`MertensGrowthAtMost a <-> zetaRightmostRealPart <= a`), from `research/MERTENS_CONVERSE_IDENTIFICATION.lean`. In particular `|M(x)| <= C_eps x^(1/2+h+eps)` for every `eps > 0`. Call this (U).

## 3. Claim ENV-1 — kernel identity (EXACT_IDENTITY)

Let `kappa0` be a measurable function on `[1, oo)`, bounded on compact subsets, and put `kappa(u) = sum_{1<=n<=u} kappa0(u/n)`. Then for every real `Y >= 1`

```text
int_1^Y M(x) kappa(Y/x) dx/x  =  int_1^Y kappa0(v) dv/v.
```

*Proof.* For real `z >= 1`, `sum_{n<=z} M(z/n) = sum_{k<=z} sum_{d|k} mu(d) = 1`. Expand `kappa`, exchange the finite sum with the integral, and substitute `z = n x` in the `n`-th term:

```text
int_1^Y M(x) sum_{n<=Y/x} kappa0(Y/(n x)) dx/x
   = sum_{n<=Y} int_n^Y M(z/n) kappa0(Y/z) dz/z
   = int_1^Y [ sum_{n<=z} M(z/n) ] kappa0(Y/z) dz/z
   = int_1^Y kappa0(Y/z) dz/z.
```

Substituting `v = Y/z` gives the claim. ∎

The same identity holds for any Dirichlet-inverse pair `f * g = delta` with `kappa(u) = sum_{n<=u} f(n) kappa0(u/n)` and `M` replaced by the summatory function of `g`. Main already has the base identity `sum_{n<=X} M(floor(X/n)) = 1` in `g`-weighted form: `sum_convolveOne_mul_mertensSummatory_div`, `RHLean/Analysis/MobiusRenewalTelescope.lean:173`.

## 4. Claim ENV-2 — zero-forced envelope (PAPER_PROOF, explicit)

Let `rho = beta + i gamma` be a zero of zeta with `0 < beta < 1`, and put `C_rho = 1 + |1-rho| (1 + |rho|/beta)`. Then

```text
(a) real Y >= 1:     int_1^Y |M(x)| dx/x  >=  ( |1-rho| (Y^beta - 1)/|rho| - log Y ) / C_rho
(b) integer B >= 2:  E(B)        >=  ( |1-rho| (B^beta - 1)/|rho| - log B ) / ( 2 C_rho sqrt(B) )
(c) integer R >= 2:  sqrt(K_R)   >=  ( |1-rho| (R^beta - 1)/|rho| - (1 + C_rho) log R ) / ( 2 sqrt(2) C_rho sqrt(R) )
```

So every zero forces `E(B) >= c(rho) B^(beta-1/2)` and `K_R >= c(rho)^2 R^(2 beta-1)` at **every** scale beyond an explicit threshold, not only along a subsequence.

*Proof.* Step 1 (Euler–Maclaurin at a real cutoff). For `Re s = sigma > 0`, `s != 1`, real `u >= 1`:

```text
sum_{n<=u} n^(-s) = zeta(s) + u^(1-s)/(1-s) + E_s(u),
E_s(u) = -{u} u^(-s) + s int_u^oo {t} t^(-s-1) dt,        |E_s(u)| <= (1 + |s|/sigma) u^(-sigma).
```

(For `sigma > 1` write the tail `sum_{n>u} n^(-s)` as a Stieltjes integral against `floor t = t - {t}` and integrate by parts; both sides continue analytically to `sigma > 0`.)

Step 2 (the kernel is bounded exactly at a zero). Take `kappa0(v) = (1-rho) v^rho - 1`. Then

```text
kappa(u) = (1-rho) u^rho sum_{n<=u} n^(-rho) - floor(u)
         = (1-rho) zeta(rho) u^rho + u + (1-rho) u^rho E_rho(u) - floor(u)
         = {u} + (1-rho) u^rho E_rho(u),
```

because `zeta(rho) = 0`. Hence `|kappa(u)| <= 1 + |1-rho| (1 + |rho|/beta) = C_rho` for all `u >= 1`. At a point that is not a zero the term `(1-s) zeta(s) u^s` survives and the kernel grows like `u^sigma`.

Step 3. ENV-1 with this `kappa0` reads

```text
int_1^Y M(x) kappa(Y/x) dx/x = (1-rho)(Y^rho - 1)/rho - log Y.
```

Take absolute values: the left side is at most `C_rho int_1^Y |M(x)| dx/x`, the right side is at least `|1-rho|(Y^beta - 1)/|rho| - log Y`. This is (a).

Step 4. For `1 <= x < B`, `|M(x)| <= E(B) sqrt(x)`, so `int_1^B |M| dx/x <= 2 E(B) sqrt(B)`; with (a) at `Y = B` this is (b). For `1 <= x < R`, `|M(x)| <= 1 + sqrt(K_R (x+1)) <= 1 + sqrt(2 K_R x)`, so `int_1^R |M| dx/x <= log R + 2 sqrt(2 K_R R)`; with (a) at `Y = R` this is (c). ∎

Remarks.

- The pairing in Step 3 has the exact value `(1-rho)(Y^rho-1)/rho - log Y`. It does not involve `zeta'(rho)`, the multiplicity of `rho`, or any other zero. That is why no information about `1/zeta` inside the strip is needed.
- Discrete form for formalization: with `K0(v) = (1-rho)(v^rho-1)/rho - log v` and `K(u) = sum_{n<=u} K0(u/n)`, Möbius inversion gives `sum_{d<=N} mu(d) K(N/d) = K0(N)`, and `|u K'(u)| = |kappa(u)| <= C_rho` gives `|K0(N)| <= C_rho sum_{d<=N} |M(d)| log(1 + 1/d)`.
- Contrapositive (what a clean history buys): if `B^(beta-1/2) > B^(-1/2) + (|rho|/|1-rho|) (2 C_rho E(B) + log B / sqrt(B))` for some `B`, then `zeta(beta + i gamma) != 0`. Since `C_rho` grows like `|gamma|^2`, this excludes only zeros whose height is below a power of `B` (here `|gamma|^2` up to roughly `B^(beta-1/2)`). Higher zeros are invisible to a first-bad argument run on history alone.
- Literature. Lower bounds for averages of `|M|` forced by a zero are classical (Pintz, 1980s; made explicit by Johnston and Trudgian, arXiv:2511.09978; see also Pintz, arXiv:2608.24878). No novelty is claimed for the kind of statement. What is used here is the short elementary proof with the log weight, and its application to `K_R`, `alpha_R`, `q(X)` and `E(B)`.

## 5. Claim ENV-3 — envelope law (PAPER_PROOF)

```text
(a)  lim_{R->oo} log K_R / log R = 2h          lim_{B->oo} log E(B) / log B = h
(b)  lim_{X->oo} q(X) = h
```

These are limits along all integers, not limsups.

*Proof.* (a) Upper bounds follow from (U): `K_R <= (C_eps + 1)^2 R^(2h+2eps)`. If `h = 0` the lower bounds are `K_R >= 1`, `E >= 1`. If `h > 0`, pick a zero with `beta >= 1/2 + h - eps` (it exists by the definition of the supremum) and apply ENV-2(b),(c): `K_R >= c R^(2h-2eps)` for `R >= R_0`.

(b) Upper bound: `alpha_R <= (C R^(1+2h+2eps) + 1)^2 / (R^2 * c R^(2h-2eps)) <= C' R^(2h+6eps)` for `R >= R_0`, so `A(X) <= C'' X^(h+3eps)`.

Lower bound, for `h > 0`. Keep the zero `rho` of part (a), so `beta >= 1/2 + h - eps`. First, large values occur at every scale: for `eps > 0` and `Y >= Y_0(eps)` there is `x` in `[Y^(1-6eps), Y]` with `|M(x)| >= Y^(1/2+h-2eps)`. Indeed, if `|M(x)| < T` on that interval, then by (U)

```text
int_1^Y |M| dx/x  <=  2 C Y^((1-6eps)(1/2+h+eps)) + 6 eps T log Y  <=  2 C Y^(beta-eps) + 6 eps T log Y,
```

and ENV-2(a) forces `T >= c Y^beta / log Y >= Y^(1/2+h-2eps)` for large `Y`. Now take such an `x` with `eps < h/4` and `R = floor(sqrt(x+1))`. Then `X_R <= x`, `x - X_R <= 2R`, so `|M(X_R) - 1| >= (1/2) Y^(1/2+h-2eps)`, while `R^2 <= Y+1` and `K_R <= C (Y+1)^(h+eps)`. Therefore `A(Y) >= alpha_R >= c Y^(h-5eps)`. ∎

Consequences.

- `SquareRootAmplificationZeroLogGrowthStatement` holds if and only if `Theta <= 1/2`. Main has the eventual-budget consumer (`squareRootAmplificationZeroLog_eventually_native_envelope`) and the algebraic iteration (`all_exponents_of_contracting_upgrade`), whose `upgrade` hypothesis is not instantiated. The first half of ENV-5 below supplies that step directly, with no new analysis. The converse and the exact limit are new.
- For any certified `b >= 1/2` with `MertensGrowthAtMost b`: `limsup q <= b - 1/2` and `A(X) <= C_eps X^(b-1/2+eps)`. With the certified exponent this is `3/8 - 7/(64 N_pack)`, against `3/4 - 1/(24 N_*)` on the scoreboard. Using the true `K_R` recovers exactly half of the amplification exponent. The other half is RH itself.
- If `h > 0`, then `A(X) -> oo` like `X^h`: finite A fails. If `h = 0`, then `A(X) <= C_eps X^eps`, which does not give finite A. So finite A implies RH, and this law does not decide the converse: that is a question about the fine-scale oscillation of `M(x)/sqrt(x)`.

## 6. Claims ENV-4 and ENV-5 — the universal bound and its dictionary (PAPER_PROOF)

**ENV-4 (critical universal bound).** For every `eps > 0` there is `C` such that for all integers `R >= 2` and `B >= 2`

```text
|M(R^2-1) - 1| <= C R^(1+eps) K_R        alpha_R <= C^2 R^(2 eps) K_R        E(B^2) <= C B^eps E(B)^2.
```

More generally `E(B^k) <= C B^eps E(B)^k` for every fixed `k >= 2`.

*Proof.* By (U), `|M(R^2-1) - 1| <= C R^(1+2h+2eps) + 1`. By ENV-3(a), `K_R >= max(1, c R^(2h-2eps))` for `R >= R_0`. Divide, absorb finitely many `R < R_0` into the constant, and rename `eps`. The `E` forms are the same computation. ∎

**ENV-5 (dictionary).** Fix `0 <= lam < 2` and `eta >= 0`. The following are equivalent.

```text
(1)  for every eps > 0 there is C with  |M(R^2-1) - 1| <= C R^(1+eta+eps) K_R^(lam/2)  for all R >= 2
(2)  Theta <= 1/2 + eta/(2 - lam)
```

*Proof.* (1) implies (2). For `x >= 3` let `R = floor(sqrt(x+1))`, so `|M(x)| <= |M(X_R)| + 2R`. Insert (1) and `K_R <= C R^(2h+eps)`: `|M(x)| <= C x^(b'+eps)` with `b' = 1/2 + eta/2 + (lam/2) h`. By `growthAtMost_iff_rightmost_le`, `Theta <= b'`. If `h = 0` there is nothing to prove; otherwise `h <= eta/2 + (lam/2) h`, that is `h <= eta/(2-lam)`. This direction uses only what is already in Lean.

(2) implies (1). If `h = 0`, use (U) and `K_R >= 1`. If `h > 0`, use (U) and `K_R^(lam/2) >= c R^(lam h - eps)` from ENV-3(a); the needed exponent inequality is `2h <= eta + lam h`, which is (2). ∎

The same equivalence holds with `|Q_R|` in place of `|M(R^2-1) - 1|`: the two differ by at most `2 sqrt(R K_R) + 1`, which every right side in (1) absorbs.

Reading.

- `lam = 2, eta = 0` is ENV-4: always true.
- `lam < 2, eta = 0` is RH, for every such `lam`. There is no partial credit along `lam` alone.
- `lam = 1` is the finite-A shape: `|Q_R| <= C R^(1+eta+eps) sqrt(K_R)` for all `eps` if and only if `Theta <= 1/2 + eta`. The iteration `b_next = (2b+1)/4 + eta/2` of #1126 has this fixed point; the dictionary gives it in one step and shows it cannot be beaten.
- `lam = 0` is the plain Mertens bound: `|M(R^2-1)| <= C R^(1+eta+eps)` if and only if `Theta <= 1/2 + eta/2`.

Why the exponent on `K_R` is 1 (heuristic reading, not used in the proofs): `M(R^2-1) = 2M(R-1) - Q_R` and `Q_R` is a quadratic form in the frozen history `mu(a) mu(b)`. A quadratic form in a history of normalized amplitude `sqrt(K_R)` has generic size `R * K_R`. Finite A asserts linear size `R sqrt(K_R)` for this particular form. ENV-4 and ENV-5 say the quadratic size always holds and that anything below it is RH.

## 7. What this says about each route

`theta(lam, eta) := 1/2 + eta/(2 - lam)`.

| Route | Native quantity | Law in terms of `Theta` / `h` | Status of the law |
| --- | --- | --- | --- |
| FINITE-AC | `alpha_R`, `A(X)`, `q(X)` | `q(X) -> h`; `alpha_R <= C R^eps K_R`; zero-log `<=>` RH; finite A `=>` RH (converse not decided here) | PAPER_PROOF here (ENV-3, ENV-4) |
| FINITE-AC one step | `eta` in `abs(Q_R) <= C R^(1+eta) sqrt(K_R)` | holds for all `eps`-losses `<=> Theta <= 1/2 + eta` | PAPER_PROOF here (ENV-5, `lam = 1`) |
| MU-LIFT | `E(B)`, exponent `r` in `E(B^k) <= B^(o(1)) E(B)^r` | `E(B) = B^(h+o(1))`; `r = k` holds unconditionally; any fixed `r < k` `<=>` RH | PAPER_PROOF here |
| OAI-NNS recursive owner | `kappa` in `theta_next = (1 + 2 theta + kappa)/4` | Same affine map as #1126 with `kappa = 2 eta`; fixed point `(1+kappa)/2 = theta(1, kappa/2)`; "`kappa < 2 theta - 1`" is "`eta < theta - 1/2`" | algebra, plus ENV-5 |
| CORR4 | `beta` in `Corr4PowerFirstOwnerGram A beta` | `corr4PowerFirstOwnerGram_iff_mertensPowerBound` (#1021): the `beta` coordinate is the Mertens exponent | PROVED_IN_LEAN_ON_MAIN (repo) |
| CODIV | energy exponent | `M(X)^2 = O(X^(2b+eps)) <=> Theta <= b` | repo identification |
| VF-LOW, SAT, JOH | prime-side walls at `R^2` | classical: `psi(x) - x = O(x^(1/2+h) log^2 x)` and `Omega_pm(x^(1/2+h-eps))`, so a one-sided wall forces `h = 0` | classical; not re-derived here. A prime-side ENV-2 involves `zeta'(rho)` |
| NYMAN | `d_N` | classical: `d_N -> 0 <=>` RH (Báez-Duarte); Beurling: density in `L^p(0,1)` `<=>` no zeros in `Re s > 1/p` | classical; not checked against the repo's weighted-`a` formulation |
| BLOCK | — | refuted at `R = 549`; unaffected | — |

Every row measures the same number. A certified upper bound `Theta <= b` from any source propagates to every row at once. The current certified `b` gives `h <= 3/8 - 7/(64 N_pack)`.

## 8. Consequences for the agent program

1. **Merge nodes.** `OPEN-AMPLIFICATION-SUBPOWER`, the one-step FINITE-AC candidate of the 2026-11-10 directive and `OPEN-MU-LIFT` / `MECH-MU-LIFT-SUBCRITICAL` are equivalent to each other: each is RH, or `Theta <= 1/2 + eta` in its fixed-exponent form. The recursive owner's contraction aims at the same fixed point through the same affine map. Work on one is work on all; they should not be scheduled as independent levers.
2. **Score proposals before working on them.** A proposed inequality in the frozen-root coordinates has parameters `(lam, eta)`. It is new for RH_Lean only if `theta(lam, eta) < 7/8 - 7/(64 N_pack)`, and it beats the public record only if `theta(lam, eta) < 0.873346`. At `lam = 1` the second condition reads `(M(R^2-1) - 1)^2 <= C R^(2.7467) K_R`. Anything weaker is already implied by the certified exponent through ENV-5.
3. **Close the "true K_R" item.** The scoreboard's unpaid term for FINITE-AC ("using K_R >= 1 loses historical feedback strength") is settled: the true `K_R` gives exactly `q -> h`. No further subpower gain can come from the envelope.
4. **Structural arguments must pass the planted-zero gate** (section 9).
5. **First-bad arguments need a high-zero input.** By the contrapositive in section 4, a clean history up to `B` excludes only zeros whose height is below a power of `B`. A first-bad contradiction that uses history alone cannot reach RH; the detector's moment input is what handles high zeros.
6. **Leaderboard.** `nearUniformSlotCount` has no numeral, so the certified exponent cannot be stated as an explicit rational today. The explicit candidate is `7/8 - 1/2400000000` once FFR3 and FFR4 compile. It would be listed as a non-record entry.

## 9. Falsifier T1 — planted-zero model

```text
F_a(s)  = zeta(s) (1 - 2^(a-s))                   Euler product, pole at 1, zeros on Re s = a
f       = coefficients of F_a :  f(n) = 1 - 2^a [2 | n]
g       = Dirichlet inverse of f :  g = mu * t,  t(2^k) = 2^(a k)
M_g(x)  = sum_k 2^(a k) M(x / 2^k)
Q^g_R   = sum_{a',b<R} g(a') g(b) F1((R^2-1)/(a' b)) = 2 M_g(R-1) - M_g(R^2-1),    F1(y) = floor(y) - 2^a floor(y/2)
```

The frozen-root identity holds verbatim with `floor` replaced by `F1`, and `F1(y) = (1 - 2^(a-1)) y + O(1)`. ENV-1 and ENV-2 hold with `f`-weighted kernels (the same `kappa0` works; the kernel is bounded at the planted zeros). So the envelope law holds in the model with `h = max(a, Theta) - 1/2`, which is at least `a - 1/2 > 0` whatever the truth about zeta: ENV-4 is true there and finite A is false there.

Use: any argument for finite A, finite C, or a subcritical lift that never uses a property of `mu` missing from `g` (boundedness `|mu| <= 1`, squarefree support, the exact floor) proves a false statement in T1 and is therefore wrong. T1 does not test arguments that do use `|mu| <= 1`; in the model `sum_{n<=x} g(n)^2` is already of size `x^(2a)`.

## 10. Numerical record (ENV-6, FINITE_EVIDENCE)

Exact census of the repo objects, `2 <= R <= 100000` (`X` up to `10^10`), from `envelope_census.c`:

| Range of R | max `alpha_R` | at R | `M(X_R)` there |
| --- | --- | --- | --- |
| 2–9 | 1.00000 | 2 (and 3) | −1 |
| 10–99 | 0.16667 | 14 | −6 |
| 100–999 | 0.12052 | 548 | 234 |
| 1000–9999 | 0.13963 | 5561 | −2544 |
| 10000–100000 | 0.21524 | 88130 | 50077 |

`K_R = 1` for `2 <= R <= 5` and `K_R = 3/2` for `6 <= R <= 100000` (set by `M(5) = -2`). `E(B) = 1` on the whole range. `max |M(n)|/sqrt(n)` for `1000 <= n < 10^10` is `0.570591` at `n = 7766842813`. The decade maxima at `R = 548` and `R = 5561` fall at the repo's existing falsifier roots (`CE-BLOCK-R549` is the neighbouring root, `CE-CORR4-R5561` the same one), a consistency check on the objects.

These numbers are flat and carry no information about the open question: with `K_R` constant, `alpha_R` is just `(M(X_R)-1)^2/(1.5 R^2)`. A zero off the line above the verified height need not move `K_R` until `R` is astronomically large. Finite scans of `alpha_R` should not be read as evidence for finite A.

Kernel checks, from `envelope_kernel_check.py`: identity ENV-1 verified to `6e-11` at `Y <= 20000` (at a zero and at a non-zero); kernel sup over 411 sample points `19.2`, `33.5`, `52.0` at the first three zeros (bounds `C_rho = 415`, `906`, `1278`), against growth `153 -> 15516` for `u = 1e2 -> 1e6` at the non-zero `0.5 + 10i`; ENV-2(a) verified for `Y = 10^2 ... 10^6`.

Planted-zero model, from `envelope_toy_falsifier.py`, `2 <= R <= 3162`:

| `a` | law `2a-1` | fitted slope of `K_R` | fitted slope of running max `alpha` | sup `alpha_R` | sup critical ratio `abs(M_g(X_R)-1)/(R K_R)` |
| --- | --- | --- | --- | --- | --- |
| 0.80 | 0.60 | 0.636 | 0.553 | 148.0 | 3.31 |
| 0.65 | 0.30 | 0.358 | 0.219 | 12.4 | 2.14 |

The slopes are rough fits over a short range. The qualitative behavior is the law: `alpha_R` grows, the critical ratio stays bounded.

Bite test in the same model. At a planted zero `s0 = a + 2 pi i / log 2` the `f`-weighted kernel is bounded (sup `15.8` for `a = 0.8`, `14.2` for `a = 0.65`, over 2600 sample points) and the `f`-weighted ENV-1 holds to relative error `5e-14` at `Y = 20000`. The resulting lower bound for `int_1^Y |M_g| dx/x` stays within a constant factor of the true value across `Y = 10^3 ... 10^7`: factor 7.7 to 8.5 for `a = 0.8`, 20 to 21.4 for `a = 0.65`. So when a zero really is off the line, ENV-2 captures the true order `Y^beta`; for zeta in the computable range it is trivial only because every known zero has `beta = 1/2`.

## 11. Lean targets (statement sketches, NOT compiled)

Names follow main. These are `Prop` definitions in the repo's statement-only style; proofs are the work.

```lean
-- research/…, importing RHLean.Proof.SquareRootAmplificationLogGrowth and research.MERTENS_CONVERSE_IDENTIFICATION
open RHLean.Proof RHLean.Analysis.MertensExponent

def envelopeKernelConstant (ρ : ℂ) : ℝ := 1 + ‖1 - ρ‖ * (1 + ‖ρ‖ / ρ.re)

/-- ENV-2(c). -/
def ZeroForcedHistoricalEnvelope : Prop :=
  ∀ ρ : ℂ, NontrivialZetaZero ρ → ∀ R : ℕ, 2 ≤ R →
    (‖1 - ρ‖ / ‖ρ‖ * ((R : ℝ) ^ ρ.re - 1) - (1 + envelopeKernelConstant ρ) * Real.log R)
        / (2 * Real.sqrt 2 * envelopeKernelConstant ρ * Real.sqrt R)
      ≤ Real.sqrt (squareRootHistoricalK R)

/-- ENV-3(b).  `max _ (1/2)` keeps the statement true under the empty-zero-set convention. -/
def AmplificationLogRatioLimit : Prop :=
  Filter.Tendsto squareRootAmplificationLogRatio Filter.atTop
    (nhds (max zetaRightmostRealPart (1 / 2) - 1 / 2))

/-- ENV-5 left side; ENV-4 is `EnvelopeBound 2 0`. -/
def EnvelopeBound (lam eta : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ R : ℕ, 2 ≤ R →
    |((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ)|
      ≤ C * (R : ℝ) ^ (1 + eta + ε) * squareRootHistoricalK R ^ (lam / 2)

def EnvelopeDictionary : Prop :=
  ∀ lam eta : ℝ, 0 ≤ lam → lam < 2 → 0 ≤ eta →
    (EnvelopeBound lam eta ↔ zetaRightmostRealPart ≤ 1 / 2 + eta / (2 - lam))

-- corollary:  SquareRootAmplificationZeroLogGrowthStatement ↔ zetaRightmostRealPart ≤ 1 / 2
```

Suggested order. (i) `EnvelopeBound lam eta → zetaRightmostRealPart ≤ 1/2 + eta/(2-lam)`: needs only `growthAtMost_iff_rightmost_le`, the square-endpoint interpolation `|M(x) - M(X_R)| <= 2R` and the trivial upper bound on `K_R`; no new analysis. At `lam = 1, eta = 0`, combined with `squareRootAmplificationZeroLog_eventually_native_envelope`, it gives the full consumer `SquareRootAmplificationZeroLogGrowthStatement → zetaRightmostRealPart ≤ 1/2`, which main does not yet have. (ii) ENV-1 in the discrete form of section 4. (iii) Euler–Maclaurin at a real cutoff with the bound on `E_s(u)`. PNT+ should already contain the integer-cutoff version (from memory: `riemannZeta0` and `Zeta0EqZeta` in `ZetaBounds.lean`; not checked against the pinned commit). (iv) ENV-2, then ENV-3 to ENV-5.

Registry edits to consider after referee review: record `OPEN-AMPLIFICATION-SUBPOWER` and `OPEN-MU-LIFT` as equivalent to RH with a proved-equivalence milestone, in the style of `MILESTONE-CORR4-POWER-IFF`; mark `OPEN-FINITE-AC` as implying RH with the converse undecided; replace the FINITE-AC quantitative line by `lim q = h <= b - 1/2`.

## 12. What is not claimed

- No proof of RH, of finite A or finite C, or of any exponent below the certified one.
- No effective constants in ENV-3 to ENV-5 when `h > 0`: they depend on a zero within `eps` of the supremum. ENV-2 is fully explicit.
- No Lean. No audit of the OpenAI import, of #1119, or of the IR/FFR paper proofs.
- The prime-side and Nyman rows of section 7 are classical statements quoted for orientation, not re-derived.
- T1 is a gate for algebra-only arguments. It says nothing about arguments that use `|mu| <= 1`.

## 13. Draft index entry for `EXTERNAL_HANDOFFS.md`

```markdown
### 2026-11-15 — Universal envelope law for the frozen-root coordinates (direct Claude session)

**[Read the complete handoff](external/2026-11-15/universal-envelope-law-handoff.md).** Based on main `59612bc8` and agent-reports `5a7f05d5`. Paper proofs and finite evidence only; no Lean; RH and every exponent gain remain OPEN.

- **EXT-20261115-ENV-1 / EXACT_IDENTITY:** `int_1^Y M(x) kappa(Y/x) dx/x = int_1^Y kappa0(v) dv/v` for `kappa(u) = sum_{n<=u} kappa0(u/n)`.
- **EXT-20261115-ENV-2 / PAPER_PROOF, explicit:** every zeta zero `rho = beta + i gamma` forces `sqrt(K_R) >= (|1-rho|(R^beta-1)/|rho| - (1+C_rho) log R)/(2 sqrt(2) C_rho sqrt(R))` for all `R >= 2`, `C_rho = 1 + |1-rho|(1+|rho|/beta)`; same for `E(B)`.
- **EXT-20261115-ENV-3 / PAPER_PROOF:** `log K_R / log R -> 2h` and `q(X) -> h`, `h = max(Theta,1/2) - 1/2`. Hence `SquareRootAmplificationZeroLogGrowthStatement <=> RH`, and `limsup q <= b - 1/2` for every certified `b`.
- **EXT-20261115-ENV-4 / PAPER_PROOF:** unconditionally `|M(R^2-1) - 1| <= C_eps R^(1+eps) K_R` for all `R >= 2`; `E(B^k) <= C_eps B^eps E(B)^k`.
- **EXT-20261115-ENV-5 / PAPER_PROOF:** for `0 <= lam < 2`, `eta >= 0`: `|M(R^2-1) - 1| <= C R^(1+eta+eps) K_R^(lam/2)` for all `eps`, `R` `<=> Theta <= 1/2 + eta/(2-lam)`. One-step FINITE-AC, zero-log amplification and MU-LIFT subcritical are one statement; the recursive-owner `kappa` recursion is the same affine map.
- **EXT-20261115-ENV-6 / FINITE_EVIDENCE:** exact census to `R = 10^5` (`K_R = 3/2`, `alpha_R <= 1`); planted-zero model T1 where the same algebra holds, ENV-4 holds and finite A fails.
- **EXT-20261115-ENV-7 / STATUS:** certified gain `7/(64 N_pack) <= 3.3e-11` (no numeral for `N_pack`); paper endpoint `1/2400000000`; public record about `0.873346` on 2026-11-13.
- **Routing:** Referee test ENV-2 and ENV-5 first, including the T1 gate; Lean may start with the direction of ENV-5 that needs no new analysis; Coordinator decide whether to merge the equivalent nodes in the registry.
```

## Reproduction

```bash
gcc -O2 -Wall -Wextra -o envelope_census envelope_census.c -lm
./envelope_census 100000 env_1e5.csv          # about 4 minutes
python3 envelope_kernel_check.py              # numpy, mpmath; about 1 minute
python3 envelope_toy_falsifier.py             # numpy; about 2 minutes
```

## References

- D. R. Johnston, T. Trudgian, "A round of Pintz to celebrate oscillations in sums", arXiv:2511.09978.
- J. Pintz, "Oscillation of partial sums of the Möbius function and zeros of Riemann's zeta function", arXiv:2608.24878.
- A. Beurling, "A closure problem related to the Riemann zeta-function", Proc. Nat. Acad. Sci. 41 (1955).
- Quasi-Riemann threshold timeline: https://discoveria.ai/en/frontieres/quasi-riemann/ (mirror of the GTimG/QuasiRiemannTracker leaderboard), fetched 2026-11-15.

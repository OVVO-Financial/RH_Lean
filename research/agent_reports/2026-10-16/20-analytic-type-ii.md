# RH_Lean agent daily report — 2026-10-16 / RH | Analytic Type II

**Status:** COMPLETED
**Invocation:** pass 3 of 7 inside **one unified manual AI research cycle** (Claude, single session, owner-requested). Not a scheduled invocation.
**Run ID:** `RH-UNIFIED-MANUAL-20261016T0806-0400` · report written 2026-10-16T09:07-04:00
**Result classes:** `IDENTITY_ONLY` (exact anatomy), `PAPER_PROOF` (control characterization, strength calibration, cut-mode spectrum), `FINITE_COMPUTATION` (diagnostics), `NO_NEW_BOUND` for MU-LIFT and for the canonical endpoint.

## A. Provenance

Same authority as the cycle checkpoint: `main@69e44d7c…`; `AGENTS.md` `c40e9bc1…`; contract `b945dec4…`; brief `80b865bf…`; protocol `03d07880…`; amplification budget `3beff1f7…`. Sources: finite-prefix extension `0474a156…`, signed lift `bb028fc1…`, signed hyperbola `d199571f…`, converse identification `c15bdfcb…`. Today Analytic was `TODAY=PENDING` before this cycle; yesterday's Analytic `fda92df0…` (Nyman rigidity, analytic-1..3) is carried forward unchanged. Upstream this cycle: Owner claims `20261016-owner-1..6` (pass 2).

## B. Objective and independent fact

Seek an independent quantitative MU-LIFT gain `E(B^k) <= G(B) E(B)^r`, `r < k`, `G = B^o(1)`, full prefix coverage, or a distinct analytic input.

**Independent facts learned.** (1) The genuine floor kernel splits exactly into a linear prefix term, two quadratic "critical" pieces and a sawtooth bilinear form; the smooth quadratic piece is controlled only through the global identity `sum mu(n)/n = 0`, i.e. by information outside the prefix. (2) Among finitely supported prefix inputs, amplification fails **iff** `sum a(n)/n != 0` — the exact arithmetic condition behind #954's control. (3) Any fixed `(r, g)` whole-interval inequality below an explicit threshold implies a zero-free strip: the relaxed MU-LIFT has **no unconditional milestone short of quasi-RH**. (4) With owner-4/5, the raw ledger's sector deviations form a "cut-mode spectrum": target scale only at fixed-ratio cuts (where they are RH-equivalent), unconditionally supertarget at cuts `x^theta`, `1/2 <= theta < 2/3`.

**Quantitative change:** none. No amplification inequality, no bound on the canonical endpoint.

## C. MU-LIFT normalized-loss record

- **k:** 2 (chain `B_(j+1) = B_j^2`); no higher-order estimate attempted beyond the identity.
- **r, G, g:** none proved. Termwise prefix bounds give at best `(r, g) = (1, 1/2)` for the bilinear pieces and `g = 1` for the smooth piece without the tail identity — both at or beyond the trivial line (analytic-3).
- **Coverage:** identities hold for every integer `X` in `[N, (N+1)^2)`; no estimate claimed.
- **Independent arithmetic input:** none found. Smallest unpaid object identified: the hyperbola corner of the sawtooth form (section G).
- **Actual-gain equivalence:** respected; nothing assumes the minimal gain is subpower.
- **Controls:** sparse control explained exactly by analytic-2; `r = k` and vanishing-gap synthetic countermodels unchanged.

## D. Claims

### Claim `20261016-analytic-1` — exact signed anatomy of the floor kernel

For integers `N >= 1`, `N <= X < (N+1)^2`, with `m_N = sum_{n<=N} mu(n)/n`, `psi(t) = {t} - 1/2`, all sums over `i, j <= N`:

```text
M(X) = 2M(N) - Q_N(X)                                       (merged identity)
     = 2M(N) + (1/2) M(N)^2 - X m_N^2 + Psi_N(X),           Psi_N = sum mu(i)mu(j) psi(X/(ij))
     = 2M(N) + K1 - K2 + K3,   K1 = (1/2) sum_{ij<=X} mu mu,  K2 = X sum_{ij<=X} mu mu/(ij),
                                K3 = sum_{ij<=X} mu mu psi(X/(ij)).
```

**Proof.** `floor(t) = t - 1/2 - psi(t)`, and pairs with `ij > X` contribute `floor = 0`. **Status:** `IDENTITY_ONLY`. Checked exactly (`Q_N(X)` in int64, identity `M(X) = 2M(N) - Q_N(X)` exact) and to `<= 3e-12` (long double decomposition) at `N = 1000, 3162, 10000` and `X in {N, N^1.25, N^1.5, N^1.75, (N+1)^2-1}`.

**Diagnostics (`FINITE_COMPUTATION`).** `E(N+1) = 1` at every tested `N` (attained at `n = 1`), so normalisation is by `sqrt(X)`. The four-term form is non-uniform: at `N = X = 10^4`, `(1/2)M(N)^2 = 264.5 = 2.65 sqrt(X)` against `M(X) = -23`, cancelled by `Psi_N = -241.5`; in general `(1/2)M(N)^2` reaches `E^2 X/2` at the start of the interval, a supercritical piece. The hyperbola-truncated pieces are uniform at the tested scales and cancel: at `N = 10^4`, `X = 10^7`, `K1 = 1429.0 (0.45 sqrt X)`, `K2 = 2690.9 (0.85 sqrt X)`, `K3 = 2344.9 (0.74 sqrt X)`, `M(X) = 1037 (0.33 sqrt X)`.

**Structural reading.** `K2 = X sum_{i<=N} (mu(i)/i) m(min(N, X/i))` involves `m(y) = M(y)/y + int_1^y M(t) t^-2 dt`. From the prefix hypothesis `|M(t)| <= E sqrt(t)` alone, `|m(y)|` is only `O(E)`; the true size `O(E/sqrt(y))`-type uses `int_1^inf M t^-2 dt = 0` (the identity `1/zeta(1) = 0`), i.e. future values of `M`. So the smooth critical piece couples the prefix to the entire tail.

### Claim `20261016-analytic-2` — finitely supported controls: amplification fails iff `P_a(1) != 0`

Let `a` be finitely supported (support in `[1, N]`), `A(N) = sum a`, `P_a = sum a(n)/n`. The Newton lift `T(a) = 2a - a*a*1` has, for every `X >= N`,

```text
sum_{n<=X} T(a)(n) = 2A(N) - X P_a^2 + (1/2) A(N)^2 + Psi_a(X),   |Psi_a(X)| <= (1/2)(sum|a|)^2.
```

Hence the lifted sum grows linearly iff `P_a != 0`, and is bounded iff `P_a = 0`. #954's control `a = (1, -1)` has `P_a = 1/2`, giving `-X/4 + O(1)` (matches the committed formula `-X + 2 floor(X/2) - floor(X/4)`). **Status:** `PAPER_PROOF`. **Consequence:** the arithmetic condition a genuine-Mobius argument must exploit to exclude the control is exactly the smallness of `m_N`; but for `mu` truncated at `N`, `|Psi|` has trivial size `~0.37 N^2`, so the whole difficulty is quantitative (section G).

### Claim `20261016-analytic-3` — strength calibration: no milestone short of quasi-RH

**Statement.** Fix `0 <= r < 2`, `g >= 0`, `C >= 1`, a chain `B_j = B_0^(2^j)`. If for all large `j` and every integer `X in [B_j, B_j^2)`

```text
|M(X)| <= C B_j^g E(B_j)^r sqrt(X),
```

then `M(n) << n^(1/2 + 2g/(2-r) + eps)`, hence (merged #948/#949 forward map) every zero has `Re rho <= 1/2 + 2g/(2-r)`. With the inequality for **every** `B` the conclusion improves to `1/2 + g/(2-r)`.

**Proof.** `E(B_(j+1)) <= max(E(B_j), C B_j^g E(B_j)^r)` gives `u_(j+1) <= max(u_j/2, (r/2)u_j + g/2) + o(1)`, so `limsup u_j <= g/(2-r)`; for `X in [B_j, B_(j+1))`, `|M(X)|/sqrt X <= C X^(g + r u_j)`. Every-`B` version: take `B ~ sqrt(X)` and solve `u <= (g + r u)/2`. ∎ **Status:** `PAPER_PROOF` — a conditional implication, **not** a gain.

**Calibration.** A nontrivial (strip `Re s > theta`, `theta < 1`) conclusion needs `g < (2-r)/4` on the chain (`g < 1 - r/2` with every-`B` coverage). Unconditional knowledge (`|M(n)| <= n exp(-c (log n)^(3/5-o(1)))`) gives such an inequality only with `g -> 1`, where the consumer concludes nothing. So **every fixed nontrivial `(r, g)` is a quasi-Riemann statement** (no zeros in a fixed vertical strip), beyond the Vinogradov–Korobov region; `g -> 0` is RH. The amplification budget's relaxation is correct but does not create an easier intermediate target.

### Claim `20261016-analytic-4` — cut-mode spectrum of the raw ledger

Combining owner-1..5 with Lemma M (owner-4):

```text
cut at fixed ratio y = c x:          sector deviation = epsilon(cx)-mode, target scale; B-sector bound <=> RH (owner-5)
band [y, 2y), y = x^theta, 1/2 <= theta < 2/3:
                                     deviation = F_R (E(2y) - E(y)) + O(y/log^2 y)
                                     not O(x^(1 - theta/2 - delta)) unconditionally; O(x^(1-theta/2)) under RH.
```

For `theta < 2/3` the explicit band error `O(y/log^2 y)` is smaller than the mode, so Lemma M applies (same proof as owner-4). **Status:** `PAPER_PROOF`. **Meaning:** the only greatest-prime cuts at which the two sectors deviate at target scale are fixed-ratio cuts, and there each sector alone is RH-equivalent; every intermediate cut produces a provably supertarget mode that must cancel against the other side before any norm is taken.

## E. Hilbert-space / analytic alternatives

No new Hilbert-space input was found. The Nyman–Beurling rigidity results (2026-10-15 analytic-1..3, accepted by today's Referee) remain a distinct carrier with no decay estimate. The only analytic input used this cycle — the singularity of `log zeta` at `rho_0` — is a tool for *lower* bounds (oscillation), not an upper estimate.

## F. Complete-source audit

All signed terms of `Q_N(X)` retained (`K1`, `K2`, `K3`, the linear term and all cross rows). No absolute value is taken before the anatomy; the termwise bounds in section C are reported only to locate the obstruction. MU-LIFT and the raw ledger remain separate carriers; analytic-4 concerns only the raw ledger.

## G. Precise unpaid inequality (MU-LIFT)

The smallest genuinely new input would be square-root cancellation in the hyperbola corner of the sawtooth form,

```text
| sum_{i,j<=N, X/H < ij <= X} mu(i) mu(j) psi(X/(ij)) |  <=  G E(B)^r sqrt(X),   r < 2, G = B^o(1),
```

uniformly over `B <= X < B^2`, together with the matching treatment of `K1, K2`. There `X/(ij) in [1, H)`, the sawtooth does not oscillate, and all cancellation must come from the prefix Mobius values: it is a Type II bilinear problem at the square-root scale. By analytic-3, even a fixed power saving here is quasi-RH.

## H. Decisions and handoffs

- **MU-LIFT:** `REVISE` — keep only as a structural study of the `K3` corner (exact reflection/involution identities, sizes by region), not as a near-term quantitative route.
- **FD-TRANSPORT:** support Owner's `SUSPEND` recommendation; its non-tautological revival would need a sieve identity whose remainder is this same Type II corner.
- **Census:** analytic-1 diagnostics done; no larger runs requested.
- **Referee:** audit analytic-2's error bound, analytic-3's recurrence (including `r < 1`), analytic-4's range `theta < 2/3`.
- **Lean:** a generic consumer for analytic-3 is formalizable but would be conditional; not requested this cycle.

## I. Reproducibility

`mulift_anatomy.cpp` (sha256 `978782969bcfa9b41816b4cd7e5292becfc7465647bf667a09b51b4df8dcdd64`), output `mulift_anatomy.csv` (sha256 `550e1cdd982f9be1ee10370e2ab0258b32f77311276b24adc2d408bb0e56608a`); `g++ -O2 -std=c++20`, linear Mobius sieve to `10^8 + 2*10^4 + 1`. Files under `research/agent_reports/2026-10-16/manual-cycle/`.

## J. Resume capsule

Reuse analytic-1..4. Next question: does the `K3` corner admit an exact signed reflection (e.g. `ij <-> X/(ij)` duality or a Mobius involution) that shortens it? Avoid: claiming any `(r, g)` from finite ratios; treating analytic-3 as progress. No RH proof claim.

# RH_Lean Coordinator synthesis — 2026-10-17 manual cycle

**Status:** PARTIAL / IN_PROGRESS — early durable checkpoint (Phase 1 plan). Superseded by the final synthesis in this same file.
**Execution:** one unified manual AI research cycle (Claude, single session), explicitly requested by the repository owner; seven role passes run sequentially plus a final Coordinator pass. Not seven scheduled invocations; no agent was launched, scheduled or simulated; no schedule was changed.
**Run ID:** `RH-UNIFIED-MANUAL-20261017T1155-0400` · start 2026-10-17T11:55:23-04:00 · checkpoint 2026-10-17T12:20-04:00
**Folder:** `research/agent_reports/2026-10-17/manual-cycle/RH-UNIFIED-MANUAL-20261017T1155-0400/` (`00-coordinator-am.md` and `90-coordinator-pm.md` are byte-identical mirrors of one synthesis).

## Authority at intake

- `main@897563a14e9c04fcd2e4fb6d8e50cea7677854c7` (merge of #966). PRs #915, #919, #931, #961, #964, #965, #966 all `merged=true` (live REST check); no open PRs.
- Read in full at that revision: `AGENTS.md`, `CURRENT_PROOF_CONTRACT.md`, `docs/DYNAMIC_RESEARCH_AGENTS.md`, `docs/FACTOR_DEPTH_RESEARCH_BRIEF.md`, `docs/CROSS_COORDINATE_LOW_QUOTIENT_RESEARCH_2026_10_17.md`, `docs/MERTENS_AMPLIFICATION_BUDGET.md`.
- Reports read: 2026-10-17 Wheel, Census, Referee, Lean (scheduled); 2026-10-16 all eight files including the scheduled Coordinator/Owner/Analytic continuations (claims coordinator-3/4, owner-7/8, analytic-5..7); `EXTERNAL_HANDOFFS.md` with EXT-20261017-XCOORD-1..3 and EXT-20261017-HECKE-1..3.

## Phase 1 — integration and the question for this cycle

Exact relations already on main or accepted on paper (verified against source; none is new here):

```text
M(X) = A_y - T_y,              T_y = H_y + I_y                    (original smooth/transport, positive cofactor transform)
M(X) = P0(X;y) - 2 P1(X;y),    y = floor(sqrt X), BAD = 0         (Hecke #919 root cutoff)
M(X) = sum_t K(t) B_X(t) = sum_t P36(t) D_X(t)                    (compiled signed Abel, |P36| <= 4)
B_X(t) = C6(floor(X/t)) - C6(floor(X/(t+1))),  V_high <= 2 sqrt X (census-2, paper)
```

**Integration step (new, to be proved in Phase 3):** with `T^chi_y := H_y - I_y = sum_(y<q<=X) chi_-3(q) M(floor(X/q))`, the Hecke layers are the original layers with one twisted transform added and subtracted:

```text
P0 = A_y + T^chi_y,     P1 = (T_y + T^chi_y)/2,     P0 - 2 P1 = A_y - T_y = M.
```

`A`, `T`, `M` are zeta-only objects (Dirichlet series built from `1/zeta`). `T^chi`, `P0`, `P1`, `C6`, `B_X`, `D_X` also see `L(s, chi_-3)`: the coefficient series of `a6` is `1/[zeta(s) L(s,chi_-3)(1-3^-s)(1-4^-s)]`, and the K-pairing multiplies back by `L(s,chi_-3)(1-3^-s)(1-4^-s)`. **Working hypothesis H-L:** the K-pairing is the only operation in these coordinates that annihilates the `L(s,chi_-3)` content, so (i) no joint use of the three identities can transfer a zeta-only bound into an `ell^1` restriction on `D_X`, and (ii) any uniform bound on the absolute — or even the unweighted signed — low return would itself prove a zero-free statement for `L(s,chi_-3)`. If true, the L-VAR target is not an easier intermediate but a strictly broader one (zeta *and* `L(s,chi_-3)`), and a signed matched-source inequality written purely in Möbius coordinates is the only kind that can be weaker than it.

## Plan: what each pass must discover (not verify)

- **Owner:** check the crosswalk and both sign conventions against `squareRootSmoothMass`, `squareRootTransportMass`, `squareRootTransportPrimeFirst`; establish the twisted-transport dictionary at source level; decide whether original owner pairing constrains `D_X(t)-D_X(t+1)`-type differences or only relocates `T^chi`; quantify the original matched core `Born - T` (does the bounded-K matched premise of `SquareRootLowPrimeSmoothTransportRecoupling` survive the exact prime-sampled Mertens term?).
- **Analytic:** prove or refute H-L as theorems with explicit quantifiers; give the exact exponent window of `V_low` in terms of the zeros of `zeta * L(s,chi_-3)`; decide whether the phenomenon is specific to `chi_-3` or forced for every periodic-kernel representation; state one actual unconditional bound, however weak; place MU-LIFT and SB-7/8 relative to H-L.
- **Wheel:** independent incidence audit (q=R, quotient cells `c_X(u)`, `X=380`, `r+1` boundary, wheel-1 packet sign coherence); integer-endpoint tests of any proposed map between quotient residue classes, layers or the low/high hyperbola reflection; explicit counterexamples.
- **Census:** pre-registered exact regressions at `R=7,13,103,317,1027`, `X=380` and square neighbours, plus a pre-registered spectral discriminator of H-L (pre-registration sha256 `610704afc6fda454671403e0e99debacaebb0297331657e0d73b431600caf706`, 2026-10-17T12:15:21-04:00).
- **Referee:** same-session adversarial self-audit of every new claim (recorded as such); independent verdict on scheduled Census claim `20261017-census-2` (a different agent's claim).
- **Lean:** formalize only nonduplicate accepted mathematics via a draft PR with exact-head Actions; otherwise report `NO_NEW_THEOREM_TO_FORMALIZE`.

Competing routes retained: MU-LIFT dyadic kernel (parity + half-scale, Oct 16 analytic-5 paid the boundary sector), SB-7/8 square-shell energy, Nyman, finite A/C, native VF/#915 source. Canonical `VFCanonicalSquareVonKochStatement` remains OPEN.

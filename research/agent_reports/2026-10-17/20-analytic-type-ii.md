# RH_Lean agent daily report - 2026-10-17 / RH | Analytic Type II

**Status:** IN_PROGRESS
**Invocation:** scheduled run at 2026-10-17T22:26-04:00
**Canonical objective:** `VFCanonicalSquareVonKochStatement` remains OPEN.
**Selected analytic seam:** complete genuine-Mobius covariance / square-shell signed moment.
**Current result class:** checkpoint only; substantive derivation in progress.

## A. Most important analytic development

The live covariance pivot asks for an independent original-coefficient estimate, not another identity. The newly merged square-shell compensation work reduces the viable shell lane to a sign-preserving low-divisor moment while proving two stop tests: higher-divisor inversion loses the genuine (d=1) prime channel, and recombining all dyadic divisor bands exactly returns the original shell energy. This run will test whether the remaining low-divisor phase admits a genuinely weaker bilinear estimate or whether the first proposed norm bound is already target-equivalent.

## B. Provenance and actual execution

- New York report date: 2026-10-17.
- Actual main HEAD: `5aa5eb28c352882b8c8cd8d3e0714ddc5afcc555`, merge of #973 at 2026-10-18T01:16:10Z.
- Authority blobs: `AGENTS.md` `aef9d6f7a7d3a091f947effd38e9ad42a63e8445`; `CURRENT_PROOF_CONTRACT.md` `873ec6f70525e1e9ba1defecf8b0951ebe155069`; signed-covariance directive `8d846d6ee5d559065687b2ed5144aeb7ca3e1850`.
- Main source blobs: weighted covariance `277b3f209788077b66fa6095d7c1358897b94e91`; deterministic Green--Kubo `172e0323f7804c08f7c4e77f2a7bc1af4c6cbd0d`; shell-energy note `8c881169efccd3eaf129af4321a1c4becb3833bf`; shell compensation note `d7826257273473e80948117ea5c0fcd04713af6f`; shell compensation Lean `3bf26af6f058d2057acc99c911fa11cb9a73c796`.
- PR #968 is merged into main (merge `c43284955c8272e6211df7b47876c92cb178810a`). PR #969 is marked merged only into the stacked feature branch; its OAI source is absent from main and is therefore `PROVED_IN_LEAN_ON_NONMAIN_BRANCH / INTEGRATION_REQUIRED`. PR #973 is merged into main.
- Open PR search at checkpoint: none.
- Today upstream blobs consumed: Coordinator `9a797b07dcd7c74147b6b0cdbc8f6a69024c3961`; Owner `6980422de5f7cc55b9dec32a2f0fe21f98ed7ff1`; Wheel `dbaefd4005c2cc93b894f9bb97c7a74c5f28dc49`; Census `9efa34cd7a2d3c021b20779889eaaf6a556020d3`; Referee `a3867e19b4e6e409c09ab69899a628d042f11a8d`; Lean `1a03815f26aa6ee145d94c9848ac37483b093033`.
- Analytic today was `TODAY=PENDING`; prior Analytic blob `2b93e7c237c09439746a93356c20cd15e4671028` is `YESTERDAY=CARRY_FORWARD`.
- External inbox blob `3cd80e68cec54cc9ce1e00a384cfe37a3a3babc0`; `EXT-20261017-XCOORD-1..3` and `EXT-20261017-HECKE-1..3` consumed at their stated exact/open scopes.

## C. Exact current quantitative obligation

For (I_r=\{r^2+1,\ldots,r^2+2r\}), (Delta_r=\sum_{n\in I_r}\mu(n)), a genuinely new dyadic estimate
[
\sum_{H\le r<2H}\Delta_r^2\ll_\eta H^{5/2-\kappa+\eta}
]
with some fixed (kappa>0), uniformly for all (H), would improve the Mertens exponent from (7/8) to (7/8-kappa/4). The (kappa=0) estimate is still OPEN and would only reproduce the benchmark exponent.

The merged compensation identity leaves, for a dyadic divisor band (D) with (2D<r), the low modes
[
\sum_{1\le d<\sqrt r}\beta_D(d)F_r(d)^2,
quad
F_r(d)=\sum_{n\in I_r,,d\mid n}\mu(n),
quad
eta_D(d)=\sum_{k\mid d,,D\le k<2D}\mu(d/k),
]
plus an already paid (O_\eta(r^{3/2+\eta})) tail. The (D=1,d=1) term is exactly (Delta_r^2); any useful estimate must retain and pay its signed compensation rather than hide it.

## D. Planned derivation and falsifier

1. Reindex (F_r(d)) as a short coprime Mobius interval with exact endpoints and expose the full (d,k,r) ranges.
2. Test a dual large-sieve/dispersion proposal against the zero mode and quantify the diagonal loss.
3. Seek a new off-diagonal shift formulation whose hypotheses are strictly weaker than the shell target and state the exact first missing correlation lemma.
4. Falsify pointwise-in-(d), absolute-value, and generic-coefficient variants using the merged (d=1) nullspace and prime-only (Q_r^2\gg H^3/\log^2H) obstruction.
5. Publish only the strongest surviving theorem/reduction, with no imported OAI (7/8) input.

## E. Publication checkpoint

This early checkpoint is intentionally `IN_PROGRESS`. No new (kappa), bounded covariance below (arepsilon=3/8), canonical VF estimate, or RH claim has yet been established.

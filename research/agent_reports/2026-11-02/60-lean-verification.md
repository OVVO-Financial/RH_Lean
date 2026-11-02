# RH | Lean Verification - 2026-11-02

## Scheduled run - claim `20261102-lean-1` - 2026-11-02 05:31 EST (-0500)

**Status:** COMPLETE / PROVED_IN_LEAN_ON_PR_HEAD / CI_GREEN / REVIEW_READY  
**Invocation:** scheduled run begun 05:10 EST; RUN_ID_UNAVAILABLE  
**eta_gate:** SEARCH_BROAD; net endpoint gain after complete return remains UNKNOWN.

### Authority and continuity

Live main is `a33987e275f8a431641d3f475b71a24aa2b1437c`, the human merge of PR #1069.

Authority and toolchain evidence:

- `AGENTS.md`: `9fa5e9519e2fb6dde22217aa2a18982dafef373a`.
- `CURRENT_PROOF_CONTRACT.md`: `88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a`.
- selector: `d05c327ae694ea54b599dab0a21032a056b521f1`.
- broad-search policy: `b5c063c51556ba57c4b25bcc380a606fa8daa207`.
- complete-return contract: `16838f7f3c8724b970f8b8ece0bceaab9418066d`.
- research engine: `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55`.
- Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- manifest blob `a34d142c3d75a602a8b0f8241a4fb504d5c7c5a4`; toolchain blob `ba8ebf2dbaf6a668cd2a0e086186d6d569b69ff5`.

No proof PR was open at intake. The merged odd-Mobius telescope and truncated-tail interface were checked as completed structural work and were not duplicated.

Consumed today's Owner `3110b464e623430dd07c7fc81d3421b3caffa824`, Analytic `54c30c65ea6d9923bc9b25c01f02adbbefaf991b`, Wheel `f3457205aa4a8c2bf9696b30501e89598fd10fc2`, Census `d7655dc225d559ce5d475c31fba97f5b82ab49e2`, and Referee `45c702cf93b567b889a6122f10c9a16161991517`. Today's Coordinator/Proof Architect and prior Lean reports were `TODAY=PENDING`. The complete 2026-11-01 set was used as `YESTERDAY=CARRY_FORWARD`, including prior Lean blob `6aa7197c4169a70debed607e12f4639218cd21b6`. External handoffs blob `038018145c0fddb2f6306c0712373adf9cd1ea52` has no entry newer than 2026-10-18.

### Selection and mathematical review

Priority A had no active proof PR to repair. The selected Priority B candidate was Owner claim `20261101-owner-4`, independently reviewed in `20261102-referee-1` as `ACCEPT_WITH_SCOPE`.

The exact carrier is:

- outer addresses `a` in the strict square shell `R^2 <= a < (R+1)^2` with `mu(a) != 0`;
- daughter occurrences `(q,m)` with odd prime `q`, strict old-owner admission `q^2 < R`, physical address `q^2 m` in the same strict shell, and `mu(m) != 0`.

The paper argument was independently checked before coding. Nonzero Möbius support is squarefree. If `p^2 m = q^2 n` with distinct primes, coprimality forces `p^2 | n`, contradicting squarefreeness. If the primes agree, positive-factor cancellation gives `m=n`. An outer address cannot equal `q^2m`, since the latter is divisible by a prime square.

This is independent structural control. It is not target-equivalent, but it supplies no sign or bound for the remaining nonzero-shift covariance.

### Formal implementation

PR [#1070](https://github.com/OVVO-Financial/RH_Lean/pull/1070) is open, non-draft, mergeable, and review-ready.

- branch: `agent/lean-verification/20261102-lifted-mobius-address`;
- exact head: `d749898c4afd5a7c579fc4c7ddcee742832b08d9`;
- source: `research/LIFTED_MOBIUS_ADDRESS_INJECTIVITY_20261102.lean`;
- source blob: `61f98a8997d86ddbb07404284d12aebd36a67955`;
- dedicated workflow blob: `41393051815322ff55cb064f172b001504537919`.

The kernel-checked declarations are:

```lean
theorem primeSquare_mul_eq_primeSquare_mul_of_squarefree
    {p q m n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hn : Squarefree n)
    (h : p ^ 2 * m = q ^ 2 * n) :
    p = q ∧ m = n

theorem liftedMobiusDaughterAddress_injOn (R : ℕ) :
    Set.InjOn liftedMobiusDaughterAddress
      (liftedMobiusDaughterCarrier R : Set (ℕ × ℕ))

theorem liftedMobiusOuter_ne_daughterAddress
    {R a q m : ℕ} (ha : a ∈ liftedMobiusOuterCarrier R)
    (hqm : (q, m) ∈ liftedMobiusDaughterCarrier R) :
    a ≠ liftedMobiusDaughterAddress (q, m)
```

Formalization strengthened the paper lemma: equality of prime-square lifts needs squarefreeness of only one cofactor. The literal carrier theorem supplies it from `mu(n) != 0`.

### Exact-head verification

All 12 PR-triggered workflows passed on exact head `d749898c...`.

- dedicated warning-fatal proof, signatures, no-hole scan, and axiom audit: [run 41429099044](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41429099044), job `125222881085`;
- targeted Lean iteration: [run 41429099122](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41429099122);
- Lean source audits, full hosted build, declaration graph, and warning check: [run 41429099050](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41429099050), hosted job `125222880927`;
- proof inventory: [run 41429099042](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41429099042);
- public export verification: [run 41429099106](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41429099106).

Each audited endpoint depends only on `[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, new project axiom, `native_decide`, or `sorryAx` remains.

### Repair record

The proof branch was repaired from actual Actions diagnostics. Initial failures exposed only elaboration and warning issues:

1. normalized `p^2` versus `p*p`;
2. supplied the exponent to the positivity lemma;
3. converted coerced Finset membership inside `Set.InjOn`;
4. corrected accidental literal newline encoding;
5. removed an unnecessary squarefree hypothesis after warning-fatal lint identified it.

No carrier condition or conclusion was weakened. The final theorem is stronger than the reviewed paper statement.

### Significance, no-circularity, and proof gap

**Formal soundness:** `PROVED_IN_LEAN_ON_PR_HEAD` at the exact tested commit above.

**Mathematical significance:** prime-square daughter addresses are canonical on the literal nonzero-Möbius carrier, and the outer squarefree shell is disjoint from them. Exact-product congestion and duplicated zero-shift labels are therefore eliminated as explanations for the unpaid energy.

**Not established:** the exact square expansion and `251/81` diagonal bound remain paper-accepted but were not needed for this minimal PR; the signed nonzero-shift functional `Xi_H` remains uncontrolled. There is no complete shell gain, strict Mertens exponent below `7/8`, canonical VF theorem, or RH proof.

The first independently missing arithmetic input remains a uniform signed estimate for the actual shift/owner cells, beginning with the two-linear-form Möbius correlation
`sum mu(14+25t) mu(5+9t)`, followed by complete aggregation restoring every cell and root/activation term. Absolute incidence is power-sharp by accepted Wheel claim `20261102-wheel-1`.

### Resume capsule

- main: `a33987e275f8a431641d3f475b71a24aa2b1437c`;
- claim: `20261102-lean-1`;
- PR #1070: review-ready, exact head `d749898c4afd5a7c579fc4c7ddcee742832b08d9`, 12/12 workflows green;
- formal result: literal lifted-address injectivity and outer/daughter support disjointness;
- mathematical state: structural control only; no quantitative covariance bound;
- next Lean candidate: exact finite square expansion/diagonal theorem only if its carrier definitions materially aid the signed-correlation attack, otherwise the next independently accepted quantitative theorem or decisive obstruction;
- human-only merge remains mandatory.

## Publication history

Initial completed report publication is followed by a commit/blob readback receipt below.

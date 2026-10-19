# Lean v4.34.1 migration for the Quasi-Riemann Tracker

RHLean builds on the compiler and dependency revisions pinned by the
[Quasi-Riemann Tracker verifier](https://github.com/GTimG/QuasiRiemannTracker/blob/main/verifier/pins.json).
Changing the compiler proves nothing new: this migration changes the build
environment and the least source needed to compile on it. No RHLean theorem
statement, hypothesis or axiom footprint changes.

## Pins

| Package | Revision |
| --- | --- |
| Lean | `leanprover/lean4:v4.34.1` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` (tag `v4.34.1`) |
| PrimeNumberTheoremAnd (PNT+) | `c39a751132c88b6e8080b74c74023fd95b3d8be0` |

These three match the
[tracker lock](https://github.com/GTimG/QuasiRiemannTracker/blob/main/verifier/standard/lake-manifest.json).
Every other entry of `lake-manifest.json` is transitive and is exactly what
`lake update` resolves from these pins: Mathlib's dependencies follow Mathlib's
lock, and LeanArchitect, checkdecls, PrimeCert and leancert follow PNT+'s lock.
The tracker lock differs only in PrimeCert and leancert, which no PNT+ module
imported by RHLean uses, and in its own extra requirements (rellich-kondrachov,
doc-gen4).

`.github/workflows/pnt-plus-strongpnt.yml` fails if the compiler, Mathlib or
PNT+ pin drifts, compiles `PrimeNumberTheoremAnd.StrongPNT`, and audits the
axioms of every PNT+ theorem the strong-Mertens layer consumes.

## Historical StrongPNT replaced by PNT+

The 4.24 project required `math-inc/strongpnt@2f5835c` and patched it at CI
time with `scripts/strongpnt_424/`. That source does not compile against
Mathlib 4.34 (removed `EMetric.ball`, `continuous_iff_continuousOn_univ`,
`Algebra.id.smul_eq_mul`, `derivWithin_fderivWithin` and more), and the pinned
PNT+ already proves the same theorems. The package is gone from the lock.

| RHLean consumes | Historical StrongPNT | PNT+ `c39a751` | Relation |
| --- | --- | --- | --- |
| strong prime number theorem | `Strong_PNT` | `StrongPNT` | identical statement |
| `1/log` zero-free region | `ZetaZeroFree_p` | `ZetaZeroFree1` | identical up to `log t ^ (1 : ℕ)` versus `log t ^ (1 : ℝ)` |
| finite-height zero-free box | `ZetaNoZerosInBox'` | `ZetaNoZerosInBox` | identical statement |
| smoothing integrability | `SmoothedChebyshevDirichlet_aux_integrable` | same name, `MediumPNT` | identical statement |

PNT+'s `ZetaInvBnd` now states its log-nine window with real powers
`log t ^ (9 : ℝ)`. `StrongMertensLogNineCorridor` converts both power forms
with `Real.rpow_natCast`; the corridor structure it produces is unchanged.

## Source changes forced by Lean and Mathlib v4.34.1

Every change below reproduces the 4.24 meaning of the proof it touches.

- **`simpa … using e` closes at reducible transparency.** Lean 4.34 checks the
  simplified `e` against the simplified goal with `withReducible`; 4.24 used
  default transparency. Lean provides `simpa … using! e` for the old check, so
  every `simpa … using` became `using!` (core uses the same spelling).
- **Swapped order-lemma names.** Mathlib #30242 renamed `mul_le_mul_left'` to
  `mul_le_mul_right` and reused the old names with the other side:
  `add_le_add_left h a` now proves `b + a ≤ c + a`. Every use of
  `add_le_add_left`, `add_le_add_right`, `add_lt_add_left`, `add_lt_add_right`
  and the primed `mul_` versions was renamed to its counterpart, so each proof
  still cites the lemma with its 4.24 statement.
- **The `₀` convention (Mathlib #39692).** Ordered-semiring lemmas gained a
  `₀` suffix and their old names now denote the ordered-monoid lemmas:
  `Finset.prod_le_prod` (with nonnegativity hypotheses) is
  `Finset.prod_le_prod₀`, and `Finset.prod_le_prod_of_subset_of_one_le'` is
  `Finset.prod_le_prod_of_subset_of_one_le`.
- **Core deprecations.** `if_pos`, `if_neg`, `dif_pos`, `dif_neg`, `if_true`
  and `if_false` are `ite_eq_left`, `ite_eq_right`, `dite_eq_left`,
  `dite_eq_right`, `ite_true` and `ite_false`, with identical statements.
- **`push_neg` is deprecated** in favour of `push Not`.
- **`List.Sorted` removed.** It was a reducible alias of `List.Pairwise`; uses
  now name `List.Pairwise`, and `Finset.sort_sorted r s` is
  `Finset.pairwise_sort s r`.
- **Renamed or removed lemmas**, each replaced by its exact successor:
  `mellin_inversion` by `mellinInv_mellin_eq`,
  `Real.rpow_le_rpow_of_exponent_nonpos` by `Real.rpow_le_rpow_of_nonpos`,
  `Nat.factorization_prod_pow_eq_self` by `Nat.prod_factorization_pow_eq_self`,
  `Prime.dvd_finset_prod_iff` by `Prime.dvd_finsetProd_iff`,
  `tendsto_finset_sum` by `tendsto_finsetSum`,
  `Nat.infinite_setOf_prime` by `Nat.infinite_setOfPred_prime`,
  `primorial_le_4_pow` by `primorial_le_four_pow` and
  `Set.diff_subset_diff_left` by `Set.sdiff_subset_sdiff_left`.
  `mul_lt_one_of_nonneg_of_lt_one_left`, deprecated without replacement, is
  `mul_le_of_le_one_right` followed by `trans_lt`.
- **New linters.** Four proofs declared with `def` are now `theorem`
  (`linter.defProp`); `letI` inside theorem proofs is `let`
  (`linter.style.haveILetI`); simp arguments and tactics that became no-ops
  under the new simp set were removed.
- **`Integrable.bdd_mul` takes an almost-everywhere bound.** The uniform
  bound in `StrongMertensZetaKernel` is passed as
  `Filter.Eventually.of_forall hbdd`.
- **`Finset.product` versus `×ˢ`.** `Finset.mem_product` is stated for
  `s ×ˢ t`; carriers written with `.product` need `Finset.product_eq_sprod`
  (or explicit membership lemmas) before it applies.
- **Structure-instance syntax.** Lean 4.34 rejects some
  `{ field := … }` literals for Prop-valued structures inside proofs; these
  now use anonymous constructors `⟨…⟩` or a `where` clause.
- **`simp [h]` with simp-tagged projections.** When a `@[simp]` projection
  lemma (for example `lowOwnerStokesNaturalWheelSystem_modulus`) rewrites a
  term that an `if` condition depends on, `simp [hne]` no longer discharges
  that `if`. Those branches use `simp only [ite_eq_right hne, …]`.
- **`ring` fallback.** A `ring` that only closed its goal through the
  `ring_nf` fallback now reports it, which the warning-fatal build rejects;
  those steps use the exact rewrite (`rw [sub_add_cancel]`).
- **No `native_decide` on noncomputable data.** Goals over `Classical`
  definitions are closed by `norm_num`, `decide` on explicit finite sets, or
  explicit arithmetic.
- **Superseded local developments.** The 4.24-era local power-series ring hom
  is replaced by Mathlib's `ArithmeticFunction.ofPowerSeries`, keeping the
  RHLean application and coefficient API. The historical StrongPNT disk
  helpers in `MERTENS_CONVERSE_LOG_INTERPOLATION` are thin adapters over PNT+
  `borelCaratheodory'`, with the same interface.
- **Individual proof repairs** where a lemma's form changed:
  `ContinuousAt.mul` is now stated point-free (`fun_mul` gives the
  pointwise form), a derivative bound now passes its constant explicitly,
  `field_simp` leaves reduced goals that are finished explicitly, and a few
  `simp` calls were replaced by the exact rewrites they performed.

## CI changes

- Every workflow dropped the StrongPNT patch steps. The PNT+ build is cached
  under `pntplus-build-v1-…` and prebuilt with
  `lake build PrimeNumberTheoremAnd.StrongPNT`.
- Workflows that compile research files directly first build the RHLean
  modules those files import
  (`scripts/compile_research_import_closure.py --library-only …`), so a build
  cache from another compiler can never be loaded in place of a fresh one.
- `strongpnt-424-port.yml` became `pnt-plus-strongpnt.yml`. The staging lane
  (`lean-434-upgrade.yml`, `.github/lean434/`, `scripts/strongpnt_434/`) is
  retired: its candidate configuration is now the root configuration.

## What this does not change

- The `export_*` packages are standalone published Lake projects with their own
  `lean-toolchain` and lock. CI audits their sources but does not build them;
  moving them to v4.34.1 is separate work.
- The ordinary Mertens/right-wall equivalence was already formalized in
  `research/MERTENS_CONVERSE_IDENTIFICATION.lean`. The tracker quantifies over
  **all Dirichlet characters**; a qualifying submission still needs
  independent Dirichlet-character estimates.

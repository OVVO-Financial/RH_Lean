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

## Source changes forced by Mathlib v4.34.1

- **Swapped order-lemma names.** Mathlib #30242 renamed `mul_le_mul_left'` to
  `mul_le_mul_right` and reused the old names with the other side:
  `add_le_add_left h a` now proves `b + a ≤ c + a`. Every use of
  `add_le_add_left`, `add_le_add_right`, `add_lt_add_left`, `add_lt_add_right`
  and the primed `mul_` versions was renamed to its counterpart, so each proof
  still cites the lemma with its 4.24 statement.
- **`List.Sorted` removed.** It was a reducible alias of `List.Pairwise`; uses
  now name `List.Pairwise`, and `Finset.sort_sorted r s` is
  `Finset.pairwise_sort s r`.
- **Renamed or removed lemmas**, each replaced by its exact successor:
  `mellin_inversion` by `mellinInv_mellin_eq`,
  `Real.rpow_le_rpow_of_exponent_nonpos` by `Real.rpow_le_rpow_of_nonpos`,
  `Nat.factorization_prod_pow_eq_self` by `Nat.prod_factorization_pow_eq_self`,
  and `Finset.prod_le_prod_of_subset_of_one_le'` by
  `Finset.prod_le_prod_of_subset_of_one_le`.
- **Deprecated without replacement.** `mul_lt_one_of_nonneg_of_lt_one_left`
  is replaced by `mul_le_of_le_one_right` followed by `trans_lt`.
- **`Finset.product` versus `×ˢ`.** `Finset.sum_product` is now stated with
  `×ˢ`; `Finset.product_eq_sprod` bridges the two spellings.

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

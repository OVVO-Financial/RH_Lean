# RHLean cache architecture (Lean 4.34.1)

## Why 80-minute pulls happened

GitHub Actions caches are immutable, and pull-request caches created under
`refs/pull/*/merge` cannot be read by a *sibling* pull request. The original
Gaussian NNS workflow restored a cache successfully as an ACTION, but restored
only partial build artifacts, so Lake spent tens of minutes compiling native
RHLean and the original OpenAI Gaussian imports again.

A successful `actions/cache/restore` step **does not mean** `cache-hit=true`.
Inspect both `cache-matched-key` and the compiled `.olean` prerequisites.

## Cache producers and consumers

- `.github/workflows/lean.yml` is the existing default-branch producer for
  source-addressed `rhlean-build-...` and `pntplus-build-v1-...` caches.
  `.github/actions/lean-compiled-cache` consumes those exact caches, rather
  than creating a second multi-gigabyte RHLean cache namespace. The separate
  Wiener build is seeded once on main as `pntplus-wiener-v1-...`.
- `.github/workflows/oai-compiled-cache-foundation-434.yml` runs on **main**
  (on relevant push, weekly, or manual dispatch). It compiles OpenAI's
  immutable pinned original imports, including GaussianCommon, the FreeRow
  dependencies, detector marked moments, and FinalAssemblyUnconditional.
  Only verified success publishes the immutable `-complete` key.
- `.github/actions/oai-434-shared-cache` restores the compiled OpenAI DAG,
  patches upstream packages idempotently, preserves unmodified native PNT,
  and distinguishes complete from partial caches. All mixed RHLean/OAI
  workflows should use it after checking out the original OpenAI source.
- A partial cache is **never** a certificate and must be compiled through
  the necessary original dependencies. Newly edited research leaves are
  always kernel-checked with warning-as-error and axiom tests intact.

## Required acceptance

1. A successful baseline workflow on main must log a complete OAI build and
   the cache publication. A first cold build can still be expensive once.
2. On a subsequent PR, the OpenAI shared action logs `complete=true`;
   no imported OAI prerequisite is rebuilt, while changed proof leaves
   still get compiled.
3. A cache miss (toolchain/pin/source change or eviction) falls back to a
   real Lake build; it never changes Lean/Mathlib/PNT/OAI pins or bypasses
   proof verification.
4. A partial failure checkpoint is only saved on failure (avoids filling
   GitHub's 10 GiB cache quota with duplicate multi-GB archives).

## Source constraints

The mixed projects require *unpatched* PrimeNumberTheoremAnd at commit
`c39a751132c88b6e8080b74c74023fd95b3d8be0`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1, and
original OpenAI `1581d4cbdd69a0faf34b2089614fe2a814316a6a`.
Stand-alone OAI workflows that patch PNT must NOT reuse this shared-PNT
cache; they need a separately keyed producer.

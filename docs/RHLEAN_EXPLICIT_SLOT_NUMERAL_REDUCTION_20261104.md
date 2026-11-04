# Exact rational slot seed: reduce the existential witness to one detector-budget numeral

Date: 2026-11-04. Status: **mathematical reduction; NOT a certified numeric exponent improvement**.

## 1. Exact calculation in the pinned OpenAI constructor

Source: `openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a`,
`lean/OAI/NumberTheory/DirichletL/ParametersSlotLengths.lean`.

For any integer `N >= 2`, the constructor uses
```text
w(j) = 1 + j/N                 (0 <= j < N)
A = sum_j w(j) = (3*N - 1)/2
ell(j) = w(j)/(6*A) = (N+j)/(3*N*(3*N-1))
ell(0) = 1/(3*(3*N-1))
sum_j ell(j) = 1/6.
```
The function `ell` is strictly increasing, so **the exact physical minimum** is
```text
ell_* = ell(0) = 1/(3*(3*N-1)).
delta_slot = ell_*/24 = 1/(72*(3*N-1)).
```
This is an identity about the specific constructed profile, not an inference from
`HighData.slots_sum`, `HighData.slots_pos`, or abstract `exists_high_data_fine`.
In fact, arbitrary positive `N`-slot families with fixed sum have no positive
minimum bounded below solely as a function of `N`.

## 2. Replace the unbounded choice in the first constructor

The current proof invokes
`exists_nat_gt (max 1 (1/(3*L)))`. This chooses an *unspecified* integer
larger than the threshold; its existential proof alone cannot bound `N` above.

For `L > 0`, a deterministic valid replacement is
```text
N_exp(L) = Nat.floor (max 1 (1/(3*L))) + 2.
```
Then `N_exp >= 2` and `N_exp > 1/(3*L)`; additionally
```text
N_exp <= max(1,1/(3*L)) + 2,
delta_slot = 1/(72*(3*N_exp-1))
           >= 1/(72*(3*max(1,1/(3*L))+5)).
```
The last bound remains **symbolic** until a fixed positive numerical lower
bound on `L` is proved.

In `ParametersHighDataFine.exists_high_data_fine`, the slot length
constructor receives
```text
dmin = 1/200
dmax = 7/8
mesh = min(t, detectorMesh (1/1000000) t)
R = t
L = dmin * min(mesh,R)
  = (1/200) * min(t,detectorMesh (1/1000000) t).
```
Consequently, constructing a specific admissible `t = t0 > 0` and a
numerical lower bound on `detectorMesh (1/1000000) t0` would furnish an
explicit positive rational `L0`; then `N_exp(L0)` and the positive
numerical rational `1/(72*(3*N_exp(L0)-1))` become available.

**Important:** `exists_central_budget` currently chooses `t`
existentially. We cannot simply substitute a decimal `t0` without proving
all its central budget, geometric, height and detector constraints.

## 3. Required Lean statement and end-to-end consumer

1. Formalize `sum (j : Fin N), (1 + (j.val : R)/N) = (3*N-1)/2`
   for `0 < N`, using a finite arithmetic-progression sum.
2. Define a deterministic profile `explicitSlotLengths (N)` and prove
   `ell 0 = 1/(3*(3*N-1))`, `ell 0 <= ell j`, sum `1/6`,
   injectivity, positivity and the inherited mesh inequalities.
3. Replace the nonquantified `exists_nat_gt` witness in a *new*
   `exists_physical_slot_lengths_explicit` theorem; do **not** mutate
   the pinned OpenAI file. Preserve original analytic imports.
4. Produce a numerical `t0`, `L0` and `B : Nat`, with a formal
   theorem constructing `D : HighData (1/1000000)` such that
   `actualSlotMinimum D >= 1/(3*(3*B-1))`.
5. Only then instantiate `native_beta_le_slot_calibrated_boundary_low_first`
   to derive the actual **numeral**
   `HeckeZeroSupremum.beta <= 7/8 - 1/(72*(3*B-1))`, and separately the
   corresponding actual Mertens bound.
6. Re-run warning-fatal Lean 4.34.1, complete axiom/import-closure audit,
   original physical-source equivalence audit, and independent review of
   the analytic zero detector. A green proof of a conditional numerical
   lemma is not evidence that its numerical witness exists.

## 4. Proof-status distinctions and falsification checks

- Existing `VF919ActualSlotMinRetighten` supplies an **existential**
  `HighData` witness with a strictly positive, source-dependent gain.
- Existing `VF919ExplicitPhysicalSlotSeed` defines an integer using
  `ceil(24/actualSlotMinimum D)+1`. That integer itself depends on the
  inaccessible witness. It is NOT a fixed evaluated numerical constant.
- The new formula for `ell_*` is rigorously obtained from the pinned
  canonical profile. It has **not** yet been carried by a new compiled
  numerical-`HighData` constructor through the end-to-end zero detector.
- An audit of permitted axioms checks logical dependencies against Lean's
  kernel, but does not independently validate the interpretation of
  imported analytic theorems, definitions of beta, or equivalence to
  classical zeta/Mertens bounds. Keep the extraordinary zero-free claim
  explicitly conditional on those semantic identifications until reviewed.

## 5. Agent assignments

- **Arithmetic/Constructor:** formalize the exact arithmetic-progression
  profile and bounded choice `N_exp`, with a standalone kernel check.
- **Analytic:** extract an explicit admissible `t0` from central-budget
  inequalities and a numerical positive lower bound for `detectorMesh`.
- **Lean verification:** construct exact finite slot `HighData` using
  `t0`, independently of an unbounded `exists_nat_gt` choice.
- **Referee:** audit every external zero-detector hypothesis and whether
  `HeckeZeroSupremum.beta` is the unrestricted zeta-zero boundary; flag
  any circularity, reinterpretation, or stronger-than-claimed premise.

**Acceptance criterion:** an evaluated positive rational constant `c`
and a kernel-checked actual endpoint `HeckeZeroSupremum.beta <= 7/8-c`,
with full dependency audit. Until that happens, status remains
**explicit formula for the canonical slot family, not a certified numeral**.

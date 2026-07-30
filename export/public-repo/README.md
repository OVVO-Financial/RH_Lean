# Prime-Wheel Formalization Export

This directory is a copy-ready seed for a new public repository accompanying the paper **Squared-Complex Framework: Elementary Pointwise Bridge**.

Copy the contents of `export/public-repo/` into the root of the new repository. The export is intentionally isolated from the broader `RH_Lean` sandbox.

## Contents

- `paper/` — manuscript source and paper build notes.
- `formalization/` — standalone Lean 4 project pinned to Lean/mathlib `v4.24.0`.
- `docs/` — theorem status, source provenance, and publication checklist.
- `.github/workflows/` — public-repository Lean verification.

## Mathematical boundary

The formalization proves the complete exact reduction

`explicit pinned Dirichlet nonconcentration ↔ prime-wheel harmonic bound ↔ primorial residual bound ↔ global Mertens-energy bound`.

It does **not** assert either remaining mathematical input:

1. the RH-scale maximal Dirichlet/nonconcentration bound;
2. the classical theorem `MertensEnergyBoundedStatement ↔ RiemannHypothesisStatement`.

The public endpoint accepts only the classical criterion as an explicit theorem argument. The primorial-to-global Mertens bridge is constructed internally and is not assumed.

## Build

```bash
cd formalization
lake update
lake build RHLean --wfail
bash scripts/audit_assumptions.sh
```

## Paper

The LaTeX source is at `paper/Squared_Complex_Framework_Elementary_Pointwise_Bridge.tex`. See `paper/README.md` for compilation instructions.

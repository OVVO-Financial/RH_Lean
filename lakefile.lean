import Lake
open Lake DSL

package «RHLean» where
  version := v!"0.1.0"

-- Quasi-Riemann Tracker compatibility target: Lean + Mathlib v4.34.1.
-- This is an IN-PROGRESS migration; do not merge until the lockfile,
-- external dependencies, full RHLean build, and axiom audits are verified.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.1"

-- Preserve the historical external theorem-source revisions while separately
-- repairing their compatibility with Mathlib 4.34.1. The existing
-- scripts/strongpnt_424 patches target Mathlib 4.24 ONLY and cannot be assumed
-- correct or sufficient on this branch.
require PrimeNumberTheoremAnd from git
  "https://github.com/AlexKontorovich/PrimeNumberTheoremAnd.git" @ "7f3cd7c3e1c85d60478ed8934be42a06b07de374"

require StrongPNT from git
  "https://github.com/math-inc/strongpnt.git" @ "2f5835c322314f55f1026ec2f139d704b7c45c69"

lean_lib RHLean

import Lake
open Lake DSL

package «RHLean» where
  version := v!"0.1.0"

-- Lean v4.34.1 migration candidate. Modern PNT+ already contains the
-- strong prime-number-theorem, logarithmic zero-free, and finite-box inputs.
-- Use its audited source rather than compiling obsolete StrongPNT 4.21 code.
require PrimeNumberTheoremAnd from git
  "https://github.com/AlexKontorovich/PrimeNumberTheoremAnd.git" @ "c39a751132c88b6e8080b74c74023fd95b3d8be0"

-- Put Mathlib last to retain the tracker's exact v4.34.1 dependency graph.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

lean_lib RHLean

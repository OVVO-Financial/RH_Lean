import Lake
open Lake DSL

package «RHLean» where
  version := v!"0.1.0"

-- Quasi-Riemann Tracker compatibility target: Lean v4.34.1 and its exact
-- Mathlib source commit (the v4.34.1 tag).
-- IN-PROGRESS migration: not mergeable until full proof/axiom validation.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

-- Align the PNT+ source with the tracker reference lock. This may require
-- repairs in RHLean and in the historical StrongPNT interface.
require PrimeNumberTheoremAnd from git
  "https://github.com/AlexKontorovich/PrimeNumberTheoremAnd.git" @ "c39a751132c88b6e8080b74c74023fd95b3d8be0"

-- Keep the historical finished StrongPNT SOURCE unchanged until a verified
-- Mathlib 4.34.1 port exists. scripts/strongpnt_424 target Lean 4.24 ONLY;
-- do NOT treat them as a successful migration or change theorem assumptions.
require StrongPNT from git
  "https://github.com/math-inc/strongpnt.git" @ "2f5835c322314f55f1026ec2f139d704b7c45c69"

lean_lib RHLean

import Lake
open Lake DSL

package «RHLean» where
  version := v!"0.1.0"

-- Staged Lean v4.34.1 target; never use the historical 4.24 patch scripts
-- as a substitute for a verified 4.34.1 source port.
-- Order matters: the explicit PNT+ revision overrides StrongPNT's old
-- transitive PNT+ requirement, then Mathlib v4.34.1 overrides all
-- transitive Mathlib versions (including the older PNT+ pins).
require StrongPNT from git
  "https://github.com/math-inc/strongpnt.git" @ "2f5835c322314f55f1026ec2f139d704b7c45c69"

require PrimeNumberTheoremAnd from git
  "https://github.com/AlexKontorovich/PrimeNumberTheoremAnd.git" @ "c39a751132c88b6e8080b74c74023fd95b3d8be0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

lean_lib RHLean

import Lake
open Lake DSL

package «RHLean» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.24.0"

-- StrongPNT pins an older PrimeNumberTheoremAnd snapshot built against Mathlib 4.21.
-- Override that transitive dependency with the upstream snapshot that was explicitly
-- bumped to Mathlib 4.24, while keeping the completed StrongPNT theorem source fixed.
require PrimeNumberTheoremAnd from git
  "https://github.com/AlexKontorovich/PrimeNumberTheoremAnd.git" @ "7f3cd7c3e1c85d60478ed8934be42a06b07de374"

require StrongPNT from git
  "https://github.com/math-inc/strongpnt.git" @ "2f5835c322314f55f1026ec2f139d704b7c45c69"

lean_lib RHLean

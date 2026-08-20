import Lake
open Lake DSL

package «RHLean» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.24.0"

require StrongPNT from git
  "https://github.com/math-inc/strongpnt.git" @ "2f5835c322314f55f1026ec2f139d704b7c45c69"

lean_lib RHLean

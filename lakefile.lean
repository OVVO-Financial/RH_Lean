import Lake
open Lake DSL

package «RHLean» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.2"

lean_lib RHLean

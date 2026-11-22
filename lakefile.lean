import Lake
open Lake DSL

package «RHLean» where
  version := v!"0.1.0"

-- Compiler, Mathlib and PNT+ match the Quasi-Riemann Tracker verifier pins.
-- PNT+ supplies the strong prime number theorem, the 1/log zero-free region
-- and the finite-height zero-free box that the strong-Mertens layer consumes.
require PrimeNumberTheoremAnd from git
  "https://github.com/AlexKontorovich/PrimeNumberTheoremAnd.git" @ "c39a751132c88b6e8080b74c74023fd95b3d8be0"

-- Mathlib comes last so its pin overrides the one PNT+ inherits transitively.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

-- Compile just the existing two verified VF_mid research modules as
-- dependencies of the native Alpoge Gz delta transfer. Do not glob
-- the research tree: it contains many exploratory and conditional files.
lean_lib RHLean where
  roots := #[`RHLean, `research.VF_MID_VON_KOCH_BRIDGE,
    `research.VF_MID_LI_UNIFORM_QUADRATURE]

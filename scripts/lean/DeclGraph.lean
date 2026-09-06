/-
Exact elaborated declaration dependency graph for RHLean.

`scripts/decl_graph.py` reads Lean *source text* and records which declaration
mentions which name.  That graph is cheap, runs in CI without a build, and is
good enough to navigate, but it is syntactic: it cannot see a dependency that
only elaboration introduces (instance resolution, notation and macro expansion,
`simp` closing a goal with lemmas nobody named, dot-notation on a hypothesis).

This program produces the exact graph instead.  It loads the compiled
environment, walks every constant declared in an `RHLean.*` module, and reads
the constants actually referenced by that declaration's type and by its proof
term.  Per `AGENTS.md`, compiled Lean source is authoritative, so where the two
graphs disagree this one wins.

It deliberately depends on `Lean` only -- not on Mathlib and not on `RHLean`
itself -- so it compiles against the bare toolchain and loads the project's
`.olean` files at run time.  It is not part of the `lakefile.lean` build target,
so it cannot break the ordinary project build.

Run it from the repository root, after `lake build`:

    lake env lean --run scripts/lean/DeclGraph.lean lean-decl-graph.jsonl

Output is JSON Lines, one record per declaration:

    {"name":"...","module":"...","kind":"theorem",
     "typeRefs":[...],"valueRefs":[...],
     "externalTypeRefs":N,"externalValueRefs":N}

`scripts/decl_graph.py --from-lean <file>` converts that into the same
`rhlean-decl-graph/1` JSON the syntactic producer emits, including translating
Lean's `_private.<module>.<n>.<name>` mangling into the `<name>#<module>` ids
that schema uses.
-/
import Lean

open Lean

namespace RHLeanDeclGraph

/-- Root namespace of the authoritative source tree. -/
def rootModule : Name := `RHLean

/-- Is `m` the root module or one of its submodules? -/
def isProjectModule (m : Name) : Bool :=
  m == rootModule || rootModule.isPrefixOf m

/-- Constructor name of a `ConstantInfo`, used as the declaration kind. -/
def constantKind : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "ctor"
  | .recInfo _    => "rec"

/-- Escape a name for embedding in a JSON string literal. -/
def jsonString (s : String) : String :=
  Json.render (Json.str s)

/-- Render an array of names as a JSON array, keeping only project constants. -/
def refsJson (names : Array Name) (project : NameSet) (self : Name) :
    String × Nat := Id.run do
  let mut kept : Array String := #[]
  let mut external : Nat := 0
  let mut seen : NameSet := {}
  for n in names do
    if n == self || seen.contains n then
      continue
    seen := seen.insert n
    if project.contains n then
      kept := kept.push (jsonString n.toString)
    else
      external := external + 1
  return ("[" ++ String.intercalate "," kept.toList ++ "]", external)

end RHLeanDeclGraph

open RHLeanDeclGraph in
def main (args : List String) : IO UInt32 := do
  let outPath : System.FilePath := args.head?.getD "lean-decl-graph.jsonl"

  -- `lake env` puts the project and its dependencies on LEAN_PATH, which
  -- `initSearchPath` honours; the sysroot supplies core.
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := rootModule }] Options.empty 1024

  let moduleNames := env.header.moduleNames
  let moduleData := env.header.moduleData

  -- Every constant declared in a project module.  Collecting this first lets
  -- the reference lists be restricted to project constants, which is what keeps
  -- the output small: the Mathlib constants a proof touches are counted, not
  -- listed.
  let mut project : NameSet := {}
  let mut projectModules : Nat := 0
  for i in [0 : moduleNames.size] do
    let m := moduleNames[i]!
    if isProjectModule m then
      projectModules := projectModules + 1
      for cn in moduleData[i]!.constNames do
        project := project.insert cn

  let handle ← IO.FS.Handle.mk outPath IO.FS.Mode.write
  let mut emitted : Nat := 0
  for i in [0 : moduleNames.size] do
    let m := moduleNames[i]!
    if !isProjectModule m then
      continue
    for cn in moduleData[i]!.constNames do
      match env.find? cn with
      | none => pure ()
      | some info =>
        let (typeRefs, extType) :=
          refsJson info.type.getUsedConstants project cn
        let (valueRefs, extValue) := match info.value? with
          | some v => refsJson v.getUsedConstants project cn
          | none   => ("[]", 0)
        let line :=
          "{\"name\":" ++ jsonString cn.toString
            ++ ",\"module\":" ++ jsonString m.toString
            ++ ",\"kind\":" ++ jsonString (constantKind info)
            ++ ",\"typeRefs\":" ++ typeRefs
            ++ ",\"valueRefs\":" ++ valueRefs
            ++ ",\"externalTypeRefs\":" ++ toString extType
            ++ ",\"externalValueRefs\":" ++ toString extValue
            ++ "}"
        handle.putStrLn line
        emitted := emitted + 1
  handle.flush

  IO.eprintln s!"RHLean elaborated declaration graph"
  IO.eprintln s!"  project modules : {projectModules}"
  IO.eprintln s!"  project constants: {project.size}"
  IO.eprintln s!"  records written : {emitted}"
  IO.eprintln s!"  output          : {outPath}"
  return 0

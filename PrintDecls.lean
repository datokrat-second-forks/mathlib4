import Lean

/-!
# `printDecls` — list the declarations a module adds

Given one or more module names, this tool imports them and prints, for each, the
name and pretty-printed type of every declaration the module adds to the
environment — i.e. every constant stored in the module's `.olean`, which is
exactly what its commands produced via `addDecl`, excluding private and
compiler/elaborator-internal declarations.

Two modes:

```
lake exe printDecls Mathlib.My.Module           -- print one module to stdout
lake exe printDecls --out DIR [Mod1 Mod2 ...]   -- dump each module to DIR/<Mod>.txt
```

In `--out` mode, if no module names are given they are read from stdin (one per
line). Crucially, **all requested modules are imported into a single
environment once**, and each is then dumped from `env.header.moduleData`. This
avoids re-importing the shared dependency closure per module, which is what makes
dumping all of Mathlib in one process far faster than one process per file.

Modules must already be built; any whose `.olean` is missing are skipped with a
warning rather than aborting the whole import.
-/

open Lean

/-- Render the public declarations of `modName` (already imported into `env`) as
`name : type` lines. Returns `""` if the module is not in the environment. -/
def renderModule (env : Environment) (modName : Name) : MetaM String := do
  let some idx := env.getModuleIdx? modName | return ""
  let md := env.header.moduleData[idx.toNat]!
  let mut out := ""
  for ci in md.constants do
    -- Skip private declarations and compiler/elaborator-internal ones
    -- (`.match_1`, equation lemmas, `._simp_1`, etc.).
    if isPrivateName ci.name || ci.name.isInternalDetail then continue
    let fmt ← Meta.ppExpr ci.type
    out := out ++ s!"{ci.name} : {fmt.pretty}\n"
  return out

/-- Whether a module's `.olean` can be found on the search path. -/
def oleanExists (m : Name) : IO Bool := do
  try
    let _ ← findOLean m
    pure true
  catch _ =>
    pure false

/-- Import the built subset of `mods` into one environment (with extension state
loaded, so the pretty printer has notation), then run `act` over it in `MetaM`. -/
def withModules (mods : Array Name) (act : Environment → MetaM Unit) : IO Unit := unsafe do
  initSearchPath (← findSysroot)
  -- Extension initializers must be runnable before extension state can be loaded;
  -- `loadExts := true` is required so `@[app_unexpander]` notation is recovered.
  enableInitializersExecution
  let mut present := #[]
  for m in mods do
    if ← oleanExists m then
      present := present.push { module := m }
    else
      IO.eprintln s!"skip (not built): {m}"
  let env ← importModules present (opts := {}) (trustLevel := 1024) (loadExts := true)
  try
    let ctx : Core.Context := { fileName := "<printDecls>", fileMap := default }
    let state : Core.State := { env }
    discard <| (Meta.MetaM.run' (act env)).toIO ctx state
  finally
    env.freeRegions

/-- Read module names (one per line) from stdin, ignoring blanks. -/
def readModulesFromStdin : IO (Array Name) := do
  let s ← (← IO.getStdin).readToEnd
  return s.splitOn "\n" |>.filterMap (fun l =>
    let l := l.trimAscii.toString
    if l.isEmpty then none else some l.toName) |>.toArray

def main (args : List String) : IO UInt32 := do
  match args with
  | "--out" :: outDir :: rest =>
    let mods ← if rest.isEmpty then readModulesFromStdin else pure (rest.map (·.toName)).toArray
    IO.FS.createDirAll outDir
    withModules mods fun env => do
      for m in mods do
        IO.FS.writeFile (System.FilePath.mk outDir / s!"{m}.txt") (← renderModule env m)
    return 0
  | [modStr] =>
    withModules #[modStr.toName] fun env => do
      IO.print (← renderModule env modStr.toName)
    return 0
  | _ =>
    IO.eprintln "usage: printDecls <Module>            (print one module to stdout)"
    IO.eprintln "       printDecls --out DIR [Mods...]  (dump modules to DIR/<Mod>.txt;"
    IO.eprintln "                                        reads module names from stdin if none given)"
    return 1

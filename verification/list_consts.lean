-- Usage, after `lake build`: lake env lean verification/list_consts.lean
-- then: lake env leanexport SICLean -- $(cat project-consts.txt) > project-export.ndjson
import SICLean
open Lean Elab Command in
/-- Write the names of the constants of the SICLean and CebotarevDensity modules, one per line,
leaving out unsafe and partial definitions. No theorem can use these, and leanexport leaves out
unsafe declarations unless it is given the option --export-unsafe. -/
elab "#list_consts " path:str : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut out : Array String := #[]
  let mut skipped : Nat := 0
  let mut nonKernel : Array Name := #[]
  for i in [0:mods.size] do
    let m := mods[i]!.toString
    if m.startsWith "SICLean" || m.startsWith "CebotarevDensity" then
      for c in env.header.moduleData[i]!.constNames do
        let some ci := env.find? c | continue
        let isPartial := match ci with
          | .defnInfo d => d.safety == .partial
          | _ => false
        if ci.isUnsafe || isPartial then
          nonKernel := nonKernel.push c
          continue
        let s := c.toString (escape := false)
        if s.toName == c && !s.contains (Char.ofNat 32) then out := out.push s else skipped := skipped + 1
  IO.FS.writeFile path.getString ("\n".intercalate out.toList ++ "\n")
  logInfo m!"listed {out.size} constants, skipped {skipped} whose names do not round-trip, left out {nonKernel.size} unsafe or partial definitions: {nonKernel.toList.take 12}"
#list_consts "project-consts.txt"

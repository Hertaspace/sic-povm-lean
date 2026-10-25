-- Usage, after `lake build`: lake env lean verification/axiom_scan.lean
import SICLean
open Lean Elab Command in
/-- Scan every constant from SICLean modules whose name starts with one of the `|`-separated prefixes. -/
elab "#axiom_scan_prefix " pfx:str : command => do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ps := pfx.getString.splitOn "|"
  let mut n : Nat := 0
  let mut nm : Nat := 0
  let mut bad : Array (Name × Name) := #[]
  let mods := env.header.moduleNames
  for i in [0:mods.size] do
    let m := mods[i]!.toString
    if ps.any (fun p => m.startsWith p) then
      nm := nm + 1
      for c in env.header.moduleData[i]!.constNames do
        n := n + 1
        for a in (← collectAxioms c) do
          if !std.contains a then bad := bad.push (c, a)
  logInfo m!"scanned {n} constants from {nm} modules matching {pfx.getString}; nonstandard axiom uses: {bad}"
#axiom_scan_prefix "SICLean|CebotarevDensity"

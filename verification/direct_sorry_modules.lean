-- Usage, after `lake build`: lake env lean verification/direct_sorry_modules.lean
import SICLean
open Lean Elab Command in
/-- List the SICLean modules containing constants whose own type or value mentions `sorryAx` directly. -/
elab "#direct_sorry_modules" : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut hits : Array Name := #[]
  for i in [0:mods.size] do
    if (`SICLean).isPrefixOf mods[i]! then
      for c in env.header.moduleData[i]!.constNames do
        let some ci := env.find? c | continue
        let uses := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])
        if uses.contains ``sorryAx then hits := hits.push mods[i]!
  let uniq := hits.toList.eraseDups
  logInfo m!"modules with direct sorryAx uses: {uniq.map (fun m => (m, hits.toList.count m))}"
#direct_sorry_modules

import Proofs
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Audit all constants owned by the production library, including private and
compiler-generated declarations. The Comparator challenge is never imported. -/
open Lean Elab Command
set_option maxRecDepth 32768
set_option maxHeartbeats 0

run_cmd do
  let env ← getEnv
  let roots := (env.constants.toList.map Prod.fst).filter fun name =>
    match env.getModuleIdxFor? name with
    | none => false
    | some idx =>
      let owner := env.header.moduleNames[idx.toNat]!
      owner == `HiddenCircuits || owner.toString.startsWith "HiddenCircuits." || owner == `Proofs
  unless roots.length > 0 do
    throwError "No production declarations were loaded"
  for name in roots do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration is absent from the checked kernel environment: {name}"
    match env.find? name with
    | some (.axiomInfo _) => throwError "Production-owned axiom: {name}"
    | _ => pure ()
  let action : CollectAxioms.M Unit := roots.forM CollectAxioms.collect
  let (_, result) := (action.run env).run {}
  let unexpected := result.axioms.filter fun name =>
    name != ``propext && name != ``Classical.choice && name != ``Quot.sound
  unless unexpected.isEmpty do
    throwError "Unexpected transitive axioms: {unexpected}"
  let names := roots.toArray.qsort Name.lt
  let rows := names.toList.map fun name =>
    let idx := (env.getModuleIdxFor? name).get!
    s!"{env.header.moduleNames[idx.toNat]!}\t{name}"
  liftIO <| IO.FS.writeFile ".lake/check/declarations.tsv" (String.intercalate "\n" rows ++ "\n")
  logInfo m!"AXIOM_AUDIT_PASS declarations={roots.length} axioms={(result.axioms.qsort Name.lt).toList}"

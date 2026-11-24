import Overfull
import Lean.Util.CollectAxioms

/-!
This audit fails if a project theorem depends on an axiom other than Lean's
standard logical axioms. It inspects the kernel environment, not source-text
matches, and therefore detects indirect use of an unfinished proof.

It audits the proved declarations present in this project and the imported
Vizing proof. The main asymptotic theorem remains an unproved specification.
-/

open Lean Elab Command

example : Overfull.SharpnessFamily := Overfull.sharpness_family
example : Overfull.FiniteVizingBound := Overfull.finite_vizing_bound

elab "#audit_overfull" : command => do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for moduleName in env.header.moduleNames do
    if (`Overfull).isPrefixOf moduleName then
      logInfo ("IMPORTED_PROJECT_MODULE " ++ moduleName.toString)
    if (`Vizing).isPrefixOf moduleName then
      logInfo ("IMPORTED_EXTERNAL_MODULE " ++ moduleName.toString)
  let mut count := 0
  for (name, info) in env.constants.toList do
    let some moduleIdx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[moduleIdx.toNat]!
    if (`Overfull).isPrefixOf moduleName || (`Vizing).isPrefixOf moduleName then
      match info with
      | .axiomInfo _ => throwError "Axiom declared in audited source is forbidden: {name}"
      | .thmInfo _ =>
          let axioms ← collectAxioms name
          let forbidden := axioms.filter (fun a => !allowed.contains a)
          unless forbidden.isEmpty do
            throwError "Unapproved axioms in {name}: {forbidden}"
          let record := Json.mkObj [
            ("name", toJson name.toString),
            ("module", toJson moduleName.toString),
            ("axioms", toJson (axioms.map Name.toString))]
          logInfo ("VERIFIED_DECLARATION " ++ record.compress)
          count := count + 1
      | _ => pure ()
  if count == 0 then
    throwError "No Overfull theorem was found"
  logInfo m!"OVERFULL_AXIOM_AUDIT_OK {count}"

#audit_overfull

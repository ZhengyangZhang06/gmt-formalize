import Poincare.SimonGMT
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Kernel dependency audit for the Simon GMT development

Compilation of this module inspects every imported declaration in the
`Poincare.SimonGMT` namespace. It rejects any axiom dependency other than
Lean's standard quotient, propositional-extensionality, and choice principles.
As the aggregate imports grow, this check automatically covers the new modules.
-/

meta section

open Lean Elab Command

private def allowedAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

elab "#assert_simon_gmt_axioms" : command => do
  let env ← getEnv
  let mut failures : Array (Name × Name) := #[]
  let mut checked : Nat := 0
  for (name, _) in env.constants do
    if name.toString.startsWith "Poincare.SimonGMT" then
      checked := checked + 1
      let axioms ← liftCoreM <| Lean.collectAxioms name
      for axiomName in axioms do
        unless allowedAxioms.contains axiomName do
          failures := failures.push (name, axiomName)
  if checked == 0 then
    throwError "namespace audit inspected zero Poincare.SimonGMT declarations"
  logInfo m!"audited {checked} Poincare.SimonGMT declarations"
  unless failures.isEmpty do
    let details := String.intercalate "\n" <|
      failures.toList.map fun (name, axiomName) => s!"{name}: {axiomName}"
    throwError "unexpected axiom dependencies:\n{details}"

#assert_simon_gmt_axioms

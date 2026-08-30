import Solution
import Lean

set_option linter.style.header false

/-!
# Public theorem axiom audit

The audit follows every public Palomar theorem transitively and fails
elaboration if a proof depends on anything beyond Lean's standard logical
axioms. In particular, this catches placeholders, custom axioms, and native
evaluation shortcuts in the solution proof closure.
-/

namespace HadamardFormalAxiomAudit

open Lean Meta

def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

def auditedDeclarations : List Name :=
  [``HadamardFormal.handshake_mod_four,
    ``HadamardFormal.cooperWallis,
    ``HadamardFormal.hadamard_7172,
    ``HadamardFormal.hadamard_8476,
    ``HadamardFormal.hadamard_2884,
    ``HadamardFormal.hadamard_4532,
    ``HadamardFormal.hadamard_7004,
    ``HadamardFormal.hadamard_7828,
    ``HadamardFormal.hadamard_9476,
    ``HadamardFormal.hadamard_11948]

def runAxiomAudit : MetaM Unit := do
  let mut offenders : Array String := #[]
  for decl in auditedDeclarations do
    unless (← getEnv).contains decl do
      throwError "axiom audit: audited declaration `{decl}` does not exist"
    let axioms ← Lean.collectAxioms decl
    logInfo s!"axioms {decl}: {axioms.toList}"
    let bad := axioms.filter fun axiomName ↦ !allowedAxioms.contains axiomName
    unless bad.isEmpty do
      offenders := offenders.push s!"{decl} depends on {bad.toList}"
  unless offenders.isEmpty do
    throwError "axiom audit FAILED: {String.intercalate "; " offenders.toList}"
  logInfo s!"axiom audit passed: {auditedDeclarations.length} declarations; \
    axioms confined to {allowedAxioms}"

#eval runAxiomAudit

end HadamardFormalAxiomAudit

-- Axiom report for every theorem in the OpenGauss run 2 module (`RequestProject.CSF`).
-- Each theorem is tagged `ok` (standard axioms only) or `SORRY` (depends on `sorryAx`).
-- Run from the `opengauss/` folder after `lake build`:
--   lake env lean ../verification/axiom_report_run2.lean
-- Output of the 28 Sep 2026 run: `opengauss/run2-axioms.txt`.

import RequestProject.CSF
open Lean Elab Command

elab "#axiom_report" : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? `RequestProject.CSF | throwError "module not found"
  let skip := ["injEq", "inj", "sizeOf_spec", "ext", "ext_iff"]
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx && !n.isInternal then
      if let .thmInfo _ := ci then
        unless n.components.any (fun c => skip.contains c.toString) do
          names := names.push n
  for n in names.qsort (fun a b => a.toString < b.toString) do
    let axs ← collectAxioms n
    let tag := if axs.contains ``sorryAx then "SORRY " else "ok    "
    logInfo m!"{tag} {n} : {axs}"

#axiom_report

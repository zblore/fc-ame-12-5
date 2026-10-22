/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import AME125

/-!
Audit: the headline statement is the same term as Formal Conjectures' `ame_12_5_open`, the main
results use only the three standard axioms, and the kernel checks of the certificates
(`certs0_ok` to `certs9_ok`, `certs_masks`) use at most `propext`. Any failure is an error, so
`lake env lean` exits nonzero. As a control, Formal Conjectures' own declaration must show
`sorryAx`, which shows the axiom check can fail.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some ours := env.find? `AME125.ame_12_5_open
    | throwError "AME125.ame_12_5_open missing"
  let some theirs := env.find? `OpenQuantumProblem35.ame_12_5_open
    | throwError "OpenQuantumProblem35.ame_12_5_open missing"
  unless ours.type == theirs.type do
    throwError m!"statements differ: {ours.type} vs {theirs.type}"
  unless ours.levelParams == theirs.levelParams do
    throwError m!"universe parameters differ: {ours.levelParams} vs {theirs.levelParams}"
  let standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [`AME125.ame_12_5_open, `AME125.ame125State_isAME, `AME125.graphState_isAME,
      `AME125.graphState_isNormalized, `AME125.reduced_graphState, `AME125.cutInj_all,
      `AME125.controlState_not_isAME] do
    -- `collectAxioms` returns `[]` for a name that does not exist, so check existence first.
    if (env.find? n).isNone then throwError m!"{n} missing"
    let axs ← collectAxioms n
    let extra := axs.filter fun a ↦ !standard.contains a
    unless extra.isEmpty do throwError m!"{n} uses axioms outside the standard three: {extra}"
  let kernel : List Name := [`AME125.certs0_ok, `AME125.certs1_ok, `AME125.certs2_ok,
    `AME125.certs3_ok, `AME125.certs4_ok, `AME125.certs5_ok, `AME125.certs6_ok,
    `AME125.certs7_ok, `AME125.certs8_ok, `AME125.certs9_ok, `AME125.certs_masks]
  for n in kernel do
    if (env.find? n).isNone then throwError m!"{n} missing"
    let axs ← collectAxioms n
    unless axs.all (· == ``propext) do throwError m!"the kernel check {n} uses axioms: {axs}"
  let fc ← collectAxioms `OpenQuantumProblem35.ame_12_5_open
  unless fc.contains ``sorryAx do
    throwError "control failed: Formal Conjectures' statement no longer shows sorryAx"
  logInfo m!"audit passed: statement identical ({ours.type}); standard axioms only; kernel \
    checks use at most propext; control ok"

/-- The statement, restated by hand, is proved by the headline theorem. -/
example : ∃ ψ : OpenQuantumProblem35.StateVector 12 5, OpenQuantumProblem35.IsAME ψ :=
  AME125.ame_12_5_open

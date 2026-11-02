/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

import AME125

/-!
Audit: the statement `Solution` proves under Formal Conjectures' name has exactly the type of the
headline theorem, the main results use only the three standard axioms, and the kernel checks of
the certificates (`certs0_ok` to `certs9_ok`, `certs_masks`) use at most `propext`. Any failure is
an error, so `lake env lean` exits nonzero. As a control, the filter the checks use must report
`sorryAx` when it is added to the headline's axioms, which shows the check can fail.
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
  -- The axioms outside the standard three; every check below and the control use this filter.
  let nonstandard (axs : Array Name) : Array Name := axs.filter fun a ↦ !standard.contains a
  for n in [`OpenQuantumProblem35.ame_12_5_open, `AME125.ame_12_5_open,
      `AME125.ame125State_isAME, `AME125.graphState_isAME, `AME125.graphState_isNormalized,
      `AME125.reduced_graphState, `AME125.cutInj_all, `AME125.controlState_not_isAME] do
    -- `collectAxioms` returns `[]` for a name that does not exist, so check existence first.
    if (env.find? n).isNone then throwError m!"{n} missing"
    let axs ← collectAxioms n
    let extra := nonstandard axs
    unless extra.isEmpty do throwError m!"{n} uses axioms outside the standard three: {extra}"
  let kernel : List Name := [`AME125.certs0_ok, `AME125.certs1_ok, `AME125.certs2_ok,
    `AME125.certs3_ok, `AME125.certs4_ok, `AME125.certs5_ok, `AME125.certs6_ok,
    `AME125.certs7_ok, `AME125.certs8_ok, `AME125.certs9_ok, `AME125.certs_masks]
  for n in kernel do
    if (env.find? n).isNone then throwError m!"{n} missing"
    let axs ← collectAxioms n
    unless axs.all (· == ``propext) do throwError m!"the kernel check {n} uses axioms: {axs}"
  -- An empty list would pass the checks above vacuously, for instance if a proof were hidden
  -- from this file, so the headline must show all three standard axioms.
  let headline ← collectAxioms `OpenQuantumProblem35.ame_12_5_open
  unless standard.all headline.contains do
    throwError m!"the headline shows axioms {headline}, not the standard three"
  -- Control: the same filter must report `sorryAx` added to the headline's axioms, and nothing
  -- else.
  unless nonstandard (headline.push ``sorryAx) == #[``sorryAx] do
    throwError "control failed: the filter does not report sorryAx"
  logInfo m!"audit passed: statement identical ({ours.type}); standard axioms only; kernel \
    checks use at most propext; control ok"

/-- The statement, restated by hand, is proved by the headline theorem. -/
example : ∃ ψ : OpenQuantumProblem35.StateVector 12 5, OpenQuantumProblem35.IsAME ψ :=
  AME125.ame_12_5_open

/-! `combineFirst` differs from Formal Conjectures' text in one proof step (see `Challenge.lean`).
Here is Formal Conjectures' original, with `omega`, under another name; it is the same function. -/

namespace OpenQuantumProblem35

/--
Merge a configuration on the first $m$ parties and a configuration on the remaining $n-m$
parties into a configuration on all $n$ parties.
-/
def combineFirstFC {n d : ℕ} (m : ℕ) (hm : m ≤ n)
    (x : Config m d) (y : Config (n - m) d) : Config n d :=
  fun i =>
    if hi : i.1 < m then
      x ⟨i.1, hi⟩
    else
      y ⟨i.1 - m, by
        have him : m ≤ i.1 := Nat.le_of_not_gt hi
        omega⟩

example : @combineFirstFC = @combineFirst := rfl

end OpenQuantumProblem35

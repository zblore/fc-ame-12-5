/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

import AME125
-- `import all` makes the proofs and private declarations of each module visible here; a plain
-- import of a module hides them, and every declaration would look unreachable.
import all AME125.Data
import all AME125.GraphState
import all AME125.Certificate
import all AME125.FormalTarget
import all AME125.Control

/-!
Audit: every hand-written declaration in `AME125`, private ones included, is reachable from one
of the two results the project exists to state: the headline `AME125.ame_12_5_open` and the
control `AME125.controlState_not_isAME` (deliberately independent of the certificates).
Reachable means it occurs, directly or through other `AME125` declarations, in the statement or
proof of one of them. Any unreachable declaration is an error, so `lake env lean` exits nonzero.
As a control, an orphan recursive definition whose equation lemma mentions it must be reported,
which shows the check can fail; an audit that counted any mention as a use would pass it.
-/

open Lean Elab Command

namespace AME125Audit

/-- `n` is an `AME125` name; a private name counts by its user-facing form. -/
def inAME125 (n : Name) : Bool := (`AME125).isPrefixOf (privateToUserName n)

/-- The hand-written declarations of `AME125`: everything under the prefix except internal names,
constructors, recursors, inductive types and the lemmas Lean generates. -/
def handWritten (env : Environment) : Array Name :=
  -- Lean generates equation lemmas (`xPow.eq_1`, `eq_def`, `eq_unfold`), congruence lemmas
  -- (`congr_simp`) and, for structures and inductives, constructors, projections, recursors,
  -- `ext`/`injEq` lemmas and per-constructor eliminators (`Kind.J.elim`, `Kind.ctorElim`), none
  -- written by hand.
  -- They are recognised by name only, so these suffixes are reserved: never use them for a
  -- hand-written declaration (`audit/lexical.py` enforces this, reading this list).
  let generated : List String :=
    ["congr_simp", "eq_def", "eq_unfold", "mk", "injEq", "inj", "ext", "ext_iff", "rec",
      "recOn", "casesOn", "noConfusion", "noConfusionType", "ctorIdx", "toCtorIdx", "sizeOf_spec",
      "brecOn", "below", "binductionOn", "ibelow", "elim", "ctorElim", "ctorElimType",
      "splitter"]
  -- Pattern matches compile to auxiliaries `f.match_1`, `f.match_2`, … (and lemmas about them).
  let numbered (pre : String) (s : String) : Bool :=
    s.startsWith pre && s.length > pre.length && (s.toList.drop pre.length).all Char.isDigit
  let isGenerated (n : Name) : Bool :=
    (match n with
      | .str _ s => generated.contains s || numbered "eq_" s
      | _ => false) ||
    n.components.any fun c ↦ match c with
      | .str _ s => numbered "match_" s
      | _ => false
  env.constants.fold (fun (acc : Array Name) n ci ↦
    let u := privateToUserName n
    if inAME125 n && !u.isInternal && !isGenerated u &&
        !(ci matches .ctorInfo _ | .recInfo _ | .inductInfo _) then acc.push n else acc) #[]

/-- The constants a declaration mentions: in its type, its value, and, for an inductive type,
its constructors. -/
def mentions (ci : ConstantInfo) : Array Name :=
  let value := match ci with
    | .thmInfo t => t.value.getUsedConstants
    | .defnInfo d => d.value.getUsedConstants
    | .opaqueInfo o => o.value.getUsedConstants
    | .inductInfo i => i.ctors.toArray
    | _ => #[]
  ci.type.getUsedConstants ++ value

/-- The `AME125` constants reachable from `todo`. Constants outside `AME125` are not followed,
since nothing outside the project mentions it. -/
partial def reachable (env : Environment) (todo : List Name) (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n || !inAME125 n then reachable env rest seen
    else
      let next := (env.find? n).map (fun ci ↦ (mentions ci).toList) |>.getD []
      reachable env (next ++ rest) (seen.insert n)

/-- The hand-written `AME125` declarations not reachable from `roots`. -/
def unreachable (env : Environment) (roots : List Name) : Array Name :=
  let seen := reachable env roots
  (handWritten env).filter fun n ↦ !seen.contains n

end AME125Audit

/-- Control: an orphan recursive definition. Its equation lemma (realised below) mentions it, so
an audit that counted any mention as a use would pass it; this one must report it. -/
public def AME125.vacuityControl : ℕ → ℕ
  | 0 => 0
  | n + 1 => AME125.vacuityControl n

open AME125Audit in
run_cmd do
  let roots : List Name :=
    [`AME125.ame_12_5_open, `AME125.controlState_not_isAME]
  let control : Name := `AME125.vacuityControl
  for r in roots do
    if ((← getEnv).find? r).isNone then throwError m!"{r} missing"
  let eqn ← liftTermElabM <| realizeGlobalConstNoOverloadCore (control ++ `eq_1)
  let env ← getEnv
  unless (env.find? eqn).isSome do
    throwError "control failed: its equation lemma was not generated"
  let ours := (handWritten env).filter (· != control)
  let orphans := unreachable env roots
  unless orphans.contains control do
    throwError "control failed: an orphan definition was not reported"
  let real := orphans.filter (· != control)
  unless real.isEmpty do
    throwError m!"declarations not reachable from the roots: {real.toList}"
  unless ours.size ≥ 40 do throwError m!"only {ours.size} declarations found; wrong prefix?"
  let msg := s!"vacuity audit passed: {ours.size} declarations, all reachable from the two roots"
  logInfo m!"{msg}; control ok"

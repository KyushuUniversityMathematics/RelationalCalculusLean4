import Dedekind
import Lean.Elab.Tactic
open Lean Elab Tactic
variable [c:Dedekind]

@[simp]theorem cap_idem' : α ⊓ β ⊓ β = α ⊓ β := by
  rw[← cap_assoc, cap_idem]
@[simp]theorem cup_idem' : α ⊔ β ⊔ β = α ⊔ β := by
  rw[← cup_assoc, cup_idem]

open Lean Meta Simp

elab "sort" : tactic => do
  let goal ← getMainTarget
  evalTactic (← `(tactic| ac_nf))
  evalTactic (← `(tactic| try simp))
  if (← getGoals).isEmpty then
    pure ()
  else
    let goal' ← getMainTarget
    if goal == goal' then
      throwError "sort failed to rearrange"

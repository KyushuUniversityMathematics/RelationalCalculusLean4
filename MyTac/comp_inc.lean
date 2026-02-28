import Lean
import Dedekind
open Lean Elab Tactic

syntax (name := myconpinc) "comp_inc" : tactic

@[tactic myconpinc]
partial def evalMyConpInc : Tactic := fun _ => do
  withMainContext do
    let rec loop : TacticM Unit := do
      let g ← getMainGoal
      let tgtBefore ← instantiateMVars (← g.getType)
      evalTactic (← `(tactic| repeat rw [← comp_assoc]))
      evalTactic (← `(tactic| try apply comp_inc_compat_ab_ab'))

      evalTactic (← `(tactic| repeat rw [comp_assoc]))
      evalTactic (← `(tactic| try apply comp_inc_compat_ab_a'b))


      -- ゴールが変わったときだけ再帰
      let g' ← getMainGoal
      let tgtAfter ← instantiateMVars (← g'.getType)

      -- 型が変わったときだけ再帰
      unless (← Meta.isExprDefEq tgtBefore tgtAfter) do
        loop
    loop
variable[c:Dedekind]
theorem test_comp_inc(f f':c.rel X Y)(g:c.rel Y Z):
  f ⊑ f' → f ∘ g ⊑ f' ∘ g := by
  intro H
  comp_inc
  assumption

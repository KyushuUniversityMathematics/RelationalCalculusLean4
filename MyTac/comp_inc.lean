import Lean.Elab.Tactic
import Dedekind
open Lean Elab Tactic

elab "comp_inc": tactic => do
  let g ← getMainGoal
  evalTactic (← `(tactic|
    repeat first
    |rw [← comp_assoc]
    |apply comp_inc_compat_ab_ab'
    |apply comp_inc_compat_ab_a
    |apply comp_inc_compat_a_ab
  ))
  evalTactic (← `(tactic|
    repeat first
    |rw [comp_assoc]
    |apply comp_inc_compat_ab_a'b
    |apply comp_inc_compat_ab_b
    |apply comp_inc_compat_b_ab
  ))

  let g' ← getMainGoal
  if g == g' then
    throwError "comp_inc tactic failed to make progress"
  else
    evalTactic (← `(tactic|
      repeat first
      |assumption
      |simp
    ))

-- variable[c:Dedekind]
-- theorem test_comp_inc(f f':c.rel X Y)(g:c.rel Y Z):
--   f ⊑ f' → f ∘ g ⊑ f' ∘ g := by
--   intro H
--   comp_inc
--   assumption

import MyTac.sort
open Lean Meta Elab Tactic
open Lean.Elab.Term
variable [c:Dedekind]

elab "cap_cup_simp" : tactic => do
  evalTactic (← `(tactic|
    conv => rhs; repeat first
                          |rw[cup_cap_distr_l]
                          |rw[cup_cap_distr_r]))
  evalTactic (← `(tactic|
    conv => lhs; repeat first
                          |rw[cap_cup_distr_l]
                          |rw[cap_cup_distr_r]))
  evalTactic (← `(tactic| sort))
  evalTactic (← `(tactic| simp [inc_cap, inc_cup]))

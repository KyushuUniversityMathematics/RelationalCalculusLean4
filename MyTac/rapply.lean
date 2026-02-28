import Lean
import Dedekind
open Lean Meta Elab Tactic Conv

private def last2Sides? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e' ← whnf e
  let args := e'.getAppArgs
  if args.size ≥ 2 then
    pure (some (args[args.size - 2]!, args[args.size - 1]!))
  else
    pure none

/-- デバッグ用 head 名取得 -/
private def headNameStr (e : Expr) : MetaM String := do
  let e' ← whnf e
  match e'.getAppFn.constName? with
  | some n => pure s!"{n}"
  | none   => pure "«non-const head»"

syntax (name := rapply) "rapply " term : tactic
@[tactic rapply] def evalRapply : Tactic := fun stx => do
  match stx with
  | `(tactic| rapply $hTerm) =>
    withMainContext do
      let hExpr  ← elabTerm hTerm none
      let hType  ← inferType hExpr
      let g      ← getMainGoal
      let gType  ← g.getType
      let hSides ← last2Sides? hType
      let gSides ← last2Sides? gType
      match hSides, gSides with
      | some (hL, hR), some (gL, gR) =>
        if (← isDefEq gL hL) && (← isDefEq gR hR) then
          evalTactic (← `(tactic| exact $hTerm))
        else if ← isDefEq gL hL then
          evalTactic (← `(tactic| refine inc_trans $hTerm ?_))
        else if ← isDefEq gR hR then
          evalTactic (← `(tactic| refine inc_trans ?_ $hTerm))
        else
          throwError m!"rapply: lhs/rhs 不一致\n  given: {← ppExpr hL} ⊑ {← ppExpr hR}\n  goal : {← ppExpr gL} ⊑ {← ppExpr gR}\n  head(hyp)={← headNameStr hType} head(goal)={← headNameStr gType}"
      | _, _ =>
        throwError m!"rapply: 末尾2引数が取得できません。\n  hyp-type: {← ppExpr hType}\n  goal-type: {← ppExpr gType}\n  head(hyp)={← headNameStr hType} head(goal)={← headNameStr gType}"
  | _ => throwUnsupportedSyntax

theorem mytest {c : Dedekind} {X Y Z : c.ob} {f f' : c.rel X Y} {g g' : c.rel Y Z}
  (H1 : f ⊑ f') (H2 : g ⊑ g') : (f ∘ g) ⊑ (f' ∘ g') := by
  have H3 : f ∘ g ⊑ f' ∘ g := by
    apply comp_inc_compat_ab_a'b H1
  rapply H3
  apply comp_inc_compat_ab_ab'
  rapply H2

import Lean

open Lean Elab Tactic Meta

theorem acrw1{op : X → X → X}{x y : X}(assoc : ∀ a b c : X, op (op a b) c = op a (op b c))(H : op x y = w) :
  ∀ z, op x (op y z) = op w z := by
  intro z
  rw[← assoc, H]

theorem acrw2{op : X → X → X}{x y : X}(assoc : ∀ a b c : X, op (op a b) c = op a (op b c))(H : op x y = w) :
  ∀ z, op (op z x) y = op z w := by
  intro z
  rw[assoc, H]

theorem acrw3{op : X → X → X}{x y : X}(assoc : ∀ a b c : X, op (op a b) c = op a (op b c))(H : op x y = a) :
  ∀ z w, op (op w x) (op y z) = op (op w a) z := by
  intro z w
  rw[assoc, acrw1 assoc H, ← assoc]



-- 構文定義は Parser 側
namespace Lean.Parser.Tactic
syntax (name := mytac) "mytac" "[" ident,+ "]" ("at" ident)? : tactic
end Lean.Parser.Tactic

-- 実装は Elab 側
namespace Lean.Elab.Tactic

@[builtin_tactic Lean.Parser.Tactic.mytac]
def evalMyTac : Tactic := fun stx => do
  let cfg ← elabRewriteConfig stx[1]
  let loc := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (rewriteLocalDecl term symm · cfg)
      (rewriteTarget term symm cfg)
      (throwTacticEx `mytac · "Did not find an occurrence of the pattern in the current goal")

end Lean.Elab.Tactic

  

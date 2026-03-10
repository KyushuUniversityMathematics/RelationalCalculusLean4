import Dedekind
import Lean
variable [c : Dedekind]

open Lean Meta Elab Tactic Conv
open Lean.Elab.Term

inductive RelExpr : c.ob → c.ob → Type
| atom   {X Y} : c.rel X Y → RelExpr X Y
| id     {X}   : RelExpr X X
| comp   {X Y Z} : RelExpr X Y → RelExpr Y Z → RelExpr X Z
| cap    {X Y} : RelExpr X Y → RelExpr X Y → RelExpr X Y
| cup    {X Y} : RelExpr X Y → RelExpr X Y → RelExpr X Y
| inv    {X Y} : RelExpr X Y → RelExpr Y X
| residual {X Y Z} : RelExpr X Y → RelExpr Y Z → RelExpr X Z
| empty  {X Y} : RelExpr X Y
| universal {X Y} : RelExpr X Y
| rpc    {X Y} : RelExpr X Y → RelExpr X Y → RelExpr X Y

def RelExpr.eval :
  {X Y : c.ob} →
  RelExpr X Y →
  c.rel X Y
| _, _, RelExpr.atom f        => f
| _, _, RelExpr.id            => idr _
| _, _, RelExpr.comp f g      => f.eval ∘ g.eval
| _, _, RelExpr.cap f g       => f.eval ⊓ g.eval
| _, _, RelExpr.cup f g       => f.eval ⊔ g.eval
| _, _, RelExpr.inv f         => (f.eval)#
| _, _, RelExpr.residual f g  => f.eval ▹ g.eval
| _, _, RelExpr.empty         => φ _ _
| _, _, RelExpr.universal     => Δ _ _
| _, _, RelExpr.rpc f g       => f.eval ⇒ g.eval

def flattenCap :
  {X Y : c.ob} →
  RelExpr X Y →
  List (RelExpr X Y)
| _, _, RelExpr.cap a b =>
    flattenCap a ++ flattenCap b
| _, _, t => [t]

def rebuildCap : List (RelExpr X Y) → RelExpr X Y
| []      => RelExpr.universal
| x :: xs => RelExpr.cap x (rebuildCap xs)

def atomKey : Expr → Option String
| Expr.fvar id   => some id.name.toString
| Expr.const n _ => some n.toString
| Expr.lit (.natVal n) => some (toString n)
| _ => none
def atomRelLt (a b : RelExpr X Y) : Bool :=
  match a, b with
  | RelExpr.atom ea, RelExpr.atom eb =>
      let ea' := Tactic.elabTerm ea
      let eb' := Tactic.elabTerm eb
      match atomKey ea', atomKey eb' with
      | some sa, some sb => sa > sb
      | some _, none     => false
      | none, some _     => true
      | none, none       => false
  | RelExpr.atom _, _ => false
  | _, RelExpr.atom _ => true
  | _, _              => false

def normalizeCap (e : RelExpr X Y) : RelExpr X Y :=
  let xs := flattenCap e
  let xs := xs.mergeSort  -- ここで mergeSort
  rebuildCap xs

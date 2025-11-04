class Quiver where
  ob  : Type u
  rel : ob → ob → Type v

class PreCategory extends Quiver where
  id    : (X : ob) → (rel X X)
  comp  : (rel X Y) → (rel Y Z) → (rel X Z)

infixl:80 " ∘ " => PreCategory.comp

class Category extends PreCategory where
  comp_id_l : (f : rel X Y) → (id X ∘ f) = f
  comp_id_r : (f : rel X Y) → (f ∘ id Y) = f
  comp_assoc   : ∀ {X Y Z W : ob} (f : rel W X) (g : rel X Y) (h : rel Y Z),
                (f ∘ g) ∘ h = f ∘ (g ∘ h)

class Dedekind_Notations extends Category where
  inverse : rel X Y → rel Y X
  redidual : rel X Y → rel Y Z → rel X Z
  empty : (X : ob) → (Y : ob) → rel X Y
  universal : (X : ob) → (Y : ob) → rel X Y
  inc : rel X Y → rel X Y → Prop
  cup : rel X Y → rel X Y → rel X Y
  cupP: (rel X Y → Prop) → (rel X Y → rel Z W) → rel Z W
  cap : rel X Y → rel X Y → rel X Y
  capP: (rel X Y → Prop) → (rel X Y → rel Z W) → rel Z W
  rpc : rel X Y → rel X Y → rel X Y

def idr [c : Dedekind_Notations](X:c.ob) := c.id X
def inverse [c : Dedekind_Notations]{X Y:c.ob}(f : c.rel X Y) := c.inverse f
postfix:120 " # " => inverse
infixl:80 " ▹ " => Dedekind_Notations.redidual
def φ [c : Dedekind_Notations] := c.empty
def Δ [c : Dedekind_Notations] := c.universal
infixl:51 " ⊑ " => Dedekind_Notations.inc
infixl:70 " ⊔ " => Dedekind_Notations.cup
def cupP [c : Dedekind_Notations]{X Y Z W:c.ob}(P : c.rel X Y → Prop)(f : c.rel X Y → c.rel Z W) := c.cupP P f
infixl:70 " ⊓ " => Dedekind_Notations.cap
def capP [c : Dedekind_Notations]{X Y Z W:c.ob}(P : c.rel X Y → Prop)(f : c.rel X Y → c.rel Z W) := c.capP P f
infixl:81 " ⇒ " => Dedekind_Notations.rpc
def complement [c : Dedekind_Notations]{X Y:c.ob}(f : c.rel X Y) := f ⇒ φ X Y
postfix:120 " ⁻ " => complement

class Dedekind extends Dedekind_Notations where
    inc_refl (f:rel X Y) : f ⊑ f
    inc_trans {f g h : rel X Y} : inc f g → inc g h → inc f h
    inc_antisym {f g : rel X Y}: f ⊑ g → g ⊑ f → f = g
    inc_cap {f g h : rel X Y} : f ⊑ g ⊓ h ↔ f ⊑ g ∧ f ⊑ h
    inc_capP {f : rel Z W} {P : rel X Y → Prop}{α : rel X Y → rel Z W} : f ⊑ (capP P α) ↔ ∀ g, P g → f ⊑ α g
    inc_cup {f g h : rel X Y} : f ⊔ g ⊑ h ↔ f ⊑ h ∧ g ⊑ h
    inc_cupP {f : rel Z W} {P : rel X Y → Prop}{β : rel X Y → rel Z W} : cupP P β ⊑ f ↔ ∀ g, P g → β g ⊑ f
    inc_empty  (f : rel X Y) : φ X Y ⊑ f
    inc_universal (f : rel X Y) : f ⊑ Δ X Y
    inc_rpc {f g h : rel X Y} : f ⊑ g ⇒ h ↔ f ⊓ g ⊑ h
    inv_invol (f : rel X Y) : (f#)# = f
    comp_inv (f : rel X Y) (g : rel Y Z) : (f ∘ g)# = g# ∘ f#
    inc_inv {f g : rel X Y} : f ⊑ g → f# ⊑ g#
    dedekind : f ∘ g ⊓ h ⊑ (f ⊓ h ∘ g#) ∘ (g ⊓ f# ∘ h)
    inc_redidual {f : rel X Y}{g : rel Y Z}{h : rel X Z}  : h ⊑ f ▹ g ↔ f# ∘ h ⊑ g

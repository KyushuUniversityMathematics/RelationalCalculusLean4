import Dedekind

class Schroder extends Dedekind where
  complement_classic {f:rel X Y}: f ⊔ f⁻ = Δ X Y

section schroder
variable [c:Schroder]
@[simp]theorem complement_classic (f:c.rel X Y): f ⊔ f⁻ = Δ X Y := c.complement_classic
@[simp]theorem complement_classic' (f:c.rel X Y): f⁻ ⊔ f = Δ X Y := by
  rw[cup_comm, complement_classic]
@[simp]theorem complement_invol (f:c.rel X Y) : (f⁻)⁻ = f := by
  apply inc_antisym _ complement_invol_inc
  rw[← cap_universal (f⁻⁻), ← complement_classic f, cap_cup_distr_l, cap_comm _ (f⁻), cap_complement_empty, cup_empty]
  simp
theorem complement_move : f = g⁻ ↔ f⁻ = g := by
  constructor
  · intro H
    rw[H, complement_invol]
  · intro H
    rw[← complement_invol f, H]
theorem de_morgan2 : (f ⊓ g)⁻ = f⁻ ⊔ g⁻ := by
  simp[← complement_move, de_morgan1]
theorem de_morgan4 : (capP P α)⁻ = cupP P (fun x => (α x)⁻) := by
  rw[← complement_move, de_morgan3]
  apply inc_antisym
  · rw[inc_capP]
    intro h H0
    rw[complement_invol]
    apply capP_inc H0
  · rw[inc_capP]
    intro h H0
    rw[← complement_invol (α h)]
    apply capP_inc H0
theorem inc_complement : f ⊑ g → g⁻ ⊑ f⁻ := by
  intro H
  rw[← complement_invol g, complement, inc_rpc] at H
  conv => rhs; rw[complement]
  rw[inc_rpc, cap_comm]
  assumption
@[simp]theorem cup_to_rpc : (f ⇒ g) = f⁻ ⊔ g := by
  apply inc_antisym
  · rw[← cap_universal (f ⇒ g), ← complement_classic f, cap_cup_distr_l, cap_comm, rpc_l, inc_cup]
    constructor
    · apply inc_trans cap_r cup_r
    · apply inc_trans cap_r cup_l
  · rw[inc_rpc, cap_cup_distr_r, cap_comm, cap_complement_empty, empty_cup]
    simp
theorem contraposition : g⁻ ⇒ f⁻ = f ⇒ g := by
  simp[inc_antisym']
  ac_nf
  simp
theorem beta_contradiction : f ⇒ g ⊓ f ⇒ g⁻ = f⁻ := by
  simp[← cup_cap_distr_l]
theorem bool_lemma1 {f g : c.rel X Y} : f ⊑ g ↔ Δ X Y = f⁻ ⊔ g := by
  constructor
  · intro h
    simp
    apply inc_trans _ (cup_inc_compat_l h)
    simp
  · intro h
    rw[← cap_universal f, h, cap_cup_distr_l]
    simp
theorem bool_lemma2 {f g : c.rel X Y} : f ⊑ g ↔ f ⊓ g⁻ = φ X Y := by
  rw[bool_lemma1, ← complement_invol (φ X Y), complement_empty, complement_move, de_morgan2, complement_invol]
  constructor
  all_goals
    intro H
    rw[H]
theorem bool_lemma3 {f g : c.rel X Y} : f ⊑ g ⊔ h ↔ f ⊓ g⁻ ⊑ h := by
  constructor
  · intro H
    apply inc_trans (cap_inc_compat_r H)
    rw[cap_cup_distr_r, cap_complement_empty, empty_cup]
    simp
  · intro H
    apply inc_trans _ (cup_inc_compat_l H)
    rw[cup_cap_distr_l, complement_classic, cap_universal]
    simp
theorem bool_lemma4 {f g : c.rel X Y} : f ⊑ g ⊔ h ↔ g⁻ ⊑ f⁻ ⊔ h := by
  rw[bool_lemma3]
  constructor
  · intro H
    apply inc_trans _ (cup_inc_compat_l H)
    simp[cup_cap_distr_l]
  · intro H
    apply inc_trans (cap_inc_compat_l H)
    simp[cap_cup_distr_l]
theorem bool_lemma5 {f g : c.rel X Y} : f ⊑ g ⊔ h ↔ Δ X Y = f⁻ ⊔ g ⊔ h := by
  rw[bool_lemma1, cup_assoc]
theorem cup_capP_distr_l : f ⊔ capP P α = capP P (fun x => f ⊔ α x) := by
  apply inc_lower.mpr
  intro h
  constructor
  · intro H
    rw[inc_capP]
    intro g H0
    apply inc_trans H
    apply cup_inc_compat_l
    apply capP_inc H0
  · intro H
    rw[bool_lemma3, inc_capP]
    intro g H0
    rw[← bool_lemma3]
    apply inc_trans H
    apply capP_inc H0
theorem cup_capP_distr_r : capP P α ⊔ f = capP P (fun x => α x ⊔ f) := by
  rw[cup_comm, cup_capP_distr_l]
  apply inc_antisym
  all_goals
    rw[inc_capP]
    intro h H0
    rw[cup_comm]
    apply capP_inc H0
end schroder

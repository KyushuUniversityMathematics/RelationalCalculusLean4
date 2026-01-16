import Dedekind
import Schroder
import Dedekind_Formula
section residual
variable [c:Dedekind]
theorem double_residual {X Y Z:c.ob}(f:c.rel X Y)(g:c.rel Y Z)(h:c.rel Z W):
  f ▹ (g ▹ h) = (f ∘ g) ▹ h := by
  apply inc_lower.mpr
  intro k
  conv => rhs; rw[inc_residual, comp_inv, ← comp_assoc, ← inc_residual, ← inc_residual]
theorem inv_residual_inc : f# ∘ (f ▹ g) ⊑ g := by
  simp[← inc_residual]
theorem inc_residual_inv : g ⊑ f ▹ (f# ∘ g) := by
  simp[inc_residual]
theorem id_inc_residual {X Y:c.ob}(f:c.rel X Y):
  idr X ⊑ f ▹ f# := by
  simp[inc_residual]
theorem residual_universal {X Y Z:c.ob}(f:c.rel X Y):
  f ▹ (Δ Y Z) = Δ X Z := by
  apply inc_antisym (inc_universal _)
  simp[inc_residual]
theorem residual_inc_compat : f' ⊑ f → g ⊑ g' → (f ▹ g) ⊑ (f' ▹ g') := by
  intro H1 H2
  simp[inc_residual]
  apply inc_trans _ H2
  apply inc_trans
  · apply comp_inc_compat_ab_a'b
    rw[inv_inc_move, inv_invol]
    apply H1
  · apply inv_residual_inc
theorem residual_inc_compat_r : f' ⊑ f → (f ▹ g) ⊑ (f' ▹ g) := by
  intro H
  apply residual_inc_compat H (inc_refl g)
theorem residual_inc_compat_l : g ⊑ g' → (f ▹ g) ⊑ (f ▹ g') := by
  intro H
  apply residual_inc_compat (inc_refl f) H
theorem residual_capP_distr_l :
  f ▹ capP P α = capP P (fun x => f ▹ α x) := by
  apply inc_lower.mpr
  intro h
  rw[inc_residual]
  constructor
  · intro H
    rw[inc_capP]
    intro g H0
    rw[inc_residual]
    apply inc_trans H
    apply capP_inc H0
  · intro H
    rw[inc_capP]
    intro g H0
    rw[inc_capP] at H
    specialize H g H0
    rw[← inc_residual]
    assumption
theorem residual_cap_distr_l :
  f ▹ (g ⊓ h) = (f ▹ g) ⊓ (f ▹ h) := by
  apply inc_lower.mpr
  intro k
  rw[inc_residual, inc_cap, inc_cap, inc_residual, inc_residual]
theorem residual_cupP_distr_r :
  cupP P α ▹ f = capP P (fun x => α x ▹ f) := by
  apply inc_lower.mpr
  intro h
  constructor
  · intro H
    rw[inc_residual, ← inv_invol f, inv_inc_move, comp_inv, inv_invol, ← inc_residual, inc_cupP] at H
    rw[inc_capP]
    intro g H0
    specialize H g H0
    rw[inc_residual, inv_inc_move, comp_inv, inv_invol, ← inc_residual] at H
    assumption
  · intro H
    rw[inc_capP] at H
    rw[inc_residual, ← inv_invol f, inv_inc_move, comp_inv, inv_invol, ← inc_residual, inc_cupP]
    intro g H0
    specialize H g H0
    rw[inc_residual, inv_inc_move, comp_inv, inv_invol, ← inc_residual]
    assumption
theorem residual_cup_distr_r :
  (g ⊔ h) ▹ f = g ▹ f ⊓ h ▹ f := by
  apply inc_lower.mpr
  · intro k
    rw[inc_residual]
    simp
    rw[inc_cup, ← inc_residual, ← inc_residual, inc_cap]
theorem total_residual {X Y Z:c.ob}{f:c.rel X Y}{g:c.rel Y Z}:
  is_total f → f ▹ g ⊑ f ∘ g := by
  intro H
  apply inc_trans (comp_inc_compat_b_ab H)
  rw[← comp_assoc]
  apply comp_inc_compat_ab_ab' inv_residual_inc
theorem univalent_residual {X Y Z:c.ob}{f:c.rel X Y}{g:c.rel Y Z}:
  is_univalent f → f ∘ g ⊑ f ▹ g := by
  intro H
  rw[inc_residual, comp_assoc]
  apply comp_inc_compat_ab_b H
theorem function_residual {X Y Z:c.ob}{f:c.rel X Y}{g:c.rel Y Z}:
  is_function f → f ▹ g = f ∘ g := by
  intro H
  apply inc_antisym
  · apply total_residual H.left
  · apply univalent_residual H.right
theorem residual_id (f:c.rel X Y) : idr X ▹ f = f := by
  conv => rhs; rw[← comp_id_l f]
  apply function_residual
  simp[is_function]
theorem universal_residual {X Y:c.ob}(f:c.rel X Y):
  Δ X X ▹ f ⊑ f := by
  conv => rhs; rw[← residual_id f]
  apply residual_inc_compat_r
  simp
theorem function_residual2 {X Y Z:c.ob}{f:c.rel X Y}{g:c.rel Y Z}{h:c.rel Z W}:
  is_function f → f ∘ (g ▹ h) = (f ∘ g) ▹ h := by
  intro H
  rw[← function_residual H, double_residual]
theorem function_residual3 {X Y Z:c.ob}{f:c.rel W Z}{g:c.rel X Y}{h:c.rel Y Z}:
  is_function f → (g ▹ h) ∘ f# = g ▹ (h ∘ f#) := by
  intro H
  apply inc_lower.mpr
  intro k
  rw[inc_residual, ← function_move2 H, ← function_move2 H, inc_residual, comp_assoc]


theorem residual_property1 {X Y Z:c.ob}{f:c.rel X Y}{g:c.rel Y Z}{h:c.rel Z W}:
  (f ▹ g) ∘ h ⊑ f ▹ (g ∘ h) := by
  apply inc_trans inc_residual_inv
  apply residual_inc_compat_l
  rw[comp_assoc]
  apply comp_inc_compat_ab_a'b
  apply inv_residual_inc
theorem residual_property2 {X Y Z:c.ob}(f:c.rel X Y)(g:c.rel Y Z)(h:c.rel Y W):
  (f ▹ g)∘(g# ▹ h) ⊑ f ▹ h := by
  apply inc_trans residual_property1
  apply residual_inc_compat_l
  conv => lhs; lhs; rw[← inv_invol g]
  apply inv_residual_inc








end residual



section residual_shroder
variable [c:Schroder]
theorem residual_complement {X Y Z:c.ob}(f:c.rel X Y)(g:c.rel Y Z):
  f ▹ g = (f ∘ g⁻)⁻ := by
  apply inc_lower.mpr
  intro h
  rw[inc_residual, bool_lemma2, bool_lemma2, complement_invol]
  constructor
  · intro H
    apply inc_antisym _ (inc_empty _)
    rw[cap_comm]
    apply inc_trans dedekind1
    rw[cap_comm, H]
    simp
  · intro H
    apply inc_antisym _ (inc_empty _)
    apply inc_trans dedekind1
    simp[H]
end residual_shroder

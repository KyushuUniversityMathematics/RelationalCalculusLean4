import Dedekind
import Function
import Point

section dedekind_formula
variable [c:Dedekind]
theorem dedekind1 : f ∘ g ⊓ h ⊑ f ∘ (g ⊓ f# ∘ h) := by
  apply inc_trans dedekind
  apply comp_inc_compat_ab_a'b
  simp
theorem dedekind2 : f ∘ g ⊓ h ⊑ (f ⊓ h ∘ g#) ∘ g := by
  apply inc_trans dedekind
  apply comp_inc_compat_ab_ab'
  simp
theorem rel_inv_rel {f : c.rel X Y} : f ⊑ (f ∘ f#) ∘ f := by
  have H := @dedekind1 _ X Y f _ (idr Y) f
  simp at H
  apply inc_trans H
  rw[← comp_assoc]
  apply comp_inc_compat_ab_ab'
  simp
theorem dedekind_universal1 {f:c.rel Y Z}: (Δ X Z ∘ f#) ∘ f = Δ X Y ∘ f := by
  apply inc_antisym
  · apply comp_inc_compat_ab_a'b
    simp
  · apply inc_trans
    · apply comp_inc_compat_ab_ab' rel_inv_rel
    · simp
      apply comp_inc_compat_ab_a'b
      apply comp_inc_compat_ab_a'b
      simp
theorem dedekind_universal2b {f:c.rel X Y}: Δ Z Z ∘ g ⊑ Δ Z X ∘ f → g ⊑ (g ∘ f#) ∘ f := by
  intro H
  apply inc_trans (inc_cap.mpr ⟨inc_refl _, comp_inc_compat_b_ab (inc_universal _)⟩)
  apply inc_trans (cap_inc_compat_l H)
  rw[cap_comm]
  apply inc_trans dedekind2
  apply comp_inc_compat_ab_a'b
  simp

theorem comp_subid_cap {f g:c.rel X X}: f ⊑ idr X → g ⊑ idr X → f ∘ g = f ⊓ g := by
  intro H H0
  apply inc_antisym
  · apply inc_cap.mpr
    constructor
    · apply comp_inc_compat_ab_a H0
    · apply comp_inc_compat_ab_b H
  · have H1 : f ⊓ g ⊑ idr X := by
      rw[← cap_idem (idr X)]
      apply cap_inc_compat H H0
    rw[← comp_subid H1]
    apply comp_inc_compat
    all_goals simp
theorem residual_rpc_subid {f g:c.rel X X} : f ⊑ idr X → g ⊑ idr X → (f ▹ g) ⊓ idr X = (f ⇒ g) ⊓ idr X := by
  intro H H0
  apply inc_lower.mpr
  intro h
  rw[inc_cap, inc_cap]
  constructor
  · intro ⟨H1, H2⟩
    apply And.intro _ H2
    rw[inc_rpc]
    rw[inc_residual, inv_subid H, comp_subid_cap H H2, cap_comm] at H1
    exact H1
  · intro ⟨H1, H2⟩
    apply And.intro _ H2
    rw[inc_rpc] at H1
    rw[inc_residual, inv_subid H, comp_subid_cap H H2, cap_comm]
    exact H1
end dedekind_formula

section dedekind_formula_unit
variable [c:Dedekind_unit]
theorem dedekind_universal2a : Δ I Z ∘ g ⊑ Δ I X ∘ f → Δ Z Z ∘ g ⊑ Δ Z X ∘ f := by
  intro H
  rw[← comp_unit_universal Z, ← tarski2 Z X, ← comp_assoc, ← comp_assoc]
  apply comp_inc_compat_ab_ab' H
theorem dedekind_universal2c {f:c.rel X Y}{g : c.rel Z Y}: g ⊑ (g ∘ f#) ∘ f → Δ I Z ∘ g ⊑ Δ I X ∘ f := by
  intro H
  apply inc_trans (comp_inc_compat_ab_ab' H)
  simp
  apply comp_inc_compat_ab_a'b
  simp
theorem dedekind_universal3a {f:c.rel X Y}{g:c.rel X Z}: g ∘ Δ Z I ⊑ f ∘ Δ Y I ↔ g ∘ Δ Z Z ⊑ f ∘ Δ Y Z := by
  constructor
  · intro H
    rw[← inv_invol (_ ∘ _), ← inv_inc_move]
    simp
    apply dedekind_universal2a
    rw[← inv_invol (_ ∘ _), ← inv_inc_move]
    simp
    assumption
  · intro H
    rw[← inv_invol (_ ∘ _), ← inv_inc_move]
    simp
    apply dedekind_universal2c
    apply dedekind_universal2b
    rw[← inv_invol (_ ∘ _), ← inv_inc_move]
    simp
    assumption
theorem dedekind_universal3b {f:c.rel X Y}{g:c.rel X Z}: g ∘ Δ Z I ⊑ f ∘ Δ Y I ↔ g ⊑ (f ∘ f#) ∘ g := by
  constructor
  · intro H
    conv => lhs; rw[← inv_invol g]
    rw[← inv_inc_move, comp_inv, comp_inv, comp_assoc]
    apply dedekind_universal2b
    apply dedekind_universal2a
    rw[← inv_invol (_ ∘ _), ← inv_inc_move]
    simp
    assumption
  · intro H
    rw[← inv_invol (_ ∘ _), ← inv_inc_move]
    simp
    apply dedekind_universal2c
    rw[← inv_inc_move]
    simp
    assumption
theorem universal_total {f:c.rel X Y} :
  (f ∘ Δ Y I = Δ X I) ↔ is_total f := by
  have H := @dedekind_universal3b _ _ _ _ f (idr X)
  simp at H
  rw[is_total, ← H]
  constructor
  · intro H
    rw[H]
    simp
  · intro H
    apply inc_antisym _ H
    simp
end dedekind_formula_unit

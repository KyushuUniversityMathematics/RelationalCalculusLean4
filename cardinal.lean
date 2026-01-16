import Bernstein
import Sum_Product



def card_le [c:Dedekind](X Y : c.ob) := ∃ f : c.rel X Y, is_injective f
def card_eq [c:Dedekind](X Y : c.ob) := ∃ f : c.rel X Y, is_bijective f
def is_finite [c:Dedekind](X : c.ob) := ∀ f : c.rel X X, is_injective f → is_bijective f

section dedekind_cardinal
variable [c : Dedekind]
theorem card_eq_refl (X : c.ob) : card_eq X X := by
  exists (idr X)
  apply id_bijective
theorem card_eq_symm {X Y : c.ob} :
  card_eq X Y → card_eq Y X := by
  intro H
  cases H with | intro f Hf
  exists (f#)
  exact inv_bijective _ Hf
theorem card_eq_trans {X Y Z : c.ob} :
  card_eq X Y → card_eq Y Z → card_eq X Z := by
  intro HXY HYZ
  cases HXY with | intro f Hf
  cases HYZ with | intro g Hg
  exists (f ∘ g)
  exact comp_bijective Hf Hg
theorem card_le_trans {X Y Z : c.ob} :
  card_le X Y → card_le Y Z → card_le X Z := by
  intro HXY HYZ
  cases HXY with | intro f Hf
  cases HYZ with | intro g Hg
  exists (f ∘ g)
  apply comp_injective Hf Hg
theorem card_eq_le {X Y : c.ob} :
  card_eq X Y → card_le X Y := by
  intro H
  cases H with | intro f Hf
  exists f
  exact bijective_injective _ Hf

theorem infinite {f : c.rel X X} : is_injective f → ¬ is_bijective f → ¬ is_finite X:= by
  intro Hf Hnb Hfin
  rw[is_finite] at Hfin
  have Hbij : is_bijective f := Hfin f Hf
  contradiction
-- theorem le_infinite : ¬ is_finite X → card_le X Y → ¬ is_finite Y := by
--   intro Xnf Hle Yf
--   apply Xnf
--   cases Hle with | intro f Hf
--   contradiction

end dedekind_cardinal

section shroder_cardinal
variable [s : Schroder]
theorem card_bernstein {X Y : s.ob} :
  card_le X Y → card_le Y X → card_eq X Y := by
  rw[card_le, card_le, card_eq]
  intro HXY HYX
  exact bernstein HXY HYX
theorem finit_le_finit : is_finite Y → card_le X Y → is_finite X:= by
  rw[is_finite, card_le, is_finite]
  intro HY H f Hf
  cases H with | intro g Hg
  rw[is_injective] at Hf Hg
  let h := ((g# ∘ f) ∘ g) ⊔ (g# ∘ g)ᶜ
  have H : g ∘ (g# ∘ g)ᶜ = φ X Y := by
    apply inc_antisym _ (inc_empty _)
    conv => lhs; lhs; rw[← comp_id_l g]
    rw[← Hg.left, ← comp_empty_r g, ← comp_assoc, ← comp_assoc]
    apply comp_inc_compat_ab_ab'
    rw[comp_assoc, comp_complement'_empty Hg.right]
    simp
  have H0 : is_injective h := by
    rw[is_injective]
    constructor
    · dsimp[h]
      simp
      conv =>
        lhs;lhs;lhs;lhs;lhs
        conv =>
          lhs; rw[← comp_assoc, Hg.left]
          simp
        rw[← comp_assoc, Hf.left]
        simp
      conv =>
        lhs;lhs;lhs;rhs;lhs;lhs
        rw[← inv_invol (_ ∘ _), comp_inv, inv_invol, inv_subid complement'_le_id, H]
      conv =>
        lhs;lhs;rhs
        rw[inv_subid complement'_le_id, ← comp_assoc, H]
      conv =>
        lhs;rhs
        rw[inv_subid complement'_le_id, comp_subid complement'_le_id]
      simp
      rw[complement'_cup_id _ Hg.right]
    · dsimp[h]
      simp
      rw[inv_subid complement'_le_id]
      conv =>
        lhs; lhs; lhs; rhs; lhs; lhs; rw[← inv_invol (_ ∘ _), comp_inv, inv_invol, inv_subid complement'_le_id, H]
      conv =>
        lhs; lhs; rhs; rw[← comp_assoc, H]
      simp
      rw[comp_subid complement'_le_id, ← complement'_cup_id _ Hg.right]
      apply cup_inc_compat_r
      apply comp_inc_compat_ab_a'b
      rw[← comp_assoc, ← comp_assoc, ← comp_assoc]
      apply comp_inc_compat_ab_a
      conv => lhs; rhs; rw[comp_assoc, Hg.left]
      simp
      exact Hf.right
  have H0 : idr Y ⊑ h# ∘ h := by
    have H := (HY _ H0)
    rw[is_bijective] at H
    exact (inc_antisym'.mpr H.right).right
  rw[is_bijective]
  apply And.intro Hf.left
  apply inc_antisym Hf.right
  have H0 : idr Y ⊑ ((g# ∘ f#) ∘ f) ∘ g ⊔ (g# ∘ g)ᶜ := by
    apply inc_trans H0
    dsimp[h]
    simp
    conv =>
      lhs; lhs; lhs; lhs; lhs; lhs
      rw[← comp_assoc, Hg.left]
      simp
    conv =>
      lhs; lhs; lhs; rhs; lhs; lhs
      rw[← comp_inv, H]
    simp
    conv =>
      lhs; rhs
      rw[inv_subid complement'_le_id, comp_subid complement'_le_id]
    conv =>
      lhs; lhs; rhs
      rw[← comp_assoc, H]
    simp
  rw[← comp_id_l (f#), ← comp_id_r (_ ∘ _), ← Hg.left, comp_assoc]
  conv => rhs; rw[← cup_empty (_ ∘ _), ← comp_empty_l (g#), ← H, ← comp_cup_distr_r, ← comp_assoc, ← comp_assoc, ← comp_assoc, ← comp_cup_distr_l]
  apply comp_inc_compat_ab_a'b
  apply comp_inc_compat_a_ab
  rw[comp_assoc, comp_assoc]
  assumption

end shroder_cardinal

section sum
variable [c : Dedekind_sum]
theorem sum_card_le1 : card_le X (X + Y) := by
  exists (in_l X Y)
  apply inl_injective
theorem sum_card_le2 : card_le Y (X + Y) := by
  exists (in_r X Y)
  apply inr_injective
theorem sum_card_eq : card_eq (X + Y) (Y + X) := by
  exists (in_l X Y# ∘ in_r Y X ⊔ (in_r X Y# ∘ in_l Y X))
  constructor
  · simp
  · simp
    rw[cup_comm]
    simp
end sum

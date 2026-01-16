import Dedekind_Formula
import Function
import Schroder

section domain
variable [c:Dedekind]
def domain (f:c.rel X Y) := f ∘ f# ⊓ idr X

theorem domain_subid {f:c.rel X Y}: domain f ⊑ idr X := by
  simp[domain]
theorem domain_def {f:c.rel X Y}: domain f = f ∘ Δ Y X ⊓ idr X := by
  rw[domain]
  apply inc_antisym
  · apply cap_inc_compat_r
    apply comp_inc_compat_ab_ab'
    simp
  · apply inc_cap.mpr
    constructor
    · apply inc_trans dedekind1
      simp
    · simp
@[simp]theorem domain_inv {f:c.rel X Y}: (domain f)# = domain f := by
  rw[domain, inv_subid]
  simp
theorem domain_comp1 (f:c.rel X Y) : domain f ∘ f = f := by
  rw[domain]
  apply inc_antisym
  · apply comp_inc_compat_ab_b
    simp
  · rw[cap_comm]
    apply inc_trans _ dedekind2
    simp
theorem domain_comp2 : f# ∘ domain f = f# := by
  rw[inv_move, comp_inv, domain_inv, inv_invol, domain_comp1]
theorem domain_inc_compat {f g:c.rel X Y} :
  f ⊑ g → domain f ⊑ domain g := by
  intro H
  rw[domain, domain]
  apply cap_inc_compat_r
  apply comp_inc_compat H
  simp[H]
theorem domain_total {f:c.rel X Y}: is_total f ↔ domain f = idr X := by
  rw[is_total, domain]
  constructor
  · intro H
    rw[← inc_def1r.mpr H]
  · intro H
    apply inc_def1r.mp
    rw[H]
theorem domain_inc_id {f:c.rel X X} : f ⊑ idr X ↔ domain f = f := by
  rw[domain]
  constructor
  · intro H
    rw[inv_subid H, comp_subid H, ← inc_def1l.mpr H]
  · intro H
    rw[← H]
    simp
theorem comp_domain1 : domain (f ∘ g) ⊑ domain f := by
  rw[domain, domain]
  simp
  apply inc_trans
  · rw[← cap_idem (idr _), cap_assoc]
    apply cap_inc_compat_r
    conv => lhs; lhs; rw[← comp_assoc, ← comp_assoc]; rhs; rw[comp_assoc]
    apply inc_trans dedekind1
    rw[comp_id_r]
    apply inc_refl
  · apply cap_inc_compat_r
    apply comp_inc_compat_ab_ab'
    simp
theorem comp_domain2 : domain (f ∘ g) = domain (f ∘ domain g) := by
  apply inc_antisym
  · conv => lhs; rw[← domain_comp1 g]
    rw[comp_assoc]
    apply inc_trans comp_domain1
    simp
  · apply inc_trans
    · apply domain_inc_compat
      apply comp_inc_compat_ab_ab'
      rw[domain]
      apply cap_l
    · simp
      apply comp_domain1
theorem comp_domain3 : is_total g → domain (f ∘ g) = domain f := by
  rw[is_total]
  intro H
  apply inc_antisym
  · apply comp_domain1
  · rw[domain, domain]
    simp
    apply cap_inc_compat_r
    apply comp_inc_compat_ab_a'b
    rw[← comp_assoc]
    apply comp_inc_compat_a_ab H
theorem comp_domain4 : domain (f#) ⊑ domain g → domain (f ∘ g) = domain f := by
  intro H
  apply inc_antisym
  · apply comp_domain1
  · rw[domain, domain]
    rw[← domain_comp1 (f#)]
    apply cap_inc_compat_r
    simp
    apply comp_inc_compat_ab_a'b
    rw[← comp_assoc]
    apply comp_inc_compat_ab_ab'
    apply inc_trans H
    rw[domain]
    simp
theorem comp_domain5 : is_univalent f → (domain (f#) ⊑ domain g ↔ domain (f ∘ g) = domain f) := by
  rw[is_univalent]
  intro H
  constructor
  · apply comp_domain4
  · intro H0
    rw[domain, domain]
    simp
    apply cap_inc_compat_r
    conv => lhs; rhs; rw[← domain_comp1 f, ← H0, domain]
    simp
    apply inc_trans comp_cap_distr
    apply inc_trans cap_l
    simp
    rw[← comp_assoc]
    apply inc_trans (comp_inc_compat_ab_a H)
    rw[← comp_assoc]
    apply comp_inc_compat_ab_b H
theorem comp_domain6 : f ∘ (domain g) ⊑ domain (f ∘ g) ∘ f := by
  apply inc_trans comp_cap_distr_l
  rw[cap_comm]
  conv => lhs; lhs; simp; rw[← comp_id_l f]
  apply inc_trans dedekind2
  rw[cap_comm, domain]
  simp
theorem comp_domain7 : is_univalent f → f ∘ domain g = domain (f ∘ g) ∘ f := by
  rw[is_univalent]
  intro H
  apply inc_antisym
  · apply comp_domain6
  · rw[domain, domain]
    apply inc_trans comp_cap_distr_r
    simp
    apply inc_trans
    · apply cap_inc_compat_r
      rw[← comp_assoc]
      apply comp_inc_compat_ab_a H
    · rw[← comp_assoc]
      apply inc_trans dedekind1
      apply comp_inc_compat_ab_ab'
      apply cap_inc_compat_l H
theorem comp_domain8 {f: c.rel X X}: f ⊑ idr X → domain (f ∘ g) = f ∘ domain g := by
  intro H
  apply inc_antisym
  · rw[← cap_idem (domain (f ∘ g)), comp_subid_cap H domain_subid]
    apply cap_inc_compat
    · apply inc_trans comp_domain1
      rw[domain_inc_id.mp H]
      simp
    · apply domain_inc_compat
      apply comp_inc_compat_ab_b H
  · apply inc_trans comp_domain6
    apply comp_inc_compat_ab_a H
theorem cap_domain {f f':c.rel X Y}: domain (f ⊓ f') = f ∘ f'# ⊓ idr X := by
  apply inc_antisym
  · apply cap_inc_compat_r
    apply comp_inc_compat
    · simp
    · rw[inv_inc_move]
      simp
  · rw[← cap_idem (idr X), cap_assoc]
    apply cap_inc_compat_r
    apply inc_trans dedekind
    simp
    conv => lhs; rhs; rw[cap_comm]
    simp
theorem cupP_domain_distr : domain (cupP P α) = cupP P (fun x => domain (α x)) := by
  rw[domain, inv_cupP_distr, comp_cupP_distr_l, cap_cupP_distr_r]
  apply cupP_eq
  intro f H
  rw[← cap_domain]
  congr
  apply Eq.symm
  rw[inc_def1r]
  apply cupP_inc H
theorem cup_domain_distr : domain (f ⊔ g) = domain f ⊔ domain g := by
  rw[← cup_to_cupP, cupP_domain_distr]
  simp
  apply inc_antisym
  · rw[inc_cupP]
    intro h H
    cases H with | inl H | inr H
    all_goals
      rw[H]
      simp
  · apply inc_cup.mpr
    constructor
    · apply cupP_inc
      left
      rfl
    · apply cupP_inc
      right
      simp
theorem domain_universal1 {f:c.rel X Y} : domain f ∘ Δ X Z = f ∘ Δ Y Z := by
  apply inc_antisym
  · rw[domain]
    apply inc_trans (comp_inc_compat_ab_a'b cap_l)
    rw[← comp_assoc]
    apply comp_inc_compat_ab_ab'
    simp
  · conv => lhs; rw[← domain_comp1 f, ← comp_assoc]
    apply comp_inc_compat_ab_ab'
    simp
theorem domain_universal2 {f:c.rel X Y}{g:c.rel Y Z} : f ∘ domain g = f ⊓ Δ X Z ∘ g# := by
  apply inc_antisym
  · rw[inc_cap]
    constructor
    · apply comp_inc_compat_ab_a (domain_subid)
    · apply inc_trans (comp_inc_compat_ab_ab' cap_l)
      rw[comp_assoc]
      apply comp_inc_compat_ab_a'b
      simp
  · rw[← inv_universal Z X, ← comp_inv, ← domain_universal1]
    simp
    rw[cap_comm]
    apply inc_trans dedekind2
    apply comp_inc_compat_ab_a'b
    simp
    apply comp_inc_compat_ab_a domain_subid
theorem domain_lemma1 : is_univalent f → is_univalent g → f ⊑ g → domain f = domain g → f = g := by
  rw[is_univalent, is_univalent]
  intro Hf Hg H H0
  apply inc_antisym H
  rw[← domain_comp1 g, ← H0]
  apply inc_trans comp_cap_distr_r
  apply inc_trans cap_l
  rw[← comp_assoc]
  apply comp_inc_compat_ab_a
  apply inc_trans _ Hg
  apply comp_inc_compat_ab_a'b
  simp
  assumption
theorem domain_lemma2a {f:c.rel X Y}{g:c.rel X Z}: domain f ⊑ domain g ↔ f ∘ Δ Y Y ⊑ g ∘ Δ Z Y := by
  constructor
  · intro H
    rw[← domain_comp1 f, ← comp_assoc]
    apply inc_trans (comp_inc_compat_ab_a'b H)
    apply inc_trans (comp_inc_compat_ab_a'b cap_l)
    rw[← comp_assoc]
    apply comp_inc_compat_ab_ab'
    simp
  · intro H
    apply inc_trans
    · apply domain_inc_compat
      rw[← cap_idem f]
      conv => lhs; rhs; rw[← comp_id_r f]
      apply cap_inc_compat_l
      apply comp_inc_compat_ab_ab'
      apply inc_universal
    · apply inc_trans
      · apply domain_inc_compat
        apply cap_inc_compat_l H
      · apply inc_trans
        · apply domain_inc_compat
          rw[cap_comm]
          apply inc_trans dedekind1
          simp
          apply inc_refl
        · rw[← comp_assoc]
          apply comp_domain1
theorem domain_lemma2b {f:c.rel X Y}{g:c.rel X Z}: domain f ⊑ domain g ↔ f ⊑ (g ∘ g#) ∘ f := by
  constructor
  · intro H
    rw[domain_lemma2a] at H
    rw[← cap_idem f]
    conv => lhs; rhs; rw[← comp_id_r f]
    apply inc_trans
    · apply cap_inc_compat_l
      apply comp_inc_compat_ab_ab'
      apply inc_universal
    · apply inc_trans (cap_inc_compat_l H)
      rw[cap_comm]
      apply inc_trans dedekind1
      simp
  · intro H
    apply inc_trans (domain_inc_compat H)
    rw[← comp_assoc]
    apply comp_domain1
theorem domain_corollary1 {f:c.rel X Y}{g:c.rel X Z}{h:c.rel W Y}{k:c.rel W Z} :
is_total f → is_total g → f# ∘ g ⊑ h# ∘ k → is_total (f ∘ h# ⊓ g ∘ k#) := by
  intro Hf Hg H
  rw[is_total]
  have H0 := comp_inc_compat Hf Hg
  simp at H0 ⊢
  rw[← cap_idem (idr X)]
  apply inc_trans (cap_inc_compat_r H0)
  apply inc_trans
  · apply cap_inc_compat_r
    apply comp_inc_compat_ab_a'b
    rw[← comp_assoc]
    apply comp_inc_compat_ab_ab' H
  · simp
    rw[← comp_assoc]
    apply inc_trans dedekind
    simp
    conv => lhs; rhs; rw[cap_comm]
    simp
end domain

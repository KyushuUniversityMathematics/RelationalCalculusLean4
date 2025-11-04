import dedekind_formula
import function
import shroder

section domain
variable [c:Dedekind]
def domain (f:c.rel X Y) := f ∘ f# ⊓ idr X

theorem domain_diagonal {f:c.rel X Y}: domain f ⊑ idr X := by
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
theorem domain_inv {f:c.rel X Y}: (domain f)# = domain f := by
  rw[domain, inv_diagonal]
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
  apply comp_inc_compat _ _ _ _ H
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
    rw[inv_diagonal H, comp_diagonal H, ← inc_def1l.mpr H]
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
    apply inc_trans (comp_cap_distr _ _ _ _)
    apply inc_trans (cap_l _ _)
    simp
    rw[← comp_assoc]
    apply inc_trans (comp_inc_compat_ab_a H)
    rw[← comp_assoc]
    apply comp_inc_compat_ab_b H
theorem comp_domain6 : f ∘ (domain g) ⊑ domain (f ∘ g) ∘ f := by
  apply inc_trans (comp_cap_distr_l _ _ _)
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
    apply inc_trans (comp_cap_distr_r _ _ _)
    simp
    apply inc_trans
    · apply cap_inc_compat_r
      rw[← comp_assoc]
      apply comp_inc_compat_ab_a H
    · rw[← comp_assoc]
      apply inc_trans dedekind1
      apply comp_inc_compat_ab_ab'
      apply cap_inc_compat_l _ _ _ H
theorem comp_domain8 {f: c.rel X X}: f ⊑ idr X → domain (f ∘ g) = f ∘ domain g := by
  intro H
  apply inc_antisym
  · rw[← cap_idem (domain (f ∘ g)), comp_diagonal_cap H domain_diagonal]
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
  rw[cupP_cup_eq]
  apply
  rw[comp_cupP_distr_r, cap_cupP_distr_r]
  apply inc_antisym
  · rw[inc_cupP]
    intro h H0
    rw[comp_cupP_distr_r, cap_cupP_distr_r, inc_cupP]
    intro k H1
    rw[inc_cupP]
    apply cap_inc_compat_r
    apply comp_inc_compat
    · simp
    · rw[inv_inc_move]
      simp

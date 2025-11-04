import Dedekind
import shroder
import function
import domain

class Dedekind_sum extends Dedekind where
  sum_axiom : ∀ X Y : ob, ∃ Z : ob, ∃ (inl : rel X Z) (inr : rel Y Z),
    inl ∘ inl# = idr X ∧ inr ∘ inr# = idr Y ∧ inl ∘ inr# = φ X Y ∧ inl# ∘ inl ⊔ inr# ∘ inr = idr Z
noncomputable def sum_ob [c : Dedekind_sum](X Y : c.ob) : c.ob :=
  Classical.choose (c.sum_axiom X Y)
infixl:51 " + " => sum_ob
noncomputable def in_l [c : Dedekind_sum](X Y : c.ob) : c.rel X (X+Y) :=
  Classical.choose (Classical.choose_spec (c.sum_axiom X Y))
noncomputable def in_r [c : Dedekind_sum](X Y : c.ob) : c.rel Y (X+Y) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (c.sum_axiom X Y)))

section dedekind_sum
variable [c : Dedekind_sum]
@[simp] theorem inl_id : in_l X Y ∘ (in_l X Y)# = idr X := by
  have H := (Classical.choose_spec (Classical.choose_spec (c.sum_axiom X Y)))
  cases H with | intro inr H
  exact H.left
@[simp] theorem inl_id_l : ∀ x:c.rel Z X, (x ∘ in_l X Y) ∘ in_l X Y # = x ∘ idr X := acomp_l inl_id
@[simp] theorem inr_id : in_r X Y ∘ (in_r X Y)# = idr Y :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (c.sum_axiom X Y)))).right.left
@[simp] theorem inr_id_l : ∀ x:c.rel Z Y, (x ∘ in_r X Y) ∘ in_r X Y # = x ∘ idr Y := acomp_l inr_id
@[simp] theorem inl_inr_empty : in_l X Y ∘ (in_r X Y)# = φ X Y :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (c.sum_axiom X Y)))).right.right.left
@[simp] theorem inl_inr_empty_l : ∀ x:c.rel Z X, (x ∘ in_l X Y) ∘ in_r X Y # = x ∘ φ X Y := acomp_l inl_inr_empty
@[simp] theorem inr_inl_empty : in_r X Y ∘ (in_l X Y)# = φ Y X := by
  rw[← inv_invol (in_r _ _), ← comp_inv, inl_inr_empty]
  simp
@[simp] theorem inr_inl_empty_l : ∀ x:c.rel Z Y, (x ∘ in_r X Y) ∘ in_l X Y # = x ∘ φ Y X := acomp_l inr_inl_empty
@[simp] theorem inl_inr_cup_id : (in_l X Y)# ∘ in_l X Y ⊔ (in_r X Y)# ∘ in_r X Y = idr (X + Y) :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (c.sum_axiom X Y)))).right.right.right
theorem inl_injective (X Y : c.ob) : is_injective (in_l X Y) := by
  rw[is_injective, ← inl_inr_cup_id]
  apply And.intro inl_id (cup_l _ _)
theorem inr_injective (X Y : c.ob) : is_injective (in_r X Y) := by
  rw[is_injective, ← inl_inr_cup_id]
  apply And.intro inr_id (cup_r _ _)
noncomputable def rel_sum (f : c.rel X Z) (g : c.rel Y Z) := (in_l X Y)# ∘ f ⊔ (in_r X Y)# ∘ g
infixl:50 " + " => rel_sum
theorem sum_inc_compat {f f' : c.rel X Z} {g g' : c.rel Y Z} :
  f ⊑ f' → g ⊑ g' → (f + g) ⊑ (f' + g') := by
  intro Hf Hg
  apply cup_inc_compat
  · apply comp_inc_compat_ab_ab' Hf
  · apply comp_inc_compat_ab_ab' Hg
theorem sum_inc_compat_l {f f' : c.rel X Z} {g : c.rel Y Z} :
  f ⊑ f' → (f + g) ⊑ (f' + g) := by
  intro Hf
  apply cup_inc_compat
  · apply comp_inc_compat_ab_ab' Hf
  · apply inc_refl
theorem sum_inc_compat_r {f : c.rel X Z} {g g' : c.rel Y Z} :
  g ⊑ g' → (f + g) ⊑ (f + g') := by
  intro Hg
  apply cup_inc_compat
  · apply inc_refl
  · apply comp_inc_compat_ab_ab' Hg
theorem total_sum {f : c.rel X Z} {g : c.rel Y Z} :
  is_total f → is_total g → is_total (f + g) := by
  rw[rel_sum, is_total, is_total, is_total]
  intro Hf Hg
  simp
  rw[cup_comm, ← cup_assoc, cup_assoc, ← inl_inr_cup_id]
  conv => lhs; rw[← comp_id_r (in_l _ _ #), ← comp_id_r (in_r _ _ #)]
  apply inc_trans _ (cup_l _ _)
  rw[cup_comm]
  apply cup_inc_compat
  · apply comp_inc_compat_ab_a'b
    rw[← comp_assoc]
    apply comp_inc_compat_ab_ab' Hg
  · apply comp_inc_compat_ab_a'b
    rw[← comp_assoc]
    apply comp_inc_compat_ab_ab' Hf
theorem univalent_sum {f : c.rel X Z}{g : c.rel Y Z} :
  is_univalent f → is_univalent g → is_univalent (f + g) := by
  rw[is_univalent, rel_sum, is_univalent, is_univalent]
  intro Hf Hg
  simp
  apply inc_cup.mpr
  constructor
  all_goals assumption
theorem function_sum {f : c.rel X Z}{g : c.rel Y Z} :
  is_function f → is_function g → is_function (f + g) := by
  intro Hf Hg
  apply total_univalent_function.mp
  constructor
  · apply total_sum (function_total Hf) (function_total Hg)
  · apply univalent_sum (function_univalent Hf) (function_univalent Hg)
theorem sum_conjugate {f : c.rel X Z}{g : c.rel Y Z}{h: c.rel (X + Y) Z} :
  in_l X Y ∘ h = f ∧ (in_r X Y) ∘ h = g ↔ h = (f + g) := by
  constructor
  · intro ⟨Hf, Hg⟩
    rw[rel_sum, ← Hf, ← Hg]
    simp
    rw[← comp_cup_distr_r]
    simp
  · intro H
    rw[H, rel_sum]
    simp
theorem sum_comp : (f + g)# ∘ (h + k) = (f# ∘ h) ⊔ (g# ∘ k) := by
  rw[rel_sum, rel_sum, comp_cup_distr_l]
  simp
theorem sum_cap_distr_l : (f + g ⊓ g') ⊑ (f + g) ⊓ (f + g') := by
  rw[rel_sum, rel_sum, rel_sum, ← cup_cap_distr_l]
  apply cup_inc_compat_l
  apply comp_cap_distr_l
theorem sum_cap_distr_r : (f ⊓ f' + g) ⊑ (f + g) ⊓ (f' + g) := by
  rw[rel_sum, rel_sum, rel_sum, ← cup_cap_distr_r]
  apply cup_inc_compat_r
  apply comp_cap_distr_l
theorem sum_cup_distr_l : (f + g ⊔ g') = (f + g) ⊔ (f + g') := by
  rw[rel_sum, rel_sum, rel_sum]
  conv => rhs; lhs; rw[cup_comm]
  rw[cup_assoc]
  conv => rhs; lhs; rw[← cup_assoc, cup_idem, cup_comm]
  rw[← cup_assoc, ← comp_cup_distr_l]
theorem sum_cup_distr_r : (f ⊔ f' + g) = (f + g) ⊔ (f' + g) := by
  rw[rel_sum, rel_sum, rel_sum]
  conv => rhs; lhs; rw[cup_comm]
  rw[cup_assoc]
  conv => rhs; lhs; rw[← cup_assoc, ← comp_cup_distr_l]
  rw[← cup_assoc, cup_comm, cup_assoc, cup_idem]
theorem comp_sum_distr_r {f : c.rel X Z}{g : c.rel Y Z}{h : c.rel Z W} :
  (f + g) ∘ h = rel_sum (f ∘ h) (g ∘ h) := by
  rw[rel_sum, comp_cup_distr_r, rel_sum]
  simp
end dedekind_sum


class Dedekind_prod extends Dedekind where
  product_axiom : ∀ X Y : ob, ∃ Z : ob, ∃ (fst : rel Z X) (snd : rel Z Y),
    fst ∘ fst# ⊓ snd ∘ snd# = idr Z ∧ fst# ∘ snd = Δ X Y ∧ is_function fst ∧ is_function snd
noncomputable def prod_ob [c : Dedekind_prod](X Y : c.ob) : c.ob :=
  Classical.choose (c.product_axiom X Y)
infixl:52 " × " => prod_ob
noncomputable def fst [c : Dedekind_prod](X Y : c.ob) : c.rel (X × Y) X :=
  Classical.choose (Classical.choose_spec (c.product_axiom X Y))
noncomputable def snd [c : Dedekind_prod](X Y : c.ob) : c.rel (X × Y) Y :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (c.product_axiom X Y)))

section dedekind_prod
variable [c : Dedekind_prod]
@[simp]theorem fst_snd_cap_id : fst X Y ∘ (fst X Y)# ⊓ snd X Y ∘ (snd X Y)# = idr (X × Y) :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (c.product_axiom X Y)))).left
@[simp]theorem fst_snd_universal (X Y:c.ob) : (fst X Y)# ∘ snd X Y = Δ X Y :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (c.product_axiom X Y)))).right.left
@[simp]theorem fst_snd_universal_l  : ∀ x:c.rel Z X, (x ∘ fst X Y#) ∘ snd X Y = x ∘ Δ X Y := acomp_l (fst_snd_universal X Y)
@[simp]theorem snd_fst_universal (X Y : c.ob) : (snd X Y)# ∘ fst X Y = Δ Y X := by
  rw[← inv_invol (_ ∘ _), comp_inv, inv_invol, fst_snd_universal, inv_universal]
@[simp]theorem snd_fst_universal_l : ∀ x:c.rel Z Y, (x ∘ snd X Y#) ∘ fst X Y = x ∘ Δ Y X := acomp_l (snd_fst_universal X Y)
theorem fst_function (X Y : c.ob) : is_function (fst X Y) := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (c.product_axiom X Y)))).right.right.left
theorem snd_function (X Y : c.ob) : is_function (snd X Y) := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (c.product_axiom X Y)))).right.right.right
noncomputable def rel_prod {X Y Z : c.ob}(f : c.rel Z X)(g : c.rel Z Y) : c.rel Z (X × Y) :=
  f ∘ fst X Y# ⊓ g ∘ snd X Y#
infixl:51 " × " => rel_prod
theorem prod_inc_compat {f f' : c.rel Z X} {g g' : c.rel Z Y} :
  f ⊑ f' → g ⊑ g' → rel_prod f g ⊑ rel_prod f' g' := by
  intro Hf Hg
  rw[rel_prod, rel_prod]
  apply cap_inc_compat
  · apply comp_inc_compat_ab_a'b Hf
  · apply comp_inc_compat_ab_a'b Hg
theorem prod_inc_compat_l {f : c.rel Z X} {g g' : c.rel Z Y} :
  g ⊑ g' → rel_prod f g ⊑ rel_prod f g' := by
  intro Hg
  rw[rel_prod, rel_prod]
  apply cap_inc_compat
  · apply inc_refl
  · apply comp_inc_compat_ab_a'b Hg
theorem prod_inc_compat_r {f f' : c.rel Z X} {g : c.rel Z Y} :
  f ⊑ f' → rel_prod f g ⊑ rel_prod f' g := by
  intro Hf
  rw[rel_prod, rel_prod]
  apply cap_inc_compat
  · apply comp_inc_compat_ab_a'b Hf
  · apply inc_refl
theorem total_prod {f : c.rel Z X} {g : c.rel Z Y} :
  is_total f → is_total g → is_total (rel_prod f g) := by
  rw[rel_prod, is_total, is_total]
  intro Hf Hg
  rw[domain_total, cap_domain]
  simp
  apply Eq.symm
  apply inc_def1r.mpr
  apply inc_trans
  · rw[← comp_id_r (idr _)]
    apply comp_inc_compat _ _ _ _ Hf Hg
  · simp
    apply comp_inc_compat_ab_a'b
    rw[← comp_assoc]
    apply comp_inc_compat_ab_ab'
    simp
theorem univalent_prod {f : c.rel Z X}{g : c.rel Z Y} :
  is_univalent f → is_univalent g → is_univalent (f × g) := by
  rw[rel_prod, is_univalent, is_univalent, is_univalent]
  intro Hf Hg
  simp
  apply inc_trans (comp_cap_distr_l _ _ _)
  rw[← fst_snd_cap_id]
  apply cap_inc_compat
  · apply inc_trans (comp_cap_distr_r _ _ _)
    simp
    apply inc_trans (cap_l _ _)
    apply comp_inc_compat_ab_a'b
    rw[← comp_assoc]
    apply comp_inc_compat_ab_a Hf
  · apply inc_trans (comp_cap_distr_r _ _ _)
    simp
    apply inc_trans (cap_r _ _)
    apply comp_inc_compat_ab_a'b
    rw[← comp_assoc]
    apply comp_inc_compat_ab_a Hg
theorem function_prod {f : c.rel Z X}{g : c.rel Z Y} :
  is_function f → is_function g → is_function (f × g) := by
  intro Hf Hg
  apply total_univalent_function.mp
  constructor
  · apply total_prod (function_total Hf) (function_total Hg)
  · apply univalent_prod (function_univalent Hf) (function_univalent Hg)
theorem prod_fst_surjective {X Y : c.ob} :
  is_surjective (fst X Y) ↔ ∀Z, Δ X Z = Δ X Y ∘ Δ Y Z := by
  constructor
  · rw[is_surjective]
    intro ⟨H, H0⟩ Z
    apply inc_antisym _ (inc_universal _)
    rw[← comp_id_l (Δ X Z), ← H, ← fst_snd_universal X Y, ← comp_assoc, ← comp_assoc]
    apply comp_inc_compat_ab_ab'
    apply inc_trans (comp_inc_compat_b_ab (function_total (snd_function X Y)))
    rw[← comp_assoc]
    apply comp_inc_compat_ab_ab'
    simp
  · intro H
    rw[← total_function_surjective]
    apply And.intro _ (fst_function X Y)
    rw[is_total]
    simp
    rw[← cap_universal (idr _), H X, ← fst_snd_universal X Y, ← comp_assoc, cap_comm]
    apply inc_trans dedekind1
    simp
    apply comp_inc_compat_ab_ab'
    simp
theorem prod_snd_surjective {X Y : c.ob} :
  is_surjective (snd X Y) ↔ ∀Z, Δ Y Z = Δ Y X ∘ Δ X Z := by
  constructor
  · rw[is_surjective]
    intro ⟨H, H0⟩ Z
    apply inc_antisym _ (inc_universal _)
    rw[← comp_id_l (Δ Y Z), ← H, ← snd_fst_universal X Y, ← comp_assoc, ← comp_assoc]
    apply comp_inc_compat_ab_ab'
    apply inc_trans (comp_inc_compat_b_ab (function_total (fst_function X Y)))
    rw[← comp_assoc]
    apply comp_inc_compat_ab_ab'
    simp
  · intro H
    rw[← total_function_surjective]
    apply And.intro _ (snd_function X Y)
    rw[is_total]
    simp
    rw[← cap_universal (idr _), H Y, ← snd_fst_universal X Y, ← comp_assoc, cap_comm]
    apply inc_trans dedekind1
    simp
    apply comp_inc_compat_ab_ab'
    simp
theorem prd_fst_domain1 {f:c.rel X Y}{g:c.rel X Z} : (f × g) ∘ fst Y Z = (domain g) ∘ f := by
  rw[← inv_invol (_ ∘ f), comp_inv, inv_diagonal domain_diagonal, domain_universal2]

import Dedekind
import shroder
import function
import domain
import conjugate

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
  apply And.intro inl_id cup_l
theorem inr_injective (X Y : c.ob) : is_injective (in_r X Y) := by
  rw[is_injective, ← inl_inr_cup_id]
  apply And.intro inr_id cup_r
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
  apply inc_trans _ cup_l
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
theorem fst_function {X Y : c.ob} : is_function (fst X Y) := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (c.product_axiom X Y)))).right.right.left
theorem snd_function {X Y : c.ob} : is_function (snd X Y) := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (c.product_axiom X Y)))).right.right.right
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
    apply comp_inc_compat Hf Hg
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
  apply inc_trans comp_cap_distr_l
  rw[← fst_snd_cap_id]
  apply cap_inc_compat
  · apply inc_trans comp_cap_distr_r
    simp
    apply inc_trans cap_l
    apply comp_inc_compat_ab_a'b
    rw[← comp_assoc]
    apply comp_inc_compat_ab_a Hf
  · apply inc_trans comp_cap_distr_r
    simp
    apply inc_trans cap_r
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
    apply inc_trans (comp_inc_compat_b_ab (function_total snd_function))
    rw[← comp_assoc]
    apply comp_inc_compat_ab_ab'
    simp
  · intro H
    rw[← total_function_surjective]
    apply And.intro _ fst_function
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
    apply inc_trans (comp_inc_compat_b_ab (function_total fst_function))
    rw[← comp_assoc]
    apply comp_inc_compat_ab_ab'
    simp
  · intro H
    rw[← total_function_surjective]
    apply And.intro _ snd_function
    rw[is_total]
    simp
    rw[← cap_universal (idr _), H Y, ← snd_fst_universal X Y, ← comp_assoc, cap_comm]
    apply inc_trans dedekind1
    simp
    apply comp_inc_compat_ab_ab'
    simp
theorem prod_fst_domain1 {f:c.rel X Y}{g:c.rel X Z} : (f × g) ∘ fst Y Z = (domain g) ∘ f := by
  rw[← inv_invol (_ ∘ f), comp_inv, domain_inv, domain_universal2]
  simp
  apply inc_antisym
  · apply inc_trans comp_cap_distr_r
    simp
    apply cap_inc_compat_r
    rw[← comp_assoc]
    apply comp_inc_compat_ab_a
    apply function_univalent fst_function
  · rw[cap_comm, ← snd_fst_universal, comp_assoc]
    apply inc_trans dedekind2
    apply comp_inc_compat_ab_a'b
    rw[rel_prod, cap_comm]
    simp
theorem prod_fst_domain2 {f:c.rel X Y}{g:c.rel X Z} : (f × g) ∘ fst Y Z = f ↔ domain f ⊑ domain g := by
  rw[prod_fst_domain1]
  constructor
  · intro H
    rw[domain_lemma2b]
    conv => lhs; rw[← H]
    apply comp_inc_compat_ab_a'b
    simp[domain]
  · intro H
    apply inc_antisym
    · apply comp_inc_compat_ab_b domain_diagonal
    · conv => lhs; rw[← domain_comp1 f]
      apply comp_inc_compat_ab_a'b H
theorem prod_snd_domain1 {f:c.rel X Y}{g:c.rel X Z} : (f × g) ∘ snd Y Z = (domain f) ∘ g := by
  rw[← inv_invol (_ ∘ g), comp_inv, domain_inv, domain_universal2]
  simp
  apply inc_antisym
  · apply inc_trans comp_cap_distr_r
    simp
    rw[cap_comm]
    apply cap_inc_compat_r
    rw[← comp_assoc]
    apply comp_inc_compat_ab_a
    apply function_univalent snd_function
  · rw[cap_comm, ← fst_snd_universal, comp_assoc]
    apply inc_trans dedekind2
    apply comp_inc_compat_ab_a'b
    rw[rel_prod, cap_comm]
    simp
theorem prod_snd_domain2 {f:c.rel X Y}{g:c.rel X Z} : (f × g) ∘ snd Y Z = g ↔ domain g ⊑ domain f := by
  rw[prod_snd_domain1]
  constructor
  · intro H
    rw[domain_lemma2b]
    conv => lhs; rw[← H]
    apply comp_inc_compat_ab_a'b
    simp[domain]
  · intro H
    apply inc_antisym
    · apply comp_inc_compat_ab_b domain_diagonal
    · conv => lhs; rw[← domain_comp1 g]
      apply comp_inc_compat_ab_a'b H
theorem prod_to_cap {f:c.rel X Y}{g:c.rel X Z} :
  domain (f × g) = domain f ⊓ domain g := by
  rw[← comp_diagonal_cap domain_diagonal domain_diagonal, ← comp_domain3 (function_total snd_function), prod_snd_domain1, comp_domain8 domain_diagonal]
theorem prod_conjugate1 {f:c.rel X Y}{g:c.rel X Z} : is_function f → is_function g →
  (f × g) ∘ fst Y Z = f ∧ (f × g) ∘ snd Y Z = g := by
  intro ⟨Hf0, Hf1⟩ ⟨Hg0, Hg1⟩
  constructor
  · rw[prod_fst_domain1, domain, ← inc_def1r.mpr Hg0]
    simp
  · rw[prod_snd_domain1, domain, ← inc_def1r.mpr Hf0]
    simp
theorem prod_conjugate2 {f:c.rel X (Y × Z)} : is_function f →
  rel_prod (f ∘ fst Y Z) (f ∘ snd Y Z) = f := by
  intro H
  rw[rel_prod, ← comp_assoc, ← comp_assoc, ← function_cap_distr_l H]
  simp
theorem diagonal_conjugate:
  conjugate (fun _ => True) (fun f => f ⊑ idr (X×Y)) (fun f:c.rel X Y => domain ((fst X Y ∘ f) ⊓ snd X Y)) (fun g:c.rel (X×Y) (X×Y) => (fst X Y#∘ g) ∘ snd X Y) := by
  constructor
  · intro f _
    constructor
    · simp[domain_diagonal]
    · simp
      rw[cap_domain]
      apply inc_antisym
      · apply inc_trans
        · apply comp_inc_compat_ab_a'b
          apply comp_inc_compat_ab_ab' cap_l
        · simp
          rw[← comp_assoc]
          apply inc_trans
          · apply comp_inc_compat_ab_a snd_function.right
          · apply comp_inc_compat_ab_b fst_function.right
      · conv=>lhs;rw[← cap_universal f, ← fst_snd_universal, ← comp_id_r (fst X Y#), cap_comm]
        apply inc_trans dedekind2
        apply comp_inc_compat_ab_a'b
        apply inc_trans dedekind1
        apply comp_inc_compat_ab_ab'
        rw[cap_comm]
        simp
  · intro g Hg
    constructor
    · simp
    · simp
      conv => rhs; rw[← domain_inc_id.mp Hg, ← comp_domain3 (function_total snd_function)]
      congr
      apply inc_antisym
      · rw[← comp_assoc]
        apply inc_trans dedekind2
        apply comp_inc_compat_ab_b
        simp
        apply inc_trans
        · apply cap_inc_compat_l
          apply comp_inc_compat_ab_a
          rw[inv_diagonal Hg]
          assumption
        · simp
      · conv => lhs; rw[inc_def1l.mpr Hg]
        apply inc_trans comp_cap_distr_r
        simp
        apply cap_inc_compat_r
        rw[← comp_assoc]
        apply comp_inc_compat_b_ab
        simp[← fst_snd_cap_id]
end dedekind_prod

class Dedekind_sub' extends Dedekind where
  sub_axiom : ∀ f:rel X X, f ⊑ idr X → ∃ Y : ob, ∃ (i : rel Y X),
    i# ∘ i = f ∧ i ∘ i# = idr Y ∧ is_function i
noncomputable def sub [c : Dedekind_sub']{X:c.ob}(f:c.rel X X)(H:f ⊑ idr X) : c.ob :=
  Classical.choose (c.sub_axiom f H)
noncomputable def sub_inj [c : Dedekind_sub']{X:c.ob}{f:c.rel X X}(H:f ⊑ idr X) : c.rel (sub f H) X :=
  Classical.choose (Classical.choose_spec (c.sub_axiom f H))
theorem sub_spec [c : Dedekind_sub']{X:c.ob}{f:c.rel X X}(H:f ⊑ idr X) :
  (sub_inj H)# ∘ (sub_inj H) = f :=
  (Classical.choose_spec (Classical.choose_spec (c.sub_axiom f H))).left
theorem sub_id [c : Dedekind_sub']{X:c.ob}{f:c.rel X X}(H:f ⊑ idr X) :
  (sub_inj H) ∘ (sub_inj H)# = idr (sub f H) :=
  (Classical.choose_spec (Classical.choose_spec (c.sub_axiom f H))).right.left
theorem sub_injective [c : Dedekind_sub']{X:c.ob}{f:c.rel X X}(H:f ⊑ idr X) :
  is_injective (sub_inj H) := by
  rw[← univalent_function_injective]
  constructor
  · simp[is_univalent, inv_invol, sub_id H]
  · exact (Classical.choose_spec (Classical.choose_spec (c.sub_axiom f H))).right.right


class Dedekind_rationality extends Dedekind where
  rationality : ∀ X Y : ob, ∀ f:rel X Y, ∃ Z : ob, ∃ (a : rel Z X) (b : rel Z Y),
    a ∘ a# ⊓ b ∘ b# = idr Z ∧ a# ∘ b = f ∧ is_function a ∧ is_function b

instance dedekindProd_of_rationality [c : Dedekind_rationality] : Dedekind_prod where
  product_axiom X Y := by
    obtain ⟨Z, a, b, hcap, huniv, ha, hb⟩ := c.rationality X Y (Δ X Y)
    exact ⟨Z, a, b, hcap, by simpa using huniv, ha, hb⟩


noncomputable def rational_ob [c : Dedekind_rationality]{X Y : c.ob}(f:c.rel X Y) : c.ob :=
  Classical.choose (c.rationality X Y f)
noncomputable def rational1 [c : Dedekind_rationality]{X Y : c.ob}(f:c.rel X Y) : c.rel (rational_ob f) X :=
  Classical.choose (Classical.choose_spec (c.rationality X Y f))
noncomputable def rational2 [c : Dedekind_rationality]{X Y : c.ob}(f:c.rel X Y) : c.rel (rational_ob f) Y :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (c.rationality X Y f)))

section dedekind_rationality
variable [c : Dedekind_rationality]
@[simp] theorem rational_cap_id {X Y : c.ob}(f:c.rel X Y) :
  rational1 f ∘ (rational1 f)# ⊓ rational2 f ∘ (rational2 f)# = idr (rational_ob f) :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (c.rationality X Y f)))).left
@[simp] theorem rational_comp{X Y : c.ob}(f:c.rel X Y) :
  (rational1 f)# ∘ rational2 f = f :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (c.rationality X Y f)))).right.left
@[simp] theorem rational_comp_l {X Y : c.ob}(f:c.rel X Y) : ∀ x:c.rel Z X,
  (x ∘ rational1 f#) ∘ rational2 f = x ∘ f := acomp_l (rational_comp f)
theorem rational1_function {X Y : c.ob}(f:c.rel X Y) :
  is_function (rational1 f) :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (c.rationality X Y f)))).right.right.left
theorem rational2_function {X Y : c.ob}(f:c.rel X Y) :
  is_function (rational2 f) :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (c.rationality X Y f)))).right.right.right


theorem sharpness {f:c.rel X Y}{h:c.rel W Y}{g:c.rel X Z}{k:c.rel W Z} :
  (f ∘ h#)⊓(g ∘ k#) = (f × g) ∘ (h × k)# := by
  apply Eq.symm
  apply inc_antisym
  · simp[rel_prod, rel_prod]
    apply inc_trans comp_cap_distr_l
    apply inc_trans (cap_inc_compat_r comp_cap_distr_r)
    apply inc_trans (cap_inc_compat_l comp_cap_distr_r)
    apply inc_trans (cap_inc_compat_r cap_l)
    apply inc_trans (cap_inc_compat_l cap_r)
    apply cap_inc_compat
    · simp
      apply comp_inc_compat_ab_a'b
      rw[← comp_assoc]
      apply comp_inc_compat_ab_a fst_function.right
    · simp
      apply comp_inc_compat_ab_a'b
      rw[← comp_assoc]
      apply comp_inc_compat_ab_a snd_function.right
  · let af := rational1 f
    let bf := rational2 f
    let ag := rational1 g
    let bg := rational2 g
    let ah := rational1 (h#)
    let bh := rational2 (h#)
    let ak := rational1 (k#)
    let bk := rational2 (k#)
    let afh := rational1 (bf ∘ ah#)
    let bfh := rational2 (bf ∘ ah#)
    let agk := rational1 (bg ∘ ak#)
    let bgk := rational2 (bg ∘ ak#)
    have Hfh : f∘ h# = ((af# ∘ afh#) ∘ bfh) ∘ bh := by
      rw[acomp_l (rational_comp _), comp_assoc, rational_comp, ← comp_assoc, rational_comp]
    have Hgk : g∘ k# = ((ag# ∘ agk#) ∘ bgk) ∘ bk := by
      rw[acomp_l (rational_comp _), comp_assoc, rational_comp, ← comp_assoc, rational_comp]
    let x := rational1 (f ∘ h# ⊓ g ∘ k#)
    let y := rational2 (f ∘ h# ⊓ g ∘ k#)
    have Hfh : x# ∘ y ⊑ (afh ∘ af)# ∘ (bfh ∘ bh) := by
      rw[rational_comp (f ∘ h# ⊓ g ∘ k#), Hfh]
      simp
    have Hgk : x# ∘ y ⊑ (agk ∘ ag)# ∘ (bgk ∘ bk) := by
      rw[rational_comp (f ∘ h# ⊓ g ∘ k#), Hgk]
      simp
    have Hfh := domain_corollary1 (rational1_function (f ∘ h# ⊓ g ∘ k#)).left (rational2_function (f ∘ h# ⊓ g ∘ k#)).left Hfh
    have Hgk := domain_corollary1 (rational1_function (f ∘ h# ⊓ g ∘ k#)).left (rational2_function (f ∘ h# ⊓ g ∘ k#)).left Hgk
    let μ1 := rational1 (f ∘ h # ⊓ g ∘ k#) ∘ (afh ∘ af) # ⊓ rational2 (f ∘ h # ⊓ g ∘ k#) ∘ (bfh ∘ bh) #
    let μ2 := rational1 (f ∘ h # ⊓ g ∘ k#) ∘ (agk ∘ ag) # ⊓ rational2 (f ∘ h # ⊓ g ∘ k#) ∘ (bgk ∘ bk) #
    let v1 := (μ1 ∘ afh) ∘ bf
    let v2 := (μ2 ∘ agk) ∘ bg
    have Hfh := comp_total Hfh (rational1_function (bf ∘ ah#)).left
    have Hfh := comp_total Hfh (rational2_function f).left
    have Hgk := comp_total Hgk (rational1_function (bg ∘ ak#)).left
    have Hgk := comp_total Hgk (rational2_function g).left
    have H:v1# ∘ v2 ⊑ fst Y Z # ∘ snd Y Z := by
      simp
    have H: is_total (v1 ∘ fst Y Z# ⊓ v2 ∘ snd Y Z#) := domain_corollary1 Hfh Hgk H
    rw[← rational_comp (f ∘ h # ⊓ g ∘ k#)]
    apply inc_trans
    · apply comp_inc_compat_ab_a'b
      apply comp_inc_compat_a_ab H
    · simp
      rw[← comp_assoc]
      apply comp_inc_compat
      · apply inc_trans comp_cap_distr_l
        apply cap_inc_compat
        · simp
          apply comp_inc_compat_ab_a'b
          dsimp[v1]
          apply inc_trans
          · apply comp_inc_compat_ab_ab'
            rw[← comp_assoc]
            apply comp_inc_compat_ab_a'b cap_l
          · simp
            rw[← comp_assoc, ← comp_assoc, ← comp_assoc]
            apply inc_trans (comp_inc_compat_ab_b (rational1_function _).right)
            apply inc_trans
            · apply comp_inc_compat_ab_ab'
              simp
              apply comp_inc_compat_ab_b (rational1_function _).right
            · rw[rational_comp]
              simp
        · simp
          apply comp_inc_compat_ab_a'b
          dsimp[v2]
          apply inc_trans
          · apply comp_inc_compat_ab_ab'
            rw[← comp_assoc]
            apply comp_inc_compat_ab_a'b cap_l
          · simp
            rw[← comp_assoc, ← comp_assoc, ← comp_assoc]
            apply inc_trans (comp_inc_compat_ab_b (rational1_function _).right)
            apply inc_trans
            · apply comp_inc_compat_ab_ab'
              simp
              apply comp_inc_compat_ab_b (rational1_function _).right
            · rw[rational_comp]
              simp
      · have H0 : afh ∘ bf = bfh ∘ ah := by
          apply inc_antisym
          · apply inc_trans (comp_inc_compat_b_ab (rational2_function _).left)
            simp
            conv => lhs; lhs; rw[← comp_assoc]; rhs; rw[← inv_invol (_ ∘ _), comp_inv, inv_invol, rational_comp]
            simp
            rw[← comp_assoc]
            apply comp_inc_compat_ab_a (rational2_function _).right
          · apply inc_trans (comp_inc_compat_b_ab (rational1_function _).left)
            simp
            rw[acomp_l (rational_comp _)]
            simp
            rw[← comp_assoc]
            apply comp_inc_compat_ab_a (rational1_function _).right
        have H1 : agk ∘ bg = bgk ∘ ak := by
          apply inc_antisym
          · apply inc_trans (comp_inc_compat_b_ab (rational2_function _).left)
            simp
            conv => lhs; lhs; rw[← comp_assoc]; rhs; rw[← inv_invol (_ ∘ _), comp_inv, inv_invol, rational_comp]
            simp
            rw[← comp_assoc]
            apply comp_inc_compat_ab_a (rational2_function _).right
          · apply inc_trans (comp_inc_compat_b_ab (rational1_function _).left)
            simp
            rw[acomp_l (rational_comp _)]
            simp
            rw[← comp_assoc]
            apply comp_inc_compat_ab_a (rational1_function _).right
        apply inc_trans comp_cap_distr_r
        simp[rel_prod]
        apply cap_inc_compat
        · rw[← comp_assoc]
          apply comp_inc_compat_ab_ab'
          dsimp[v1]
          apply inc_trans
          · apply comp_inc_compat_ab_a'b
            dsimp[μ1]
            simp
            apply comp_inc_compat_ab_ab' cap_r
          · simp
            rw[← comp_assoc]
            apply inc_trans (comp_inc_compat_ab_a (rational2_function _).right)
            apply inc_trans
            · rw[← comp_inv, H0, comp_inv]
              apply comp_inc_compat_ab_a'b
              rw[← comp_assoc]
              apply comp_inc_compat_ab_a (rational2_function _).right
            · rw[rational_comp]
              simp
        · rw[← comp_assoc]
          apply comp_inc_compat_ab_ab'
          dsimp[v2]
          simp
          rw[← comp_assoc]
          apply inc_trans
          · apply comp_inc_compat_ab_ab'
            dsimp[μ2]
            simp
            apply comp_inc_compat_ab_a'b cap_r
          · rw[← comp_inv, H1]
            simp
            rw[← comp_assoc]
            apply inc_trans (comp_inc_compat_ab_a (rational2_function _).right)
            apply inc_trans
            · apply comp_inc_compat_ab_a'b
              rw[← comp_assoc]
              apply comp_inc_compat_ab_a (rational2_function _).right
            · rw[rational_comp]
              simp

theorem diagonal_rational1 {f:c.rel X X}: f ⊑ idr X → rational1 f = rational2 f := by
  intro H
  apply inc_antisym
  · apply inc_trans (comp_inc_compat_b_ab (rational2_function f).left)
    rw[← comp_assoc, ← inv_invol (_# ∘ _), comp_inv, inv_invol, rational_comp, inv_diagonal H]
    apply comp_inc_compat_ab_a H
  · apply inc_trans (comp_inc_compat_b_ab (rational1_function f).left)
    rw[← comp_assoc, ← inv_invol (_# ∘ _), rational_comp, inv_invol]
    apply comp_inc_compat_ab_a H
theorem diagonal_rational2 {f:c.rel X X}: f ⊑ idr X → rational1 f ∘ rational1 f# = idr (rational_ob f) := by
  intro H
  rw[← rational_cap_id f, ← diagonal_rational1 H]
  simp
theorem diagonal_rational3 {f:c.rel X X}: f ⊑ idr X → rational1 f# ∘ rational1 f = f := by
  intro H
  conv => lhs; rhs; rw[diagonal_rational1 H]
  simp

instance dedekindSum_of_rationality [c : Dedekind_rationality] : Dedekind_sub' where
  sub_axiom f H := by
    exists (rational_ob f), (rational1 f)
    exact ⟨diagonal_rational3 H, diagonal_rational2 H, rational1_function f⟩

noncomputable def ZERO := rational_ob (φ c.exists_ob c.exists_ob)
notation "∅" => ZERO
theorem zero_def : idr ∅ = φ ∅ ∅ := by
  dsimp[ZERO]
  rw[← comp_id_r (idr _), ← diagonal_rational2 (inc_empty (idr c.exists_ob))]
  simp
  rw[acomp_l (diagonal_rational3 (inc_empty (idr c.exists_ob)))]
  simp
end dedekind_rationality

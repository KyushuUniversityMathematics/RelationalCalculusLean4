import Sum_Product
import Point
import Residual
import MyTac.mytactic
import Bernstein

section cantor
class Cantor extends Dedekind_Rationality where
  power : ∀ X:ob, ∃ Y:ob, ∃ f:rel Y X,
  ((f ▹ f#)⊓(f ▹ f#)# ⊑ idr Y)∧(∀ Z, ∀g:rel Z X, idr Z ⊑ (g ▹ f#) ∘ (f ▹ g#))

variable [c : Cantor]
noncomputable def pow (X : c.ob):c.ob :=
  Classical.choose (c.power X)
notation "𝒫" X:100 => pow X
noncomputable def inp (X : c.ob):c.rel (𝒫 X) X :=
  Classical.choose (Classical.choose_spec (c.power X))
notation "∋_" X:100 => inp X
noncomputable def subset (X : c.ob):= (∋_ X ▹ (∋_ X)#)
theorem subset_cap_subid {X : c.ob} :
  ((subset X)⊓(subset X)# ⊑ idr (𝒫 X)) :=
  (Classical.choose_spec (Classical.choose_spec (c.power X))).left
theorem inc_comp {X Z : c.ob} (g:c.rel Z X):
  idr Z ⊑ (g ▹ (∋_ X)#) ∘ ((∋_ X) ▹ g#) :=
  (Classical.choose_spec (Classical.choose_spec (c.power X))).right Z g

noncomputable def rel_fun {X Y:c.ob}(f : c.rel X Y) : c.rel X (𝒫 Y) :=
  (f ▹ (∋_ Y)#) ⊓ ((∋_ Y) ▹ f#)#
postfix:120 " ᶠ " => rel_fun

theorem rel_fun_spec {X Y:c.ob}(f : c.rel X Y) :
  is_function (fᶠ) := by
  constructor
  · rw[inc_def1r.mpr (inc_comp f)]
    apply inc_trans dedekind
    rw[rel_fun]
    conv => lhs; rhs; rw[cap_comm]
    simp
  · rw[rel_fun]
    apply inc_trans comp_cap_distr_l
    apply inc_trans
    · apply cap_inc_compat
      · simp
        apply comp_inc_compat_ab_a'b cap_r
      · simp
        apply comp_inc_compat_ab_a'b cap_l
    · rw[← comp_inv]
      apply inc_trans
      · apply cap_inc_compat_r
        conv => lhs; rhs; rw[← inv_invol f]
        apply residual_property2
      · apply inc_trans _ subset_cap_subid
        apply cap_inc_compat_l
        rw[inc_inv]
        conv => lhs; rhs; rw[← inv_invol f]
        apply residual_property2
theorem subset_cap_id :
  subset X ⊓ (subset X)# = idr (𝒫 X) := by
  apply inc_antisym subset_cap_subid
  have H := (rel_fun_spec (∋_ X)).left
  have H0 := (@subset_cap_subid _ X)
  rw[subset] at H0
  rw[rel_fun, inv_subid H0, comp_subid H0] at H
  assumption
theorem rel_fun_def (f:c.rel X Y) : fᶠ ∘ (∋_ Y) = f := by
  apply inc_antisym
  · rw[rel_fun]
    apply inc_trans
    · apply comp_inc_compat_ab_a'b cap_r
    · conv => rhs; rw[← inv_invol f]
      rw[inv_inc_move]
      simp
      apply inv_residual_inc
  · myconv => lhs; apply comp_inc_compat_b_ab (rel_fun_spec f).left
    comp_inc
    simp[rel_fun]
    myconv => lhs; lhs; apply cap_l
    conv => rhs; rw[← inv_invol (∋_ Y)]
    rw[inv_inc_move]
    simp
    apply inv_residual_inc

theorem rel_inc_fun {f:c.rel X (𝒫 Y)} :
  is_function f → (f∘(∋_ Y))ᶠ = f := by
  intro H
  conv => rhs; rw[← comp_id_r f, ← subset_cap_id, function_cap_distr_l H, subset, function_residual2 H]
  conv => rhs; rhs; rw[← inv_invol (_ ∘ _), comp_inv, inv_invol, function_residual3 H]
  rw[rel_fun]
  simp

theorem comp_id_func {X Y:c.ob}(f : c.rel X Y) :
  f∘f# = idr X → fᶠ ∘ fᶠ# = idr X := by
  intro H
  apply inc_antisym _ (rel_fun_spec f).left
  rw[← H]
  conv => rhs; lhs; rw[← rel_fun_def f]
  comp_inc
  simp[← inv_inc_move]
  rw[rel_fun]
  apply inc_trans cap_l
  conv => lhs; rw[← comp_id_l (f ▹ _), ← H, ← comp_assoc]
  apply comp_inc_compat_ab_ab' inv_residual_inc
theorem comp_function_eq : is_function f → (f ∘ g)ᶠ = f ∘ gᶠ := by
  intro H
  rw[← rel_inc_fun (comp_function H (rel_fun_spec g)), ← comp_assoc, rel_fun_def g]
theorem total_cap_function {X Y:c.ob}{f : c.rel X Y}{g : c.rel X Y} :
  is_total f → f ⊓ g = φ X Y → fᶠ ⊓ gᶠ = φ X (𝒫 Y) := by
  intro H H0
  apply inc_antisym _ (inc_empty _)
  rw[rel_fun]
  apply inc_trans (cap_inc_compat_r cap_l)
  apply inc_trans
  · apply cap_inc_compat_r (total_residual H)
  · apply inc_trans dedekind2
    simp[rel_fun_def g, H0]

instance cantor_unit : Dedekind_Unit := by
  constructor
  exists 𝒫 ∅
  constructor
  · intro H
    obtain ⟨X, H0⟩ := c.exists_notzero
    apply H0
    apply inc_antisym _ (inc_empty _)
    apply inc_trans (rel_fun_spec (φ X ∅)).left
    rw[← comp_id_r (_ᶠ), ← H]
    simp
  · constructor
    · apply inc_antisym (inc_universal _)
      apply inc_trans _ subset_cap_subid
      have H : subset ∅ = Δ (𝒫 ∅) (𝒫 ∅) := by
        apply inc_antisym (inc_universal _)
        rw[subset, ← comp_id_r (∋_ ∅), zero_def]
        simp
        simp[inc_residual]
      simp[H]
    · intro X
      apply inc_antisym (inc_universal _)
      apply inc_trans (comp_inc_compat_a_ab (rel_fun_spec (φ X ∅)).left)
      rw[comp_assoc]
      apply comp_inc_compat
      all_goals simp
theorem injective_sum {f:c.rel X W}{g:c.rel Y W}: is_injective f → is_injective g → f ∘ g# = φ X Y →
  ∃ Z : c.ob, ∃ (inl : c.rel X Z) (inr : c.rel Y Z),
  inl ∘ inl# = idr X ∧ inr ∘ inr# = idr Y ∧ inl ∘ inr# = φ X Y ∧ inl# ∘ inl ⊔ inr# ∘ inr = idr Z := by
  intro H H0 H1
  let k := f# ∘ f ⊔ g# ∘ g
  have H2 : k ⊑ idr W := inc_cup.mpr ⟨H.right, H0.right⟩
  exists _, f ∘ (sub_inj H2)#, g ∘ (sub_inj H2)#
  constructor
  · simp
    rw[acomp_l (sub_spec H2)]
    dsimp[k]
    simp[H.left, H1]
  · constructor
    · simp
      rw[acomp_l (sub_spec H2)]
      dsimp[k]
      have H3 : g ∘ f# = φ Y X := by
        conv => rhs; rw[← inv_empty]
        rw[inv_move]
        simp[H1]
      simp[H0.left, H3]
    · constructor
      · simp
        apply inc_antisym _ (inc_empty _)
        rw[← H1]
        comp_inc
        myconv => lhs; lhs; apply (sub_injective H2).right
        simp
      · simp
        dsimp[k] at H2
        rw[← comp_cup_distr_r, ← comp_assoc, ← comp_assoc, ← comp_cup_distr_l, ← sub_spec H2]
        simp
        rw[(sub_injective H2).left, comp_id_l, (sub_injective H2).left]
theorem sum_I (X : c.ob) :
  ∃ Y : c.ob, ∃ (inl : c.rel X Y) (inr : c.rel I Y),
    inl ∘ inl# = idr X ∧ inr ∘ inr# = idr I ∧ inl ∘ inr# = φ X I ∧ inl# ∘ inl ⊔ inr# ∘ inr = idr Y := by
  have H : is_injective (idr Xᶠ) := by
    rw[← univalent_function_injective (idr Xᶠ)]
    apply And.intro _ (rel_fun_spec _)
    rw[is_univalent]
    simp
    rw[comp_id_func]
    simp
    simp
  have H0 : is_injective (φ I Xᶠ) := by
    rw[← univalent_function_injective (φ I Xᶠ)]
    apply And.intro _ (rel_fun_spec _)
    rw[is_univalent]
    simp[unit_id_universal]
  have H1 : is_function (Δ X I) := by
    rw[is_function]
    simp
    constructor
    · simp[comp_unit_universal]
    · simp[unit_id_universal]
  have H1 : idr Xᶠ ∘ φ I Xᶠ # = φ X I := by
    apply inc_antisym _ (inc_empty _)
    rw[← cap_universal (_ ∘ _)]
    apply inc_trans dedekind2
    simp
    rw[← comp_function_eq H1]
    simp
    rw[total_cap_function]
    simp
    simp[is_total]
    simp
  apply injective_sum H H0 H1
instance cantor_sum [c : Cantor] : Dedekind_Sum := by
  constructor
  intro X Y
  obtain ⟨XI, iX, jX, HX, HX0, HX1, HX2⟩ := sum_I X
  obtain ⟨YI, iY, jY, HY, HY0, HY1, HY2⟩ := sum_I Y
  let f := iX × Δ X I ∘ jY
  let g := Δ Y I ∘ jX × iY
  apply (@injective_sum _ _ _ _ f g)
  · rw[← univalent_function_injective f]
    constructor
    · simp[is_univalent]
      dsimp[f]
      simp[← sharpness, HX]
    · dsimp[f]
      apply function_prod
      · constructor
        · simp[HX]
        · simp[← HX2]
      · constructor
        · simp[acomp_l HY0, comp_unit_universal]
        · simp[← HY2]
          apply inc_trans _ cup_r
          apply comp_inc_compat_ab_a'b
          rw[← comp_assoc]
          apply comp_inc_compat_ab_a
          simp[unit_id_universal]
  · rw[← univalent_function_injective g]
    constructor
    · simp[is_univalent]
      dsimp[g]
      simp[← sharpness, HY]
    · dsimp[g]
      apply function_prod
      · constructor
        · simp[acomp_l HX0, comp_unit_universal]
        · simp[← HX2]
          apply inc_trans _ cup_r
          apply comp_inc_compat_ab_a'b
          rw[← comp_assoc]
          apply comp_inc_compat_ab_a
          simp[unit_id_universal]
      · constructor
        · simp[HY]
        · simp[← HY2]
  · dsimp[f, g]
    simp[← sharpness, HX1]

def is_symmetric_idempotent (θ:c.rel X X) := θ# ⊑ θ ∧ θ ∘ θ = θ
@[simp]
theorem symmetric_idempotent_def {θ:c.rel X X} :
  is_symmetric_idempotent θ ↔ θ ∘ θ# = θ := by
  rw[is_symmetric_idempotent]
  constructor
  · rintro ⟨H, H0⟩
    have H:θ# = θ := by
      apply inc_antisym
      · simp[H]
      · simp_all[inv_inc_move]
    grind
  · intro H
    constructor
    · conv => lhs; rw[← H];simp;rw[H]
      simp
    · have H0 : θ ∘ θ# = θ# := by
        rw[inv_move]
        simp
        assumption
      conv => lhs; rhs; rw[← H, H0]
      assumption
theorem corational_function {X Y : c.ob} (α : c.rel X Y) :
  α = (α ∘ α#) ∘ α  → ∃ f : c.rel X (𝒫 Y), ∃ g : c.rel Y (𝒫 Y),
  is_function f ∧ is_function g ∧ α = f ∘ g# := by
  intro H
  -- have H : α ∘ α# = (α ∘ α#) ∘ (α ∘ α#) := by simp[← H]
  let θ := α# ∘ α ⊔ idr Y
  exists αᶠ, θᶠ
  have Hf : is_function (αᶠ) := rel_fun_spec α
  have Hg : is_function (θᶠ) := rel_fun_spec θ
  simp[Hf, Hg]
  apply inc_antisym
  · rw[← comp_id_r (αᶠ), ← subset_cap_id, subset, function_cap_distr Hf Hg]
    rw[function_residual2 Hf, rel_fun_def, function_residual3 Hg, ← comp_inv, rel_fun_def]
    conv => lhs; rw[← inv_invol α]
    rw[← inv_inc_move]
    simp
    rw[function_residual2 Hg, rel_fun_def, function_residual3 Hf, ← comp_inv, rel_fun_def]
    rw[← inv_inc_move]
    simp
    rw[inc_cap]
    constructor
    · rw[inc_residual]
      dsimp[θ]
      simp
    · rw[inv_inc_move, inc_residual, inv_inc_move]
      simp
      dsimp[θ]
      simp
      rw[← H]
      simp
  · conv => rhs;rw[← rel_fun_def α]
    comp_inc
    rw[← comp_id_l (∋_Y)]
    myconv => rhs; lhs; apply Hg.right
    rw[← comp_assoc, rel_fun_def]
    apply comp_inc_compat_a_ab
    dsimp[θ]
    simp


def is_equivalence (θ:c.rel X X) := idr X ⊑ θ ∧ θ# = θ ∧ θ ∘ θ = θ
theorem equivalence_function {θ : c.rel X X} : is_equivalence θ →
  ∃ f : c.rel X (𝒫 X), is_function f ∧ f ∘ f# = θ := by
    rintro ⟨H, H0, H1⟩
    exists θᶠ
    simp[rel_fun_spec θ]
    apply inc_antisym
    · conv => rhs; rw[← rel_fun_def θ]
      comp_inc
      rw[← comp_id_l (∋_ X)]
      myconv => rhs; lhs; apply (rel_fun_spec θ).right
      rw[← comp_assoc, rel_fun_def θ]
      apply comp_inc_compat_a_ab H
    · conv => rhs;lhs; rw[← comp_id_r (θᶠ)]
      rw[← subset_cap_id, subset, function_cap_distr (rel_fun_spec θ) (rel_fun_spec θ)]
      rw[function_residual2 (rel_fun_spec θ), rel_fun_def, function_residual3 (rel_fun_spec θ), ← comp_inv, rel_fun_def]
      conv => lhs; rw[← H0]
      rw[← inv_inc_move]
      simp
      rw[function_residual2 (rel_fun_spec θ), rel_fun_def, function_residual3 (rel_fun_spec θ), ← comp_inv, rel_fun_def]
      conv => lhs; rw[← H0]
      rw[← inv_inc_move]
      simp
      rw[inc_cap]
      constructor
      · rw[inc_residual]
        simp_all
      · rw[inv_inc_move, inc_residual]
        simp_all
theorem symmetric_idempotent_univalent {θ:c.rel X X} :
  is_symmetric_idempotent θ → ∃ α:c.rel X (𝒫 X), is_univalent α ∧ α ∘ α # = θ := by
  rintro ⟨H, H0⟩
  have H1 : is_equivalence (θ ⊔ idr X) := by
    constructor
    · simp
    · constructor
      · simp
        congr
        apply inc_antisym H
        simp_all[inv_inc_move]
      · simp_all
  rcases equivalence_function H1 with ⟨f, H2, H3⟩
  exists (domain θ) ∘ f
  constructor
  · rw[is_univalent]
    simp
    rw[acomp_l (comp_subid domain_subid)]
    myconv => lhs; lhs; rhs; apply domain_subid
    simp
    exact H2.right
  · simp
    rw[acomp_l H3]
    simp
    rw[domain_comp1, comp_subid domain_subid]
    have H : θ# = θ := by
      apply inc_antisym
      · simp[H]
      · simp_all[inv_inc_move]
    conv => lhs; lhs; lhs; rw[← H]
    rw[domain_comp2, H, domain]
    simp_all
theorem symmetric_idempotent_split {θ:c.rel X X} :
  is_symmetric_idempotent θ ↔
  ∃ Y, ∃ η:c.rel X Y, η ∘ η # = θ ∧ η# ∘ η = idr Y := by
  constructor
  · intro H
    rcases symmetric_idempotent_univalent H with ⟨α, H0, H1⟩
    rw[is_univalent] at H0
    rcases Dedekind_sub'.sub_axiom H0 with ⟨Y, j, H2, H3, H4⟩
    exists _,  α ∘ j#
    constructor
    · simp
      rw[acomp_l H2]
      simp[H1, acomp_l H1, H.right]
    · simp
      conv => lhs;lhs; rw[← comp_assoc, ← H2]
      simp[H3]
  · rintro ⟨Y, η, H, H0⟩
    rw[symmetric_idempotent_def, ← H]
    simp[acomp_l H0]
theorem equivalence_symmetric_idempotent {θ:c.rel X X} :
  is_equivalence θ → is_symmetric_idempotent θ := by
  simp[is_equivalence]
  intro _ H H0
  simp_all
end cantor

section choice
class Cantor_Choice extends Cantor where
  choice {α : rel X Y}: is_total α → ∃ f : rel X Y, is_function f ∧ (f ⊑ α)

variable [c : Cantor_Choice]
theorem complement'_cap_empty {u:c.rel X X}:
  u ⊑ idr X → ∃ v, u ⊓ v = φ X X ∧ u ⊔ v = idr X := by
  intro H
  let l := in_l X X
  let r := in_r X X
  let θ := idr (X+X) ⊔ (l# ∘ u) ∘ r ⊔ (r# ∘ u) ∘ l
  have H0 : (l ∘ θ) ∘ r# = u := by
    dsimp[θ]
    simp
    rw[inl_inr_empty, inl_id, acomp_l inr_id]
    simp
  have H1 : (l ∘ θ) ∘ l# = idr X := by
    dsimp[θ]
    simp
    rw[inl_inr_empty, inl_id, acomp_l inr_inl_empty]
    simp
  have H2 : (r ∘ θ) ∘ r# = idr X := by
    dsimp[θ]
    simp
    rw[inr_inl_empty, inr_id, acomp_l inl_inr_empty]
    simp
  have H3 : is_equivalence θ := by
    dsimp[θ]
    constructor
    · simp[← cup_assoc]
    · constructor
      · simp
        rw[← cup_assoc, ← cup_assoc]
        congr 1
        rw[cup_comm]
        congr
        all_goals exact inv_subid H
      · simp
        rw[acomp_l inl_id, acomp_l inr_id, acomp_l inl_inr_empty, acomp_l inr_inl_empty]
        simp
        rw[acomp_l (comp_subid H), acomp_l (comp_subid H)]
        conv => lhs; lhs; lhs; lhs; rw[cup_comm, cup_assoc, cup_assoc];lhs; rw[cup_comm, cup_assoc, cup_idem]
        conv => lhs; lhs; rw[cup_comm, cup_assoc, cup_assoc];lhs; rw[cup_comm, cup_assoc, cup_idem, cup_comm, ← cup_assoc, cup_comm]
        rw[← cup_assoc, ← cup_assoc, cup_comm]
        conv => rhs; rw[← cup_assoc, cup_comm]
        rw[← cup_assoc, ← cup_assoc, ← cup_assoc]
        congr 1
        rw[cup_assoc, cup_assoc, cup_comm]
        congr 1
        apply inc_antisym
        · rw[← cup_assoc, ← inc_def2r.mpr, ← inc_def2r.mpr]
          · simp
          · rw[← @inl_inr_cup_id _ _ X]
            apply inc_trans _ cup_l
            dsimp[l]
            comp_inc
            apply comp_inc_compat_ab_b H
          · apply inc_trans _ cup_r
            rw[← @inl_inr_cup_id _ _ X]
            apply inc_trans _ cup_r
            dsimp[r]
            comp_inc
            apply comp_inc_compat_ab_b H
        · simp
  · rcases symmetric_idempotent_split.mp (equivalence_symmetric_idempotent H3) with ⟨Y, q, H4, H5⟩
    have H6:is_total (q#) := by
      simp[is_total, ← H5]
    rcases c.choice H6 with ⟨f, H7, H8⟩
    let x := (l ∘ q) ∘ f
    let y := (r ∘ q) ∘ f
    exists ((x ∘ l#) ∘ y) ∘ r#
    have H9 : is_function x := by
      dsimp[x]
      constructor
      · simp
        conv => rhs; lhs; lhs; rw[← comp_assoc]
        myconv =>rhs; lhs; lhs; rhs; apply H7.left
        simp
        rw[acomp_l H4, H1]
        simp
      · simp
        rapply H7.right
        conv => rhs;rhs; rw[← comp_id_l f, ← H5]
        comp_inc
        apply comp_inc_compat_ab_b
        rw[← inl_inr_cup_id]
        apply inc_trans _ cup_l
        simp[l]
    have H10 : is_function y := by
      dsimp[y]
      constructor
      · simp
        conv => rhs; lhs; lhs; rw[← comp_assoc]
        myconv =>rhs; lhs; lhs; rhs; apply H7.left
        simp
        rw[acomp_l H4, H2]
        simp
      · simp
        rapply H7.right
        conv => rhs;rhs; rw[← comp_id_l f, ← H5]
        comp_inc
        apply comp_inc_compat_ab_b
        rw[← inl_inr_cup_id]
        apply inc_trans _ cup_r
        simp[r]
    have H12 : x ∘ l# ⊑ idr X := by
      dsimp[x]
      rw[← H1, ← H4]
      comp_inc
      assumption
    have H13 : y ∘ r# ⊑ idr X := by
      dsimp[y]
      rw[← H2, ← H4]
      comp_inc
      assumption
    constructor
    · apply inc_antisym _ (inc_empty _)
      rw[← inl_inr_empty]
      conv => rhs; change l ∘ r#; rw[← comp_id_r l]
      myconv => rhs; lhs; rhs; apply (H9.right)
      rw[← comp_id_r (x#)]
      myconv => rhs; lhs; rhs; lhs; rhs; apply H
      simp
      have H11 : u ∘ x = u ∘ y := by
        dsimp[x, y]
        rw[← comp_id_r q, ← H5]
        simp
        rw[acomp_l H4, acomp_l H4]
        congr 2
        dsimp[θ]
        simp
        rw[acomp_l inl_id, acomp_l inl_inr_empty, acomp_l inr_inl_empty, acomp_l inr_id]
        simp[comp_subid H]
        rw[cup_comm]


      rw[acomp_l H11, ← comp_assoc, comp_cap_subid H12 H13, cap_comm, ← cap_assoc]
      conv => lhs; rhs; rw[cap_comm]
      rw[← inv_subid H12]
      simp
      rw[← inv_id, inv_inc_move] at H12
      simp at H12
      rw[comp_cap_subid H12 H]
      conv => rhs; rw[← comp_assoc]
      rw[comp_cap_subid _ H13]
      · simp
      · apply inc_trans cap_l
        assumption
    · apply inc_antisym
      · simp_all[inc_cup]
        rw[← comp_assoc]
        rapply H12
        exact comp_inc_compat_ab_a H13
      · rapply H9.left
        rw[← comp_id_r (x#), comp_assoc]
        myconv => lhs; rhs; apply H10.left
        conv => lhs; lhs; lhs; rw[← comp_id_r x, ← inl_inr_cup_id]; change x ∘ (l# ∘ l ⊔ r# ∘ r)
        conv => lhs; lhs; simp; rw[← comp_assoc]; lhs; rhs; rw[← inv_invol (_ ∘ _), comp_inv, inv_invol, inv_subid H12]
        rw[comp_subid H12]
        have H11 : x ∘ r# ⊑ u := by
          dsimp[x]
          rw[← H0, ← H4]
          comp_inc
          assumption
        conv => lhs; lhs; rhs; rw[← comp_assoc];rhs; rw[← inv_invol (_ ∘ _), comp_inv, inv_invol, inv_subid (inc_trans H11 H)]
        rw[comp_subid (inc_trans H11 H)]
        apply inc_trans
        · apply comp_inc_compat_ab_a'b
          apply cup_inc_compat_l H11
        · conv => lhs; rhs; lhs; rw[← comp_id_r y, ← inl_inr_cup_id]; change y ∘ ( l# ∘ l ⊔ r# ∘ r)
          have H11 : y ∘ l# ⊑ u := by
            dsimp[y]
            rw[← inv_subid H, ← H0, ← H4]
            simp
            comp_inc
            assumption
          conv => lhs; rhs; simp; rw[← comp_assoc]; lhs; rhs; rw[← inv_invol (_ ∘ _), comp_inv, inv_invol, inv_subid (inc_trans H11 H)]
          rw[comp_subid (inc_trans H11 H)]
          apply inc_trans
          · apply comp_inc_compat_ab_ab'
            apply cup_inc_compat_r H11
          · conv => lhs; rhs; rhs; rw[← comp_assoc]; rhs; rw[← inv_invol (_ ∘ _), comp_inv, inv_invol, inv_subid H13]
            rw[comp_subid H13]
            simp
            rw[comp_subid H]
            apply inc_trans
            · apply cup_inc_compat_r
              apply cup_inc_compat_r
              apply cup_inc_compat_r
              apply comp_inc_compat_ab_a'b H12
            · simp
              rw[cup_comm, cup_assoc, ← comp_assoc]
              apply inc_trans
              · apply cup_inc_compat_r
                apply cup_inc_compat_r
                apply comp_inc_compat_ab_ab' H13
              · simp

theorem split {X Y : c.ob} (α : c.rel X Y) :
  ∃ β :c.rel X Y, α ⊓ β = φ X Y ∧ α ⊔ β = Δ X Y := by
  let Z := rational_ob (Δ X Y)
  let p := rational1 (Δ X Y)
  let q := rational2 (Δ X Y)
  let u := (p ∘ α) ∘ q# ⊓ idr Z
  have H : u ⊑ idr Z := by dsimp[u];simp
  rcases complement'_cap_empty H with ⟨v, H0, H1⟩
  exists (p# ∘ v) ∘ q
  constructor
  · apply inc_antisym _ (inc_empty _)
    rw[cap_comm, ← comp_assoc]
    apply inc_trans dedekind1
    simp
    rw[← comp_empty_r (p#)]
    comp_inc
    apply inc_trans dedekind2
    rw[← comp_empty_l q]
    comp_inc
    have H2 : v ⊑ idr Z := by
      rw[← H1]
      simp
    rw[inc_def1l.mpr H2, ← cap_assoc]
    conv => lhs; rhs; rw[cap_comm]; change u
    rw[cap_comm, H0]
    simp
  · apply inc_antisym (inc_universal _)
    conv => lhs; rw[← rational_comp (Δ X Y)]; change p# ∘ q; rw[← comp_id_r (p#), ← H1]
    simp[u]
    apply cup_inc_compat_r
    apply inc_trans comp_cap_distr
    simp
    rw[comp_id_r, rational_comp]
    simp
    rw[← comp_assoc]
    apply inc_trans
    · apply comp_inc_compat_ab_a'b
      apply comp_inc_compat_ab_b (rational1_function _).right
    · apply comp_inc_compat_ab_a (rational2_function _).right

instance cantor_choice_schroder : Schroder := by
  constructor
  intro X Y α
  rcases split α with ⟨β, H0, H1⟩
  rw[← H1]
  congr
  rw[inc_lower]
  intro h
  constructor
  · rw[complement, inc_rpc]
    intro H
    rw[← cap_universal h, ← H1, cap_cup_distr_l, inc_cup]
    simp
    rapply H
    simp
  · intro H
    rw[complement, inc_rpc, ← H0, cap_comm]
    apply cap_inc_compat_l H

end choice

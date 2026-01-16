import sum_product
import point
import residual
import MyTac.mytactic

class cantor extends Dedekind_rationality where
  power : ∀ X, ∃ Y, ∃ f:rel Y X,
  ((f ▹ f#)⊓(f ▹ f#)#⊑idr Y)∧(∀ Z, ∀g:rel Z X, idr Z ⊑ (g ▹ f#) ∘ (f ▹ g#))

variable [c : cantor]
noncomputable def pow (X : c.ob):c.ob :=
  Classical.choose (c.power X)
notation "𝒫" X:100 => pow X
noncomputable def inp (X : c.ob):c.rel (𝒫 X) X :=
  Classical.choose (Classical.choose_spec (c.power X))
notation "∋_" X:100 => inp X
noncomputable def subset (X : c.ob):= (∋_ X ▹ (∋_ X)#)
theorem subset_cap_diagonal {X : c.ob} :
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
      · apply inc_trans _ subset_cap_diagonal
        apply cap_inc_compat_l
        rw[inc_inv]
        conv => lhs; rhs; rw[← inv_invol f]
        apply residual_property2
theorem subset_cap_id :
  subset X ⊓ (subset X)# = idr (𝒫 X) := by
  apply inc_antisym subset_cap_diagonal
  have H := (rel_fun_spec (∋_ X)).left
  have H0 := (@subset_cap_diagonal _ X)
  rw[subset] at H0
  rw[rel_fun, inv_diagonal H0, comp_diagonal H0] at H
  assumption
theorem rel_fun_inc (f:c.rel X Y) : fᶠ ∘ (∋_ Y) = f := by
  apply inc_antisym
  · rw[rel_fun]
    apply inc_trans
    · apply comp_inc_compat_ab_a'b cap_r
    · conv => rhs; rw[← inv_invol f]
      rw[inv_inc_move]
      simp
      apply inv_residual_inc
  · myconv => lhs; apply comp_inc_compat_b_ab (rel_fun_spec f).left
    rw[← comp_assoc]
    apply comp_inc_compat_ab_ab'
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
  conv => rhs; lhs; rw[← rel_fun_inc f]
  rw[← comp_assoc]
  apply comp_inc_compat_ab_ab'
  simp[← inv_inc_move]
  rw[rel_fun]
  apply inc_trans cap_l
  conv => lhs; rw[← comp_id_l (f ▹ _), ← H, ← comp_assoc]
  apply comp_inc_compat_ab_ab' inv_residual_inc
theorem comp_function_eq : is_function f → (f ∘ g)ᶠ = f ∘ gᶠ := by
  intro H
  rw[← rel_inc_fun (comp_function H (rel_fun_spec g)), ← comp_assoc, rel_fun_inc g]
theorem total_cap_function {X Y:c.ob}{f : c.rel X Y}{g : c.rel X Y} :
  is_total f → f ⊓ g = φ X Y → fᶠ ⊓ gᶠ = φ X (𝒫 Y) := by
  intro H H0
  apply inc_antisym _ (inc_empty _)
  rw[rel_fun]
  apply inc_trans (cap_inc_compat_r cap_l)
  apply inc_trans
  · apply cap_inc_compat_r (total_residual H)
  · apply inc_trans dedekind2
    simp[rel_fun_inc g, H0]

instance cantor_unit : Dedekind_unit := by
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
      apply inc_trans _ subset_cap_diagonal
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
        apply comp_inc_compat_ab_a'b
        rw[← comp_assoc]
        apply comp_inc_compat_ab_a (sub_injective H2).right
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
instance cantor_sum [c : cantor] : Dedekind_sum := by
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

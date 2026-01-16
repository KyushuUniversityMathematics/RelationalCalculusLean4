import Dedekind
import Dedekind_Axioms

variable [c:Dedekind]
def is_total (f:c.rel X Y) := idr X ⊑ f ∘ f#
def is_univalent (f:c.rel X Y) := f# ∘ f ⊑ idr Y
def is_function (f:c.rel X Y) := idr X ⊑ f ∘ f# ∧ f# ∘ f ⊑ idr Y
def is_injective (f:c.rel X Y) := f ∘ f# = idr X ∧ f# ∘ f ⊑ idr Y
def is_surjective (f:c.rel X Y) := f# ∘ f = idr Y ∧ idr X ⊑ f ∘ f#
def is_bijective (f:c.rel X Y) := f ∘ f# = idr X ∧ f# ∘ f = idr Y

theorem total_univalent_function {f:c.rel X Y} :
  is_total f ∧ is_univalent f ↔ is_function f := by
  rw[is_function, is_total, is_univalent]
theorem total_function_surjective (f:c.rel X Y) :
  is_total (f#) ∧ is_function f ↔ is_surjective f := by
  rw[is_function, is_total, is_surjective, inv_invol, ← inc_antisym', and_assoc]
  apply Iff.intro
  · rintro ⟨H, H0, H1⟩
    exact ⟨H1, H, H0⟩
  · rintro ⟨H, H0, H1⟩
    exact ⟨H0, H1, H⟩
theorem univalent_function_injective (f:c.rel X Y) :
  is_univalent (f#) ∧ is_function f ↔ is_injective f := by
  rw[is_function, is_univalent, is_injective, inv_invol, ← inc_antisym', and_assoc]
theorem surjective_injective_bijective (f:c.rel X Y) :
  is_surjective f ∧ is_injective f ↔ is_bijective f := by
  rw[is_bijective, is_surjective, is_injective, and_assoc, ← inc_antisym', ← inc_antisym', and_assoc, and_assoc, and_assoc]
  apply Iff.intro
  · rintro ⟨H, H0, H1, H2, H3, H4⟩
    exact ⟨H2, H1, H4, H0⟩
  · rintro ⟨H, H0, H1, H2⟩
    exact ⟨H1, H2, H0, H, H0, H1⟩
theorem inv_function_bijective (f:c.rel X Y) :
  is_function f ∧ is_function (f#) ↔ is_bijective f := by
  rw[is_function, is_function, is_bijective, inv_invol, ← inc_antisym', and_assoc, and_assoc, ← inc_antisym']
  apply Iff.intro
  · rintro ⟨H, H0, H1, H2⟩
    exact ⟨H2, H, H0, H1⟩
  · rintro ⟨H, H0, H1, H2⟩
    exact ⟨H0, H1, H2, H⟩
theorem function_total {f:c.rel X Y} :
  is_function f → is_total f := by
  rw[← total_univalent_function]
  rintro ⟨H, H0⟩
  assumption
theorem function_univalent {f:c.rel X Y} :
  is_function f → is_univalent f := by
  rw[← total_univalent_function]
  rintro ⟨H, H0⟩
  assumption
theorem injective_function (f:c.rel X Y) :
  is_injective f → is_function f := by
  rw[← univalent_function_injective]
  rintro ⟨H, H0⟩
  exact H0
theorem surjective_function (f:c.rel X Y) :
  is_surjective f → is_function f := by
  rw[← total_function_surjective]
  rintro ⟨H, H0⟩
  exact H0
theorem bijective_surjective (f:c.rel X Y) :
  is_bijective f → is_surjective f := by
  rw[← surjective_injective_bijective]
  intro ⟨H, H0⟩
  exact H
theorem bijective_injective (f:c.rel X Y) :
  is_bijective f → is_injective f := by
  rw[← surjective_injective_bijective]
  intro ⟨H, H0⟩
  exact H0
theorem inv_bijective (f:c.rel X Y) :
  is_bijective f → is_bijective (f#) := by
  rw[is_bijective, is_bijective, inv_invol, and_comm]
  intro H
  assumption

theorem comp_univalent {f:c.rel X Y} {g:c.rel Y Z} :
  is_univalent f → is_univalent g → is_univalent (f ∘ g) := by
  rw[is_univalent, is_univalent, is_univalent, comp_inv, comp_assoc]
  intro H H0
  apply inc_trans _ H0
  apply comp_inc_compat_ab_a'b
  conv => rhs; rw[← comp_id_r (g#)]
  rw[← comp_assoc]
  apply comp_inc_compat_ab_ab' H
theorem comp_total {f:c.rel X Y} {g:c.rel Y Z} :
  is_total f → is_total g → is_total (f ∘ g) := by
  rw[is_total, is_total, is_total, comp_inv, ← comp_assoc]
  intro H H0
  apply inc_trans H
  apply comp_inc_compat_ab_ab'
  rw[comp_assoc]
  conv => lhs; rw[← comp_id_l (f#)]
  apply comp_inc_compat_ab_a'b H0
theorem comp_function {f:c.rel X Y} {g:c.rel Y Z} :
  is_function f → is_function g → is_function (f ∘ g) := by
  rw[← total_univalent_function, ← total_univalent_function, ← total_univalent_function]
  intro ⟨H, H0⟩ ⟨H1, H2⟩
  constructor
  · apply comp_total H H1
  · apply comp_univalent H0 H2
theorem comp_injective {f:c.rel X Y} {g:c.rel Y Z} :
  is_injective f → is_injective g → is_injective (f ∘ g) := by
  rw[← univalent_function_injective, ← univalent_function_injective, ← univalent_function_injective, comp_inv]
  intro ⟨H, H0⟩ ⟨H1, H2⟩
  constructor
  · apply comp_univalent H1 H
  · apply comp_function H0 H2
theorem comp_surjective {f:c.rel X Y} {g:c.rel Y Z} :
  is_surjective f → is_surjective g → is_surjective (f ∘ g) := by
  rw[← total_function_surjective, ← total_function_surjective, ← total_function_surjective, comp_inv]
  intro ⟨H, H0⟩ ⟨H1, H2⟩
  constructor
  · apply comp_total H1 H
  · apply comp_function H0 H2
theorem comp_bijective {f:c.rel X Y} {g:c.rel Y Z} :
  is_bijective f → is_bijective g → is_bijective (f ∘ g) := by
  rw[← inv_function_bijective, ← inv_function_bijective, ← inv_function_bijective, comp_inv]
  intro ⟨H, H0⟩ ⟨H1, H2⟩
  constructor
  · apply comp_function H H1
  · apply comp_function H2 H0

theorem id_bijective (X:c.ob) :
  is_bijective (idr X) := by
  rw[is_bijective]
  simp
theorem id_function (X:c.ob) :
  is_function (idr X) := by
  rw[is_function]
  simp
theorem total_comp {f:c.rel X Y} {g:c.rel Y Z} :
  is_total (f ∘ g) → is_total f := by
  rw[is_total, is_total, comp_inv, ← comp_assoc]
  intro H
  rw[← inc_def1r] at H
  rw[H]
  apply inc_trans dedekind
  apply comp_inc_compat
  all_goals simp
theorem univalent_comp {f:c.rel X Y} {g:c.rel Y Z} :
  is_univalent (f ∘ g) → is_total (f#) → is_univalent g := by
  rw[is_univalent, is_univalent, is_total, comp_inv, comp_assoc, inv_invol]
  intro H H0
  apply inc_trans _ H
  apply comp_inc_compat_ab_a'b
  conv => lhs; rw[← comp_id_r (g#)]
  rw[← comp_assoc]
  apply comp_inc_compat_ab_ab' H0
theorem total_inc : is_total f → f ⊑ g → is_total g := by
  rw[is_total, is_total]
  intro H H0
  apply inc_trans H
  apply comp_inc_compat  H0 (inc_inv.mpr H0)
theorem univalent_inc : is_univalent g → f ⊑ g → is_univalent f := by
  rw[is_univalent, is_univalent]
  intro H H0
  apply inc_trans _ H
  apply comp_inc_compat (inc_inv.mpr H0) H0
theorem function_inc {f:c.rel X Y} {g:c.rel X Y} :
  is_function f → is_function g → f ⊑ g → f = g := by
  rw[is_function, is_function]
  intro ⟨H, H0⟩ ⟨H1, H2⟩ H3
  apply inc_antisym H3
  apply inc_trans
  · rw[← comp_id_l g]
    apply comp_inc_compat_ab_a'b H
  · apply inc_trans (comp_inc_compat_ab_a'b _)
    · conv => rhs; rw[← comp_id_r f]
      rw[← comp_assoc]
      apply comp_inc_compat_ab_ab' H2
    · apply comp_inc_compat_ab_ab' (inc_inv.mpr H3)
theorem function_rel_inv_rel  :
  is_function f → (f ∘ f#) ∘ f = f := by
  rw[is_function]
  intro ⟨H, H0⟩
  apply inc_antisym
  · rw[← comp_assoc]
    exact comp_inc_compat_ab_a H0
  · apply comp_inc_compat_b_ab H
theorem function_capP_distr {f:c.rel X Y}{g:c.rel W Z} {P : c.rel A B → Prop}{α : c.rel A B → c.rel Y Z} :
  is_function f → is_function g → (f ∘ capP P α) ∘ g# = capP P (fun x => (f ∘ (α x)) ∘ g#) := by
  rw[is_function, is_function]
  intro ⟨H, H0⟩ ⟨H1, H2⟩
  apply inc_antisym comp_capP_distr
  apply inc_trans (comp_inc_compat_b_ab H)
  rw[← comp_assoc, ← comp_assoc]
  apply comp_inc_compat_ab_ab'
  apply inc_trans (comp_inc_compat_a_ab H1)
  rw[comp_assoc]
  apply comp_inc_compat_ab_a'b
  apply inc_trans comp_capP_distr
  rw[inc_capP]
  intro h H3
  apply inc_trans _ (comp_inc_compat_ab_b H0)
  apply inc_trans _ (comp_inc_compat_ab_a H2)
  rw[← comp_assoc, ← comp_assoc]
  conv => rhs; rhs; rw[comp_assoc, comp_assoc]
  rw[comp_assoc]
  apply capP_inc H3
theorem function_capP_distr_l {f:c.rel X Y} {P : c.rel A B → Prop} {α : c.rel A B → c.rel Y Z} :
  is_function f → f ∘ capP P α = capP P (fun x => f ∘ (α x)) := by
  intro H
  rw[← comp_id_r (f ∘ _), ← inv_id]
  rw[function_capP_distr H (id_function Z)]
  simp
theorem function_capP_distr_r {g:c.rel Z Y} {P : c.rel A B → Prop} {α : c.rel A B → c.rel X Y} :
  is_function g → capP P α ∘ g# = capP P (fun x => (α x) ∘ g#) := by
  intro H
  rw[← comp_id_l (capP _ _)]
  rw[function_capP_distr (id_function X) H]
  simp
theorem function_cap_distr {f:c.rel X Y} {g:c.rel W Z} {h a:c.rel Y Z} :
  is_function f → is_function g →
  (f ∘ (h ⊓ a)) ∘ g# = ((f ∘ h) ∘ g#) ⊓ ((f ∘ a) ∘ g#) := by
  intro H H0
  rw[← cap_to_capP, ← cap_to_capP, function_capP_distr H H0]
  simp
  apply inc_antisym
  · rw[inc_capP]
    intro b H1
    cases H1 with |inl H1 |inr H1
    · simp
      rw[H1]
      apply capP_inc
      left
      rfl
    · simp
      rw[H1]
      apply capP_inc
      right
      rfl
  · rw[inc_capP]
    intro b H1
    cases H1 with |inl H1 |inr H1
    · rw[H1]
      apply capP_inc
      left
      rfl
    · rw[H1]
      apply capP_inc
      right
      rfl
theorem function_cap_distr_l {f:c.rel X Y} {h a:c.rel Y Z} :
  is_function f → f ∘ (h ⊓ a) = (f ∘ h) ⊓ (f ∘ a) := by
  intro H
  rw[← comp_id_r (f ∘ _), ← inv_id]
  rw[function_cap_distr H (id_function Z)]
  simp
theorem function_cap_distr_r {g:c.rel Z Y} {h a:c.rel X Y} :
  is_function g → (h ⊓ a) ∘ g# = (h ∘ g#) ⊓ (a ∘ g#) := by
  intro H
  rw[← comp_id_l (h ⊓ a)]
  rw[function_cap_distr (id_function X) H]
  simp

theorem function_move1 {f:c.rel X Y} {g:c.rel Y Z} {h:c.rel X Z} :
  is_function f → (h ⊑ f ∘ g ↔ f# ∘ h ⊑ g) := by
  rw[is_function]
  intro ⟨H, H0⟩
  constructor
  · intro H1
    apply inc_trans _ (comp_inc_compat_ab_b H0)
    rw[← comp_assoc]
    apply comp_inc_compat_ab_ab' H1
  · intro H1
    apply inc_trans (comp_inc_compat_b_ab H)
    rw[← comp_assoc]
    apply comp_inc_compat_ab_ab' H1
theorem function_move2 {f:c.rel X Y} {g:c.rel Y Z} {h:c.rel X Z} :
  is_function g → (f ∘ g ⊑ h ↔ f ⊑ h ∘ g#) := by
  rw[is_function]
  intro ⟨H, H0⟩
  constructor
  · intro H1
    apply inc_trans (comp_inc_compat_a_ab H)
    rw[comp_assoc]
    apply comp_inc_compat_ab_a'b H1
  · intro H1
    apply inc_trans _ (comp_inc_compat_ab_a H0)
    rw[comp_assoc]
    apply comp_inc_compat_ab_a'b H1

-- 途中

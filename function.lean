import Dedekind
import MyTac.mytactic

variable [c:Dedekind]
@[simp]def is_total (f:c.rel X Y) := idr X ⊑ f ∘ f#
@[simp]def is_univalent (f:c.rel X Y) := f# ∘ f ⊑ idr Y
@[simp]def is_function (f:c.rel X Y) := idr X ⊑ f ∘ f# ∧ f# ∘ f ⊑ idr Y
@[simp]def is_injective (f:c.rel X Y) := f ∘ f# = idr X ∧ f# ∘ f ⊑ idr Y
@[simp]def is_surjective (f:c.rel X Y) := f# ∘ f = idr Y ∧ idr X ⊑ f ∘ f#
@[simp]def is_bijective (f:c.rel X Y) := f ∘ f# = idr X ∧ f# ∘ f = idr Y

theorem total_univalent_function {f:c.rel X Y} :
  is_total f ∧ is_univalent f ↔ is_function f := by
  simp
theorem total_function_surjective (f:c.rel X Y) :
  is_total (f#) ∧ is_function f ↔ is_surjective f := by
  simp[inc_antisym']
  constructor
  all_goals simp_all
theorem univalent_function_injective (f:c.rel X Y) :
  is_univalent (f#) ∧ is_function f ↔ is_injective f := by
  simp[inc_antisym']
  constructor
  all_goals simp_all
theorem surjective_injective_bijective (f:c.rel X Y) :
  is_surjective f ∧ is_injective f ↔ is_bijective f := by
  simp[inc_antisym']
  constructor
  all_goals simp_all
theorem inv_function_bijective (f:c.rel X Y) :
  is_function f ∧ is_function (f#) ↔ is_bijective f := by
  simp[inc_antisym']
  constructor
  all_goals simp_all
theorem function_total {f:c.rel X Y} :
  is_function f → is_total f := by
  simp_all
theorem function_univalent {f:c.rel X Y} :
  is_function f → is_univalent f := by
  simp_all
theorem injective_function (f:c.rel X Y) :
  is_injective f → is_function f := by
  simp_all
theorem surjective_function (f:c.rel X Y) :
  is_surjective f → is_function f := by
  simp_all
theorem bijective_surjective (f:c.rel X Y) :
  is_bijective f → is_surjective f := by
  simp_all
theorem bijective_injective (f:c.rel X Y) :
  is_bijective f → is_injective f := by
  simp_all
theorem inv_bijective (f:c.rel X Y) :
  is_bijective f → is_bijective (f#) := by
  simp_all

theorem comp_univalent {f:c.rel X Y} {g:c.rel Y Z} :
  is_univalent f → is_univalent g → is_univalent (f ∘ g) := by
  simp
  intro H H0
  transby H0
  comp_inc
theorem comp_total {f:c.rel X Y} {g:c.rel Y Z} :
  is_total f → is_total g → is_total (f ∘ g) := by
  simp
  intro H H0
  transby H
  comp_inc
theorem comp_function {f:c.rel X Y} {g:c.rel Y Z} :
  is_function f → is_function g → is_function (f ∘ g) := by
  simp
  rintro H H0 H1 H2
  constructor
  · transby H
    comp_inc
  · transby H2
    comp_inc
theorem comp_injective {f:c.rel X Y} {g:c.rel Y Z} :
  is_injective f → is_injective g → is_injective (f ∘ g) := by
  simp
  intro H H0 H1 H2
  constructor
  · simp_all[acomp_l H1]
  · transby H2
    comp_inc
theorem comp_surjective {f:c.rel X Y} {g:c.rel Y Z} :
  is_surjective f → is_surjective g → is_surjective (f ∘ g) := by
  simp
  intro H H0 H1 H2
  constructor
  · simp_all[acomp_l H]
  · transby H0
    comp_inc
theorem comp_bijective {f:c.rel X Y} {g:c.rel Y Z} :
  is_bijective f → is_bijective g → is_bijective (f ∘ g) := by
  simp
  intro H H0 H1 H2
  constructor
  · simp_all[acomp_l H1]
  · simp_all[acomp_l H0]

theorem id_bijective (X:c.ob) : is_bijective (idr X) := by simp
theorem id_function (X:c.ob) : is_function (idr X) := by simp
theorem total_comp {f:c.rel X Y} {g:c.rel Y Z} :
  is_total (f ∘ g) → is_total f := by
  simp
  intro H
  rw[← inc_def1r] at H
  rw[H]
  apply inc_trans dedekind
  apply comp_inc_compat
  all_goals simp
theorem univalent_comp {f:c.rel X Y} {g:c.rel Y Z} :
  is_univalent (f ∘ g) → is_total (f#) → is_univalent g := by
  simp
  intro H H0
  transby H
  comp_inc
theorem total_inc : is_total f → f ⊑ g → is_total g := by
  simp
  intro H H0
  transby H
  apply comp_inc_compat H0
  simp_all
theorem univalent_inc : is_univalent g → f ⊑ g → is_univalent f := by
  simp
  intro H H0
  transby H
  apply comp_inc_compat _ H0
  simp_all
theorem function_inc {f:c.rel X Y} {g:c.rel X Y} :
  is_function f → is_function g → f ⊑ g → f = g := by
  simp
  intro H H0 H1 H2 H3
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
  simp
  intro H H0
  apply inc_antisym
  · comp_inc
  · apply comp_inc_compat_b_ab H
theorem function_capP_distr {f:c.rel X Y}{g:c.rel W Z} {P : c.rel A B → Prop}{α : c.rel A B → c.rel Y Z} :
  is_function f → is_function g → (f ∘ capP P α) ∘ g# = capP P (fun x => (f ∘ (α x)) ∘ g#) := by
  simp
  intro H H0 H1 H2
  apply inc_antisym comp_capP_distr
  transby comp_inc_compat_b_ab H
  transby comp_inc_compat_a_ab H1
  comp_inc
  transby comp_capP_distr
  rw[inc_capP]
  intro h H3
  transby comp_inc_compat_ab_b H0
  transby comp_inc_compat_ab_a H2
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
  simp
  intro H H0 H1 H2
  apply inc_antisym comp_cap_distr
  transby comp_inc_compat_b_ab H
  transby comp_inc_compat_a_ab H1
  comp_inc
  transby comp_cap_distr
  simp[inc_cap]
  constructor
  all_goals
    transby comp_inc_compat_ab_b H0
    transby comp_inc_compat_ab_a H2
  · transby cap_l
    comp_inc
  · transby cap_r
    comp_inc
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
  simp
  intro H H0
  constructor
  · intro H1
    transby comp_inc_compat_ab_b H0
    comp_inc
  · intro H1
    transby comp_inc_compat_b_ab H
    comp_inc
theorem function_move2 {f:c.rel X Y} {g:c.rel Y Z} {h:c.rel X Z} :
  is_function g → (f ∘ g ⊑ h ↔ f ⊑ h ∘ g#) := by
  simp
  intro H H0
  constructor
  · intro H1
    transby comp_inc_compat_a_ab H
    comp_inc
  · intro H1
    transby comp_inc_compat_ab_a H0
    comp_inc

theorem function_rpc_distr : is_function f → is_function g →
  (f ∘ (α ⇒ β)) ∘ g# = ((f ∘ α) ∘ g#) ⇒ ((f ∘ β) ∘ g#) := by
  intro H H0
  rw[inc_lower]
  intro x
  constructor
  · intro H1
    rw[inc_rpc]
    transby cap_inc_compat_r H1
    rw[← function_cap_distr H H0]
    comp_inc
    simp[cap_comm, rpc_l]
  · intro H1
    rw[inc_rpc, ← function_move2 H0, function_move1 H] at H1
    rw[← function_move2 H0, function_move1 H, inc_rpc]
    transby dedekind
    simp
    transby H1
    transby (comp_inc_compat_ab_a'b (cap_l))
    -- myconv => lhs; lhs; apply cap_l
    comp_inc
    transby dedekind
    comp_inc

theorem function_rpc_distr_l : is_function f → (f ∘ (α ⇒ β)) = ((f ∘ α) ⇒ (f ∘ β)) := by
  intro H
  rw[← comp_id_r (f ∘ _), ← inv_id]
  rw[function_rpc_distr H (id_function _)]
  simp
theorem function_rpc_distr_r : is_function g → ((α ⇒ β) ∘ g#) = ((α ∘ g#) ⇒ (β ∘ g#)) := by
  intro H
  rw[← comp_id_l (_ ⇒ _)]
  rw[function_rpc_distr (id_function _) H]
  simp

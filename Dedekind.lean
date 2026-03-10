import Dedekind_Axioms
import Std
open Std

variable [c : Dedekind]

section Axioms
@[simp] theorem comp_id_l (f:c.rel X Y) : (idr X) ∘ f = f := c.comp_id_l f
@[simp] theorem comp_id_r (f:c.rel X Y) : f ∘ (idr Y) = f := c.comp_id_r f
@[simp] theorem comp_assoc {W:c.ob} (f : c.rel W X) (g : c.rel X Y) (h : c.rel Y Z) :
  f ∘ (g ∘ h) = (f ∘ g) ∘ h := by rw[← c.comp_assoc f g h]
theorem acomp_l {x : c.rel X Y}{y : c.rel Y Z}{z : c.rel X Z} :
  x ∘ y = z → ∀ w:c.rel W X, (w ∘ x) ∘ y = w ∘ z := by
  intro H w
  rw[← comp_assoc, H]

@[simp] theorem inc_refl (f : c.rel X Y) : f ⊑ f := c.inc_refl f
theorem inc_trans {f g h : c.rel X Y} : f ⊑ g → g ⊑ h → f ⊑ h := @c.inc_trans X Y f g h
theorem inc_antisym {f g : c.rel X Y}: f ⊑ g → g ⊑ f → f = g := @c.inc_antisym X Y f g
theorem inc_antisym' {f g : c.rel X Y} : f = g ↔ f ⊑ g ∧ g ⊑ f := by
  constructor
  · intro H
    simp[H]
  · simp
    exact inc_antisym
theorem inc_cap {f g h : c.rel X Y} : f ⊑ g ⊓ h ↔ f ⊑ g ∧ f ⊑ h := @c.inc_cap X Y f g h
theorem inc_capP {X Y Z W}{f : c.rel Z W} {P : c.rel X Y → Prop}{α : c.rel X Y → c.rel Z W} : f ⊑ capP P α ↔ ∀ g, P g → f ⊑ α g := @c.inc_capP Z W X Y f P α
theorem inc_cup {f g h : c.rel X Y} : f ⊔ g ⊑ h ↔ f ⊑ h ∧ g ⊑ h := @c.inc_cup X Y f g h
theorem inc_cupP {X Y Z W}{f : c.rel Z W} {P : c.rel X Y → Prop}{β : c.rel X Y → c.rel Z W} : cupP P β ⊑ f ↔ ∀ g, P g → β g ⊑ f := @c.inc_cupP Z W X Y f P β
@[simp] theorem inc_empty  (f : c.rel X Y) : φ X Y ⊑ f := c.inc_empty f
@[simp] theorem inc_universal (f : c.rel X Y) : f ⊑ Δ X Y := c.inc_universal f
theorem inc_rpc {f g h : c.rel X Y} : f ⊑ g ⇒ h ↔ f ⊓ g ⊑ h := @c.inc_rpc X Y f g h
@[simp] theorem inv_invol (f : c.rel X Y) : f## = f := c.inv_invol f
@[simp] theorem comp_inv (f : c.rel X Y) (g : c.rel Y Z) : (f ∘ g)# = g# ∘ f# := c.comp_inv f g
@[simp] theorem inc_inv {f g : c.rel X Y} : f# ⊑ g# ↔ f ⊑ g := by
  constructor
  · intro H
    rw[←inv_invol f, ←inv_invol g]
    exact c.inc_inv H
  · exact c.inc_inv
theorem dedekind : f ∘ g ⊓ h ⊑ (f ⊓ h ∘ g#) ∘ (g ⊓ f# ∘ h) := c.dedekind
theorem inc_residual {f : c.rel X Y}{g : c.rel Y Z}{h : c.rel X Z} : h ⊑ f ▹ g ↔ f# ∘ h ⊑ g := @c.inc_residual X Y Z f g h
end Axioms
section basic_lemmas
@[simp] theorem cap_l {f g : c.rel X Y} : f ⊓ g ⊑ f :=
  (inc_cap.mp (inc_refl (f ⊓ g))).left
@[simp] theorem cap_r {f g : c.rel X Y} : f ⊓ g ⊑ g :=
  (inc_cap.mp (inc_refl (f ⊓ g))).right
@[simp] theorem cup_l {f g : c.rel X Y} : f ⊑ f ⊔ g :=
  (inc_cup.mp (inc_refl (f ⊔ g))).left
@[simp] theorem cup_r {f g : c.rel X Y} : g ⊑ f ⊔ g :=
  (inc_cup.mp (inc_refl (f ⊔ g))).right
theorem inc_def1l : f = f ⊓ g ↔ f ⊑ g := by
  constructor
  · intro H
    rw[H]
    simp
  · simp_all[inc_antisym', inc_cap]
theorem inc_def1r : g = f ⊓ g ↔ g ⊑ f := by
  constructor
  · intro H
    rw[H]
    simp
  · simp_all[inc_antisym', inc_cap]
theorem inc_def2l : f = f ⊔ g ↔ g ⊑ f := by
  constructor
  · intro H
    rw[H]
    simp
  · simp_all[inc_antisym', inc_cup]
theorem inc_def2r : g = f ⊔ g ↔ f ⊑ g := by
  constructor
  · intro H
    rw[H]
    simp
  · simp_all[inc_antisym', inc_cup]
@[simp] theorem cap_assoc (f g h:c.rel X Y) : f ⊓ (g ⊓ h) = f ⊓ g ⊓ h := by
  simp[inc_antisym', inc_cap]
  constructor
  · simp[inc_trans cap_r]
  · simp[inc_trans cap_l]
@[simp] theorem cup_assoc (f g h:c.rel X Y) : f ⊔ (g ⊔ h) = f ⊔ g ⊔ h := by
  simp[inc_antisym', inc_cup]
  constructor
  · simp[inc_trans _ cup_l]
  · simp[inc_trans _ cup_r]
theorem cap_comm (f g:c.rel X Y): f ⊓ g = g ⊓ f := by
  simp[inc_antisym', inc_cap]

theorem cup_comm (f g:c.rel X Y): f ⊔ g = g ⊔ f := by
  simp[inc_antisym', inc_cup]

instance : @Associative (c.rel X Y) cap :=
  ⟨fun a b c' => (cap_assoc a b c').symm⟩
instance : @Associative (c.rel X Y) cup :=
  ⟨fun a b c' => (cup_assoc a b c').symm⟩
instance : @Commutative (c.rel X Y) cap :=
  ⟨fun a b => (cap_comm a b)⟩
instance : @Commutative (c.rel X Y) cup :=
  ⟨fun a b => (cup_comm a b)⟩
@[simp] theorem cup_cap_abs (f g:c.rel X Y): f ⊔ (f ⊓ g) = f := by
  simp[inc_antisym', inc_cup]

@[simp] theorem cap_cup_abs (f g:c.rel X Y): f ⊓ (f ⊔ g) = f := by
  simp[inc_antisym', inc_cap]

@[simp] theorem cap_idem (f:c.rel X Y): f ⊓ f = f := by
  simp[inc_antisym', inc_cap]

@[simp] theorem cup_idem (f:c.rel X Y): f ⊔ f = f := by
  simp[inc_antisym', inc_cup]

theorem cap_inc_compat {f f' g g':c.rel X Y} :
  f ⊑ f' → g ⊑ g' → f ⊓ g ⊑ f' ⊓ g' := by
  intro h1 h2
  simp[inc_cap, inc_trans _ h1, inc_trans _ h2]
theorem cap_inc_compat_l {f g g':c.rel X Y} :
  g ⊑ g' → f ⊓ g ⊑ f ⊓ g' := by
  apply cap_inc_compat
  simp
theorem cap_inc_compat_r {f f' g:c.rel X Y} :
  f ⊑ f' → f ⊓ g ⊑ f' ⊓ g := by
  intro h
  apply cap_inc_compat h
  simp
theorem cup_inc_compat {f f' g g':c.rel X Y} :
  f ⊑ f' → g ⊑ g' → f ⊔ g ⊑ f' ⊔ g' := by
  intro h1 h2
  simp[inc_cup, inc_trans h1, inc_trans h2]
theorem cup_inc_compat_l {f g g':c.rel X Y} :
  g ⊑ g' → f ⊔ g ⊑ f ⊔ g' := by
  apply cup_inc_compat
  simp
theorem cup_inc_compat_r {f f' g:c.rel X Y} :
  f ⊑ f' → f ⊔ g ⊑ f' ⊔ g := by
  intro h
  apply cup_inc_compat h
  simp
@[simp] theorem eq_empty (f:c.rel X Y) : f = φ X Y ↔ f ⊑ φ X Y := by
  simp[inc_antisym']
@[simp] theorem empty_eq (f:c.rel X Y) : φ X Y = f ↔ f ⊑ φ X Y := by
  simp[inc_antisym']
@[simp] theorem cap_empty (f:c.rel X Y) : f ⊓ φ X Y = φ X Y := by
  simp
@[simp] theorem empty_cap (f:c.rel X Y) : φ X Y ⊓ f = φ X Y := by
  simp
@[simp] theorem cup_empty (f:c.rel X Y) : f ⊔ φ X Y = f := by
  simp[inc_antisym', inc_cup]
@[simp] theorem empty_cup (f:c.rel X Y) : φ X Y ⊔ f = f := by
  simp[inc_antisym', inc_cup]
@[simp] theorem eq_universal (f:c.rel X Y) : f = Δ X Y ↔ Δ X Y ⊑ f := by
  simp[inc_antisym']
@[simp] theorem universal_eq (f:c.rel X Y) : Δ X Y = f ↔ Δ X Y ⊑ f := by
  simp[inc_antisym']
@[simp] theorem cap_universal (f:c.rel X Y) : f ⊓ Δ X Y = f := by
  simp[inc_antisym', inc_cap]
@[simp] theorem universal_cap (f:c.rel X Y) : Δ X Y ⊓ f = f := by
  simp[inc_antisym', inc_cap]
@[simp] theorem cup_universal (f:c.rel X Y) : f ⊔ Δ X Y = Δ X Y := by
  simp
@[simp] theorem universal_cup (f:c.rel X Y) : Δ X Y ⊔ f = Δ X Y := by
  simp
theorem inc_lower {f g:c.rel X Y} :
  f = g ↔ (∀ h, h ⊑ f ↔ h ⊑ g) := by
  constructor
  · simp_all
  · intro H
    simp[inc_antisym', ← H f, H g]
theorem inc_upper {f g:c.rel X Y} :
  f = g ↔ (∀ h, f ⊑ h ↔ g ⊑ h) := by
  constructor
  · simp_all
  · intro H
    simp[inc_antisym', ← H f, H g]
theorem cap_cup_distr_l {f g h:c.rel X Y} :
  f ⊓ (g ⊔ h) = (f ⊓ g) ⊔ (f ⊓ h) := by
  rw[inc_upper]
  intro a
  constructor
  · intro H
    rw[cap_comm , cap_comm f h, c.inc_cup, ← c.inc_rpc, ← c.inc_rpc, ← c.inc_cup, c.inc_rpc, cap_comm]
    exact H
  · intro H
    rw[cap_comm , cap_comm f h, c.inc_cup, ← c.inc_rpc, ← c.inc_rpc, ← c.inc_cup, c.inc_rpc, cap_comm] at H
    exact H
theorem cap_cup_distr_r {f g h:c.rel X Y} :
  (f ⊔ g) ⊓ h = (f ⊓ h) ⊔ (g ⊓ h) := by
  simp only [cap_comm _ h]
  exact cap_cup_distr_l
theorem cup_cap_distr_l {f g h:c.rel X Y} :
  f ⊔ (g ⊓ h) = (f ⊔ g) ⊓ (f ⊔ h) := by
  rw[cap_cup_distr_l]
  conv => rhs;rw[cap_comm, cap_cup_abs]
  rw[cap_cup_distr_r, cup_assoc, cup_cap_abs]
theorem cup_cap_distr_r {f g h:c.rel X Y} :
  (f ⊓ g) ⊔ h = (f ⊔ h) ⊓ (g ⊔ h) := by
  simp only [cup_comm _ h]
  exact cup_cap_distr_l

theorem cap_cup_unique {f g h:c.rel X Y} :
  f ⊓ g = f ⊓ h → f ⊔ g = f ⊔ h → g = h := by
  intro H1 H2
  rw[← cup_cap_abs g f, cap_comm, H1, cup_cap_distr_l, cup_comm, H2, cup_comm, cup_comm g h, ← cup_cap_distr_l, H1, cap_comm, cup_cap_abs]

def is_atomic (f:c.rel X Y) : Prop :=
  f ≠ φ X Y ∧ ∀ g:c.rel X Y, g ⊑ f → g = f ∨ g = φ X Y
theorem atomic_empty {f g:c.rel X Y} : is_atomic f →
  g ⊑ f → g ≠ f → g = φ X Y := by
  rw[is_atomic]
  intro ⟨h1, h2⟩ h3 h4
  rcases h2 g h3
  · contradiction
  · assumption
theorem atomic_eq {f g:c.rel X Y} : is_atomic f →
  g ⊑ f → g ≠ φ X Y → g = f := by
  rw[is_atomic]
  intro ⟨h1, h2⟩ h3 h4
  rcases h2 g h3
  · assumption
  · contradiction
theorem atomic_cap_empty {f g:c.rel X Y} : is_atomic f →  is_atomic g →
  f ≠ g → f ⊓ g = φ X Y := by
  intro Hf Hg H
  by_cases H0 : (f ⊓ g = φ X Y)
  · exact H0
  · exfalso
    have Hf : f ⊓ g = f := by
      apply atomic_eq Hf
      · simp
      · assumption
    have Hg : f ⊓ g = g := by
      apply atomic_eq Hg
      · simp
      · assumption
    rw[← Hf, Hg] at H
    contradiction
theorem atomic_cup {f g h:c.rel X Y} : is_atomic f →
  f ⊑ g ⊔ h → f ⊑ g ∨ f ⊑ h := by
  intro Hf H
  rw[← inc_def1l, cap_cup_distr_l] at H
  have H0 : f ⊓ g ≠ φ X Y ∨ f ⊓ h ≠ φ X Y := by
    by_cases H1 : f ⊓ g = φ X Y
    · right
      rw[H1, empty_cup] at H
      rw[← H]
      exact Hf.left
    · left
      assumption
  cases H0 with | inl  H0 | inr H0
  · left
    rw[← inc_def1l]
    rw[← atomic_eq Hf _ H0]
    · rw[← cap_assoc, cap_idem]
    · simp
  · right
    rw[← inc_def1l]
    rw[← atomic_eq Hf _ H0]
    · rw[← cap_assoc, cap_idem]
    · simp
theorem rpc_universal (f:c.rel X Y) : f ⇒ f = Δ _ _ := by
  simp[inc_antisym', inc_rpc]
theorem rpc_r : f ⇒ g ⊓ g = g := by
  simp[inc_antisym', inc_cap, inc_rpc]
theorem inc_def3 : f ⇒ g = Δ _ _ ↔ f ⊑ g := by
  simp[inc_antisym', inc_rpc, universal_cap]
theorem rpc_l : f ⊓ (f ⇒ g) = f ⊓ g := by
  apply inc_antisym
  · simp[inc_cap]
    rw[cap_comm, ← inc_rpc]
    simp
  · simp[inc_cap, inc_rpc]
    simp[cap_comm, cap_assoc]

theorem rpc_inc_compat : f' ⊑ f → g ⊑ g' → f ⇒ g ⊑ f' ⇒ g' := by
  intro H H'
  apply inc_rpc.mpr
  apply inc_trans
  · apply cap_inc_compat_l H
  · rw[cap_comm, rpc_l]
    apply inc_trans _ H'
    simp
theorem rpc_inc_compat_l : f' ⊑ f → f ⇒ g ⊑ f' ⇒ g := by
  intro H
  apply rpc_inc_compat
  all_goals simp_all
theorem rpc_inc_compat_r : g ⊑ g' → f ⇒ g ⊑ f ⇒ g' := by
  intro H
  apply rpc_inc_compat
  all_goals simp_all
theorem universal_rpc (f:c.rel X Y) : Δ _ _ ⇒ f = f := by
  apply inc_lower.mpr
  intro h
  rw[inc_rpc, cap_universal]
theorem rpc_lemma1 (f:c.rel X Y) : f ⇒ g ⊑ (f ⊓ h) ⇒ (g ⊓ h) := by
  rw[inc_rpc, cap_assoc, cap_comm _ f, rpc_l, ← cap_assoc]
  apply cap_r
theorem rpc_lemma2 (f:c.rel X Y) : f ⇒ g ⊓ f ⇒ h = f ⇒ (g ⊓ h) := by
  apply inc_lower.mpr
  intro a
  rw[inc_rpc, inc_cap, inc_rpc, inc_rpc, inc_cap]
theorem rpc_lemma3 (f:c.rel X Y) : f ⇒ g ⊓ g ⇒ h ⊑ (f ⊔ g) ⇒ (g ⊓ h) := by
  rw[inc_rpc, cap_cup_distr_l, cap_comm _ f, cap_assoc, rpc_l, ← cap_assoc, rpc_l, ← cap_assoc, cap_comm _ g, rpc_l, ← cap_cup_distr_r]
  apply cap_r
theorem rpc_lemma4 (f:c.rel X Y) : f ⇒ g ⊓ g ⇒ h ⊑  f ⇒ h := by
  rw[inc_rpc, cap_comm, cap_assoc, rpc_l, ← cap_assoc, rpc_l, cap_assoc]
  apply cap_r
theorem rpc_lemma5 (f:c.rel X Y) : f ⇒ (g ⇒ h) = (f ⊓ g) ⇒ h := by
  apply inc_lower.mpr
  intro a
  rw[inc_rpc, inc_rpc, inc_rpc, cap_assoc]
theorem rpc_lemma6 (f:c.rel X Y) : f ⇒ (g ⇒ h) ⊑ (f ⇒ g) ⇒ (f ⇒ h) := by
  rw[inc_rpc, rpc_lemma5, inc_rpc, ← cap_assoc, cap_comm _ f, rpc_l, cap_comm, rpc_l]
  apply cap_r
theorem rpc_lemma7 (f:c.rel X Y) : g ⊑ f → f ⊑ h → (f ⊓ a = g ∧ f ⊔ a = h
  ↔ h ⊑ f ⊔ f ⇒ g ∧ a = h ⊓ f ⇒ g) := by
  intro H H0
  apply Iff.intro
  · rintro ⟨H1, H2⟩
    constructor
    · rw[← H2]
      apply cup_inc_compat_l
      rw[inc_rpc, cap_comm, H1]
      simp
    · rw[← H2, cap_cup_distr_r, rpc_l, ← inc_def1r.mpr H]
      have H3 : a ⊑ f ⇒ g := by
        rw[inc_antisym', cap_comm, ← inc_rpc] at H1
        exact H1.left
      rw[← inc_def1l.mpr H3, inc_def2r, ← H1]
      simp
  · rintro ⟨H1, H2⟩
    constructor
    · rw[H2, cap_assoc, cap_comm _ h, ← cap_assoc, rpc_l, cap_assoc, cap_comm h, ← inc_def1l.mpr H0, cap_comm, ← inc_def1l.mpr H]
    · rw[H2, cup_cap_distr_l, ← inc_def2r.mpr H0, ← inc_def1l.mpr H1]

theorem complement_universal : Δ X Y⁻ = φ X Y := by
  apply universal_rpc
theorem complement_empty : φ X Y⁻ = Δ X Y := by
  apply inc_antisym
  · simp
  · rw[complement, inc_rpc]
    simp
theorem complement_universal' {f:c.rel X Y}: f⁻ = Δ X Y ↔ f = φ X Y := by
  apply Iff.intro
  · rw[inc_antisym', complement, inc_rpc, universal_cap]
    rintro ⟨H1, H2⟩
    apply inc_antisym
    · assumption
    · simp
  · intro H
    rw[H]
    apply complement_empty
theorem complement_invol_inc {f:c.rel X Y}: f ⊑ f⁻⁻ := by
  rw[complement, inc_rpc, cap_comm, ← inc_rpc, complement]
  simp
@[simp] theorem cap_complement_empty (f:c.rel X Y) : f ⊓ f⁻ = φ X Y := by
  apply inc_antisym
  · rw[cap_comm, ← inc_rpc, complement]
    simp
  · simp
@[simp] theorem complement_cap_empty (f:c.rel X Y) : f⁻ ⊓ f = φ X Y := by
  simp[cap_comm]
theorem de_morgan1 (f g:c.rel X Y) : (f ⊔ g)⁻ = f⁻ ⊓ g⁻ := by
  apply inc_lower.mpr
  intro h
  rw[complement, inc_rpc, inc_cap, cap_cup_distr_l, complement, complement, inc_rpc, inc_rpc, inc_cup]

end basic_lemmas
section relational_properties
theorem rel_unique : φ X Y = Δ X Y → ∀ f g:c.rel X Y, f = g := by
  intro H f g
  apply inc_antisym
  all_goals(
    apply inc_trans
    · apply inc_universal
    · rw[← H]
      simp)
theorem comp_inc_compat_ab_ab' {f:c.rel X Y} {g g':c.rel Y Z} :
  g ⊑ g' → f ∘ g ⊑ f ∘ g' := by
  intro H
  rw[← inv_invol f]
  apply inc_residual.mp
  apply inc_trans H
  apply inc_residual.mpr
  simp
theorem comp_inc_compat_ab_a'b {f f':c.rel X Y} {g:c.rel Y Z} :
  f ⊑ f' → f ∘ g ⊑ f' ∘ g := by
  intro H
  rw[← inc_inv]
  simp
  apply comp_inc_compat_ab_ab'
  simp
  assumption
theorem cupP_False (P:c.rel X Y → Prop)(α : c.rel X Y → c.rel Z W) : (∀ f, ¬ P f) → cupP P α = φ Z W := by
  intro H
  apply c.inc_antisym
  · rw[inc_cupP]
    intro f H'
    have H'' := H f
    contradiction
  · simp
theorem capP_False (P:c.rel X Y → Prop)(α : c.rel X Y → c.rel Z W) : (∀ f, P f = False) → capP P α = Δ Z W := by
  intro H
  apply c.inc_antisym
  · simp
  · rw[inc_capP]
    intro f H'
    rw[H f] at H'
    contradiction
theorem comp_inc_compat {f f':c.rel X Y} {g g':c.rel Y Z} :
  f ⊑ f' → g ⊑ g' → f ∘ g ⊑ f' ∘ g' := by
  intro H H'
  apply inc_trans
  · apply comp_inc_compat_ab_a'b H
  · apply comp_inc_compat_ab_ab' H'
theorem comp_inc_compat_ab_a {f:c.rel X Y} {g:c.rel Y Y} :
  g ⊑ idr Y → f ∘ g ⊑ f := by
  intro H
  conv => rhs; rw[← comp_id_r f]
  apply comp_inc_compat_ab_ab' H
theorem comp_inc_compat_a_ab {f:c.rel X Y} {g:c.rel Y Y} :
  idr Y ⊑ g → f ⊑ f ∘ g := by
  intro H
  conv => lhs; rw[← comp_id_r f]
  apply comp_inc_compat_ab_ab' H
theorem comp_inc_compat_ab_b {f:c.rel X X} {g:c.rel X Y} :
  f ⊑ idr X → f ∘ g ⊑ g := by
  intro H
  conv => rhs; rw[← comp_id_l g]
  apply comp_inc_compat_ab_a'b H
theorem comp_inc_compat_b_ab {f:c.rel X X} {g:c.rel X Y} :
  idr X ⊑ f → g ⊑ f ∘ g := by
  intro H
  conv => lhs; rw[← comp_id_l g]
  apply comp_inc_compat_ab_a'b H
theorem cupP_cup_eq {P : c.rel X Y → Prop}(α : c.rel X Y → c.rel Z W) :
  P f → α f ⊔ cupP P α = cupP P α := by
  intro H
  apply inc_upper.mpr
  intro g
  apply Iff.intro
  · rw[inc_cup]
    rintro ⟨H1, H2⟩
    exact H2
  · rw[inc_cup]
    intro H0
    constructor
    · rw[inc_cupP] at H0
      apply H0
      assumption
    · exact H0
theorem cupP_inc : P f → α f ⊑ cupP P α := by
  intro H
  rw[← inc_def2r, cupP_cup_eq α H]
theorem cupP_eq : (∀ f, P f → α f = β f) → cupP P α = cupP P β := by
  intro H
  apply inc_antisym
  · rw[inc_cupP]
    intro f H0
    rw[H f H0]
    apply cupP_inc H0
  · rw[inc_cupP]
    intro f H0
    rw[← H f H0]
    apply cupP_inc H0
theorem cupP_f_id (f:c.rel X Y → c.rel Z W) : cupP P f = cupP (fun x => ∃ β , x = f β ∧ P β) id := by
  apply inc_antisym
  · rw[inc_cupP]
    intro g H
    apply (@cupP_inc _ _ _ _ _ _ id)
    exists g
  · rw[inc_cupP]
    intro g H
    rcases H with ⟨β, H1, H2⟩
    simp[H1]
    apply cupP_inc
    assumption
theorem eq_cupP :(∀ x, (∃ α, (x = f α) ∧ P α) ↔ (∃ α, x = g α ∧ Q α)) →
  cupP P f = cupP Q g := by
  rw[cupP_f_id, cupP_f_id g]
  intro H
  congr
  apply funext
  intro x
  rw[H x]

theorem capP_cap_eq {P : c.rel X Y → Prop}(α : c.rel X Y → c.rel Z W) :
  P f → α f ⊓ capP P α = capP P α := by
  intro H
  apply inc_lower.mpr
  intro g
  apply Iff.intro
  · rw[inc_cap]
    rintro ⟨H1, H2⟩
    exact H2
  · rw[inc_cap]
    intro H0
    constructor
    · rw[inc_capP] at H0
      apply H0
      assumption
    · exact H0
theorem capP_inc : P f → capP P α ⊑ α f := by
  intro H
  rw[← inc_def1r, capP_cap_eq α H]
theorem capP_eq : (∀ f, P f → α f = β f) → capP P α = capP P β := by
  intro H
  apply inc_antisym
  · rw[inc_capP]
    intro f H0
    rw[← H f H0]
    apply capP_inc H0
  · rw[inc_capP]
    intro f H0
    rw[H f H0]
    apply capP_inc H0
theorem cap_cupP_distr_l : f ⊓ cupP P α = cupP P (fun x => f ⊓ α x) := by
  apply inc_upper.mpr
  intro h
  constructor
  · intro H
    rw[inc_cupP]
    intro g H0
    apply inc_trans _ H
    apply cap_inc_compat_l
    apply cupP_inc H0
  · intro H
    rw[cap_comm, ← inc_rpc, inc_cupP]
    intro g H0
    rw[inc_rpc, cap_comm]
    apply inc_trans _ H
    apply cupP_inc H0
theorem cap_cupP_distr_r : cupP P α ⊓ f = cupP P (fun x => α x ⊓ f) := by
  rw[cap_comm _ f, cap_cupP_distr_l]
  apply inc_antisym
  · rw[inc_cupP]
    intro h H
    rw[cap_comm]
    apply cupP_inc H
  · rw[inc_cupP]
    intro h H
    rw[cap_comm]
    apply cupP_inc H
theorem de_morgan3 (P : c.rel X Y → Prop)(α : c.rel X Y → c.rel Z W) : (cupP P α)⁻ = capP P (fun x => (α x)⁻) := by
  apply inc_lower.mpr
  intro f
  rw[complement, inc_rpc, inc_capP]
  conv => rhs; rhs; rw[complement, inc_rpc]
  apply Iff.intro
  · intro H g H0
    apply inc_trans _ H
    apply cap_inc_compat_l
    apply cupP_inc H0
  · intro H
    rw[cap_comm, ← inc_rpc, inc_cupP]
    conv => rhs; rw[inc_rpc, cap_comm]
    assumption
theorem cup_to_cupP  : cupP (fun x => x = f ∨ x = g) id = f ⊔ g := by
  apply inc_upper.mpr
  intro h
  rw[inc_cup, inc_cupP]
  apply Iff.intro
  · intro H
    constructor
    all_goals apply H
    · left; rfl
    · right; rfl
  · rintro ⟨Hl, Hr⟩ a H0
    cases H0 with | inl H0 | inr H0
    all_goals rw[H0, id]; assumption
theorem cap_to_capP  : capP (fun x => x = f ∨ x = g) id = f ⊓ g := by
  apply inc_lower.mpr
  intro h
  rw[inc_cap, inc_capP]
  apply Iff.intro
  · intro H
    constructor
    all_goals apply H;simp
  · rintro ⟨Hl, Hr⟩ a H0
    cases H0 with | inl H0 | inr H0
    all_goals rw[H0, id]; assumption
theorem inv_move : f = g# ↔ f# = g := by
  apply Iff.intro
  · intro H
    rw[H]
    simp
  · intro H
    rw[← inv_invol f, ← inv_invol g]
    rw[H]
    simp
@[simp] theorem comp_inv_inv (f:c.rel X Y) (g:c.rel Y Z) :
  (g# ∘ f#)# = f ∘ g := by
  rw[comp_inv, inv_invol, inv_invol]
theorem inv_inc_move {f:c.rel X Y}{g:c.rel Y X} :
  f ⊑ g# ↔ f# ⊑ g := by
  rw[← inv_invol f, inc_inv]
  simp
@[simp] theorem inv_invol' : f# = g# ↔ f = g := by
  rw[inv_move]
  simp
@[simp] theorem inv_cup_distr : (f ⊔ g)# = f# ⊔ g# := by
  apply inc_antisym
  · rw[← inv_inc_move]
    apply inc_cup.mpr
    constructor
    · rw[inv_inc_move]
      apply cup_l
    · rw[inv_inc_move]
      apply cup_r
  · rw[← inc_inv, ← inv_inc_move]
    apply inc_cup.mpr
    simp
@[simp] theorem inv_cupP_distr (P : c.rel X Y → Prop)(α : c.rel X Y → c.rel Z W) :
  (cupP P α)# = cupP P (fun x => (α x)#) := by
  apply inc_upper.mpr
  intro h
  rw[inc_cupP, ← inv_inc_move, inc_cupP]
  conv => rhs; rhs; rw[← inv_inc_move]
@[simp] theorem inv_cap_distr : (f ⊓ g)# = f# ⊓ g# := by
  apply inc_antisym
  · apply inc_cap.mpr
    constructor
    · rw[← inv_inc_move]
      simp
    · rw[← inv_inc_move]
      simp
  · rw[inv_inc_move]
    apply inc_cap.mpr
    constructor
    · rw[← inv_inc_move]
      simp
    · rw[← inv_inc_move]
      simp
@[simp] theorem inv_capP_distr (P : c.rel X Y → Prop)(α : c.rel X Y → c.rel Z W) :
  (capP P α)# = capP P (fun x => (α x)#) := by
  apply inc_lower.mpr
  intro h
  rw[inc_capP, inv_inc_move, inc_capP]
  conv => rhs; rhs; rw[inv_inc_move]
@[simp] theorem rpc_inv_distr : (f ⇒ g)# = f# ⇒ g# := by
  apply inc_lower.mpr
  intro h
  apply Iff.intro
  · intro H
    rw[inc_rpc, inv_inc_move]
    simp
    rw[← inc_rpc, ← inv_inc_move]
    assumption
  · intro H
    rw[inv_inc_move, inc_rpc, ← inc_inv]
    simp
    rw[← inc_rpc]
    assumption
@[simp] theorem inv_empty : (φ X Y)# = φ Y X := by
  apply c.inc_antisym
  · rw[← inv_inc_move]
    simp
  · rw[← inc_inv, ← inv_inc_move]
    simp
@[simp] theorem inv_universal (X Y : c.ob) : (Δ X Y)# = Δ Y X := by
  apply c.inc_antisym
  · simp
  · rw[inv_inc_move]
    simp
@[simp] theorem inv_id (X:c.ob) : (idr X)# = idr X := by
  conv =>
    lhs
    rw[← comp_id_l (idr X #)]
    conv =>
      lhs
      rw[← inv_invol (idr X)]
  rw[← comp_inv, ← inv_move]
  simp
theorem inv_subid {f:c.rel X X} : f ⊑ idr X → f# = f := by
  intro H
  have H0:= @dedekind c X X f X (idr X) (idr X)
  simp at H0
  rw[← inc_def1l.mpr H] at H0
  rw[← inc_inv, inv_id] at H
  rw[← inc_def1r.mpr H] at H0
  apply inc_antisym
  · rw[← inc_inv, comp_inv, inv_invol] at H0
    apply inc_trans H0
    conv=> rhs; rw[← comp_id_r f]
    apply comp_inc_compat_ab_ab' H
  · apply inc_trans H0
    conv=> rhs; rw[← comp_id_l (f#)]
    apply comp_inc_compat_ab_a'b
    rw[← inc_inv, inv_id]
    assumption
theorem comp_subid {f:c.rel X X} : f ⊑ idr X → f∘f = f := by
  intro H
  have H0:= @dedekind c X X f X (idr X) (idr X)
  simp at H0
  rw[← inc_def1l.mpr H] at H0
  apply inc_antisym
  · conv=> rhs; rw[← comp_id_r f]
    apply comp_inc_compat_ab_ab' H
  · rw[← inc_inv, inv_id] at H
    rw[← inc_def1r.mpr H, inv_subid] at H0
    assumption
    rw[← inc_inv, inv_id]
    assumption
theorem comp_cap_subid {u v:c.rel X X}: u ⊑ idr X → v ⊑ idr X →
  u ∘ v = u ⊓ v := by
  intro H H'
  apply inc_antisym
  · rw[inc_cap]
    constructor
    · apply comp_inc_compat_ab_a H'
    · apply comp_inc_compat_ab_b H
  · conv => lhs; rw[← comp_subid H]
    apply inc_trans dedekind
    apply inc_trans
    · apply comp_inc_compat_ab_ab' cap_r
    · apply inc_trans
      · apply comp_inc_compat_ab_a'b cap_l
      · simp[inv_subid H, comp_subid H]
theorem inv_complement (f:c.rel X Y) : (f⁻)# = (f#)⁻ := by
apply inc_antisym
· conv => rhs; rw[complement]
  rw[inc_rpc, ← inv_cap_distr, cap_comm, cap_complement_empty, inv_empty]
  simp
· conv => rhs; rw[complement]
  rw[inv_inc_move, inc_rpc]
  conv => lhs; rhs; rw[← inv_invol f]
  rw[← inv_cap_distr, ← inv_inc_move, cap_comm, cap_complement_empty]
  simp
theorem comp_cupP_distr_l {f:c.rel X Y} {P : c.rel W A → Prop} {α : c.rel W A → c.rel Y Z} :
  f ∘ (cupP P α) = cupP P (fun x => f ∘ (α x)) := by
  apply inc_upper.mpr
  intro h
  apply Iff.intro
  · intro H
    rw[inc_cupP]
    intro g H0
    apply inc_trans _ H
    apply comp_inc_compat_ab_ab'
    apply cupP_inc H0
  · intro H
    rw[← inv_invol f, ← inc_residual, inc_cupP]
    intro g H0
    rw[inc_residual, inv_invol f]
    rw[inc_cupP] at H
    apply H _ H0
theorem comp_cupP_distr_r {P : c.rel X Y → Prop} {α : c.rel X Y → c.rel Z W} {g:c.rel W A} :
  (cupP P α) ∘ g = cupP P (fun x => (α x) ∘ g) := by
  rw[← inv_invol (_∘ g), ← inv_move, comp_inv, inv_cupP_distr, inv_cupP_distr, comp_cupP_distr_l]
  apply inc_upper.mpr
  intro h
  rw[inc_cupP, inc_cupP]
  simp
@[simp] theorem comp_cup_distr_l {f:c.rel X Y} {g g':c.rel Y Z} :
  f ∘ (g ⊔ g') = (f ∘ g) ⊔ (f ∘ g') := by
  apply inc_upper.mpr
  intro h
  apply Iff.intro
  · intro H
    apply c.inc_cup.mpr
    constructor
    all_goals
      apply inc_trans _ H
      apply comp_inc_compat_ab_ab'
      simp
  · intro H
    rw [← inv_invol f, ← inc_residual]
    apply inc_cup.mpr
    constructor
    all_goals
      rw[inc_residual]
      apply inc_trans _ H
      simp
@[simp] theorem comp_cup_distr_r {f f':c.rel X Y} {g:c.rel Y Z} :
  (f ⊔ f') ∘ g = (f ∘ g) ⊔ (f' ∘ g) := by
  rw[← inv_invol f, ← inv_invol f', ← inv_invol g, ← inv_cup_distr, ← comp_inv, comp_cup_distr_l]
  simp
theorem comp_capP_distr {f:c.rel X Y}{g:c.rel Z W} {P : c.rel A B → Prop} {α : c.rel A B → c.rel Y Z} :
  (f ∘ capP P α) ∘ g ⊑ capP P (fun x => (f ∘ (α x)) ∘ g) := by
  rw[inc_capP]
  intro h H
  apply comp_inc_compat_ab_a'b
  apply comp_inc_compat_ab_ab'
  apply capP_inc H
theorem comp_capP_distr_l {f:c.rel X Y} {P : c.rel A B → Prop} {α : c.rel A B → c.rel Y Z} :
  f ∘ capP P α ⊑ capP P (fun x => f ∘ (α x)) := by
  have H := @comp_capP_distr _ _ _ _ _ _ _ f (idr Z) P α
  simp at H
  assumption
theorem comp_capP_distr_r {g:c.rel Y Z} {P : c.rel A B → Prop} {α : c.rel A B → c.rel X Y} :
  capP P α ∘ g ⊑ capP P (fun x => (α x) ∘ g) := by
  have H := @comp_capP_distr _ _ _ _ _ _ _ (idr X) g P α
  simp at H
  assumption
@[simp] theorem comp_cap_distr {f:c.rel X Y} {g g':c.rel Y Z}{h:c.rel Z W} :
  (f ∘ (g ⊓ g')) ∘ h ⊑ ((f ∘ g) ∘ h) ⊓ (f ∘ g') ∘ h := by
  apply inc_cap.mpr
  constructor
  all_goals
    rw[← comp_assoc, ← comp_assoc]
    apply comp_inc_compat_ab_ab'
    apply comp_inc_compat_ab_a'b
    simp
@[simp] theorem comp_cap_distr_l {f:c.rel X Y} {g g':c.rel Y Z} :
  f ∘ (g ⊓ g') ⊑ (f ∘ g) ⊓ (f ∘ g') := by
  have H := @comp_cap_distr _ _ _ _ _ f g g' (idr Z)
  simp_all
@[simp] theorem comp_cap_distr_r {f f':c.rel X Y} {g:c.rel Y Z} :
  (f ⊓ f') ∘ g ⊑ (f ∘ g) ⊓ (f' ∘ g) := by
  have H := @comp_cap_distr _ _ _ _ _ (idr X) f f' g
  simp_all
@[simp] theorem comp_empty_r (f:c.rel X Y) : f ∘ φ Y Z = φ X Z := by
  apply inc_antisym
  · rw[← inv_invol f, ← inc_residual]
    simp
  · simp
@[simp] theorem comp_empty_l (f:c.rel Y Z) : φ X Y ∘ f = φ X Z := by
  rw[← inv_invol']
  simp
theorem comp_either_empty {f:c.rel X Y}{g:c.rel Y Z} :
  f = φ X Y ∨ g = φ Y Z → f ∘ g = φ X Z := by
  intro H
  cases H
  case inl H' =>
    rw[H']
    simp
  case inr H' =>
    rw[H']
    simp
theorem comp_neither_empty {f:c.rel X Y}{g:c.rel Y Z} :
  f ∘ g ≠ φ X Z → f ≠ φ X Y ∧ g ≠ φ Y Z := by
  intro H
  constructor
  all_goals
  · intro H'
    rw[H'] at H
    simp at H

end relational_properties

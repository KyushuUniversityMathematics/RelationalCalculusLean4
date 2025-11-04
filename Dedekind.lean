import Dedekind_Axioms

variable [c : Dedekind]

section Axioms
@[simp] theorem comp_id_l (f:c.rel X Y) : (idr X) ∘ f = f := c.comp_id_l f
@[simp] theorem comp_id_r (f:c.rel X Y) : f ∘ (idr Y) = f := c.comp_id_r f
@[simp] theorem comp_assoc {W:c.ob} (f : c.rel W X) (g : c.rel X Y) (h : c.rel Y Z) :
  f ∘ (g ∘ h) = (f ∘ g) ∘ h := by rw[← c.comp_assoc f g h]
theorem acomp_r {x : c.rel X Y}{y : c.rel Y Z}{z : c.rel X Z} :
  x ∘ y = z → ∀ w:c.rel Z W, x ∘ (y ∘ w) = z ∘ w := by
  intro H w
  rw[comp_assoc, H]
theorem acomp_l {x : c.rel X Y}{y : c.rel Y Z}{z : c.rel X Z} :
  x ∘ y = z → ∀ w:c.rel W X, (w ∘ x) ∘ y = w ∘ z := by
  intro H w
  rw[← comp_assoc, H]
theorem acomp_lr {x : c.rel X Y}{y : c.rel Y Z}{z : c.rel X Z} :
  x ∘ y = z → ∀ w:c.rel W X, ∀ v:c.rel Z U, (w ∘ x) ∘ (y ∘ v) = (w ∘ z) ∘ v := by
  intro H w v
  rw[comp_assoc, acomp_l H w]

@[simp] theorem inc_refl (f : c.rel X Y) : f ⊑ f := c.inc_refl f
theorem inc_trans {f g h : c.rel X Y} : f ⊑ g → g ⊑ h → f ⊑ h := @c.inc_trans X Y f g h
theorem inc_antisym {f g : c.rel X Y}: f ⊑ g → g ⊑ f → f = g := @c.inc_antisym X Y f g
theorem inc_antisym' {f g : c.rel X Y} : f ⊑ g ∧ g ⊑ f ↔ f = g := by
  apply Iff.intro
  · intro H
    apply inc_antisym H.left H.right
  · intro H
    rw[H]
    simp
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
  apply Iff.intro
  · intro H
    rw[←inv_invol f, ←inv_invol g]
    exact c.inc_inv H
  · exact c.inc_inv
@[simp] theorem dedekind : f ∘ g ⊓ h ⊑ (f ⊓ h ∘ g#) ∘ (g ⊓ f# ∘ h) := c.dedekind
theorem inc_residual {f : c.rel X Y}{g : c.rel Y Z}{h : c.rel X Z} : h ⊑ f ▹ g ↔ f# ∘ h ⊑ g := @c.inc_redidual X Y Z f g h
end Axioms
section basic_lemmas
@[simp] theorem cap_l (f g : c.rel X Y) : f ⊓ g ⊑ f :=
  (c.inc_cap.mp (c.inc_refl (f ⊓ g))).left
@[simp] theorem cap_r (f g : c.rel X Y) : f ⊓ g ⊑ g :=
  (c.inc_cap.mp (c.inc_refl (f ⊓ g))).right
@[simp] theorem cup_l (f g : c.rel X Y) : f ⊑ f ⊔ g :=
  (c.inc_cup.mp (c.inc_refl (f ⊔ g))).left
@[simp] theorem cup_r (f g : c.rel X Y) : g ⊑ f ⊔ g :=
  (c.inc_cup.mp (c.inc_refl (f ⊔ g))).right
theorem inc_def1l : f = f ⊓ g ↔ f ⊑ g := by
  apply Iff.intro
  · intro H
    rw[H]
    simp
  · intro H
    apply c.inc_antisym
    · exact c.inc_cap.mpr ⟨c.inc_refl f, H⟩
    · simp
theorem inc_def1r : g = f ⊓ g ↔ g ⊑ f := by
  apply Iff.intro
  · intro H
    rw[H]
    simp
  · intro H
    apply c.inc_antisym
    · exact c.inc_cap.mpr ⟨H, c.inc_refl g⟩
    · simp
theorem inc_def2l : f = f ⊔ g ↔ g ⊑ f := by
  apply Iff.intro
  · intro H
    rw[H]
    simp
  · intro H
    apply c.inc_antisym
    · simp
    · apply c.inc_cup.mpr
      exact ⟨c.inc_refl f, H⟩
theorem inc_def2r : g = f ⊔ g ↔ f ⊑ g := by
  apply Iff.intro
  · intro H
    rw[H]
    simp
  · intro H
    apply c.inc_antisym
    · simp
    · apply c.inc_cup.mpr
      exact ⟨H, c.inc_refl g⟩
@[simp] theorem cap_assoc : f ⊓ (g ⊓ h) = f ⊓ g ⊓ h := by
  apply c.inc_antisym
  · apply c.inc_cap.mpr
    constructor
    · apply c.inc_cap.mpr
      constructor
      · simp
      · apply c.inc_trans
        apply cap_r
        apply cap_l
    · apply c.inc_trans
      apply cap_r
      apply cap_r
  · apply c.inc_cap.mpr
    constructor
    · apply c.inc_trans
      apply cap_l
      apply cap_l
    · apply c.inc_cap.mpr
      constructor
      · apply c.inc_trans
        apply cap_l
        apply cap_r
      · simp
@[simp] theorem cup_assoc : f ⊔ (g ⊔ h) = f ⊔ g ⊔ h := by
  apply c.inc_antisym
  · apply c.inc_cup.mpr
    constructor
    · exact c.inc_trans (cup_l f g) (cup_l (f ⊔ g) h)
    · apply c.inc_cup.mpr
      constructor
      · exact c.inc_trans (cup_r f g) (cup_l (f ⊔ g) h)
      · exact cup_r (f ⊔ g) h
  · apply c.inc_cup.mpr
    constructor
    · apply c.inc_cup.mpr
      constructor
      · apply cup_l
      · exact c.inc_trans (cup_l g h) (cup_r f (g ⊔ h))
    · exact c.inc_trans (cup_r g h) (cup_r f (g ⊔ h))
theorem cap_comm (f g:c.rel X Y): f ⊓ g = g ⊓ f := by
  apply c.inc_antisym
  · apply c.inc_cap.mpr
    constructor
    · exact cap_r f g
    · exact cap_l f g
  · apply c.inc_cap.mpr
    constructor
    · exact cap_r g f
    · exact cap_l g f
theorem cup_comm (f g:c.rel X Y): f ⊔ g = g ⊔ f := by
  apply c.inc_antisym
  · exact c.inc_cup.mpr ⟨cup_r g f, cup_l g f⟩
  · exact c.inc_cup.mpr ⟨cup_r f g, cup_l f g⟩
@[simp] theorem cup_cap_abs (f g:c.rel X Y): f ⊔ (f ⊓ g) = f := by
  apply c.inc_antisym
  · apply c.inc_cup.mpr
    simp
  · simp
@[simp] theorem cap_cup_abs (f g:c.rel X Y): f ⊓ (f ⊔ g) = f := by
  apply c.inc_antisym
  · simp
  · apply c.inc_cap.mpr
    simp
@[simp] theorem cap_idem (f:c.rel X Y): f ⊓ f = f := by
  apply c.inc_antisym
  · simp
  · apply c.inc_cap.mpr
    simp
@[simp] theorem cup_idem (f:c.rel X Y): f ⊔ f = f := by
  apply c.inc_antisym
  · apply c.inc_cup.mpr
    simp
  · simp
theorem cap_inc_compat (f f' g g':c.rel X Y) :
  f ⊑ f' → g ⊑ g' → f ⊓ g ⊑ f' ⊓ g' := by
  intro H H'
  apply c.inc_cap.mpr
  constructor
  · apply c.inc_trans
    apply cap_l
    apply H
  · apply c.inc_trans
    apply cap_r
    apply H'
theorem cap_inc_compat_l (f g g':c.rel X Y) :
  g ⊑ g' → f ⊓ g ⊑ f ⊓ g' := by
  intro H
  apply cap_inc_compat
  simp
  apply H
theorem cap_inc_compat_r (f f' g:c.rel X Y) :
  f ⊑ f' → f ⊓ g ⊑ f' ⊓ g := by
  intro H
  apply cap_inc_compat
  apply H
  simp
theorem cup_inc_compat (f f' g g':c.rel X Y) :
  f ⊑ f' → g ⊑ g' → f ⊔ g ⊑ f' ⊔ g' := by
  intro H H'
  apply c.inc_cup.mpr
  constructor
  · apply c.inc_trans
    apply H
    apply cup_l
  · apply c.inc_trans
    apply H'
    apply cup_r
theorem cup_inc_compat_l (f g g':c.rel X Y) :
  g ⊑ g' → f ⊔ g ⊑ f ⊔ g' := by
  intro H
  apply cup_inc_compat
  apply c.inc_refl
  apply H
theorem cup_inc_compat_r {f f' g:c.rel X Y} :
  f ⊑ f' → f ⊔ g ⊑ f' ⊔ g := by
  intro H
  apply cup_inc_compat
  apply H
  apply c.inc_refl
@[simp] theorem cap_empty (f:c.rel X Y) : f ⊓ φ X Y = φ X Y := by
  apply c.inc_antisym
  all_goals simp
@[simp] theorem empty_cap (f:c.rel X Y) : φ X Y ⊓ f = φ X Y := by
  rw[cap_comm]
  simp
@[simp] theorem cup_empty (f:c.rel X Y) : f ⊔ φ X Y = f := by
  apply c.inc_antisym
  · apply c.inc_cup.mpr
    all_goals simp
  · simp
@[simp] theorem empty_cup (f:c.rel X Y) : φ X Y ⊔ f = f := by
  rw[cup_comm]
  simp
@[simp] theorem cap_universal (f:c.rel X Y) : f ⊓ Δ X Y = f := by
  apply c.inc_antisym
  · simp
  · apply c.inc_cap.mpr
    all_goals simp
@[simp] theorem universal_cap (f:c.rel X Y) : Δ X Y ⊓ f = f := by
  rw[cap_comm]
  simp
@[simp] theorem cup_universal (f:c.rel X Y) : f ⊔ Δ X Y = Δ X Y := by
  apply c.inc_antisym
  all_goals simp
@[simp] theorem universal_cup (f:c.rel X Y) : Δ X Y ⊔ f = Δ X Y := by
  rw[cup_comm]
  simp
theorem inc_lower {f g:c.rel X Y} :
  f = g ↔ (∀ h, h ⊑ f ↔ h ⊑ g) := by
  apply Iff.intro
  · intro H h
    rw[H]
  · intro H
    apply c.inc_antisym
    · apply (H f).mp
      simp
    · apply (H g).mpr
      simp
theorem inc_upper {f g:c.rel X Y} :
  f = g ↔ (∀ h, f ⊑ h ↔ g ⊑ h) := by
  apply Iff.intro
  · intro H h
    rw[H]
  · intro H
    apply c.inc_antisym
    · apply (H g).mpr
      apply c.inc_refl
    · apply (H f).mp
      apply c.inc_refl
theorem cap_cup_distr_l (f g h:c.rel X Y) :
  f ⊓ (g ⊔ h) = (f ⊓ g) ⊔ (f ⊓ h) := by
  apply inc_upper.mpr
  intro a
  apply Iff.intro
  · intro H
    rw[cap_comm , cap_comm f h, c.inc_cup, ← c.inc_rpc, ← c.inc_rpc, ← c.inc_cup, c.inc_rpc, cap_comm]
    apply H
  · intro H
    rw[cap_comm , cap_comm f h, c.inc_cup, ← c.inc_rpc, ← c.inc_rpc, ← c.inc_cup, c.inc_rpc, cap_comm] at H
    apply H
theorem cap_cup_distr_r (f g h:c.rel X Y) :
  (f ⊔ g) ⊓ h = (f ⊓ h) ⊔ (g ⊓ h) := by
  repeat rw[cap_comm _ h]
  apply cap_cup_distr_l
theorem cup_cap_distr_l (f g h:c.rel X Y) :
  f ⊔ (g ⊓ h) = (f ⊔ g) ⊓ (f ⊔ h) := by
  rw[cap_cup_distr_l]
  conv  => rhs;rw[cap_comm, cap_cup_abs]
  rw[cap_cup_distr_r, cup_assoc, cup_cap_abs]
theorem cup_cap_distr_r (f g h:c.rel X Y) :
  (f ⊓ g) ⊔ h = (f ⊔ h) ⊓ (g ⊔ h) := by
  repeat rw[cup_comm _ h]
  apply cup_cap_distr_l
theorem cap_cup_unique (f g h:c.rel X Y) :
  f ⊓ g = f ⊓ h → f ⊔ g = f ⊔ h → g = h := by
  intro H1 H2
  rw[← cup_cap_abs g f, cap_comm, H1, cup_cap_distr_l, cup_comm, H2, cup_comm, cup_comm g h, ← cup_cap_distr_l, H1, cap_comm, cup_cap_abs]

def is_atomic (f:c.rel X Y) : Prop :=
  f ≠ φ X Y ∧ ∀ g:c.rel X Y, g ⊑ f → g = f ∨ g = φ X Y
theorem atomic_empty {f g:c.rel X Y} : is_atomic f →
  g ⊑ f → g ≠ f → g = φ X Y := by
  rw[is_atomic]
  rintro ⟨Hf, Hf0⟩ H Hg
  have Hf' := Hf0 g H
  cases Hf'
  · contradiction
  · assumption
theorem atomic_eq {f g:c.rel X Y} : is_atomic f →
  g ⊑ f → g ≠ φ X Y → g = f := by
  rw[is_atomic]
  rintro ⟨Hf, Hf0⟩ H Hg
  have Hf' := Hf0 g H
  cases Hf'
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
      apply Hf.left
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
  apply inc_antisym
  · simp
  · apply inc_rpc.mpr
    simp
theorem rpc_r : f ⇒ g ⊓ g = g := by
  apply inc_antisym
  · simp
  · conv => lhs; rw[← cap_idem g]
    apply cap_inc_compat_r
    apply inc_rpc.mpr
    simp
theorem inc_def3 : f ⇒ g = Δ _ _ ↔ f ⊑ g := by
  rw[← inc_antisym', inc_rpc, universal_cap]
  simp
theorem rpc_l : f ⊓ (f ⇒ g) = f ⊓ g := by
  apply inc_lower.mpr
  intro h
  rw[inc_cap, inc_rpc, inc_cap]
  apply Iff.intro
  · rintro ⟨H1, H2⟩
    rw[← inc_def1l.mpr H1] at H2
    exact ⟨H1, H2⟩
  · rintro ⟨H1, H2⟩
    rw[← inc_def1l.mpr H1]
    exact ⟨H1, H2⟩
theorem rpc_inc_compat : f' ⊑ f → g ⊑ g' → f ⇒ g ⊑ f' ⇒ g' := by
  intro H H'
  apply inc_rpc.mpr
  apply inc_trans
  · apply cap_inc_compat_l
    apply H
  · rw[cap_comm, rpc_l]
    apply inc_trans _ H'
    simp
theorem rpc_inc_compat_l : f' ⊑ f → f ⇒ g ⊑ f' ⇒ g := by
  intro H
  apply rpc_inc_compat
  · assumption
  · simp
theorem rpc_inc_compat_r : g ⊑ g' → f ⇒ g ⊑ f ⇒ g' := by
  intro H
  apply rpc_inc_compat
  · simp
  · assumption
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
        rw[← inc_antisym', cap_comm, ← inc_rpc] at H1
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
  · rw[← inc_antisym', complement, inc_rpc, universal_cap]
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
theorem de_morgan1 (f g:c.rel X Y) : (f ⊔ g)⁻ = f⁻ ⊓ g⁻ := by
  apply inc_lower.mpr
  intro h
  rw[complement, inc_rpc, inc_cap, cap_cup_distr_l, complement, complement, inc_rpc, inc_rpc, inc_cup]

end basic_lemmas
section relational_properties
theorem rel_unique : φ X Y = Δ X Y → ∀ f g:c.rel X Y, f = g := by
  intro H f g
  apply c.inc_antisym
  all_goals(
    apply c.inc_trans
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
theorem cupP_False (P:c.rel X Y → Prop)(α : c.rel X Y → c.rel Z W) : (∀ f, P f = False) → cupP P α = φ Z W := by
  intro H
  apply c.inc_antisym
  · rw[inc_cupP]
    intro f H'
    rw[H f] at H'
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
theorem comp_inc_compat (f f':c.rel X Y) (g g':c.rel Y Z) :
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
    all_goals apply H
    · left; rfl
    · right; rfl
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
@[simp] theorem inv_universal : (Δ X Y)# = Δ Y X := by
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
theorem inv_diagonal {f:c.rel X X} : f ⊑ idr X → f# = f := by
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
theorem comp_diagonal {f:c.rel X X} : f ⊑ idr X → f∘f = f := by
  intro H
  have H0:= @dedekind c X X f X (idr X) (idr X)
  simp at H0
  rw[← inc_def1l.mpr H] at H0
  apply inc_antisym
  · conv=> rhs; rw[← comp_id_r f]
    apply comp_inc_compat_ab_ab' H
  · rw[← inc_inv, inv_id] at H
    rw[← inc_def1r.mpr H, inv_diagonal] at H0
    assumption
    rw[← inc_inv, inv_id]
    assumption
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
theorem comp_cupP_distr_l (f:c.rel X Y) (P : c.rel W A → Prop)(α : c.rel W A → c.rel Y Z) :
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
theorem comp_cupP_distr_r (P : c.rel X Y → Prop)(α : c.rel X Y → c.rel Z W) (g:c.rel W A) :
  (cupP P α) ∘ g = cupP P (fun x => (α x) ∘ g) := by
  rw[← inv_invol (_∘ g), ← inv_move, comp_inv, inv_cupP_distr, inv_cupP_distr, comp_cupP_distr_l]
  apply inc_upper.mpr
  intro h
  rw[inc_cupP, inc_cupP]
  simp
@[simp] theorem comp_cup_distr_l (f:c.rel X Y) (g g':c.rel Y Z) :
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
@[simp] theorem comp_cup_distr_r (f f':c.rel X Y) (g:c.rel Y Z) :
  (f ⊔ f') ∘ g = (f ∘ g) ⊔ (f' ∘ g) := by
  rw[← inv_invol f, ← inv_invol f', ← inv_invol g, ← inv_cup_distr, ← comp_inv, comp_cup_distr_l]
  simp
theorem comp_capP_distr (f:c.rel X Y)(g:c.rel Z W) (P : c.rel A B → Prop)(α : c.rel A B → c.rel Y Z) :
  (f ∘ capP P α) ∘ g ⊑ capP P (fun x => (f ∘ (α x)) ∘ g) := by
  rw[inc_capP]
  intro h H
  apply comp_inc_compat_ab_a'b
  apply comp_inc_compat_ab_ab'
  apply capP_inc H
theorem comp_capP_distr_l (f:c.rel X Y) (P : c.rel A B → Prop)(α : c.rel A B → c.rel Y Z) :
  f ∘ capP P α ⊑ capP P (fun x => f ∘ (α x)) := by
  have H := comp_capP_distr f (idr Z) P α
  simp at H
  assumption
theorem comp_capP_distr_r (g:c.rel Y Z) (P : c.rel A B → Prop)(α : c.rel A B → c.rel X Y) :
  capP P α ∘ g ⊑ capP P (fun x => (α x) ∘ g) := by
  have H := comp_capP_distr (idr X) g P α
  simp at H
  assumption
@[simp] theorem comp_cap_distr (f:c.rel X Y) (g g':c.rel Y Z)(h:c.rel Z W) :
  (f ∘ (g ⊓ g')) ∘ h ⊑ ((f ∘ g) ∘ h) ⊓ (f ∘ g') ∘ h := by
  apply inc_cap.mpr
  constructor
  all_goals
    rw[← comp_assoc, ← comp_assoc]
    apply comp_inc_compat_ab_ab'
    apply comp_inc_compat_ab_a'b
    simp
@[simp] theorem comp_cap_distr_l (f:c.rel X Y) (g g':c.rel Y Z) :
  f ∘ (g ⊓ g') ⊑ (f ∘ g) ⊓ (f ∘ g') := by
  have H := comp_cap_distr f g g' (idr Z)
  simp at H
  assumption
@[simp] theorem comp_cap_distr_r (f f':c.rel X Y) (g:c.rel Y Z) :
  (f ⊓ f') ∘ g ⊑ (f ∘ g) ⊓ (f' ∘ g) := by
  have H := comp_cap_distr (idr X) f f' g
  simp at H
  assumption
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

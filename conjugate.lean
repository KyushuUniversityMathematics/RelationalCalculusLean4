import Function

variable [c : Dedekind]
def conjugate  (P:c.rel X Y → Prop)(Q:c.rel X' Y' → Prop)(α:c.rel X Y→c.rel X' Y')(β:c.rel X' Y'→c.rel X Y) :=
  (∀ f:c.rel X Y, P f → Q (α f)∧ β (α f) = f)∧
  (∀ g:c.rel X' Y', Q g → P (β g)∧ α (β g) = g)

def conjugate_True{X Y X' Y':c.ob} := conjugate (fun _:c.rel X Y => True) (fun _:c.rel X' Y' => True)

theorem inv_conjugate : conjugate_True (@inverse _ X Y) (@inverse _ Y X) := by
  rw[conjugate_True, conjugate]
  constructor
  all_goals
  · intro f _
    simp
theorem injection_conjugate {j:c.rel Z Y}: is_injective j → conjugate (fun f:c.rel X Y => is_function f ∧ f# ∘ f ⊑ j# ∘ j) (fun g:c.rel X Z => is_function g) (fun f:c.rel X Y => f ∘ j#) (fun g:c.rel X Z => g ∘ j) := by
  intro ⟨H, H0⟩
  constructor
  · intro f ⟨⟨H1, H2⟩, H3⟩
    constructor
    · simp
      constructor
      · rw[← comp_id_r (idr _)]
        apply inc_trans (comp_inc_compat H1 H1)
        rw[comp_assoc]
        apply comp_inc_compat_ab_a'b
        rw[← comp_assoc, ← comp_assoc]
        apply comp_inc_compat_ab_ab' H3
      · rw[← comp_id_r (idr _), ← H, comp_assoc]
        apply comp_inc_compat_ab_a'b
        rw[← comp_assoc, ← comp_assoc]
        apply comp_inc_compat_ab_ab' H3
    · simp
      apply inc_antisym
      · rw[← comp_assoc]
        apply comp_inc_compat_ab_a H0
      · rw[← comp_assoc]
        apply inc_trans _ (comp_inc_compat_ab_ab' H3)
        rw[comp_assoc]
        apply comp_inc_compat_b_ab H1
  · intro g ⟨H1, H2⟩
    constructor
    · simp
      constructor
      · rw[acomp_l H]
        simp
        apply And.intro H1
        apply inc_trans _ H0
        apply comp_inc_compat_ab_a'b
        rw[← comp_assoc]
        apply comp_inc_compat_ab_a H2
      · apply comp_inc_compat_ab_a'b
        rw[← comp_assoc]
        apply comp_inc_compat_ab_a H2
    · simp
      rw[acomp_l H]
      simp

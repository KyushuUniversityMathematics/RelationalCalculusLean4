import Dedekind
import Init.Classical

class Dedekind_unit extends Dedekind where
  unit : ∃ X : ob, φ X X ≠ idr X ∧ idr X = Δ X X ∧ (∀ Y : ob, Δ Y X ∘ Δ X Y = Δ Y Y)
noncomputable def I [c : Dedekind_unit]:= Classical.choose c.unit


section dedekind_unit
variable [c : Dedekind_unit]

theorem unit_empty_not_id : φ I I ≠ idr I :=
  (Classical.choose_spec c.unit).left
theorem unit_id_universal : idr I = Δ I I :=
  (Classical.choose_spec c.unit).right.left
theorem comp_unit_universal (Y : c.ob) : Δ Y I ∘ Δ I Y = Δ Y Y :=
  (Classical.choose_spec c.unit).right.right Y

-- theorem tarski1 {f: c.rel X Y}: f ≠ φ X Y → (Δ I X ∘ f) ∘ Δ Y I = idr I := by
--   intro H

theorem tarski2 (X Y : c.ob) : Δ X I ∘ Δ I Y = Δ X Y := by
  apply inc_antisym
  · simp
  · apply inc_trans
    · apply comp_inc_compat_b_ab
      apply inc_universal
    · rw[← comp_unit_universal X, ← comp_assoc]
      apply comp_inc_compat_ab_ab'
      simp

end dedekind_unit

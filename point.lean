import Function

class Dedekind_Unit extends Dedekind where
  I : ob
  unit_empty_not_id : φ I I ≠ idr I
  unit_id_universal : idr I = Δ I I
  comp_unit_universal : Δ X I ∘ Δ I X = Δ X X

section dedekind_unit
variable [c : Dedekind_Unit]

def I : c.ob := c.I
theorem unit_empty_not_id : φ I I ≠ idr I := c.unit_empty_not_id
@[simp] theorem unit_id_universal : Δ I I = idr I := c.unit_id_universal.symm
theorem comp_unit_universal (X : c.ob) : Δ X I ∘ Δ I X = Δ X X :=
  c.comp_unit_universal

@[simp] theorem unit_inc_id : α ⊑ idr I := by
  rw[← unit_id_universal]
  apply inc_universal
@[simp] theorem unit_cap_id : α ⊓ idr I = α := by
  rw[← unit_id_universal, cap_universal]
@[simp] theorem unit_id_cap : idr I ⊓ α = α := by
  rw[← unit_id_universal, universal_cap]
@[simp] theorem unit_cup_id : α ⊔ idr I = idr I := by
  rw[← unit_id_universal, cup_universal]
@[simp] theorem unit_id_cup : idr I ⊔ α = idr I := by
  rw[← unit_id_universal, universal_cup]
@[simp] theorem unit_eq_id : f = idr I ↔ idr I ⊑ f := by
  rw[← unit_id_universal, eq_universal]
@[simp] theorem unit_id_eq : idr I = f ↔ idr I ⊑ f := by
  rw[← unit_id_universal, universal_eq]





theorem tarski2 (X Y : c.ob) : Δ X I ∘ Δ I Y = Δ X Y := by
  apply inc_antisym
  · simp
  · apply inc_trans
    · apply comp_inc_compat_b_ab
      apply inc_universal
    · rw[← comp_unit_universal X, ← comp_assoc]
      apply comp_inc_compat_ab_ab'
      simp
theorem tarski : is_total (Δ I Y) → Δ X Y ∘ Δ Y Z = Δ X Z := by
  simp
  intro H
  rw[← tarski2 X Z, ← comp_id_r (Δ _ _)]
  apply inc_trans (comp_inc_compat_ab_a'b (comp_inc_compat_ab_ab' H))
  simp
  rw[tarski2, ← comp_assoc, tarski2]
  simp

end dedekind_unit

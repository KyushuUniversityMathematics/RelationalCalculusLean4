import shroder
import function
open Classical

section bernstein_dedekind
variable [c : Dedekind]
def tau (α : c.rel X Y → c.rel X Y) := capP (fun f => α f ⊑ f) id
def monotonic (α: c.rel X Y → c.rel Z W) := ∀ f g, f ⊑ g → α f ⊑ α g
theorem tau1 (α:c.rel X Y → c.rel X Y) (θ:c.rel X Y) :
  α θ ⊑ θ → tau α ⊑ θ := by
  intro H
  rw[tau]
  apply capP_inc
  assumption
theorem tau2 (α:c.rel X Y → c.rel X Y) :
  monotonic α → α (tau α) ⊑ tau α := by
  rw[monotonic]
  intro H
  conv => rhs; rw[tau]
  rw[inc_capP]
  intro θ Hθ
  apply inc_trans _ Hθ
  apply H
  apply tau1
  assumption
theorem tau3 (α:c.rel X Y → c.rel X Y) :
  monotonic α → tau α ⊑ α (tau α) := by
  intro H
  apply tau1
  apply H
  apply tau2
  assumption
theorem tarski_fixpoint (α:c.rel X Y → c.rel X Y) :
  monotonic α → α (tau α) = tau α := by
  intro H
  apply inc_antisym
  · apply tau2
    assumption
  · apply tau3
    assumption
def complement'(f:c.rel X X) := f⁻ ⊓ idr X
postfix:120 " ᶜ " => complement'

theorem complement'_le_id {f:c.rel X X} : fᶜ ⊑ idr X := by
  simp[complement']
theorem comp_complement'_empty {f:c.rel X X} : f ⊑ idr X → f ∘ fᶜ = φ X X := by
  intro H
  apply inc_antisym
  · rw[← cap_empty (idr X), cap_comm, ← cap_complement_empty f, ← cap_assoc, ← complement']
    apply inc_cap.mpr
    constructor
    · apply comp_inc_compat_ab_a
      apply complement'_le_id
    · apply comp_inc_compat_ab_b
      assumption
  · simp
theorem comp_complement'_empty2 {f:c.rel X X} : f ⊑ idr X → fᶜ ∘ f = φ X X := by
  intro H
  apply inc_antisym _ (inc_empty _)
  rw[← cap_empty (idr X), cap_comm, ← cap_complement_empty f, ← cap_assoc, ← complement']
  apply inc_cap.mpr
  constructor
  · apply comp_inc_compat_ab_b
    apply complement'_le_id
  · apply comp_inc_compat_ab_a H
theorem complement'_de_morgan (f:c.rel X X) : (f ⊔ g)ᶜ = fᶜ ⊓ gᶜ := by
  rw[complement', de_morgan1, complement', complement']
  conv =>
    rhs
    rw[cap_assoc]
    lhs
    rw[← cap_assoc]
    rhs
    rw[cap_comm]
  repeat rw[← cap_assoc]
  simp
theorem complement'_empty : (φ X X)ᶜ = idr X := by
  rw[complement', complement_empty]
  simp
theorem complement'_id : (idr X)ᶜ = φ X X := by
  rw[complement', cap_comm, cap_complement_empty]
end bernstein_dedekind
variable [c : Shroder]
section Bernstein



theorem complement'_cup_id (f:c.rel X X) : f ⊑ idr X → f ⊔ fᶜ = idr X := by
  intro H
  rw[complement', cup_cap_distr_l, complement_classic]
  simp
  rw[← inc_def2r.mpr H]
theorem complement'_invol (f:c.rel X X) : f ⊑ idr X → fᶜᶜ = f := by
  intro H
  rw[complement', complement', de_morgan2, cap_cup_distr_r, complement_invol, cap_comm (_⁻), cap_complement_empty, cup_empty, ← inc_def1l.mpr H]
theorem complement'_inc (f:c.rel X X) : f ⊑ g → gᶜ ⊑ fᶜ := by
  intro H
  rw[complement', complement']
  apply cap_inc_compat_r
  · apply inc_complement H
theorem complement'_de_morgan2 (f:c.rel X X) : (f ⊓ g)ᶜ = fᶜ ⊔ gᶜ := by
  rw[complement', de_morgan2, complement', complement', ← cap_cup_distr_r]

theorem bernstein : (∃ f:c.rel X Y, is_injective f) → (∃ g : c.rel Y X, is_injective g) →
∃ (h:c.rel X Y), is_bijective h := by
  intro Hf Hg
  cases Hf with | intro f Hf
  cases Hg with | intro g Hg
  rw[is_injective] at Hf Hg
  let F := fun x => ((g# ∘ ((f# ∘ x) ∘ f)ᶜ) ∘ g)ᶜ
  let u := tau F
  have H : monotonic F := by
    rw[monotonic]
    intro θ θ' H
    apply complement'_inc
    apply comp_inc_compat_ab_a'b
    apply comp_inc_compat_ab_ab'
    apply complement'_inc
    apply comp_inc_compat_ab_a'b
    apply comp_inc_compat_ab_ab' H
  have H : F u = u := tarski_fixpoint F H
  let v := ((f# ∘ u) ∘ f)ᶜ

  exists ((u ∘ f) ∘ vᶜ ⊔ ((uᶜ ∘ g#) ∘ v))
  have Hu : u ⊑ idr X := by
    rw[← H]
    dsimp [F]
    apply complement'_le_id
  have Hv : v ⊑ idr Y := by
    apply complement'_le_id
  have Hv' : (f#∘u)∘f ⊑ idr Y := by
    apply inc_trans _ Hf.right
    apply comp_inc_compat_ab_a'b
    apply comp_inc_compat_ab_a Hu
  have Hv' : (f#∘u)∘f = vᶜ := by
    dsimp [v]
    rw[complement'_invol _ Hv']
  have Hu' : (g#∘v)∘g ⊑ idr X := by
    apply inc_trans _ Hg.right
    apply comp_inc_compat_ab_a'b
    apply comp_inc_compat_ab_a Hv
  have Hu' : (g#∘v)∘g = uᶜ := by
    dsimp [v]
    conv => rhs ; rw[← H]; dsimp [F]
    rw[complement'_invol _ Hu']

  rw[is_bijective]
  constructor
  · simp
    rw[inv_diagonal complement'_le_id, inv_diagonal Hu, inv_diagonal complement'_le_id, inv_diagonal complement'_le_id]
    rw[acomp_l (comp_diagonal complement'_le_id), acomp_l (comp_complement'_empty Hv), acomp_l (comp_complement'_empty2 Hv), acomp_l (comp_diagonal Hv)]
    simp
    rw[← Hv']
    simp
    rw[acomp_l (Hf.left), acomp_l (Hf.left)]
    simp
    rw[comp_diagonal Hu, comp_diagonal Hu]
    conv => lhs; rhs; lhs; rw[← comp_assoc, ← comp_assoc] ; rhs; rw[comp_assoc, Hu']
    rw[comp_diagonal complement'_le_id, comp_diagonal complement'_le_id, complement'_cup_id _ Hu]
  · simp
    rw[inv_diagonal complement'_le_id, inv_diagonal Hu, inv_diagonal complement'_le_id, inv_diagonal complement'_le_id]
    rw[acomp_l (comp_diagonal complement'_le_id), acomp_l (comp_complement'_empty2 Hu), acomp_l (comp_complement'_empty Hu), acomp_l (comp_diagonal Hu)]
    rw[← Hu']
    simp
    rw[acomp_l (Hg.left), acomp_l (Hg.left)]
    simp
    rw[comp_diagonal Hv, comp_diagonal Hv]
    conv => lhs; lhs; lhs; rw[← comp_assoc, ← comp_assoc] ; rhs; rw[comp_assoc, Hv']
    rw[comp_diagonal complement'_le_id, comp_diagonal complement'_le_id, cup_comm, complement'_cup_id _ Hv]
end Bernstein

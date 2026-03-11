import Cantor

namespace REL

def REL_PreCategory : PreCategory := by
  refine
    { ob := Type
      rel := fun X Y => X → Y → Prop
      id := fun X x y => x = y
      comp := fun α β x z => ∃ y, α x y ∧ β y z }

def REL_Category : Category :=
  { toPreCategory := REL_PreCategory
    comp_id_l := by
      intro X Y f
      funext x
      funext y
      apply propext
      constructor
      · intro h
        rcases h with ⟨t, ht, hty⟩
        exact ht ▸ hty
      · intro h
        exact ⟨x, rfl, h⟩
    comp_id_r := by
      intro X Y f
      funext x
      funext y
      apply propext
      constructor
      · intro h
        rcases h with ⟨t, hxt, hty⟩
        exact hty ▸ hxt
      · intro h
        exact ⟨y, h, rfl⟩
    comp_assoc := by
      intro W X Y Z f g h
      funext w
      funext z
      apply propext
      constructor
      · intro hwz
        rcases hwz with ⟨y, ⟨x, hwx, hxy⟩, hyz⟩
        exact ⟨x, hwx, ⟨y, hxy, hyz⟩⟩
      · intro hwz
        rcases hwz with ⟨x, hwx, ⟨y, hxy, hyz⟩⟩
        exact ⟨y, ⟨x, hwx, hxy⟩, hyz⟩ }

def REL_Dedekind_Notations : Dedekind_Notations :=
  { toCategory := REL_Category
    inverse := fun {X Y : Type} (R : X → Y → Prop) (y : Y) (x : X) => R x y
    residual := fun {X Y Z : Type} (R : X → Y → Prop) (S : Y → Z → Prop) (x : X) (z : Z) =>
      ∀ y, R x y → S y z
    empty := fun _ _ _ _ => False
    universal := fun _ _ _ _ => True
    inc := fun {X Y : Type} (R S : X → Y → Prop) => ∀ x y, R x y → S x y
    cup := fun {X Y : Type} (R S : X → Y → Prop) x y => R x y ∨ S x y
    cupP := fun {X Y Z W : Type} (P : (X → Y → Prop) → Prop) (f : (X → Y → Prop) → Z → W → Prop) z w =>
      ∃ α, P α ∧ f α z w
    cap := fun {X Y : Type} (R S : X → Y → Prop) x y => R x y ∧ S x y
    capP := fun {X Y Z W : Type} (P : (X → Y → Prop) → Prop) (f : (X → Y → Prop) → Z → W → Prop) z w =>
      ∀ α, P α → f α z w
    rpc := fun {X Y : Type} (R S : X → Y → Prop) x y => R x y → S x y }

def REL_Dedekind : Dedekind := by
  refine
    { toDedekind_Notations := REL_Dedekind_Notations
      notzero := ?_
      notzeroP := ?_
      inc_refl := ?_
      inc_trans := ?_
      inc_antisym := ?_
      inc_cap := ?_
      inc_capP := ?_
      inc_cup := ?_
      inc_cupP := ?_
      inc_empty := ?_
      inc_universal := ?_
      inc_rpc := ?_
      inv_invol := ?_
      comp_inv := ?_
      inc_inv := ?_
      dedekind := ?_
      inc_residual := ?_ }
  · exact Unit
  · intro H
    have h := congrFun (congrFun H Unit.unit) Unit.unit
    apply h.mpr
    rfl
  · intro X Y α
    intro x y h
    exact h
  · intro X Y f g h hfg hgh x y hxy
    exact hgh x y (hfg x y hxy)
  · intro X Y f g hfg hgf
    funext x
    funext y
    apply propext
    constructor
    · intro hxy
      exact hfg x y hxy
    · intro hxy
      exact hgf x y hxy
  · intro X Y f g h
    constructor
    · intro hfgcap
      constructor
      · intro x y hxy
        exact (hfgcap x y hxy).left
      · intro x y hxy
        exact (hfgcap x y hxy).right
    · intro hfg
      intro x y hxy
      exact ⟨hfg.left x y hxy, hfg.right x y hxy⟩
  · intro Z W X Y f P α
    constructor
    · intro hf g hg
      intro z w hzw
      exact (hf z w hzw) g hg
    · intro hf z w hzw g hg
      exact hf g hg z w hzw
  · intro X Y f g h
    constructor
    · intro hcup
      constructor
      · intro x y hxy
        exact hcup x y (Or.inl hxy)
      · intro x y hxy
        exact hcup x y (Or.inr hxy)
    · intro hfg x y hxy
      cases hxy with
      | inl hf => exact hfg.left x y hf
      | inr hg => exact hfg.right x y hg
  · intro Z W X Y f P β
    constructor
    · intro hcup g hg z w hβ
      exact hcup z w ⟨g, hg, hβ⟩
    · intro hcup z w hzw
      rcases hzw with ⟨g, hg, hβ⟩
      exact hcup g hg z w hβ
  · intro X Y f x y h
    exact False.elim h
  · intro X Y f x y h
    trivial
  · intro X Y f g h
    constructor
    · intro hinc x y hfg
      exact (hinc x y hfg.left) hfg.right
    · intro hinc x y hf
      intro hg
      exact hinc x y ⟨hf, hg⟩
  · intro X Y f
    funext y
    funext x
    rfl
  · intro X Y Z f g
    funext z
    funext x
    apply propext
    constructor
    · intro h
      rcases h with ⟨y, hxy, hyz⟩
      exact ⟨y, hyz, hxy⟩
    · intro h
      rcases h with ⟨y, hyz, hxy⟩
      exact ⟨y, hxy, hyz⟩
  · intro X Y f g hfg y x hyx
    exact hfg x y hyx
  · intro X Y Z f g h x z hxz
    rcases hxz.left with ⟨y, hxy, hyz⟩
    refine ⟨y, ?_, ?_⟩
    · refine ⟨hxy, ?_⟩
      exact ⟨z, hxz.right, hyz⟩
    · refine ⟨hyz, ?_⟩
      exact ⟨x, hxy, hxz.right⟩
  · intro X Y Z f g h
    constructor
    · intro hh y z hyz
      rcases hyz with ⟨x, hxy, hxz⟩
      exact hh x z hxz y hxy
    · intro hh x z hxz y hxy
      exact hh y z ⟨x, hxy, hxz⟩

def REL_Rationality : Dedekind_Rationality := by
  refine
    { toDedekind := REL_Dedekind
      rational_ob := ?_
      rational1 := ?_
      rational2 := ?_
      rational_cap_id := ?_
      rational_comp := ?_
      rational1_function := ?_
      rational2_function := ?_ }
  let _ : Dedekind := REL_Dedekind
  · intro X Y α
    exact {x : X × Y // α x.1 x.2}
  · intro X Y α
    exact fun z x => z.1.1 = x
  · intro X Y α
    exact fun z y => z.1.2 = y
  · intro X Y α
    funext z
    funext z'
    apply propext
    constructor
    · intro hz
      rcases hz with ⟨h1, h2⟩
      rcases h1 with ⟨x, hz1, hz2⟩
      rcases h2 with ⟨y, hy1, hy2⟩
      apply Subtype.ext
      exact Prod.ext (hz1.trans hz2.symm) (hy1.trans hy2.symm)
    · intro hzz
      cases hzz
      exact ⟨⟨z.1.1, rfl, rfl⟩, ⟨z.1.2, rfl, rfl⟩⟩
  · intro X Y α
    funext x
    funext y
    apply propext
    constructor
    · intro hxy
      rcases hxy with ⟨z, hx, hy⟩
      exact (hx.symm ▸ hy.symm ▸ z.2)
    · intro hxy
      exact ⟨⟨(x, y), hxy⟩, rfl, rfl⟩
  · intro X Y α
    constructor
    · intro z z' hzz
      cases hzz
      exact ⟨z.1.1, rfl, rfl⟩
    · intro x x' hxx'
      rcases hxx' with ⟨z, hz1, hz2⟩
      exact hz1.symm.trans hz2
  · intro X Y α
    constructor
    · intro z z' hzz
      cases hzz
      exact ⟨z.1.2, rfl, rfl⟩
    · intro y y' hyy'
      rcases hyy' with ⟨z, hz1, hz2⟩
      exact hz1.symm.trans hz2

def REL_Cantor : Cantor := by
  refine
    { toDedekind_Rationality := REL_Rationality
      pow := ?_
      ni := ?_
      power_axiom1 := ?_
      power_axiom2 := ?_ }
  let _ : Dedekind_Rationality := REL_Rationality
  · intro X
    exact X → Prop
  · intro X
    exact fun p x => p x
  · intro X p q hpq
    have hpq' : (∀ x, p x → q x) ∧ (∀ x, q x → p x) := by
      simpa [Dedekind_Notations.residual, inverse, cap, REL_Dedekind_Notations, REL_Category, REL_PreCategory] using hpq
    apply funext
    intro x
    apply propext
    constructor
    · intro hpx
      exact hpq'.left x hpx
    · intro hqx
      exact hpq'.right x hqx
  · intro X Z g z z' hzz
    cases hzz
    refine ⟨fun x => g z x, ?_, ?_⟩
    · intro x hgzx
      exact hgzx
    · intro x hp
      exact hp

def REL_Cantor_Choice : Cantor_Choice := by
  refine
    { toCantor := REL_Cantor
      choice := ?_ }
  let _ : Cantor := REL_Cantor
  intro X Y α H
  have hex : ∀ x : X, ∃ y : Y, α x y := by
    intro x
    have hxx : (α ∘ α # ) x x := H x x rfl
    rcases hxx with ⟨y, hxy, _⟩
    exact ⟨y, hxy⟩
  refine ⟨fun x y => (Classical.choose (hex x)) = y, ?_, ?_⟩
  · constructor
    · intro x x' hxx
      cases hxx
      refine ⟨Classical.choose (hex x), rfl, ?_⟩
      rfl
    · intro y y' hyy
      rcases hyy with ⟨x, hxy, hxy'⟩
      exact hxy.symm.trans hxy'
  · intro x y hxy
    have hx : α x (Classical.choose (hex x)) := Classical.choose_spec (hex x)
    exact hxy.symm ▸ hx

-- Explicit witness: no typeclass argument is required at use sites.
noncomputable def cantorConcrete : Cantor_Choice := REL_Cantor_Choice

theorem cantorConcrete_exists : ∃ c : Cantor_Choice, c = cantorConcrete := by
  exact ⟨cantorConcrete, rfl⟩
-- theorem PropRel (P:Prop): P ↔ fun (_ _ : Unit) => P

end REL
variable [c:Cantor_Choice]
omit c in theorem test {P Q:Prop} : ((P → Q) → P) → P := by
  rcases REL.cantorConcrete_exists with ⟨c0, hc0⟩
  letI : Cantor_Choice := c0
  subst hc0
  let α : (REL.cantorConcrete).rel I I := fun _ _ => P
  let β : (REL.cantorConcrete).rel I I := fun _ _ => Q
  have H : Δ I I ⊑ ((α ⇒ β) ⇒ α) ⇒ α := by
    intro a b
    simp [de_morgan1, de_morgan2]
    rw [cap_comm, cap_cup_abs]
    simp
  classical
  have hNonempty : Nonempty I := by
    by_cases hE : Nonempty I
    · exact hE
    · have hneq : φ I I ≠ idr I := unit_empty_not_id
      apply False.elim
      apply hneq
      funext x
      exfalso
      exact hE ⟨x⟩
  rcases hNonempty with ⟨x0⟩
  have hxy : (((α ⇒ β) ⇒ α) ⇒ α) x0 x0 := H x0 x0 (by trivial)
  change ((((α ⇒ β) ⇒ α) x0 x0) → α x0 x0) at hxy
  change (((α ⇒ β) x0 x0 → α x0 x0) → α x0 x0) at hxy
  change (((α x0 x0 → β x0 x0) → α x0 x0) → α x0 x0) at hxy
  simpa [α, β] using hxy

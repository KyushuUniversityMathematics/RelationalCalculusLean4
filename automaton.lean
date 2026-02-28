import Cantor
open Classical
variable [c : Cantor]

section definition

structure nfa(σ :Type)(Q : c.ob) where
  (τ : c.rel I Q)
  (δ : σ → c.rel Q Q)
  (β : c.rel Q I)

def δstar {σ :Type}{Q : c.ob}(M : nfa σ Q)(l:List σ) : c.rel Q Q :=
  match l with
  | [] => idr Q
  | a::l' => M.δ a ∘ δstar M l'
noncomputable def acceptRel {σ : Type} {Q : c.ob} (A : nfa σ Q) (l : List σ)
  : c.rel I I := (A.τ ∘ δstar A l) ∘ A.β

notation:90 A " ⟪" l "⟫" => acceptRel A l
def accept {σ :Type}{Q : c.ob}(A : nfa σ Q)(l:List σ) :=
  A ⟪ l ⟫ = idr I

theorem δstar_append {σ :Type}{Q : c.ob}(M : nfa σ Q)(l1 l2:List σ) :
  δstar M (l1 ++ l2) = δstar M l1 ∘ δstar M l2 := by
  induction l1 with
  | nil =>
    simp[δstar, comp_id_l]
  | cons a l1' ih =>
    simp[δstar, ih, comp_assoc]
end definition

section cup
noncomputable def cup_nfa {σ :Type}{Q Q' : c.ob}(M : nfa σ Q)(M' : nfa σ Q') : nfa σ (Q + Q') :=
  { τ := (M.τ# + M'.τ#)#,
    δ := fun a => (M.δ a ∘ in_l Q Q') + (M'.δ a ∘ in_r Q Q'),
    β := M.β + M'.β
  }
infixl:65 " + " => cup_nfa

theorem cup_nfaP (l : List σ){Q Q' : c.ob}(M : nfa σ Q)(M' : nfa σ Q') :
  (M + M') ⟪ l ⟫ = M ⟪ l ⟫ ⊔ M' ⟪ l ⟫ := by
  rw[acceptRel, acceptRel, acceptRel]
  have H : δstar (M + M') l = (in_l Q Q'# ∘ δstar M l) ∘ in_l Q Q' ⊔ (in_r Q Q'# ∘ δstar M' l) ∘ in_r Q Q' := by
    induction l with
    | nil =>
      simp[δstar]
    | cons a l' ih =>
      simp[δstar, ih]
      simp[cup_nfa, rel_sum]
  rw[H]
  simp[cup_nfa, rel_sum]
end cup

section cap
noncomputable def cap_nfa {σ :Type}{Q Q' : c.ob}(M : nfa σ Q)(M' : nfa σ Q') : nfa σ (Q × Q') :=
  {
    τ := M.τ × M'.τ,
    δ := fun a => (fst Q Q' ∘ M.δ a) × (snd Q Q' ∘ M'.δ a),
    β :=  (M.β# × M'.β#)#
  }
infixl:70 " × " => cap_nfa
theorem prod_inv {f:c.rel X X}{g:c.rel Y Y}:
((fst X Y ∘ f) × (snd X Y ∘ g)) = ((fst X Y ∘ f#) × (snd X Y ∘ g#))# := by
  simp[rel_prod, rel_prod]
theorem sharpness1 {f:c.rel X Y}{g:c.rel Y Y}:
  (fst X Y ∘ f × snd X Y ∘ g) ∘ (fst X Y ∘ f'# × snd X Y ∘ g'#)# = (fst X Y ∘ (f ∘ f') × snd X Y ∘ (g ∘ g')) := by
  simp[← sharpness]
  simp[rel_prod]
theorem cap_nfaP (l : List σ){Q Q' : c.ob}(M : nfa σ Q)(M' : nfa σ Q') :
  (M × M') ⟪ l ⟫ = M ⟪ l ⟫ ⊓ M' ⟪ l ⟫ := by
  rw[acceptRel, acceptRel, acceptRel]
  have H : δstar (M × M') l = (fst Q Q' ∘ δstar M l) × (snd Q Q' ∘ δstar M' l) := by
    induction l with
    | nil =>
      simp[δstar, rel_prod]
    | cons a l' ih =>
      simp[δstar, ih]
      simp[cap_nfa]
      conv => lhs; rhs; rw[prod_inv]
      rw[← sharpness]
      simp[rel_prod]
  rw[H]
  simp[cap_nfa]
  rw[prod_inv, ← sharpness]
  simp
  rw[← rel_prod, ← sharpness]
  simp

end cap

section inv
noncomputable def inv_nfa {σ :Type}{Q : c.ob}(M : nfa σ Q) : nfa σ Q :=
  {
    τ := M.β#,
    δ := fun a => M.δ a#,
    β := M.τ#
  }
postfix:75 " ᴿ " => inv_nfa
theorem inv_nfaP (l : List σ){Q : c.ob}(M : nfa σ Q) :
  (Mᴿ) ⟪ l ⟫ = (M ⟪ List.reverse l ⟫)# := by
  rw[acceptRel, acceptRel]
  have H : δstar (Mᴿ) l = (δstar M (List.reverse l))# := by
    induction l with
    | nil =>
      simp[δstar]
    | cons a l' ih =>
      simp[δstar, ih]
      simp[δstar_append, inv_nfa, δstar]
  rw[H]
  simp[inv_nfa]

end inv

section concat
noncomputable def concat_nfa {σ :Type}{Q Q' : c.ob}(M : nfa σ Q)(M' : nfa σ Q') : nfa σ (Q + Q') :=
  {
    τ := M.τ ∘ in_l Q Q',
    δ := fun a => (in_l Q Q'# ∘ M.δ a) ∘ in_l Q Q'
          ⊔ (((in_l Q Q'# ∘ M.β) ∘ M'.τ) ∘ M'.δ a) ∘ in_r Q Q'
          ⊔ (in_r Q Q'# ∘ M'.δ a) ∘ in_r Q Q',
    β := ((in_l Q Q'# ∘ M.β) ∘ M'.τ) ∘ M'.β ⊔ in_r Q Q'# ∘ M'.β
  }

infixl:60 " ~ " => concat_nfa


theorem concat_nfaP (l : List σ){Q Q' : c.ob}(M : nfa σ Q)(M' : nfa σ Q') :
  (M ~ M') ⟪ l ⟫ = cupP (fun x => ∃ u v, l = u ++ v ∧ x = (M ⟪ u ⟫) ∘ (M' ⟪ v ⟫)) id := by
  rw[acceptRel]
  have H : δstar (M ~ M') l = (in_l Q Q'# ∘ δstar M l) ∘ in_l Q Q'⊔
    (in_l Q Q'#∘ cupP (fun x => ∃ u v, l = u ++ v ∧ v ≠ [] ∧ x = ((δstar M u∘ M.β)∘ M'.τ) ∘ δstar M' v) id) ∘ in_r Q Q' ⊔
    ((in_r Q Q'# ∘ δstar M' l) ∘ in_r Q Q') := by
    induction l with
    | nil =>
      simp[δstar]
      rw[cup_comm, cup_assoc]
      conv => rhs; lhs; rw[cup_comm, inl_inr_cup_id]
      rw[inc_def2l, cupP_False]
      simp
      grind
    | cons a l' ih =>
      simp[δstar]
      rw[ih, concat_nfa]
      clear ih
      simp
      congr 1
      rw[← cup_assoc]
      congr
      apply inc_antisym
      · rw[inc_cup]
        constructor
        · comp_inc
          by_cases H: l' = []
          · rw[H, cupP_False]
            simp
            intro f H0
            rcases H0 with ⟨u, v, Huv, vnil, H⟩
            induction u with
            | nil =>
              grind
            | cons b u' ih =>
              grind
          · rw[comp_cupP_distr_l]
            rw[inc_cupP]
            intro f Hf
            simp
            rcases Hf with ⟨ u, v, Huv, hv, H ⟩
            rw[H]
            clear H f
            simp
            apply (@cupP_inc _ _ _ _ _ _ id)
            exists a::u, v
            simp[δstar]
            grind
        · comp_inc
          apply (@cupP_inc _ _ _ _ _ _ id)
          exists [], a::l'
          simp[δstar]
      · rw[← comp_cup_distr_r]
        comp_inc
        rw[← comp_assoc, ← comp_assoc, ← comp_assoc, ← comp_assoc]
        rw[← comp_cup_distr_l]
        comp_inc
        rw[inc_cupP]
        intro f Hf
        simp
        rcases Hf with ⟨ u, v, Huv, hv, H ⟩
        rw[H]
        clear H f
        cases u with
        | nil =>
          have Huv : v = a::l' := by grind
          myconv => rhs; apply cup_r
          simp[Huv, δstar]
        | cons b u' =>
          have Hb : b = a := by grind
          rw[Hb] at Huv ⊢
          clear Hb b
          myconv => rhs; apply cup_l
          simp[δstar]
          comp_inc
          apply (@cupP_inc _ _ _ _ _ _ id)
          exists u', v
          simp
          grind
  · rw[H]
    clear H
    simp[concat_nfa]
    apply inc_antisym
    · rw[inc_cup]
      constructor
      · apply (@cupP_inc _ _ _ _ _ _ id)
        exists l, []
        simp[acceptRel, δstar]
      · rw[comp_cupP_distr_l, comp_cupP_distr_r, inc_cupP]
        intro f ⟨u, v, Huv, H, H0⟩
        rw[H0]
        apply (@cupP_inc _ _ _ _ _ _ id)
        exists u, v
        simp_all[acceptRel]
    · rw[inc_cupP]
      intro f ⟨u, v, H, H0⟩
      by_cases H1:v = []
      · have H2 : l = u := by grind
        myconv => rhs; apply cup_l
        simp[H0, acceptRel, H2, H1, δstar]
      · myconv => rhs; apply cup_r
        simp[H0, acceptRel]
        comp_inc
        apply (@cupP_inc _ _ _ _ _ _ id)
        exists u, v
end concat

noncomputable def eps_nfa {σ : Type} : nfa σ I :=
  {
    τ := idr I,
    δ := fun _ => φ I I,
    β := idr I
  }

theorem eps_nfaP {σ : Type} (w : List σ) :
  eps_nfa ⟪ w ⟫ = if w = [] then idr I else φ I I := by
  rw[acceptRel]
  dsimp[eps_nfa]
  induction w with
  | nil =>
    simp[δstar]
  | cons a w' ih =>
    simp[δstar]


noncomputable def plus_nfa (M:nfa σ Q):nfa σ Q :=
  {
    τ := M.τ,
    δ := fun x=>M.δ x ⊔ (M.β ∘ M.τ) ∘ M.δ x,
    β := M.β
  }

noncomputable def plus_accept (M:nfa σ Q)(l:List (List σ)):=
match l with
  |[] => idr I
  |w::l' => M ⟪ w ⟫ ∘ plus_accept M l'

def flatten {σ :Type}(l:List (List σ)) : List σ :=
  match l with
  | [] => []
  | w::l' => w ++ flatten l'

theorem plus_nfaP (M:nfa σ Q):
  (plus_nfa M) ⟪ w ⟫ = cupP (fun x=> ∃ l, l ≠ [] ∧ w = flatten l ∧ x = plus_accept M l) id := by
  rw[acceptRel]
  have H : δstar (plus_nfa M) w ∘ M.β = cupP (fun x=>∃ u l,
    w = u ++ flatten l /\ x = (δstar M u ∘ M.β) ∘ plus_accept M l) id := by
    induction w with
    | nil =>
      simp[δstar]
      apply inc_antisym
      · apply (@cupP_inc _ _ _ _ _ _ id)
        exists [], []
        simp[flatten, plus_accept, δstar]
      · rw[inc_cupP]
        intro f ⟨u, l, ⟨Huv, Hnil⟩, Hf⟩
        simp[Hf, Huv, δstar]
        clear Hf f u Huv
        induction l with
        | nil =>
          simp[plus_accept]
        | cons v l' ih =>
          simp[plus_accept]
          dsimp[flatten] at Hnil
          by_cases H:v = []
          · simp[H] at Hnil
            simp[H, acceptRel, δstar]
            rapply ih Hnil
            conv => rhs; rw[← comp_id_r M.β, unit_id_universal]
            comp_inc
            simp
          · exfalso
            clear ih M Q
            induction v with
            | nil =>
              contradiction
            | cons b v' ihv =>
              contradiction
    | cons a w' ih =>
      simp[δstar]
      rw[← comp_assoc, ih]
      simp[plus_nfa]
      clear ih
      apply inc_antisym
      · rw[inc_cup]
        constructor
        · rw[comp_cupP_distr_l]
          rw[inc_cupP]
          intro f ⟨u, l, Hw', Hf⟩
          rw[Hf, Hw']
          clear Hf f Hw' w'
          simp
          apply (@cupP_inc _ _ _ _ _ _ id)
          exists a::u, l
        · rw[comp_cupP_distr_l]
          simp
          rw[inc_cupP]
          intro g ⟨u, l, Hw', Hf⟩
          rw[Hf, Hw']
          clear Hf g Hw' w'
          apply (@cupP_inc _ _ _ _ _ _ id)
          exists [], (a::u)::l
          simp[flatten, plus_accept, δstar, acceptRel]
      · rw[inc_cupP]
        intro f ⟨u, l, Hw', Hf⟩
        simp
        rw[Hf]
        clear Hf f
        induction l with
        | nil =>
          simp[flatten] at Hw'
          rw[← Hw']
          simp[δstar, plus_accept]
          myconv => rhs; apply cup_l
          comp_inc
          apply (@cupP_inc _ _ _ _ _ _ id)
          exists w', []
          simp[flatten, plus_accept]
        |cons h l ih =>
          induction h with
          | nil =>
            simp[flatten, plus_accept, acceptRel, δstar] at Hw' ⊢
            rapply ih Hw'
            clear ih Hw' w'
            conv => rhs;lhs;rhs; rw [← comp_id_r M.β]
            rw[unit_id_universal]
            comp_inc
            simp
          | cons x h ix =>
            clear ih ix
            simp[flatten] at Hw'
            induction u with
            | nil =>
              simp at Hw'
              rcases Hw' with ⟨H, Hw'⟩
              rw[← H]
              clear H
              simp[δstar, plus_accept, acceptRel]
              myconv=> rhs; apply cup_r
              comp_inc
              apply (@cupP_inc _ _ _ _ _ _ id)
              exists h, l
            | cons b u ih =>
              simp at Hw'
              rcases Hw' with ⟨H, Hw'⟩
              rw[← H]
              clear b H ih
              simp[δstar, plus_accept, acceptRel]
              myconv => rhs; apply cup_l
              comp_inc
              apply (@cupP_inc _ _ _ _ _ _ id)
              exists u, (x::h)::l
              simp_all[flatten, plus_accept, acceptRel, δstar]
  conv => lhs; rhs; simp[plus_nfa]
  rw[← comp_assoc, H]
  clear H
  simp[comp_cupP_distr_l, cupP_f_id]
  apply eq_cupP
  intro f
  constructor
  · intro ⟨ f', Hf, f'', Hf', β, Hf'', u, l, Hw, Hβ⟩
    simp at Hf Hf'
    rw[← Hf', ← Hf] at Hf''
    rw[Hf'', Hβ, Hw]
    clear Hf Hf' f' f'' Hf'' β Hβ Hw w
    simp
    exists u::l
    simp[flatten, plus_nfa, plus_accept, acceptRel]
  · intro ⟨ f', Hf', f'', Hf'', l, lnil, Hw, Hf⟩
    simp at Hf' Hf''
    rw[← Hf'', ← Hf'] at Hf
    rw[Hf, Hw]
    clear Hf' Hf'' f' f'' Hf Hw w
    simp
    induction l with
    | nil =>
      contradiction
    | cons w l' ih =>
      clear ih lnil
      simp[plus_accept, acceptRel, plus_nfa]
      exists (δstar M w ∘ M.β) ∘ plus_accept M l'
      constructor
      · simp
      · exists w, l'


noncomputable def star_nfa (M:nfa σ Q):nfa σ (I + Q) :=
  eps_nfa + (plus_nfa M)

theorem star_nfaP (M:nfa σ Q):
  (star_nfa M) ⟪ w ⟫ = cupP (fun x=> ∃ l, w = flatten l ∧ x = plus_accept M l) id := by
  rw[star_nfa, cup_nfaP, eps_nfaP, plus_nfaP]
  induction w with
  | nil =>
    simp[unit_id_universal]
    apply inc_antisym _ (inc_universal _)
    rw[← unit_id_universal]
    apply (@cupP_inc _ _ _ _ _ _ id)
    exists []
  | cons u w ih =>
    simp
    clear ih
    apply eq_cupP
    intro x
    constructor
    · grind
    · intro H
      rcases H with ⟨y, H, l, H0, H1⟩
      exists x
      simp
      exists l
      constructor
      · induction l with
        |nil =>
          contradiction
        |cons h l ih =>
          simp
      · grind

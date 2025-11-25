import cantor

variable [c : cantor]

section definition

structure nfa(σ :Type)(Q : c.ob) where
  (τ : c.rel I Q)
  (δ : σ → c.rel Q Q)
  (β : c.rel Q I)

def δstar {σ :Type}{Q : c.ob}(M : nfa σ Q)(l:List σ) : c.rel Q Q :=
  match l with
  | [] => idr Q
  | a::l' => M.δ a ∘ δstar M l'
noncomputable def acceptRel {σ : Type} {Q : c.ob} (A : nfa σ Q) (l : List σ) : c.rel I I :=
  (A.τ ∘ δstar A l) ∘ A.β

-- 任意：簡便な記法（不要なら削除）
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
  {
    τ := (M.τ# + M'.τ#)#,
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

noncomputable def concat_nfa {σ :Type}{Q Q' : c.ob}(M : nfa σ Q)(M' : nfa σ Q') : nfa σ (Q + Q') :=
  {
    τ := M.τ ∘ in_l Q Q',
    δ := fun a => in_l Q Q' ∘ M.δ a ⊔ (M.β ∘ M'.τ# ∘ M'.δ a),
    β := in_r Q Q'# ∘ M'.β
  }

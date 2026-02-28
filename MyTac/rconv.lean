import Lean
import Dedekind
import Lean.Elab.Tactic.Conv
open Lean Meta Elab Tactic Conv
open Lean.Elab.Tactic
open Lean.Meta
open Lean.Parser.Tactic.Conv
open Lean.Elab.Term

syntax (name := myconvSeq) "myconv" "=>" convSeq : tactic
syntax (name := convapply) "apply" term : conv

-- ナビ: lhs/rhs と、apply の仮定名（ユーザー名）
inductive Nav where
  | lhs : Nav
  | rhs : Nav
  | apply : Syntax → Nav
deriving Inhabited

abbrev NavSeq := List Nav

/-- conv 構文から lhs/rhs/apply H を抽出（DFS, partial） --/
private partial def makeNavSeq (root : Syntax) : NavSeq :=
  -- 直後以降で最初に現れる識別子（フォールバック用）
  let rec nextIdentName (xs : List Syntax) : Option Name :=
    match xs with
    | [] => none
    | Syntax.ident _ _ v _ :: _ => some v
    | Syntax.node _ _ args :: tl =>
        match nextIdentName args.toList with
        | some n => some n
        | none   => nextIdentName tl
    | _ :: tl => nextIdentName tl
  -- 本体 DFS
  let rec loop (pending : List Syntax) (acc : NavSeq) : NavSeq :=
    match pending with
    | [] => acc.reverse
    | t :: ts =>
      match t with
      -- apply 用の独自ノード: 第2引数は任意 term（Syntax）なのでそのまま記録
      | Syntax.node _ k args =>
        if k == `convapply then
          match args.toList with
          | _kw :: tArg :: _ => loop ts (Nav.apply tArg :: acc)
          | _ => loop ts acc
        else
          loop (args.toList ++ ts) acc
      -- キーワード（atom）
      | Syntax.atom _ a =>
        if a == "lhs" then
          loop ts (Nav.lhs :: acc)
        else if a == "rhs" then
          loop ts (Nav.rhs :: acc)
        else
          loop ts acc
      -- 識別子（ident）フォールバック: "apply H" を素朴に拾う
      | Syntax.ident _ _ v _ =>
        let s := v.toString
        if s == "apply" then
          match nextIdentName ts with
          | some h => loop ts (Nav.apply (mkIdent h).raw :: acc)
          | none   => loop ts acc
        else if s == "lhs" then
          loop ts (Nav.lhs :: acc)
        else if s == "rhs" then
          loop ts (Nav.rhs :: acc)
        else
          loop ts acc
      | _ =>
        loop ts acc
  loop [root] []



/-- 表示用: H も表示する --/
private def navToString : Nav → String
| .lhs => "lhs"
| .rhs => "rhs"
| .apply _ => "apply"

syntax (name := dumpNavSeq) "dumpNav" "=>" convSeq : tactic

/-- makeNavSeq の結果だけを Info に出すテスト用タクティック --/
@[tactic dumpNavSeq]
def evalDumpNavSeq : Tactic := fun stx => do
  match stx with
  | `(tactic| dumpNav => $seq) =>
      let ns := makeNavSeq seq
      let strs := ns.map navToString
      logInfo m!"[makeNavSeq] [{String.intercalate ", " strs}]"
  | _ => throwUnsupportedSyntax
-- -- テスト

/-- ns を先頭から走査し、最初の apply t の手前までの経路と t を返す --/
private def splitAtapply (ns : NavSeq) : Option (List Nav × Syntax) :=
  let rec go (accRev : List Nav) (xs : NavSeq) : Option (List Nav × Syntax) :=
    match xs with
    | [] => none
    | Nav.apply t :: _ => some (accRev.reverse, t)
    | Nav.lhs :: tl => go (Nav.lhs :: accRev) tl
    | Nav.rhs :: tl => go (Nav.rhs :: accRev) tl
  go [] ns

/-- 経路 steps と基底 term base から、対応する補題チェーン term を作る
    ルール: lhs → comp_inc_compat_ab_a'b, rhs → comp_inc_compat_ab_ab' --/
private def buildCompatTerm (steps : List Nav) (base : TSyntax `term) : TacticM (TSyntax `term) := do
  let mut t := base
  -- 下から積み上げるので逆順で包む
  for s in steps.reverse do
    match s with
    | Nav.lhs => t ← `(comp_inc_compat_ab_a'b $t)
    | Nav.rhs => t ← `(comp_inc_compat_ab_ab' $t)
    | _       => pure ()
  pure t

/-- makerwlemma: apply の引数を「term として」そのまま基底にして補題チェーンを構成 --/
private def makerwlemma (ns : NavSeq) : TacticM (TSyntax `term) := do
  match splitAtapply ns with
  | some (steps, tStx) =>
      -- tStx は `term` の Syntax。必要なら型検査だけ先に行う:
      -- try
      --   let _ ← Lean.Elab.Tactic.elabTerm tStx none
      -- catch _ =>
      --   throwError "[myconv] apply の引数が解決できません"
      let base : TSyntax `term := ⟨tStx⟩
      buildCompatTerm steps base
  | none =>
      throwError "[myconv] apply が見つかりません"

-- syntax (name := runRw) "runRw" "=>" convSeq : tactic

-- @[tactic runRw]
-- def evalRunRw : Tactic := fun stx => do
--   match stx with
--   | `(tactic| runRw => $seq) =>
--       withMainContext do
--         let ns := makeNavSeq seq
--         let t  ← makerwlemma ns
--         evalTactic (← `(tactic| apply $t))
--   | _ => throwUnsupportedSyntax

/-- Nav 列から convSeq を再構成（lhs/rhs のみを連結） --/
-- private def dropLastapply
--   (seq : TSyntax `Lean.Parser.Tactic.Conv.convSeq)
--   : TacticM (TSyntax `Lean.Parser.Tactic.Conv.convSeq) := do

--   match seq.raw with
--   | Syntax.node info kind args =>
--       -- convSeq か確認
--       logInfo m!"[dropLastapply] kind:{kind}"
--       if kind != `Lean.Parser.Tactic.Conv.convSeq then
--         return seq

--       let xs := args.toList
--       match xs with
--       | [] => logInfo m!"[dropLastapply] empty convSeq"
--       | a :: b => logInfo m!"[dropLastapply] first arg:{a}, second arg:{b}"

--       -- 末尾削除（List.dropLast を使って簡潔に書く）
--       let newArgs := xs.dropLast.toArray
--       logInfo m!"newArgs:{newArgs}"

--       return ⟨Syntax.node info kind newArgs⟩

--   | _ =>
--       return seq


@[tactic myconvSeq]
def evalMyConvSeq : Tactic := fun stx => do
  match stx with
  | `(tactic| myconv => $seq) =>
      withMainContext do
        -- makeNavSeq は Syntax を取るので raw を渡す
        let ns := makeNavSeq seq.raw
        -- 末尾が apply でない場合は通常の conv を実行
        let tailIsapply :=
          match ns.reverse.head? with
          | some (Nav.apply _) => true
          | _ => false
        if !tailIsapply then
          evalTactic (← `(tactic| conv => $seq))
          return
        -- 先頭は inc の左右選択（lhs / rhs）
        match ns with
        | Nav.lhs :: tail =>
            let tm ← makerwlemma tail
            evalTactic (← `(tactic| apply inc_trans $tm ?_))
              -- let newseq ← dropLastapply seq
              -- evalTactic (← `(tactic| conv => $newseq))
        | Nav.rhs :: tail =>
            let tm ← makerwlemma tail
            evalTactic (← `(tactic| apply inc_trans ?_ $tm))
            -- let newseq ← dropLastapply seq
            -- let newseq2 ← dropLastapply newseq
            -- logInfo m!"[myconv] newseq after rhs apply: {newseq}"
            -- logInfo m!"[myconv] newseq after rhs apply: {newseq2}"
            -- evalTactic (← `(tactic| conv => $newseq2))
        | _ =>
            evalTactic (← `(tactic| conv => $seq))
  | _ => throwUnsupportedSyntax

@[simp] theorem assumption_simp {P:Prop}(H: P) : P := H

variable [c : Dedekind]
theorem test : f ⊑ f' → g ⊑ g' → (f ∘  g) ⊑ (f' ∘ g') := by
  intro H H0
  myconv => rhs; lhs; apply H
  apply comp_inc_compat_ab_ab'
  assumption

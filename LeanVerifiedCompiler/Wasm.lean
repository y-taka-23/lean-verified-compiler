import LeanVerifiedCompiler.Common

namespace Wasm

abbrev LocalIdx := Nat
abbrev Locals := LocalIdx → Common.Val
abbrev Stack := List Common.Val
abbrev LabelIdx := Nat

inductive Instr where
  | i32Const : Common.Val → Instr
  | localGet : LocalIdx → Instr
  | localSet : LocalIdx → Instr
  | i32BinOp : Common.BinOp → Instr
  | ifElse : List Instr → List Instr → Instr
  | loop : List Instr → Instr
  | br : LabelIdx → Instr
  | label : Stack → List Instr → List Instr → Instr
  deriving Repr

structure Config where
  cont : List Instr
  locals : Locals
  stack : Stack

def update (ρ : Locals) (i : LocalIdx) (v : Common.Val) : Locals :=
  fun j => if j = i then v else ρ j

inductive Step : Config → Config → Prop where
  | i32Const :
      ∀ (v : Common.Val) (cs : List Instr) (ρ : Locals) (s : Stack),
      Step ⟨.i32Const v :: cs, ρ, s⟩ ⟨cs, ρ, v :: s⟩
  | localGet :
      ∀ (i : LocalIdx) (cs : List Instr) (ρ : Locals) (s : Stack),
      Step ⟨.localGet i :: cs, ρ, s⟩ ⟨cs, ρ, ρ i :: s⟩
  | localSet :
      ∀ (i : LocalIdx) (v : Common.Val) (cs : List Instr) (ρ : Locals) (s : Stack),
      Step ⟨.localSet i :: cs, ρ, v :: s⟩ ⟨cs, update ρ i v, s⟩
  | i32BinOp :
      ∀ (op : Common.BinOp) (v1 v2 : Common.Val)
        (cs : List Instr) (ρ : Locals) (s : Stack),
      Step
        ⟨.i32BinOp op :: cs, ρ, v2 :: v1 :: s⟩
        ⟨cs, ρ, (Common.evalBinOp op v1 v2) :: s⟩
  | ifTrue :
      ∀ (v : Common.Val) (ts fs cs : List Instr) (ρ : Locals) (s : Stack),
      v ≠ 0 → Step ⟨.ifElse ts fs :: cs, ρ, v :: s⟩ ⟨.label s [] ts :: cs, ρ, s⟩
  | ifFalse :
      ∀ (v : Common.Val) (ts fs cs : List Instr) (ρ : Locals) (s : Stack),
      v = 0 → Step ⟨.ifElse ts fs :: cs, ρ, v :: s⟩ ⟨.label s [] fs :: cs, ρ, s⟩
  | loop :
      ∀ (bs cs : List Instr) (ρ : Locals) (s : Stack),
      Step ⟨.loop bs :: cs, ρ, s⟩ ⟨.label s [.loop bs] bs :: cs, ρ, s⟩
  | labelStep :
      ∀ (bs bs' ks cs : List Instr) (ρ ρ' : Locals) (s s' s0 : Stack),
      Step ⟨bs, ρ, s⟩ ⟨bs', ρ', s'⟩ →
      Step ⟨.label s0 ks bs :: cs, ρ, s⟩ ⟨.label s0 ks bs' :: cs, ρ', s'⟩
  | labelBr0 :
      ∀ (bs ks cs : List Instr) (ρ : Locals) (s0 s : Stack),
      Step ⟨.label s0 ks (.br 0 :: bs) :: cs, ρ, s⟩ ⟨ks ++ cs, ρ, s0⟩
  | labelBrD :
      ∀ (bs ks cs : List Instr) (d : LabelIdx) (ρ : Locals) (s0 s : Stack),
      Step ⟨.label s0 ks (.br (d + 1) :: bs) :: cs, ρ, s⟩ ⟨.br d :: cs, ρ, s0⟩
  | labelEnd :
      ∀ (ks cs : List Instr) (ρ : Locals) (s0 s : Stack),
      Step ⟨.label s0 ks [] :: cs, ρ, s⟩ ⟨cs, ρ, s⟩

inductive Steps : Config → Config → Prop where
  | refl :
      ∀ (cfg : Config), Steps cfg cfg
  | step :
      ∀ (cfg1 cfg2 cfg3 : Config),
      Step cfg1 cfg2 → Steps cfg2 cfg3 → Steps cfg1 cfg3

theorem Steps.trans :
    ∀ (cfg1 cfg2 cfg3 : Config),
    Steps cfg1 cfg2 → Steps cfg2 cfg3 → Steps cfg1 cfg3 := by
  intro cfg1 cfg2 cfg3 h12 h23
  induction h12 with
  | refl =>
    exact h23
  | step _ _ _ hstep _ ih =>
    apply Steps.step
    · exact hstep
    exact ih h23

theorem Steps.lift :
    ∀ (ks cs : List Instr) (s0 : Stack) (cfg1 cfg2 : Config),
    Steps cfg1 cfg2 →
    Steps
      ⟨.label s0 ks cfg1.cont :: cs, cfg1.locals, cfg1.stack⟩
      ⟨.label s0 ks cfg2.cont :: cs, cfg2.locals, cfg2.stack⟩ := by
  intro ks cs s0 cfg1 cfg2 h
  induction h with
  | refl cfg =>
    apply Steps.refl
  | step cfg1 cfg2 cfg3 h12 h23 ih =>
    apply Steps.step
    · apply Step.labelStep _ _ _ _ _ _ _ _ _ h12
    exact ih

end Wasm

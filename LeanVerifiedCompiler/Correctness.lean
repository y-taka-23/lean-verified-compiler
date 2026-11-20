import LeanVerifiedCompiler.Compile

namespace Correctness

example : ∀ (ρ : Source.Env),
    Wasm.Steps
      ⟨Compile.compileExpr (.binOp .add (.var 0) (.lit 1)), ρ, []⟩
      ⟨[], ρ, [ρ 0 + 1]⟩ := by
  intro ρ
  simp only [Compile.compileExpr]
  apply Wasm.Steps.step
  · apply Wasm.Step.localGet
  apply Wasm.Steps.step
  · apply Wasm.Step.i32Const
  apply Wasm.Steps.step
  · apply Wasm.Step.i32BinOp
  apply Wasm.Steps.refl

theorem compileExpr_correct :
    ∀ (e : Source.Expr) (cs : List Wasm.Instr)
      (ρ : Source.Env) (s : Wasm.Stack),
    Wasm.Steps
      ⟨Compile.compileExpr e ++ cs, ρ, s⟩
      ⟨cs, ρ, Source.evalExpr e ρ :: s⟩ := by
  intro e
  induction e with
  | lit v =>
    intro cs ρ s
    simp only [Compile.compileExpr, Source.evalExpr]
    apply Wasm.Steps.step
    · apply Wasm.Step.i32Const
    apply Wasm.Steps.refl
  | var n =>
    intro cs ρ s
    simp only [Compile.compileExpr, Source.evalExpr]
    apply Wasm.Steps.step
    · apply Wasm.Step.localGet
    apply Wasm.Steps.refl
  | binOp op e1 e2 ih1 ih2 =>
    intro cs ρ s
    simp only [Compile.compileExpr, Source.evalExpr, List.append_assoc]
    apply Wasm.Steps.trans _ _ _ (ih1 _ _ _)
    apply Wasm.Steps.trans _ _ _ (ih2 _ _ _)
    apply Wasm.Steps.step
    · apply Wasm.Step.i32BinOp
    apply Wasm.Steps.refl

theorem compileStmt_correct :
    ∀ (stmt : Source.Stmt) (cs : List Wasm.Instr)
      (ρ ρ' : Source.Env) (s : Wasm.Stack),
    Source.Exec stmt ρ ρ' →
    Wasm.Steps
      ⟨Compile.compileStmt stmt ++ cs, ρ, s⟩
      ⟨cs, ρ', s⟩ := by
  intro stmt cs ρ ρ' s eh
  induction eh generalizing cs s with
  | skip ρ =>
    simp only [Compile.compileStmt, List.nil_append]
    apply Wasm.Steps.refl
  | assign n e ρ =>
    simp only [Compile.compileStmt, List.append_assoc]
    apply Wasm.Steps.trans _ _ _ (compileExpr_correct _ _ _ _)
    apply Wasm.Steps.step
    · apply Wasm.Step.localSet
    apply Wasm.Steps.refl
  | seq stmt1 stmt2 ρ ρ' ρ'' eh1 eh2 ih1 ih2 =>
    simp only [Compile.compileStmt, List.append_assoc]
    apply Wasm.Steps.trans _ _ _ (ih1 _ _)
    apply ih2
  | ifTrue stmt1 stmt2 e ρ ρ' hne eh ih =>
    simp only [Compile.compileStmt, List.append_assoc]
    apply Wasm.Steps.trans _ _ _ (compileExpr_correct _ _ _ _)
    apply Wasm.Steps.step
    · apply Wasm.Step.ifTrue
      exact hne
    have hb := Wasm.Steps.lift [] cs s _ _ (ih [] s)
    simp only [List.append_nil] at hb
    apply Wasm.Steps.trans _ _ _ hb
    apply Wasm.Steps.step
    · apply Wasm.Step.labelEnd
    apply Wasm.Steps.refl
  | ifFalse stmt1 stmt2 e ρ ρ' heq eh ih =>
    simp only [Compile.compileStmt, List.append_assoc]
    apply Wasm.Steps.trans _ _ _ (compileExpr_correct _ _ _ _)
    apply Wasm.Steps.step
    · apply Wasm.Step.ifFalse
      exact heq
    have hb := Wasm.Steps.lift [] cs s _ _ (ih [] s)
    simp only [List.append_nil] at hb
    apply Wasm.Steps.trans _ _ _ hb
    apply Wasm.Steps.step
    · apply Wasm.Step.labelEnd
    apply Wasm.Steps.refl
  | whileTrue stmt e ρ ρ' ρ'' hne eh1 eh2 ih1 ih2 =>
    simp only [Compile.compileStmt]
    apply Wasm.Steps.step
    · apply Wasm.Step.loop
    apply Wasm.Steps.trans _ _ _
      (Wasm.Steps.lift _ _ _ _ _ (compileExpr_correct _ _ _ _))
    dsimp only
    apply Wasm.Steps.step
    · apply Wasm.Step.labelStep
      apply Wasm.Step.ifTrue
      exact hne
    apply Wasm.Steps.trans _ _ _
      (Wasm.Steps.lift _ _ _ _ _ (Wasm.Steps.lift _ _ _ _ _ (ih1 _ _)))
    dsimp only
    apply Wasm.Steps.step
    · apply Wasm.Step.labelStep
      apply Wasm.Step.labelBrD
    apply Wasm.Steps.step
    · apply Wasm.Step.labelBr0
    apply ih2
  | whileFalse stmt e ρ heq =>
    simp only [Compile.compileStmt]
    apply Wasm.Steps.step
    · apply Wasm.Step.loop
    apply Wasm.Steps.trans _ _ _
      (Wasm.Steps.lift _ _ _ _ _ (compileExpr_correct _ _ _ _))
    dsimp only
    apply Wasm.Steps.step
    · apply Wasm.Step.labelStep
      apply Wasm.Step.ifFalse
      exact heq
    apply Wasm.Steps.step
    · apply Wasm.Step.labelStep
      apply Wasm.Step.labelEnd
    apply Wasm.Steps.step
    · apply Wasm.Step.labelEnd
    apply Wasm.Steps.refl

#print axioms compileStmt_correct

end Correctness

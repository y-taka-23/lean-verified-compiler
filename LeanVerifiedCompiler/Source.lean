import LeanVerifiedCompiler.Common

namespace Source

abbrev Name := Nat

inductive Expr where
  | lit : Common.Val → Expr
  | var : Name → Expr
  | binOp : Common.BinOp → Expr → Expr → Expr
  deriving Repr

#eval Expr.binOp .add (.var 0) (.lit 1)

abbrev Env := Name → Common.Val

def evalExpr (e : Expr) (ρ : Env) : Common.Val :=
  match e with
  | .lit v => v
  | .var n => ρ n
  | .binOp op e1 e2 => Common.evalBinOp op (evalExpr e1 ρ) (evalExpr e2 ρ)

#eval evalExpr
  (.binOp .add (.var 0) (.lit 1))
  (fun x => if x == 0 then 43 else 0)
#eval evalExpr
  (.binOp .add (.lit 0xFFFFFFFF) (.lit 1))
  (fun _ => 0)

inductive Stmt where
  | skip : Stmt
  | assign : Name → Expr → Stmt
  | seq : Stmt → Stmt → Stmt
  | ifElse : Expr → Stmt → Stmt → Stmt
  | whileLoop : Expr → Stmt → Stmt
  deriving Repr

def sum3 : Stmt :=
  .seq
    (.assign 0 (.binOp .add (.var 0) (.var 1)))
    (.assign 0 (.binOp .add (.var 0) (.var 2)))

def logicalNot : Stmt :=
  .ifElse (.var 0)
    (.assign 0 (.lit 0))
    (.assign 0 (.lit 1))

def mul : Stmt :=
  .seq
    (.assign 0 (.lit 0))
    (.whileLoop (.var 2)
      (.seq
        (.assign 0 (.binOp .add (.var 0) (.var 1)))
        (.assign 2 (.binOp .add (.var 2) (.lit (-1))))))

def update (ρ : Env) (n : Name) (v : Common.Val) : Env :=
  fun m => if m = n then v else ρ m

inductive Exec : Stmt → Env → Env → Prop where
  | skip :
      ∀ (ρ : Env), Exec .skip ρ ρ
  | assign :
      ∀ (n : Name) (e : Expr) (ρ : Env),
      Exec (.assign n e) ρ (update ρ n (evalExpr e ρ))
  | seq :
      ∀ (stmt1 stmt2 : Stmt) (ρ ρ' ρ'' : Env),
      Exec stmt1 ρ ρ' → Exec stmt2 ρ' ρ'' → Exec (.seq stmt1 stmt2) ρ ρ''
  | ifTrue :
      ∀ (stmt1 stmt2 : Stmt) (e : Expr) (ρ ρ' : Env),
      evalExpr e ρ ≠ 0 → Exec stmt1 ρ ρ' → Exec (.ifElse e stmt1 stmt2) ρ ρ'
  | ifFalse :
      ∀ (stmt1 stmt2 : Stmt) (e : Expr) (ρ ρ' : Env),
      evalExpr e ρ = 0 → Exec stmt2 ρ ρ' → Exec (.ifElse e stmt1 stmt2) ρ ρ'
  | whileTrue :
      ∀ (stmt : Stmt) (e : Expr) (ρ ρ' ρ'' : Env),
      evalExpr e ρ ≠ 0 → Exec stmt ρ ρ' → Exec (.whileLoop e stmt) ρ' ρ'' →
      Exec (.whileLoop e stmt) ρ ρ''
  | whileFalse :
      ∀ (stmt : Stmt) (e : Expr) (ρ : Env),
      evalExpr e ρ = 0 → Exec (.whileLoop e stmt) ρ ρ

end Source

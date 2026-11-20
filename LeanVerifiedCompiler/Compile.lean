import LeanVerifiedCompiler.Source
import LeanVerifiedCompiler.Wasm

namespace Compile

def compileExpr (e : Source.Expr) : List Wasm.Instr :=
  match e with
  | .lit v => [.i32Const v]
  | .var n => [.localGet n]
  | .binOp op e1 e2 => compileExpr e1 ++ compileExpr e2 ++ [.i32BinOp op]

#eval compileExpr (.binOp .add (.var 0) (.lit 1))

def compileStmt (stmt : Source.Stmt) : List Wasm.Instr :=
  match stmt with
  | .skip => []
  | .assign n e => compileExpr e ++ [.localSet n]
  | .seq stmt1 stmt2 => compileStmt stmt1 ++ compileStmt stmt2
  | .ifElse e stmt1 stmt2 =>
      compileExpr e ++ [.ifElse (compileStmt stmt1) (compileStmt stmt2)]
  | .whileLoop e stmt =>
      [.loop (compileExpr e ++ [.ifElse (compileStmt stmt ++ [.br 1]) []])]

#eval compileStmt Source.sum3
#eval compileStmt Source.logicalNot
#eval compileStmt Source.mul

def maxVarExpr (e : Source.Expr) : Nat :=
  match e with
  | .lit _ => 0
  | .var n => n
  | .binOp _ e1 e2 => max (maxVarExpr e1) (maxVarExpr e2)

def maxVarStmt (stmt : Source.Stmt) : Nat :=
  match stmt with
  | .skip => 0
  | .assign n e => max n (maxVarExpr e)
  | .seq stmt1 stmt2 => max (maxVarStmt stmt1) (maxVarStmt stmt2)
  | .ifElse e stmt1 stmt2 =>
      max (maxVarExpr e) (max (maxVarStmt stmt1) (maxVarStmt stmt2))
  | .whileLoop e stmt => max (maxVarExpr e) (maxVarStmt stmt)

end Compile

import LeanVerifiedCompiler.Wasm

namespace Wat

def binOpToWat (op : Common.BinOp) : String :=
  match op with
  | .add => "i32.add"
  | .sub => "i32.sub"
  | .mul => "i32.mul"
  | .shrS => "i32.shr_s"
  | .ltS => "i32.lt_s"

def instrToWat (c : Wasm.Instr) : String :=
  match c with
  | .i32Const v => "i32.const " ++ toString v.toNat
  | .localGet i => "local.get " ++ toString i
  | .localSet i => "local.set " ++ toString i
  | .i32BinOp op => binOpToWat op
  | .ifElse ts fs =>
      "if " ++ String.intercalate " " (ts.map instrToWat) ++
      " else " ++ String.intercalate " " (fs.map instrToWat) ++ " end"
  | .loop bs => "loop " ++ String.intercalate " " (bs.map instrToWat) ++ " end"
  | .br d => "br " ++ toString d
  | .label _ _ _ => "unreachable" -- コンパイラは出力しない

def moduleToWat (n : Nat) (cs : List Wasm.Instr) : String :=
  "(module \n" ++
  "(func\n" ++
  "(export \"main\")\n" ++
  "(param " ++ String.intercalate " " (List.replicate n "i32") ++ ")\n" ++
  "(result i32)\n" ++
  String.intercalate " " (cs.map instrToWat) ++ "\n" ++
  "local.get 0\n" ++
  "))"

end Wat

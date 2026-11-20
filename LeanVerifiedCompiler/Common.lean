namespace Common

abbrev Val := BitVec 32

#eval (1 : Val) + 2
#eval (0xFFFFFFFF : Val) + 1
#eval (-1 : Val)

inductive BinOp where
  | add
  | sub
  | mul
  | shrS
  | ltS
  deriving Repr

def evalBinOp (op : BinOp) (v1 v2 : Val) : Val :=
  match op with
  | .add => v1 + v2
  | .sub => v1 - v2
  | .mul => v1 * v2
  | .shrS => BitVec.sshiftRight v1 (v2.toNat % 32)
  | .ltS => if BitVec.slt v1 v2 then 1 else 0

end Common

import LeanVerifiedCompiler

def compileToWat (prog : Source.Stmt) : String :=
  Wat.moduleToWat (Compile.maxVarStmt prog + 1) (Compile.compileStmt prog)

def main : IO Unit := do
  IO.FS.createDirAll "out"
  IO.FS.writeFile "out/sum3.wat" (compileToWat Source.sum3)
  IO.FS.writeFile "out/not.wat" (compileToWat Source.logicalNot)
  IO.FS.writeFile "out/mul.wat" (compileToWat Source.mul)
  IO.FS.writeFile "out/gcd.wat" (compileToWat Gcd.prog)
  IO.FS.writeFile "out/julia.wat" (compileToWat Julia.prog)

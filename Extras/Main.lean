import LeanVerifiedCompiler
import Extras

def compileToWat (prog : Source.Stmt) : String :=
  Wat.moduleToWat (Compile.maxVarStmt prog + 1) (Compile.compileStmt prog)

def main : IO Unit := do
  IO.FS.createDirAll "out"
  IO.FS.writeFile "out/raymarching.wat" (compileToWat RayMarching.prog)
  IO.FS.writeFile "out/seasons.wat" (compileToWat Seasons.prog)
  IO.FS.writeFile "out/daisy.wat" (compileToWat Daisy.prog)

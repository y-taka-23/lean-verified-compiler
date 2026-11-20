import LeanVerifiedCompiler.Source

namespace Syntax

declare_syntax_cat iexpr
syntax num : iexpr
syntax ident : iexpr
syntax:65 iexpr:65 " + " iexpr:66 : iexpr
syntax:65 iexpr:65 " - " iexpr:66 : iexpr
syntax:70 iexpr:70 " * " iexpr:71 : iexpr
syntax:60 iexpr:60 " >> " iexpr:61 : iexpr
syntax:50 iexpr:51 " < " iexpr:51 : iexpr
syntax "(" iexpr ")" : iexpr
syntax "e{" iexpr "}" : term

macro_rules
  | `(e{ $v:num }) => `(Source.Expr.lit $v)
  | `(e{ $n:ident }) => `(Source.Expr.var $n)
  | `(e{ ($e:iexpr) }) => `(e{ $e })
  | `(e{ $e1:iexpr + $e2:iexpr }) =>
      `(Source.Expr.binOp Common.BinOp.add e{ $e1 } e{ $e2 })
  | `(e{ $e1:iexpr - $e2:iexpr }) =>
      `(Source.Expr.binOp Common.BinOp.sub e{ $e1 } e{ $e2 })
  | `(e{ $e1:iexpr * $e2:iexpr }) =>
      `(Source.Expr.binOp Common.BinOp.mul e{ $e1 } e{ $e2 })
  | `(e{ $e1:iexpr >> $e2:iexpr }) =>
      `(Source.Expr.binOp Common.BinOp.shrS e{ $e1 } e{ $e2 })
  | `(e{ $e1:iexpr < $e2:iexpr }) =>
      `(Source.Expr.binOp Common.BinOp.ltS e{ $e1 } e{ $e2 })

declare_syntax_cat istmt
syntax ident " := " iexpr ";" : istmt
syntax "if " iexpr " then " istmt+ " else " istmt+ " end" : istmt
syntax "if " iexpr " then " istmt+ " end" : istmt
syntax "while " iexpr " do " istmt+ " end" : istmt
syntax "s{" istmt+ "}" : term

macro_rules
  | `(s{ $v:ident := $e:iexpr; }) => `(Source.Stmt.assign $v e{ $e })
  | `(s{ $s1 $s2 $ss* }) => `(Source.Stmt.seq s{ $s1 } s{ $s2 $ss* })
  | `(s{ if $e:iexpr then $t* else $f* end }) =>
      `(Source.Stmt.ifElse e{ $e } s{ $t* } s{ $f* })
  | `(s{ if $e:iexpr then $t* end }) =>
      `(Source.Stmt.ifElse e{ $e } s{ $t* } Source.Stmt.skip)
  | `(s{ while $e:iexpr do $b* end }) =>
      `(Source.Stmt.whileLoop e{ $e } s{ $b* })

end Syntax

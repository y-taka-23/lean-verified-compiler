import LeanVerifiedCompiler.Syntax

namespace Extras.Syntax

syntax "!(" term ")" : iexpr
syntax "!(" term ")" ";" : istmt

macro_rules
  | `(e{ !($t:term) }) => `($t)

macro_rules
  | `(s{ !($t:term); }) => `($t)

end Extras.Syntax

/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Tactics

namespace Lean.Parser.Attr

syntax grindEq     := "="
syntax grindEqBoth := atomic("_" "=" "_")
syntax grindEqRhs  := atomic("=" "_")
syntax grindBwd    := "←"
syntax grindFwd    := "→"

syntax (name := grind) "grind" (grindEqBoth <|> grindEqRhs <|> grindEq <|> grindBwd <|> grindFwd)? : attr

end Lean.Parser.Attr

namespace Lean.Grind
/--
The configuration for `grind`.
Passed to `grind` using, for example, the `grind (config := { eager := true })` syntax.
-/
structure Config where
  /-- When `eager` is true (default: `false`), `grind` eagerly splits `if-then-else` and `match` expressions during internalization. -/
  eager : Bool := false
  /-- Maximum number of branches (i.e., case-splits) in the proof search tree. -/
  splits : Nat := 100
  /--
  Maximum number of E-matching (aka heuristic theorem instantiation)
  in a proof search tree branch.
  -/
  ematch : Nat := 5
  /--
  Maximum term generation.
  The input goal terms have generation 0. When we instantiate a theorem using a term from generation `n`,
  the new terms have generation `n+1`. Thus, this parameter limits the length of an instantiation chain. -/
  gen : Nat := 5
  /-- Maximum number of theorem instances generated using E-matching in a proof search tree branch. -/
  instances : Nat := 1000
  /-- If `matchEqs` is `true`, `grind` uses `match`-equations as E-matching theorems. -/
  matchEqs : Bool := true
  deriving Inhabited, BEq

end Lean.Grind

namespace Lean.Parser.Tactic

/-!
`grind` tactic and related tactics.
-/

-- TODO: parameters
syntax (name := grind) "grind" optConfig ("on_failure " term)? : tactic

end Lean.Parser.Tactic

/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.IntInstTesters
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util

def Int.Linear.Poly.isZero : Poly → Bool
  | .num 0 => true
  | _ => false

namespace Lean.Meta.Grind.Arith.Cutsat

/-- Creates a new variable in the cutsat module. -/
def mkVar (expr : Expr) : GoalM Var := do
  if let some var := (← get').varMap.find? { expr } then
    return var
  let var : Var := (← get').vars.size
  trace[grind.cutsat.internalize.term] "{expr} ↦ #{var}"
  modify' fun s => { s with
    vars      := s.vars.push expr
    varMap    := s.varMap.insert { expr } var
    dvdCnstrs := s.dvdCnstrs.push none
  }
  return var

def isInt (e : Expr) : GoalM Bool := do
  isDefEq (← inferType e) (mkConst ``Int)

def isAdd? (e : Expr) : GoalM (Option (Expr × Expr)) := do
  let_expr HAdd.hAdd _ _ _ inst a b ← e | return none
  unless (← isInstHAddInt inst) do
    reportIssue! "found term with non-standard instance{indentExpr e}"
    return none
  return some (a, b)

def isMul? (e : Expr) : GoalM (Option (Int × Expr)) := do
  let_expr HMul.hMul _ _ _ inst a b ← e
    | return none
  unless (← isInstHMulInt inst) do
    reportIssue! "found term with non-standard instance{indentExpr e}"
    return none
  let some k ← getIntValue? a
    | return none
  return some (k, b)

def addMonomial (e : Expr) (p : Poly) : GoalM Poly := do
  if let some (k, x) ← isMul? e then
    return .add k (← mkVar x) p
  if let some k ← getIntValue? e then
    if p.isZero then
      return .num k
    else
      reportIssue! "monomial expected, found numeral{indentExpr e}\ninternalizing as variable"
  return .add 1 (← mkVar e) p

partial def toPoly (e : Expr) : GoalM Poly := do
  if let some (a, b) ← isAdd? e then
    go a (← addMonomial b (.num 0))
  else
    addMonomial e (.num 0)
where
  go (e : Expr) (p : Poly) : GoalM Poly := do
    if let some (a, b) ← isAdd? e then
      go a (← addMonomial b p)
    else
      addMonomial e p

end Lean.Meta.Grind.Arith.Cutsat

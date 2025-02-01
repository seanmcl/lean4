import Lean

def foo (n : Nat) (f : Fin n) := match f with | ⟨k, _hk⟩ => if k == 0 then true else false

def thm : foo n f = (if f.val == 0 then true else false) := by simp [foo]

-- NB: equational theorem only applies if motive is manifest constructor
/--
info: foo.match_1.eq_1.{u_1} (n : Nat) (motive : Fin n → Sort u_1) (k : Nat) (_hk : k < n)
  (h_1 : (k : Nat) → (_hk : k < n) → motive ⟨k, _hk⟩) :
  (match ⟨k, _hk⟩ with
    | ⟨k, _hk⟩ => h_1 k _hk) =
    h_1 k _hk
-/
#guard_msgs in
#check foo.match_1.eq_1

open Lean Meta Elab Term

elab "simpMatch" t:term : command => do
  Command.runTermElabM fun _ => do
    withDeclName `_simpMatch do
      let e ← elabTerm t none
      synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := false)
      let e' ← instantiateMVars e
      let r ← Split.simpMatch e'
      logInfo m!"{indentExpr e}\n==>{indentExpr r.expr}"


-- This should simplify

/--
info:
  fun n f =>
    match ⟨↑f, ⋯⟩ with
    | ⟨k, _hk⟩ => if (k == 0) = true then true else false
==>
  fun n f => if (↑f == 0) = true then true else false
-/
#guard_msgs in
simpMatch
  fun (n : Nat) (f : Fin n) => (match Fin.mk f.val f.isLt with | ⟨k, _hk⟩ => if k == 0 then true else false)

-- But this should not

/--
info:
  fun n f =>
    match f with
    | ⟨k, _hk⟩ => if (k == 0) = true then true else false
==>
  fun n f =>
    match f with
    | ⟨k, _hk⟩ => if (k == 0) = true then true else false
-/
#guard_msgs in
simpMatch
  fun (n : Nat) (f : Fin n) => (match f with | ⟨k, _hk⟩ => if k == 0 then true else false)


/--
error: tactic 'fail' failed
case h_1
n : Nat
f : Fin n
k✝ : Nat
hk✝¹ : k✝ < n
hk✝ : 0 < n
heq✝¹ : ↑f = 0
heq✝ : HEq ⋯ hk✝
⊢ true =
    match ↑f, ⋯ with
    | 0, hk => !false
    | 1, hk => !false
    | x, hk => !true

case h_2
n : Nat
f : Fin n
k✝ : Nat
hk✝ : k✝ < n
x✝ : ∀ (hk : 0 < n), ↑f = 0 → HEq ⋯ hk → False
⊢ false =
    match ↑f, ⋯ with
    | 0, hk => !false
    | 1, hk => !false
    | x, hk => !true
-/
#guard_msgs in
example (n : Nat) (f : Fin n) :
  (fun k (hk : k < n) => (match k with | 0 => true | _ => false) =
    (match k with | 0 => not false | 1 => not false |_  => not true)) f.val f.isLt := by
  dsimp only
  split
  fail

import Lean.SimpLC.Whitelists.Root

simp_lc ignore BitVec.getLsbD_ge
simp_lc ignore BitVec.getMsbD_ge

-- TODO: this one indicates some work required around `Fin.ofNat'`
simp_lc whitelist BitVec.ofFin_sub BitVec.sub_zero

-- TODO: move to library
@[simp] theorem Fin.ofNat'_zero (n : Nat) [NeZero n] : Fin.ofNat' n 0 = 0 := rfl

namespace BitVec

-- @[simp] theorem setWidth_setWidth (x : BitVec u) (w : Nat) (h : u ≤ v ∨ w ≤ v) : setWidth w (setWidth v x) = setWidth w x := by
--   ext
--   simp only [getLsbD_setWidth, Fin.is_lt, decide_True, Bool.true_and, Bool.and_iff_right_iff_imp,
--     decide_eq_true_eq]
--   intro h
--   replace h := lt_of_getLsbD h
--   omega

-- This would be resolved by simply using `setWidth` instead of `cast`!
-- TODO: discuss with Tobias et al.
example (h : v = w) (x : BitVec v) : cast h x = setWidth w x := by
  ext
  simp
simp_lc whitelist BitVec.setWidth_eq BitVec.setWidth_cast

@[simp] theorem and_not_self (x : BitVec n) : x &&& ~~~x = 0 := by
   ext i
   simp

@[simp] theorem one_eq_zero_iff : 1#w = 0#w ↔ w = 0 := by
  constructor
  · intro h
    cases w
    · rfl
    · replace h := congrArg BitVec.toNat h
      simp at h
  · rintro rfl
    simp

-- TODO: re-evaluate these (appeared while moving `SimpLC` into Lean.)
simp_lc whitelist BitVec.udiv_one BitVec.udiv_self
simp_lc whitelist BitVec.udiv_eq_and BitVec.udiv_self
simp_lc whitelist BitVec.sub_ofFin BitVec.zero_sub

/-
The actual checks happen in `tests/lean/run/simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
-- #guard_msgs (drop info) in
-- simp_lc check in BitVec

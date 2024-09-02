/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Internal.Rat
import Std.Time.Date.Unit.Day

namespace Std
namespace Time
namespace Month
open Std.Internal
open Internal

set_option linter.all true

/--
`Ordinal` represents a bounded value for months, which ranges between 1 and 12.
-/
def Ordinal := Bounded.LE 1 12
  deriving Repr, BEq, LE, LT

instance : ToString Ordinal where
  toString x := toString x.val

instance : OfNat Ordinal n :=
  inferInstanceAs (OfNat (Bounded.LE 1 (1 + (11 : Nat))) n)

instance : Inhabited Ordinal where
  default := 1

/--
`Offset` represents an offset in months. It is defined as an `Int`.
-/
def Offset : Type := Int
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg, ToString

instance : OfNat Offset n :=
  ⟨Int.ofNat n⟩

namespace Offset

/--
Creates an `Offset` from a natural number.
-/
@[inline]
def ofNat (data : Nat) : Offset :=
  .ofNat data

/--
Creates an `Offset` from an integer.
-/
@[inline]
def ofInt (data : Int) : Offset :=
  data

end Offset

namespace Ordinal

/--
The ordinal value representing the month of January.
-/
@[inline] def january : Ordinal := 1

/--
The ordinal value representing the month of February.
-/
@[inline] def february : Ordinal := 2

/--
The ordinal value representing the month of March.
-/
@[inline] def march : Ordinal := 3

/--
The ordinal value representing the month of April.
-/
@[inline] def april : Ordinal := 4

/--
The ordinal value representing the month of May.
-/
@[inline] def may : Ordinal := 5

/--
The ordinal value representing the month of June.
-/
@[inline] def june : Ordinal := 6

/--
The ordinal value representing the month of July.
-/
@[inline] def july : Ordinal := 7

/--
The ordinal value representing the month of August.
-/
@[inline] def august : Ordinal := 8

/--
The ordinal value representing the month of September.
-/
@[inline] def september : Ordinal := 9

/--
The ordinal value representing the month of October.
-/
@[inline] def october : Ordinal := 10

/--
The ordinal value representing the month of November.
-/
@[inline] def november : Ordinal := 11

/--
The ordinal value representing the month of December.
-/
@[inline] def december : Ordinal := 12

/--
Creates an `Ordinal` from a `Nat`, ensuring the value is within bounds.
-/
@[inline]
def ofNat (data : Nat) (h : data ≥ 1 ∧ data ≤ 12 := by decide) : Ordinal :=
  Bounded.LE.ofNat' data h

/--
Converts a `Ordinal` into a `Nat`.
-/
@[inline]
def toNat (month : Ordinal) : Nat :=
  Bounded.LE.toNat month

/--
Creates an `Ordinal` from a `Fin`, ensuring the value is within bounds, if its 0 then its converted
to 1.
-/
@[inline]
def ofFin (data : Fin 13) : Ordinal :=
  Bounded.LE.ofFin' data (by decide)

/--
Transforms `Month.Ordinal` into `Second.Offset`.
-/
def toSeconds (leap : Bool) (month : Ordinal) : Second.Offset :=
  let daysAcc := #[0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]
  let time := daysAcc[month.toNat]! * 86400
  if leap && month.toNat ≥ 2
    then time + 86400
    else time

/--
Transforms `Month.Ordinal` into `Minute.Offset`.
-/
@[inline]
def toMinutes (leap : Bool) (month : Ordinal) : Minute.Offset :=
  toSeconds leap month
  |>.ediv 60

/--
Transforms `Month.Ordinal` into `Hour.Offset`.
-/
@[inline]
def toHours (leap : Bool) (month : Ordinal) : Hour.Offset :=
  toMinutes leap month
  |>.ediv 60

/--
Transforms `Month.Ordinal` into `Day.Offset`.
-/
@[inline]
def toDays (leap : Bool) (month : Ordinal) : Day.Offset :=
  toSeconds leap month
  |>.convert

/--
Size in days of each month if the year is not a leap year.
-/
@[inline]
def monthSizesNonLeap : { val : Array Day.Ordinal // val.size = 12 } :=
  ⟨#[31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31], by simp⟩

/--
Gets the number of days in a month without requiring a proof of the validity of the ordinal in a
month and year.
-/
def daysWithoutProof (leap : Bool) (month : Ordinal) : Day.Ordinal :=
  if month.val = 2 then
    if leap then 29 else 28
  else by
    let ⟨months, p⟩ := monthSizesNonLeap
    let r : Fin 12 := (month.sub 1).toFin (by decide) (by decide)
    rw [← p] at r
    exact months.get r

theorem all_greater_than_27 (leap : Bool) (i : Month.Ordinal) : daysWithoutProof leap i > 27 := by
  simp [daysWithoutProof, monthSizesNonLeap, Bounded.LE.sub, Bounded.LE.add, Bounded.LE.toFin]
  match i with
  | ⟨2, _⟩ => split <;> (simp; try split); all_goals decide
  | ⟨1, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩
  | ⟨8, _⟩ | ⟨9, _⟩ | ⟨10, _⟩ | ⟨11, _⟩ | ⟨12, _⟩ => simp; decide

/--
Check if the day is valid in a month and a leap year.
-/
abbrev Valid (leap : Bool) (month : Month.Ordinal) (day : Day.Ordinal) : Prop :=
  day.val ≤ (daysWithoutProof leap month).val

instance : Decidable (Valid leap month day) :=
  dite (day ≤ daysWithoutProof leap month) isTrue isFalse

/--
Gets the number of days in a month along with a proof of its validity.
-/
@[inline]
def days (leap : Bool) (month : Ordinal) : { day : Day.Ordinal // Valid leap month day ∧ day.val > 27 } := by
  refine ⟨daysWithoutProof leap month, ⟨Int.le_refl ((daysWithoutProof leap month).val), all_greater_than_27 leap month⟩⟩

/--
Clips the day to be within the valid range.
-/
@[inline]
def clipDay (leap : Bool) (month : Month.Ordinal) (day : Day.Ordinal) : { day : Day.Ordinal // Valid leap month day } :=
  let max : Day.Ordinal := month.days leap
  if h : day.val > max.val
    then ⟨max, Int.le_refl max.val⟩
    else ⟨day, Int.not_lt.mp h⟩

/--
Transforms a `Day.Ordinal.OfYear` into a tuple of a `Month` and a `Day`.
-/
def ofOrdinal (ordinal : Day.Ordinal.OfYear leap) : { val : Month.Ordinal × Day.Ordinal // Valid leap (Prod.fst val) (Prod.snd val) } := Id.run do
  let rec go (idx : Fin 12) (cumulative : Fin 366) :=
    let month := Month.Ordinal.ofFin idx.succ
    let ⟨days, valid, _⟩ := days leap month

    if h : cumulative.val < ordinal.val ∧ ordinal.val ≤ cumulative.val + days.val then
      let bounded := Bounded.LE.mk ordinal.val h |>.sub cumulative
      let bounded : Bounded.LE 1 days.val := bounded.cast (by omega) (by omega)

      let ⟨left, right⟩ := bounded.property
      let days₁ : Day.Ordinal := ⟨bounded.val, And.intro left (Int.le_trans right days.property.right)⟩
      ⟨⟨month, days₁⟩, Int.le_trans right valid⟩
    else
      if h : idx.val ≥ 11 then
        -- Need to remove this in the future.
        let ⟨day, valid⟩ := clipDay leap 1 1
        ⟨⟨1, day⟩, valid⟩
      else
        go ⟨idx.val + 1, Nat.succ_le_succ (Nat.not_le.mp h)⟩ (cumulative + (Fin.ofNat days.val.toNat))

  termination_by 12 - idx.val
  go 0 0

end Ordinal
end Month
end Time
end Std

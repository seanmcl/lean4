/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Internal
import Std.Time.Date.Basic
import Std.Internal.Rat

namespace Std
namespace Time
open Std.Internal
open Internal
open Lean

set_option linter.all true

/--
`PlainDate` represents a date in the Year-Month-Day (YMD) format. It encapsulates the year, month,
and day components, with validation to ensure the date is valid.
-/
structure PlainDate where

  /--
  The year component of the date. It is represented as an `Offset` type from `Year`.
  -/
  year : Year.Offset

  /--
  The month component of the date. It is represented as an `Ordinal` type from `Month`.
  -/
  month : Month.Ordinal

  /--
  The day component of the date. It is represented as an `Ordinal` type from `Day`.
  -/
  day : Day.Ordinal

  /--
  Validates the date by ensuring that the year, month, and day form a correct and valid date.
  -/
  valid : year.Valid month day

instance : BEq PlainDate where
  beq x y := x.day == y.day && x.month == y.month && x.year == y.year

namespace PlainDate

/--
Creates a `PlainDate` by clipping the day to ensure validity. This function forces the date to be
valid by adjusting the day to fit within the valid range to fit the given month and year.
-/
def clip (year : Year.Offset) (month : Month.Ordinal) (day : Day.Ordinal) : PlainDate :=
  let ⟨day, valid⟩ := month.clipDay year.isLeap day
  PlainDate.mk year month day valid

/--
Creates a `PlainDate` by rolling over the extra days to the next month.
-/
def rollOver (year : Year.Offset) (month : Month.Ordinal) (day : Day.Ordinal) : PlainDate := by
  let max : Day.Ordinal := month.days year.isLeap
  have p := month.all_greater_than_27 year.isLeap
  if h : day.val > max.val then
    if h₁ : month.val > 11 then
      let eq : month.val = 12 := Int.eq_iff_le_and_ge.mpr (And.intro month.property.right h₁)
      let h : max.val = 31 := by simp [max, Month.Ordinal.days, Month.Ordinal.daysWithoutProof, Bounded.LE.sub , Bounded.LE.add, Bounded.LE.toFin, eq]; rfl
      let h₂ := Int.le_trans day.property.right (Int.eq_iff_le_and_ge.mp h |>.right) |> Int.not_lt.mpr
      contradiction
    else
      let max₂ : Bounded.LE 28 31 := max.truncateBottom p
      let sub := Int.sub_nonneg_of_le h
      simp [←Int.sub_sub] at sub
      let roll := day.addBounds (max₂.neg) |>.truncateBottom (Int.add_le_of_le_sub_left sub)
      let day : Day.Ordinal := roll.expandTop (by decide)
      let h₂ : roll.val ≤ 27 := Int.le_trans roll.property.right (by decide)
      let month := month.truncateTop (Int.not_lt.mp h₁) |>.addTop 1 (by decide)
      refine ⟨year, month, day, ?_⟩
      exact Int.le_of_lt (Int.le_trans (Int.add_le_add_right h₂ 1) (Month.Ordinal.all_greater_than_27 year.isLeap month))
  else
    let h := Int.not_lt.mp h
    exact ⟨year, month, day, h⟩

instance : Inhabited PlainDate where
  default := clip 0 1 1

/--
Creates a new `PlainDate` from year, month, and day components.
-/
def ofYearMonthDay (year : Year.Offset) (month : Month.Ordinal) (day : Day.Ordinal) : Option PlainDate :=
  if valid : year.Valid month day
    then some (PlainDate.mk year month day valid)
    else none

/--
Creates a `PlainDate` from a year and a day ordinal within that year.
-/
def ofYearOrdinal (year : Year.Offset) (ordinal : Day.Ordinal.OfYear year.isLeap) : PlainDate :=
  let ⟨⟨month, day⟩, valid⟩ := Month.Ordinal.ofOrdinal ordinal
  PlainDate.mk year month day valid

/--
Creates a `PlainDate` from the number of days since the UNIX epoch (January 1st, 1970).
-/
def ofDaysSinceUNIXEpoch (day : Day.Offset) : PlainDate :=
  let z := day.toInt + 719468
  let era := (if z ≥ 0 then z else z - 146096).div 146097
  let doe := z - era * 146097
  let yoe := (doe - doe.div 1460 + doe.div 36524 - doe.div 146096).div 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe.div 4 - yoe.div 100)
  let mp := (5 * doy + 2).div 153
  let d := doy - (153 * mp + 2).div 5 + 1
  let m := mp + (if mp < 10 then 3 else -9)
  let y := y + (if m <= 2 then 1 else 0)
  .clip y (.clip m (by decide)) (.clip d (by decide))

/--
Calculates the `Weekday` of a given `PlainDate` using Zeller's Congruence for the Gregorian calendar.
-/
def weekday (date : PlainDate) : Weekday :=
  let q := date.day.toInt
  let m := date.month.toInt
  let y := date.year.toInt

  let y := if m < 2 then y - 1 else y
  let m := if m < 2 then m + 12 else m

  let k := y % 100
  let j := y.div 100
  let part := q + (13 * (m + 1)).div 5 + k + (k.div 4)
  let h := part + (j.div 4) - 2*j
  let d := (h + 5) % 7

  .ofFin ⟨d.toNat % 7, Nat.mod_lt d.toNat (by decide)⟩

/--
Determines the era of the given `PlainDate` based on its year.
-/
def era (date : PlainDate) : Year.Era :=
  if date.year.toInt ≥ 0 then
    .ce
  else
    .bce

/--
Checks if the `PlainDate` is in a leap year.
-/
def inLeapYear (date : PlainDate) : Bool :=
  date.year.isLeap

/--
Converts a `PlainDate` to the number of days since the UNIX epoch.
-/
def toDaysSinceUNIXEpoch (date : PlainDate) : Day.Offset :=
  let y : Int := if date.month.toInt > 2 then date.year else date.year.toInt - 1
  let era : Int := (if y ≥ 0 then y else y - 399).div 400
  let yoe : Int := y - era * 400
  let m : Int := date.month.toInt
  let d : Int := date.day.toInt
  let doy := (153 * (m + (if m > 2 then -3 else 9)) + 2).div 5 + d - 1
  let doe := yoe * 365 + yoe.div 4 - yoe.div 100 + doy

  .ofInt (era * 146097 + doe - 719468)

/--
Calculates the difference in years between a `PlainDate` and a given year.
-/
def yearsSince (date : PlainDate) (year : Year.Offset) : Year.Offset :=
  date.year - year

/--
Adds a given number of days to a `PlainDate`.
-/
@[inline]
def addDays (date : PlainDate) (days : Day.Offset) : PlainDate :=
  let dateDays := date.toDaysSinceUNIXEpoch
  ofDaysSinceUNIXEpoch (dateDays + days)

/--
Subtracts a given number of days from a `PlainDate`.
-/
@[inline]
def subDays (date : PlainDate) (days : Day.Offset) : PlainDate :=
  addDays date (-days)

/--
Adds a given number of weeks to a `PlainDate`.
-/

@[inline]
def addWeeks (date : PlainDate) (weeks : Week.Offset) : PlainDate :=
  let dateDays := date.toDaysSinceUNIXEpoch
  let daysToAdd := weeks.toDays
  ofDaysSinceUNIXEpoch (dateDays + daysToAdd)

/--
Subtracts a given number of weeks from a `PlainDate`.
-/
@[inline]
def subWeeks (date : PlainDate) (weeks : Week.Offset) : PlainDate :=
  addWeeks date (-weeks)

/--
Adds a given number of months to a `PlainDate`, clipping the day to the last valid day of the month.
-/
def addMonthsClip (date : PlainDate) (months : Month.Offset) : PlainDate :=
  let yearsOffset := months.div 12
  let monthOffset := Bounded.LE.byMod months 12 (by decide)
  let months := date.month.addBounds monthOffset

  let (yearsOffset, months) : Year.Offset × Month.Ordinal := by
    if h₁ : months.val > 12 then
      let months := months |>.truncateBottom h₁ |>.sub 12
      exact (yearsOffset.add 1, months.expandTop (by decide))
    else if h₂ : months.val < 1 then
      let months := months |>.truncateTop (Int.le_sub_one_of_lt h₂) |>.add 12
      exact (yearsOffset.sub 1, months.expandBottom (by decide))
    else
      exact (yearsOffset, months.truncateTop (Int.not_lt.mp h₁) |>.truncateBottom (Int.not_lt.mp h₂))

  PlainDate.clip (date.year.add yearsOffset) months date.day

/--
Subtracts `Month.Offset` from a `PlainDate`, it clips the day to the last valid day of that month.
-/
@[inline]
def subMonthsClip (date : PlainDate) (months : Month.Offset) : PlainDate :=
  addMonthsClip date (-months)

/--
Adds a given number of months to a `PlainDate`, rolling over any excess days into the following month.
-/
def addMonthsRollOver (date : PlainDate) (months : Month.Offset) : PlainDate :=
  let yearsOffset := months.div 12
  let monthOffset := Bounded.LE.byMod months 12 (by decide)
  let months := date.month.addBounds monthOffset

  let (yearsOffset, months) : Year.Offset × Month.Ordinal := by
    if h₁ : months.val > 12 then
      let months := months |>.truncateBottom h₁ |>.sub 12
      exact (yearsOffset.add 1, months.expandTop (by decide))
    else if h₂ : months.val < 1 then
      let months := months |>.truncateTop (Int.le_sub_one_of_lt h₂) |>.add 12
      exact (yearsOffset.sub 1, months.expandBottom (by decide))
    else
      exact (yearsOffset, months.truncateTop (Int.not_lt.mp h₁) |>.truncateBottom (Int.not_lt.mp h₂))

  let year : Year.Offset := date.year.add yearsOffset
  let ⟨days, proof, _⟩ := Month.Ordinal.days year.isLeap months

  if h : days.val ≥ date.day.val then
    have p : year.Valid months date.day := by
      simp_all [Year.Offset.Valid, Month.Ordinal.Valid]
      exact Int.le_trans h proof
    PlainDate.mk year months date.day p
  else
    let roll := Day.Offset.ofInt (date.day.val - days.toInt)
    let date := PlainDate.clip (date.year.add yearsOffset) months date.day
    let days := date.toDaysSinceUNIXEpoch + roll
    PlainDate.ofDaysSinceUNIXEpoch days

/--
Subtracts `Month.Offset` from a `PlainDate`, rolling over excess days as needed.
-/
@[inline]
def subMonthsRollOver (date : PlainDate) (months : Month.Offset) : PlainDate :=
  addMonthsRollOver date (-months)

/--
Adds `Year.Offset` to a `PlainDate`, rolling over excess days to the next month, or next year.
-/
@[inline]
def addYearsRollOver (date : PlainDate) (years : Year.Offset) : PlainDate :=
  addMonthsRollOver date (years.mul 12)

/--
Subtracts `Year.Offset` from a `PlainDate`, rolling over excess days to the next month.
-/
@[inline]
def subYearsRollOver (date : PlainDate) (years : Year.Offset) : PlainDate :=
  addMonthsRollOver date (- years.mul 12)

/--
Adds `Year.Offset` to a `PlainDate`, clipping the day to the last valid day of the month.
-/
@[inline]
def addYearsClip (date : PlainDate) (years : Year.Offset) : PlainDate :=
  addMonthsClip date (years.mul 12)

/--
Subtracts `Year.Offset` from a `PlainDate`, clipping the day to the last valid day of the month.
-/
@[inline]
def subYearsClip (date : PlainDate) (years : Year.Offset) : PlainDate :=
  addMonthsClip date (- years.mul 12)

instance : HAdd PlainDate Day.Offset PlainDate where
  hAdd := addDays

instance : HSub PlainDate Day.Offset PlainDate where
  hSub := subDays

instance : HAdd PlainDate Week.Offset PlainDate where
  hAdd := addWeeks

instance : HSub PlainDate Week.Offset PlainDate where
  hSub := subWeeks

end PlainDate
end Time
end Std

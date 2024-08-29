/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Internal.Rat
import Std.Time.Time.Unit.Millisecond

namespace Std
namespace Time
namespace Nanosecond
open Std.Internal
open Internal

set_option linter.all true

/--
`Ordinal` represents a nanosecond value that is bounded between 0 and 999,999,999 nanoseconds.
-/
def Ordinal := Bounded.LE 0 999999999
  deriving Repr, BEq, LE, LT

instance : ToString Ordinal where
  toString x := toString x.val

instance : OfNat Ordinal n where
  ofNat := Bounded.LE.ofFin (Fin.ofNat n)

instance : Inhabited Ordinal where
  default := 0

namespace Ordinal

/--
`Ordinal` represents a bounded value for nanoseconds in a day, which ranges between 0 and 86400000000000.
-/
def OfDay := Bounded.LE 0 86400000000000
  deriving Repr, BEq, LE, LT

/--
Converts a `Nanosecond.Ordinal` value to `Millisecond.Ordinal`.
-/
def toMillisecond (nano : Ordinal) : Millisecond.Ordinal :=
  nano.ediv 1000000 (by decide)

/--
Converts a `Millisecond.Ordinal` value to `Nanosecond.Ordinal`.
-/
def ofMillisecond (nano : Millisecond.Ordinal) : Nanosecond.Ordinal :=
  nano.mul_pos 1000000 (by decide)
  |>.expandTop (by decide)

end Ordinal

/--
`Offset` represents a time offset in nanoseconds and is defined as an `Int`.
-/
def Offset : Type := UnitVal (1 / 1000000000)
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg, LE, LT, ToString

instance : OfNat Offset n := ⟨UnitVal.ofNat n⟩

namespace Offset

/--
Creates an `Offset` from a natural number.
-/
@[inline]
def ofNat (data : Nat) : Offset :=
  UnitVal.mk data

/--
Creates an `Offset` from an integer.
-/
@[inline]
def ofInt (data : Int) : Offset :=
  UnitVal.mk data

end Offset

/--
`Span` represents a bounded value for nanoseconds, ranging between -999999999 and 999999999.
This can be used for operations that involve differences or adjustments within this range.
-/
def Span := Bounded.LE (-999999999) 999999999
  deriving Repr, BEq, LE, LT

instance : Inhabited Span where default := Bounded.LE.mk 0 (by decide)

namespace Span

/--
Creates a new `Offset` out of a `Span`.
-/
def toOffset (span : Span) : Offset :=
  UnitVal.mk span.val

end Span
end Nanosecond
end Time
end Std

/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Internal.Rat
import Std.Time.Internal
import Std.Time.Time.Unit.Second

namespace Std
namespace Time
namespace Minute
open Std.Internal
open Internal

set_option linter.all true

/--
`Ordinal` represents a bounded value for minutes, ranging from 0 to 59. This is useful for representing the minute component of a time.
-/
def Ordinal := Bounded.LE 0 59
  deriving Repr, BEq, LE

instance : ToString Ordinal where
  toString x := toString x.val

instance : OfNat Ordinal n :=
  inferInstanceAs (OfNat (Bounded.LE 0 (0 + (59 : Nat))) n)

instance : Inhabited Ordinal where
  default := 0

/--
`Offset` represents a duration offset in minutes. It is defined as an `Int` value.
-/
def Offset : Type := UnitVal 60
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg, ToString

instance : OfNat Offset n :=
  ⟨UnitVal.ofInt <| Int.ofNat n⟩

namespace Ordinal

/--
Creates an `Ordinal` from a natural number, ensuring the value is within the valid range (0 to 59).
-/
@[inline]
def ofNat (data : Nat) (h : data ≤ 59 := by decide) : Ordinal :=
  Bounded.LE.ofNat data h

/--
Creates an `Ordinal` from a `Fin` value, ensuring it is within the valid range (0 to 59).
-/
@[inline]
def ofFin (data : Fin 60) : Ordinal :=
  Bounded.LE.ofFin data

/--
Converts an `Ordinal` to an `Offset`. The `Ordinal` value is converted to an `Offset` by interpreting
it as the number of minutes.
-/
@[inline]
def toOffset (ordinal : Ordinal) : Offset :=
  UnitVal.ofInt ordinal.val

end Ordinal
end Minute
end Time
end Std

/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Notation
import Std.Time.Format.Basic
import Std.Time.Internal.Bounded

namespace Std
namespace Time
namespace Formats

set_option linter.all true

/--
The ISO8601 format, which is always 24 or 27 characters long, used for representing date and time in
a standardized format. The format follows the pattern `YYYY-MM-DD'T'hh:mm:ss'Z'`.
-/
def ISO8601 : Format .any := date-spec% "YYYY-MM-DD'T'hh:mm:ss.sssZ"

/--
The AmericanDate format, which follows the pattern `MM/DD/YYYY`.
-/
def AmericanDate : Format .any := date-spec% "MM-DD-YYYY"

/--
The EuropeanDate format, which follows the pattern `DD/MM/YYYY`.
-/
def EuropeanDate : Format .any := date-spec% "DD-MM-YYYY"

/--
The Time12Hour format, which follows the pattern `HH:mm:ss aa` for representing time
in a 12-hour clock format with an AM/PM marker.
-/
def Time12Hour : Format .any := date-spec% "HH:mm:ss aa"

/--
The Time24Hour format, which follows the pattern `hh:mm:ss` for representing time
in a 24-hour clock format.
-/
def Time24Hour : Format .any := date-spec% "hh:mm:ss"

/--
The SQLDate format, which follows the pattern `YYYY-MM-DD` and is commonly used
in SQL databases to represent dates.
-/
def SQLDate : Format .any := date-spec% "YYYY-MM-DD"

/--
The LongDateFormat, which follows the pattern `EEEE, MMMM D, YYYY hh:mm:ss` for
representing a full date and time with the day of the week and month name.
-/
def LongDateFormat : Format (.only .GMT) := date-spec% "EEEE, MMMM D, YYYY hh:mm:ss"

/--
The AscTime format, which follows the pattern `EEE MMM d hh:mm:ss YYYY`. This format
is often used in older systems for logging and time-stamping events.
-/
def AscTime : Format (.only .GMT) := date-spec% "EEE MMM d hh:mm:ss YYYY"

/--
The RFC822 format, which follows the pattern `EEE, DD MMM YYYY hh:mm:ss ZZZ`.
This format is used in email headers and HTTP headers.
-/
def RFC822 : Format .any := date-spec% "EEE, DD MMM YYYY hh:mm:ss ZZZ"

/--
The RFC850 format, which follows the pattern `EEEE, DD-MMM-YY hh:mm:ss ZZZ`.
This format is an older standard for representing date and time in headers.
-/
def RFC850 : Format .any := date-spec% "EEEE, DD-MMM-YY hh:mm:ss ZZZ"

end Formats

namespace LocalDate

/--
Parses a date string in the American format (`MM/DD/YYYY`) and returns a `LocalDate`.
-/
def fromAmericanDateString (input : String) : Except String LocalDate := do
  Formats.AmericanDate.parseBuilder (λm d y => LocalDate.ofYearMonthDay y m d) input

/--
Converts a Date in the American format (`MM/DD/YYYY`) into a `String`.
-/
def toAmericanDateString (input : LocalDate) : String :=
  Formats.AmericanDate.formatBuilder input.month input.day input.year

/--
Parses a date string in the American format (`MM/DD/YYYY`) and returns a `LocalDate`.
-/
def fromSQLDateString (input : String) : Except String LocalDate := do
  Formats.SQLDate.parseBuilder (λy m d => LocalDate.ofYearMonthDay y m d) input

/--
Converts a Date in the SQL format (`MM/DD/YYYY`) into a `String`.
-/
def toSQLDateString (input : LocalDate) : String :=
  Formats.SQLDate.formatBuilder input.year input.month input.day

/--
Parses a `String` in the `AmericanDate` or `SQLDate` format and returns a `LocalDate`.
-/
def parse (input : String) : Except String LocalDate :=
  fromAmericanDateString input
  <|> fromSQLDateString input

end LocalDate

namespace LocalTime

/--
Parses a time string in the 24-hour format (`hh:mm:ss`) and returns a `LocalTime`.
-/
def fromTime24Hour (input : String) : Except String LocalTime :=
  Formats.Time24Hour.parseBuilder (λh m s => LocalTime.ofHourMinuteSeconds? h.snd m s.snd) input

/--
Formats a `LocalTime` value into a 24-hour format string (`hh:mm:ss`).
-/
def toTime24Hour (input : LocalTime) : String :=
  Formats.Time24Hour.formatBuilder input.hour input.minute input.second

/--
Parses a time string in the 12-hour format (`hh:mm:ss aa`) and returns a `LocalTime`.
-/
def fromTime12Hour (input : String) : Except String LocalTime := do
  let builder h m s a : Option LocalTime := do
    let value ← Internal.Bounded.ofInt? h.snd.val
    LocalTime.ofHourMinuteSeconds? (leap₂ := false) (HourMarker.toAbsolute a value) m s.snd

  Formats.Time12Hour.parseBuilder builder input

/--
Formats a `LocalTime` value into a 12-hour format string (`hh:mm:ss aa`).
-/
def toTime12Hour (input : LocalTime) : String :=
  Formats.Time12Hour.formatBuilder input.hour input.minute input.second (if input.hour.snd.val ≥ 12 then HourMarker.pm else HourMarker.am)

/--
Parses a `String` in the `Time12Hour` or `Time24Hour` format and returns a `LocalTime`.
-/
def parse (input : String) : Except String LocalTime :=
  fromTime12Hour input
  <|> fromTime24Hour input

end LocalTime

namespace ZonedDateTime

/--
Parses a `String` in the `ISO8601` format and returns a `ZonedDateTime`.
-/
def fromISO8601String (input : String) : Except String ZonedDateTime :=
  Formats.ISO8601.parse input

/--
Formats a `ZonedDateTime` value into an ISO8601 string.
-/
def toISO8601String (date : ZonedDateTime) : String :=
  Formats.ISO8601.format date.snd

/--
Parses a `String` in the `RFC822` format and returns a `ZonedDateTime`.
-/
def fromRFC822String (input : String) : Except String ZonedDateTime :=
  Formats.RFC822.parse input

/--
Formats a `ZonedDateTime` value into an RFC822 format string.
-/
def toRFC822String (date : ZonedDateTime) : String :=
  Formats.RFC822.format date.snd

/--
Parses a `String` in the `RFC850` format and returns a `ZonedDateTime`.
-/
def fromRFC850String (input : String) : Except String ZonedDateTime :=
  Formats.RFC850.parse input

/--
Formats a `ZonedDateTime` value into an RFC850 format string.
-/
def toRFC850String (date : ZonedDateTime) : String :=
  Formats.RFC850.format date.snd

/--
Parses a `String` in the `ISO8601`, `RFC822` or `RFC850` format and returns a `ZonedDateTime`.
-/
def parse (input : String) : Except String ZonedDateTime :=
  fromISO8601String input
  <|> fromRFC822String input
  <|> fromRFC850String input

end ZonedDateTime

namespace DateTime

/--
Parses a `String` in the `AscTime` format and returns a `DateTime` object in the GMT time zone.
-/
def fromAscTimeString (input : String) : Except String (DateTime .GMT) :=
  Formats.AscTime.parse input

/--
Formats a `DateTime` value into an AscTime format string.
-/
def toAscTimeString (datetime : DateTime .GMT) : String :=
  Formats.AscTime.format datetime

/--
Parses a `String` in the `LongDateFormat` and returns a `DateTime` object in the GMT time zone.
-/
def fromLongDateFormatString (input : String) : Except String (DateTime .GMT) :=
  Formats.LongDateFormat.parse input

/--
Formats a `DateTime` value into a LongDateFormat string.
-/
def toLongDateFormatString (datetime : DateTime .GMT) : String :=
  Formats.LongDateFormat.format datetime

/--
Formats a `DateTime` value into an ISO8601 string.
-/
def toISO8601String (date : DateTime tz) : String :=
  Formats.ISO8601.format date

/--
Formats a `ZonedDateTime` value into an RFC822 format string.
-/
def toRFC822String (date : DateTime tz) : String :=
  Formats.RFC822.format date

/--
Formats a `ZonedDateTime` value into an RFC850 format string.
-/
def toRFC850String (date : DateTime tz) : String :=
  Formats.RFC850.format date

/--
Parses a `String` in the `AscTime` or `LongDate` format and returns a `DateTime`.
-/
def parse (date : String) : Except String (DateTime .GMT) :=
  fromAscTimeString date
  <|> fromLongDateFormatString date

end DateTime

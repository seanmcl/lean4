/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
import Std.Time.Time
import Std.Time.Date
import Std.Time.Zoned
import Std.Time.Format
import Std.Time.DateTime
import Std.Time.Notation
import Std.Time.Duration

namespace Std
namespace Time

/-!
# Time

The Lean4 API for date, time, and duration functionalities, following the ISO8601 standards.

# Overview

This module of the standard library defines various concepts related to time, such as dates, times,
time zones and durations. These types are designed to be strongly-typed and to avoid problems with
conversion. It offers both unbounded and bounded variants to suit different use cases, like
adding days to a date or representing ordinal values.

# Date and Time Components

Date and time components are classified into different types based how you SHOULD use them. These
components are categorized as:

## Offset

Offsets represent unbounded shifts in specific date or time units. They are typically used in operations
like `date.addDays` where a `Day.Offset` is the parameter. Some offsets, such as `Month.Offset`, do not
correspond directly to a specific duration in seconds, as their value depends on the context (if
the year is leap or the size of the month). Offsets with a clear correspondent to seconds can be
converted because they use an internal type called `UnitVal`.

- Types with a correspondence to seconds:
  - `Day.Offset`
  - `Hour.Offset`
  - `WeekOfYear.Offset`
  - `Millisecond.Offset`
  - `Nanosecond.Offset`
  - `Second.Offset`

- Types without a correspondence to seconds:
  - `Month.Offset`
  - `Year.Offset`

## Ordinal

Ordinal types represent specific bounded values in reference to another unit, e.g., `Day.Ordinal`
represents a day in a month, ranging from 1 to 31. Some ordinal types like `Hour.Ordinal` and `Second.Ordinal`,
allow for values beyond the normal range (e.g, 24 hours and 61 seconds) to accomodate special cases
with leap seconds like `24:00:00` that is valid in ISO 8601.

- Ordinal types:
  - `Day.Ordinal`: Ranges from 1 to 31.
  - `Day.Ordinal.OfYear`: Ranges from 1 to (365 or 366).
  - `Month.Ordinal`: Ranges from 1 to 12.
  - `WeekOfYear.Ordinal`: Ranges from 1 to 53.
  - `Hour.Ordinal`: Ranges from 0 to 24.
  - `Millisecond.Ordinal`: Ranges from 0 to 999.
  - `Minute.Ordinal`: Ranges from 0 to 59.
  - `Nanosecond.Ordinal`: Ranges from 0 to 999,999,999.
  - `Second.Ordinal`: Ranges from 0 to 60.
  - `Weekday`: That is a inductive type with all the seven days.

## Span

Span types are used as subcomponents of other types. They represent a range of values in the limits
of the parent type, e.g, `Nanosecond.Span` ranges from -999,999,999 to 999,999,999, as 1,000,000,000
nanoseconds corresponds to one second.

- Span types:
  - `Nanosecond.Span`: Ranges from -999,999,999 to 999,999,999.

# Date and Time Types

Dates and times are composed of these components. Dates are "absolute" value in contrast with Offsets
that are just shifts in dates and times. Types like `Date` are made using of components such as `Year.Offset`,
`Month.Ordinal`, and `Day.Ordinal`, with a proof of the date's validity.

## Date
These types provide precision down to the day level, useful for representing and manipulating dates.

- **`PlainDate`:** Represents a calendar date in the format `YYYY-MM-DD`.
- **`WeekDate`:** Uses the `YYYY-Www` format with week level precision.

## Time
These types offer precision down to the nanosecond level, useful for representing and manipulating time of day.

- **`PlainTime`**: Represents a time of day in the format `HH:mm:ss,sssssssss`.

## Date and time
Combines date and time into a single representation, useful for precise timestamps and scheduling.

- **`PlainDateTime`**: Represents both date and time in the format `YYYY-MM-DDTHH:mm:ss,sssssssss`.
- **`Timestamp`**: Represents a point in time with nanosecond-level precision. It starts on the UNIX
epoch and it should be used when you receive or need to send timestamps to other systems.

## Zoned date and times.
Combines date, time and time zones.

- **`DateTime`**: Represents both date and time but with a time zone in the type constructor.
- **`ZonedDateTime`**: An existential version of the `DateTime`.

## Duration
Represents spans of time and the difference between two points in time.

- **`Duration`**: Represents the time span or difference between two `Timestamp`s values with nanosecond precision.

# Formats

Format strings are used to convert between `String` representations and date/time types, such as `yyyy-MM-dd'T'HH:mm:ss.sssZ`.
The table below outlines the available format specifiers. Some specifiers can be modified by repeating characters to
adjust truncation and offsets. Some of them when a character is repeated `n` times, it truncates the corresponding value to
`n` characters, usually when not specified a quantity.

The supported formats include:
- `G`: Represents the era, such as AD (Anno Domini) or BC (Before Christ).
  - `G`, `GG`, `GGG` (short): Displays the era in a short format (e.g., "AD").
  - `GGGG` (full): Displays the era in a full format (e.g., "Anno Domini").
  - `GGGGG` (narrow): Displays the era in a narrow format (e.g., "A").
- `y`: Represents the year of the era.
  - `yy`: Displays the year in a two-digit format, showing the last two digits (e.g., "04" for 2004).
  - `yyyy`: Displays the year in a four-digit format (e.g., "2004").
  - `yyyy+`: Extended format for years with more than four digits.
- `D`: Represents the day of the year.
- `M`: Represents the month of the year, displayed as either a number or text.
  - `M`, `MM`: Displays the month as a number, with `MM` zero-padded (e.g., "7" for July, "07" for July with padding).
  - `MMM`: Displays the abbreviated month name (e.g., "Jul").
  - `MMMM`: Displays the full month name (e.g., "July").
  - `MMMMM`: Displays the month in a narrow form (e.g., "J" for July).
- `d`: Represents the day of the month.
- `Q`: Represents the quarter of the year.
  - `Q`, `QQ`: Displays the quarter as a number (e.g., "3", "03").
  - `QQQ` (short): Displays the quarter as an abbreviated text (e.g., "Q3").
  - `QQQQ` (full): Displays the full quarter text (e.g., "3rd quarter").
  - `QQQQQ` (narrow): Displays the full quarter text (e.g., "3rd quarter").
- `w`: Represents the week of the week-based year (e.g., "27").
- `W`: Represents the week of the month (e.g., "4").
- `E`: Represents the day of the week as text.
  - `E`, `EE`, `EEE`: Displays the abbreviated day name (e.g., "Tue").
  - `EEEE`: Displays the full day name (e.g., "Tuesday").
  - `EEEEE`: Displays the narrow day name (e.g., "T" for Tuesday).
- `e`: Represents the localized day of the week.
  - `e`, `ee`: Displays the day of the week as a number, starting from 1 (Monday) to 7 (Sunday).
  - `eee`, `eeee`, `eeeee`: Displays the localized day of the week as text (same format as `E`).
- `F`: Represents the aligned week of the month (e.g., "3").
- `a`: Represents the AM or PM designation of the day.
  - `a`, `aa`, `aaa`: Displays AM or PM in a concise format (e.g., "PM").
  - `aaaa`: Displays the full AM/PM designation (e.g., "PM").
- `B`: Represents the period of the day (e.g., "in the morning", "at night").
  - `b`, `bb`, `bbb` (short): Displays the abbreviated period of the day (e.g., "morning").
  - `bbbb` (full): Displays the full period of the day (e.g., "in the morning").
  - `bbbbb` (narrow): Displays a narrow version of the period of the day (e.g., "m" for morning).
- `h`: Represents the hour of the AM/PM clock (1-12) (e.g., "12").
- `K`: Represents the hour of the AM/PM clock (0-11) (e.g., "0").
- `k`: Represents the hour of the day in a 1-24 format (e.g., "24").
- `H`: Represents the hour of the day in a 0-23 format (e.g., "0").
- `m`: Represents the minute of the hour (e.g., "30").
- `s`: Represents the second of the minute (e.g., "55").
- `S`: Represents a fraction of a second, typically displayed as a decimal number (e.g., "978" for milliseconds).
- `A`: Represents the millisecond of the day (e.g., "1234").
- `n`: Represents the nanosecond of the second (e.g., "987654321").
- `N`: Represents the nanosecond of the day (e.g., "1234000000").
- `V`: Represents the time zone ID, which could be a city-based zone (e.g., "America/Los_Angeles"), a UTC marker (`"Z"`), or a specific offset (e.g., "-08:30").
- `z`: Represents the time zone name.
  - `z`, `zz`, `zzz`: Shows an abbreviated time zone name (e.g., "PST" for Pacific Standard Time).
  - `zzzz`: Displays the full time zone name (e.g., "Pacific Standard Time").
- `O`: Represents the localized zone offset in the format "GMT" followed by the time difference from UTC.
  - `O`: Displays the GMT offset in a simple format (e.g., "GMT+8").
  - `O`: Displays the full GMT offset, including hours and minutes (e.g., "GMT+08:00").
- `X`: Represents the zone offset, using 'Z' for UTC and specifying the offset.
  - `X`: Displays the hour offset (e.g., "-08").
  - `XX`: Displays the hour and minute offset without a colon (e.g., "-0830").
  - `XXX`: Displays the hour and minute offset with a colon (e.g., "-08:30").
  - `XXXX`: Displays the hour, minute, and second offset without a colon (e.g., "-083045").
  - `XXXXX`: Displays the hour, minute, and second offset with a colon (e.g., "-08:30:45").
  - It also uses `Z` to represent UTC without any offset.
- `x`: Represents the zone offset without using 'Z' for zero offsets.
  - `x`: Displays the hour offset (e.g., "+08").
  - `xx`: Displays the hour and minute offset without a colon (e.g., "+0830").
  - `xxx`: Displays the hour and minute offset with a colon (e.g., "+08:30").
  - `xxxx`: Displays the hour, minute, and second offset without a colon (e.g., "+083045").
  - `xxxxx`: Displays the hour, minute, and second offset with a colon (e.g., "+08:30:45").
- `Z`: Represents the zone offset, with 'Z' for UTC and an optional time offset.
  - `Z`: Displays the hour and minute offset without a colon (e.g., "+0800").
  - `ZZ`: Displays "GMT" followed by the time offset (e.g., "GMT+08:00" or Z).
  - `ZZZ`: Displays the full hour, minute, and second offset with a colon (e.g., "+08:30:45" or Z).

# Macros

In order to help the user build dates easily, there are a lot of macros available for creating dates.
The `.sssssssss` can be ommited in most cases.

- **`date(yyyy-MM-dd)`**: Defines a date in the `YYYY-MM-DD` format.
- **`time(HH:mm:ss.sssssssss)`**: Defines a time in the `HH:mm:ss:sssssssss` format, including fractional seconds.
- **`datetime("yyy-MM-ddTHH:mm:ss.sssssssss")`**: Defines a datetime in the `YYYY-MM-DD:HH:mm:ss:sssssssss` format.
- **`offset("+HH:mm")`**: Defines a timezone offset in the format `+HH:mm`.
- **`timezone("NAME/ID ZZZ")`**: Defines a timezone with a name and an offset.
- **`datespec("format")`**: Defines a date specification format at compile time using the provided format string.
-/

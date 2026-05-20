/-
Conway's Doomsday Algorithm
John Horton Conway (1937-2020)

An elegant method for calculating the day of the week for any Gregorian date.
The key insight: in any given year, certain "doomsday" dates all fall on the
same day of the week:
  4/4, 6/6, 8/8, 10/10, 12/12, 5/9, 9/5, 7/11, 11/7, and the last day of Feb.

The algorithm computes the "anchor day" for the century, then adjusts for the
year within the century using: doomsday = anchor + year//12 + year%12 + (year%12)//4

Conway passed away on Saturday, April 11, 2020.
#eval dayOfWeek 2020 4 11 -- Saturday
-/
import Mathlib.Data.Int.ModEq

namespace Conway

/-- Days of the week, starting from Sunday = 0 -/
inductive DayOfWeek where
  | sunday | monday | tuesday | wednesday | thursday | friday | saturday
  deriving Repr, BEq, DecidableEq, Inhabited

namespace DayOfWeek

/-- Convert DayOfWeek to a Fin 7 -/
def toFin : DayOfWeek → Fin 7
  | sunday => 0 | monday => 1 | tuesday => 2 | wednesday => 3
  | thursday => 4 | friday => 5 | saturday => 6

instance : Repr DayOfWeek := ⟨fun d _ => match d with
  | sunday => "Sun" | monday => "Mon" | tuesday => "Tue"
  | wednesday => "Wed" | thursday => "Thu" | friday => "Fri" | saturday => "Sat"⟩

/-- Convert a Fin 7 to DayOfWeek -/
def ofFin : Fin 7 → DayOfWeek
  | 0 => sunday | 1 => monday | 2 => tuesday | 3 => wednesday
  | 4 => thursday | 5 => friday | 6 => saturday
  | _ => sunday

@[simp] theorem ofFin_toFin (d : DayOfWeek) : ofFin (toFin d) = d := by
  cases d <;> rfl

/-- Add n days (modulo 7) -/
def add (d : DayOfWeek) (n : Nat) : DayOfWeek :=
  ofFin ⟨(d.toFin + n) % 7, by omega⟩

/-- Subtract n days (modulo 7) -/
def sub (d : DayOfWeek) (n : Nat) : DayOfWeek :=
  ofFin ⟨(d.toFin + 7 - n % 7) % 7, by omega⟩

end DayOfWeek

/-- Check if a year is a leap year in the Gregorian calendar -/
def isLeapYear (year : Nat) : Bool :=
  year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)

/-- Century anchor day computation.
  1700: Sunday, 1800: Friday, 1900: Wednesday, 2000: Tuesday, 2100: Sunday.
  Formula: (5 * (c % 4) + 2) % 7 where c = year / 100 -/
def centuryAnchor (year : Nat) : DayOfWeek :=
  let c := year / 100
  DayOfWeek.ofFin ⟨(5 * (c % 4) + 2) % 7, by omega⟩

/-- Conway's doomsday for a given year.
  doomsday = centuryAnchor + (yy / 12) + (yy % 12) + ((yy % 12) / 4)
  where yy = year % 100 -/
def doomsday (year : Nat) : DayOfWeek :=
  let yy := year % 100
  let a := yy / 12
  let b := yy % 12
  let c := b / 4
  DayOfWeek.add (centuryAnchor year) (a + b + c)

/-- The doomsday date (day of month) for each month.
  January: 3 (non-leap) or 4 (leap)
  February: 28 (non-leap) or 29 (leap)
  March: 7, April: 4, May: 9, June: 6, July: 11, August: 8
  September: 5, October: 10, November: 7, December: 12 -/
def doomsdayDate (month year : Nat) : Nat :=
  match month with
  | 1 => if isLeapYear year then 4 else 3
  | 2 => if isLeapYear year then 29 else 28
  | 3 => 7 | 4 => 4 | 5 => 9 | 6 => 6
  | 7 => 11 | 8 => 8 | 9 => 5 | 10 => 10
  | 11 => 7 | _ => 12

/-- Compute the day of the week for any Gregorian date using Conway's Doomsday algorithm.
  1. Find the doomsday for the year
  2. Find the nearest doomsday date in the same month
  3. Count the offset (positive or negative) to the target date -/
def dayOfWeek (year month day : Nat) : DayOfWeek :=
  let dd := doomsdayDate month year
  let d := doomsday year
  if day ≥ dd then
    DayOfWeek.add d (day - dd)
  else
    DayOfWeek.sub d (dd - day)

-- Conway passed away on Saturday, April 11, 2020
#eval dayOfWeek 2020 4 11 -- Saturday

-- September 11, 2001 was a Tuesday
#eval dayOfWeek 2001 9 11 -- Tuesday

-- Moon landing: July 20, 1969 was a Sunday
#eval dayOfWeek 1969 7 20 -- Sunday

-- D-Day: June 6, 1944 was a Tuesday
#eval dayOfWeek 1944 6 6 -- Tuesday

end Conway

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

/-
  `Conway.Doomsday` — L'algorithme du Doomsday de Conway
  =======================================================
  Une méthode élégante pour calculer le jour de la semaine pour toute
  date grégorienne. L'idée clé : pour une année donnée, certaines dates
  « doomsday » tombent toutes sur le même jour de la semaine :
    4/4, 6/6, 8/8, 10/10, 12/12, 5/9, 9/5, 7/11, 11/7, et le dernier
    jour de février.

  L'algorithme calcule d'abord le « jour d'ancre » pour le siècle, puis
  ajuste pour l'année dans le siècle avec :
    doomsday = ancre + année//12 + année%12 + (année%12)//4

  Conway est mort un samedi 11 avril 2020.
  #eval dayOfWeek 2020 4 11 -- Saturday

  ### i18n — convention #4980 ratifiée 2026-07-04

  Ce sous-module suit l'option A (bilingue inline FR/EN), variante pragmatique
  c.380 (deux blocs `/` top-level distincts, sans `---` interne, analogue
  c.376/c.377/c.378/c.379) : le bloc EN existant est préservé verbatim
  ci-dessus, le bloc FR miroir est ajouté juste après sans séparateur `---`.
  Convention sibling pair (`<Foo>_en.lean` à part) réservée aux modules de
  substance (cf c.374 `Astar_en.lean`) ; pour les modules de formalisation
  comme `Doomsday`, l'inline FR+EN est le bon compromis (peu de code, deux
  langues côte à côte).

  Subtilité i18n : ce module combine un namespace racine `Conway` ET un
  namespace imbriqué `Conway.DayOfWeek` (inductive days-of-week + helpers
  `toFin`/`ofFin`/`add`/`sub`). Les définitions canadiennes-anglaises
  (Conway 1973, British) restent en anglais dans les `def`/`theorem` :
  `DayOfWeek`, `centuryAnchor`, `doomsdayDate` — l'anglais est le tactic
  DSL standard de Lean/Mathlib. Seules les **docstrings `/-- ... -/`** et
  les **commentaires `-- ...`** bilingues sont ajoutées. Anti-§D byte-
  identity garanti : le namespace body est préservé bit-pour-bit.

  Cross-références : c.366 `Conway.lean` racine bilingue (MERGED),
  c.367 Grothendieck hommage (MERGED), c.373 `Knots.lean` racine bilingue,
  c.374 `Astar.lean` sibling pair, c.375 `Knots` sub-modules bilingues,
  c.376 `Knots/Invariant` bilingue 6/6 (saturation locale du lac `knot_lean`),
  c.377 `Conway/MathlibMap` bilingue (premier sous-module rollout
  `conway_lean`, PIVOT L335 strict), c.378 `Conway/LookAndSay` bilingue,
  c.379 `Conway/Fractran` bilingue (machine universelle Turing-complète),
  **c.380 `Conway/Doomsday` bilingue (algorithme Doomsday + 4 `#eval!` cas
  réels : 2020/4/11 Conway mort, 2001/9/11, 1969/7/20 Moon landing,
  1944/6/6 D-Day)**.
-/

import Mathlib.Data.Int.ModEq

namespace Conway

/-- Jours de la semaine, en partant de dimanche = 0 -/
inductive DayOfWeek where
  | sunday | monday | tuesday | wednesday | thursday | friday | saturday
  deriving Repr, BEq, DecidableEq, Inhabited

namespace DayOfWeek

/-- Convertit DayOfWeek en un Fin 7 -/
def toFin : DayOfWeek → Fin 7
  | sunday => 0 | monday => 1 | tuesday => 2 | wednesday => 3
  | thursday => 4 | friday => 5 | saturday => 6

instance : Repr DayOfWeek := ⟨fun d _ => match d with
  | sunday => "Sun" | monday => "Mon" | tuesday => "Tue"
  | wednesday => "Wed" | thursday => "Thu" | friday => "Fri" | saturday => "Sat"⟩

/-- Convertit un Fin 7 en DayOfWeek -/
def ofFin : Fin 7 → DayOfWeek
  | 0 => sunday | 1 => monday | 2 => tuesday | 3 => wednesday
  | 4 => thursday | 5 => friday | 6 => saturday
  | _ => sunday

@[simp] theorem ofFin_toFin (d : DayOfWeek) : ofFin (toFin d) = d := by
  cases d <;> rfl

/-- Ajoute n jours (modulo 7) -/
def add (d : DayOfWeek) (n : Nat) : DayOfWeek :=
  ofFin ⟨(d.toFin + n) % 7, by omega⟩

/-- Soustrait n jours (modulo 7) -/
def sub (d : DayOfWeek) (n : Nat) : DayOfWeek :=
  ofFin ⟨(d.toFin + 7 - n % 7) % 7, by omega⟩

end DayOfWeek

/-- Vérifie si une année est bissextile dans le calendrier grégorien -/
def isLeapYear (year : Nat) : Bool :=
  year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)

/-- Calcul du jour d'ancrage du siècle.
  1700 : dimanche, 1800 : vendredi, 1900 : mercredi, 2000 : mardi, 2100 : dimanche.
  Formule : (5 * (c % 4) + 2) % 7 où c = année / 100 -/
def centuryAnchor (year : Nat) : DayOfWeek :=
  let c := year / 100
  DayOfWeek.ofFin ⟨(5 * (c % 4) + 2) % 7, by omega⟩

/-- Doomsday de Conway pour une année donnée.
  doomsday = centuryAnchor + (yy / 12) + (yy % 12) + ((yy % 12) / 4)
  où yy = année % 100 -/
def doomsday (year : Nat) : DayOfWeek :=
  let yy := year % 100
  let a := yy / 12
  let b := yy % 12
  let c := b / 4
  DayOfWeek.add (centuryAnchor year) (a + b + c)

/-- La date doomsday (jour du mois) pour chaque mois.
  Janvier : 3 (non bissextile) ou 4 (bissextile)
  Février : 28 (non bissextile) ou 29 (bissextile)
  Mars : 7, Avril : 4, Mai : 9, Juin : 6, Juillet : 11, Août : 8
  Septembre : 5, Octobre : 10, Novembre : 7, Décembre : 12 -/
def doomsdayDate (month year : Nat) : Nat :=
  match month with
  | 1 => if isLeapYear year then 4 else 3
  | 2 => if isLeapYear year then 29 else 28
  | 3 => 7 | 4 => 4 | 5 => 9 | 6 => 6
  | 7 => 11 | 8 => 8 | 9 => 5 | 10 => 10
  | 11 => 7 | _ => 12

/-- Calcule le jour de la semaine pour toute date grégorienne en utilisant
  l'algorithme Doomsday de Conway.
  1. Trouver le doomsday pour l'année
  2. Trouver la date doomsday la plus proche dans le même mois
  3. Compter le décalage (positif ou négatif) jusqu'à la date cible -/
def dayOfWeek (year month day : Nat) : DayOfWeek :=
  let dd := doomsdayDate month year
  let d := doomsday year
  if day ≥ dd then
    DayOfWeek.add d (day - dd)
  else
    DayOfWeek.sub d (dd - day)

-- Conway est mort un samedi 11 avril 2020
#eval dayOfWeek 2020 4 11 -- Saturday

-- Le 11 septembre 2001 était un mardi
#eval dayOfWeek 2001 9 11 -- Tuesday

-- Alunissage : le 20 juillet 1969 était un dimanche
#eval dayOfWeek 1969 7 20 -- Sunday

-- Jour J : le 6 juin 1944 était un mardi
#eval dayOfWeek 1944 6 6 -- Tuesday

end Conway

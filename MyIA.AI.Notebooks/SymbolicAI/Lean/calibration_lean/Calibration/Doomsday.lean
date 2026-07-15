/-
  Cible de calibration : algorithme du Doomsday de Conway
  ========================================================

  Théorèmes de calibration pour l'algorithme du Doomsday de Conway, basés sur les
  définitions de conway_lean/Conway/Doomsday.lean.

  Chemins du harnais exercés :
  - Cible B (leap_year_2000, leap_year_1900) : validation P1 — decide simple.
  - Cible F (conway_death_day) : P2 — calcul multi-étapes avec arithmétique modulaire.
    Difficulté moyenne, exerce le diagnostic d'erreur distante.
  - Cible I (dayOfWeek_period_7) : P1 — requiert un raisonnement d'arithmétique modulaire.
    Preuve non triviale de type inductif mais bornée.
-/
import Mathlib.Tactic

/-! ## Définitions du Doomsday (autonomes, reflètent Conway/Doomsday.lean) -/

/-- Jours de la semaine, à partir de dimanche = 0. -/
inductive DayOfWeek where
  | sunday | monday | tuesday | wednesday | thursday | friday | saturday
  deriving Repr, BEq, DecidableEq, Inhabited

namespace DayOfWeek

/-- Convertit un DayOfWeek en Fin 7. -/
def toFin : DayOfWeek → Fin 7
  | sunday => 0 | monday => 1 | tuesday => 2 | wednesday => 3
  | thursday => 4 | friday => 5 | saturday => 6

/-- Convertit un Fin 7 en DayOfWeek. -/
def ofFin : Fin 7 → DayOfWeek
  | 0 => sunday | 1 => monday | 2 => tuesday | 3 => wednesday
  | 4 => thursday | 5 => friday | 6 => saturday
  | _ => sunday

/-- Ajoute n jours (modulo 7). -/
def add (d : DayOfWeek) (n : Nat) : DayOfWeek :=
  ofFin ⟨(d.toFin + n) % 7, by omega⟩

/-- Soustrait n jours (modulo 7). -/
def sub (d : DayOfWeek) (n : Nat) : DayOfWeek :=
  ofFin ⟨(d.toFin + 7 - n % 7) % 7, by omega⟩

end DayOfWeek

/-- Teste si une année est bissextile dans le calendrier grégorien. -/
def isLeapYear (year : Nat) : Bool :=
  year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)

/-- Calcul du jour d'ancrage du siècle. -/
def centuryAnchor (year : Nat) : DayOfWeek :=
  let c := year / 100
  DayOfWeek.ofFin ⟨(5 * (c % 4) + 2) % 7, by omega⟩

/-- Le Doomsday de Conway pour une année donnée. -/
def doomsday (year : Nat) : DayOfWeek :=
  let yy := year % 100
  let a := yy / 12
  let b := yy % 12
  let c := b / 4
  DayOfWeek.add (centuryAnchor year) (a + b + c)

/-- La date Doomsday pour chaque mois. -/
def doomsdayDate (month year : Nat) : Nat :=
  match month with
  | 1 => if isLeapYear year then 4 else 3
  | 2 => if isLeapYear year then 29 else 28
  | 3 => 7 | 4 => 4 | 5 => 9 | 6 => 6
  | 7 => 11 | 8 => 8 | 9 => 5 | 10 => 10
  | 11 => 7 | _ => 12

/-- Calcule le jour de la semaine pour toute date grégorienne. -/
def dayOfWeek (year month day : Nat) : DayOfWeek :=
  let dd := doomsdayDate month year
  let d := doomsday year
  if day ≥ dd then
    DayOfWeek.add d (day - dd)
  else
    DayOfWeek.sub d (dd - day)

/-! ## Cibles de calibration -/

/-- Cible B.1 (validation P1) : l'année 2000 est bissextile.
    decide simple — valide que la définition isLeapYear fonctionne.
    Itérations attendues : 1-2. -/
theorem leap_year_2000 : isLeapYear 2000 = true := by
  unfold isLeapYear
  decide

/-- Cible B.2 (validation P1) : l'année 1900 n'est PAS bissextile (divisible par 100 mais pas 400).
    decide simple — valide le cas limite dans isLeapYear.
    Itérations attendues : 1-2. -/
theorem leap_year_1900 : isLeapYear 1900 = false := by
  unfold isLeapYear
  decide

/-- Cible B.3 (validation P1) : l'année 2024 est bissextile.
    Autre contrôle de cohérence pour les dates récentes.
    Itérations attendues : 1-2. -/
theorem leap_year_2024 : isLeapYear 2024 = true := by
  unfold isLeapYear
  decide

/-- Cible F (P2) : Conway est décédé le samedi 11 avril 2020.
    Cela exerce le calcul complet de l'algorithme du Doomsday :
    centuryAnchor → doomsday → dayOfWeek.
    Difficulté moyenne : calcul multi-étapes avec arithmétique modulaire.
    Le prouveur doit dérouler 4-5 définitions et gérer l'arithmétique Fin 7.
    Itérations attendues : 5-8 (chaîne d'unfold → arithmétique → decide). -/
theorem conway_death_day : dayOfWeek 2020 4 11 = DayOfWeek.saturday := by
  unfold dayOfWeek doomsdayDate doomsday centuryAnchor DayOfWeek.add DayOfWeek.sub
  simp [DayOfWeek.toFin, DayOfWeek.ofFin]

/-- Cible F.2 (P2) : le 11 septembre 2001 était un mardi.
    Deuxième validation de date historique, exerce le même chemin que F.
    Itérations attendues : 5-8. -/
theorem sep11_day : dayOfWeek 2001 9 11 = DayOfWeek.tuesday := by
  unfold dayOfWeek doomsdayDate doomsday centuryAnchor DayOfWeek.add DayOfWeek.sub
  simp [DayOfWeek.toFin, DayOfWeek.ofFin]

/-- Cible I (cœur P1) : ajouter 7 jours ramène au même jour de la semaine.
    Cela exerce le raisonnement d'arithmétique modulaire.
    Le prouveur doit comprendre que Fin 7 + 7 % 7 = l'original.
    Itérations attendues : 4-7 (unfold add → arithmétique modulaire → omega/decide).
    Note : DayOfWeek autonome ici, sans import depuis Conway/Doomsday. -/
theorem dayOfWeek_add_seven (d : DayOfWeek) : DayOfWeek.add d 7 = d := by
  cases d
  · unfold DayOfWeek.add DayOfWeek.toFin DayOfWeek.ofFin; decide
  · unfold DayOfWeek.add DayOfWeek.toFin DayOfWeek.ofFin; decide
  · unfold DayOfWeek.add DayOfWeek.toFin DayOfWeek.ofFin; decide
  · unfold DayOfWeek.add DayOfWeek.toFin DayOfWeek.ofFin; decide
  · unfold DayOfWeek.add DayOfWeek.toFin DayOfWeek.ofFin; decide
  · unfold DayOfWeek.add DayOfWeek.toFin DayOfWeek.ofFin; decide
  · unfold DayOfWeek.add DayOfWeek.toFin DayOfWeek.ofFin; decide

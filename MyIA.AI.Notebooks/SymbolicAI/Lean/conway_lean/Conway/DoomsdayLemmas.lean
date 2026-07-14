/-
Voie calibration Conway — lemmes Doomsday (P2 : évaluation fermée vs décomposition par cas)
John Horton Conway (1937-2020).

Ces lemmes se construisent par-dessus `Conway.Doomsday` (l'algorithme du jour de la semaine).
Ils forment une échelle de CALIBRATION DU HARNÈS pour l'Epic de co-évolution du prouveur (#1453) :

  - `isLeapYear_2000` / `isLeapYear_1900` / `isLeapYear_2024`
        : évaluations booléennes fermées            -> decide / native_decide   (facile)
  - `dayOfWeek_conway_death`
        : l'hommage — Conway est décédé le sam. 2020-04-11 ; évaluation fermée de l'algorithme
        : un `rfl` naïf peut caler sur l'arithmétique `%` -> decide / native_decide  (facile-moyen)
  - `dayOfWeek_add_seven`
        : NON fermé (`d` libre) ; un `decide` naïf échoue car `d` est une variable.
          Le Directeur doit DÉCOMPOSER : `cases d <;> rfl`.                    (moyen)

Tous les `sorry` ont été éliminés (Epic #1453, #1651).

Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier est **FR canonique**,
avec son miroir anglais dans le fichier sibling `DoomsdayLemmas_en.lean` (modèle sibling pair
ratifié 2026-07-04, cf `code-style.md` §Lean i18n). Les énoncés de théorèmes, les tactiques
Lean, les noms de lemmes et les références Mathlib restent en anglais (compat Mathlib 4) ;
seules les docstrings de théorème et ce bloc d'en-tête diffèrent entre les deux fichiers.
-/

import Conway.Doomsday

namespace Conway

/-- CALIBRATION (decide) : 2000 est bissextile (divisible par 400). -/
theorem isLeapYear_2000 : isLeapYear 2000 = true := by
  native_decide

/-- CALIBRATION (decide) : 1900 n'est PAS bissextile (divisible par 100, pas par 400). -/
theorem isLeapYear_1900 : isLeapYear 1900 = false := by
  native_decide

/-- CALIBRATION (decide) : 2024 est bissextile. -/
theorem isLeapYear_2024 : isLeapYear 2024 = true := by
  native_decide

/-- HOMMAGE + CALIBRATION : John Conway est décédé le samedi 11 avril 2020.
    Évaluation fermée de l'algorithme Doomsday. -/
theorem dayOfWeek_conway_death : dayOfWeek 2020 4 11 = DayOfWeek.saturday := by
  native_decide

/-- CALIBRATION (décomposition par cas) : ajouter une semaine complète est l'identité.
    Un `decide` naïf échoue (`d` est libre) ; nécessite `cases d`. -/
theorem dayOfWeek_add_seven (d : DayOfWeek) : DayOfWeek.add d 7 = d := by
  cases d <;> rfl

end Conway

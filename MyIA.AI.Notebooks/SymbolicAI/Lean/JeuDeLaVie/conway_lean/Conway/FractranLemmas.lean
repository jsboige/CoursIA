/-
FRACTRAN de Conway — lemmes compagnons
John Horton Conway (1937-2020)

Ces lemmes se construisent par-dessus `Conway.Fractran` (la machine universelle FRACTRAN)
et forment une échelle de calibration sur sa sémantique step/run, en parallèle des fichiers
compagnons `Conway.DoomsdayLemmas` et `Conway.LookAndSayLemmas` déjà migrés vers sibling pair.
Jusqu'ici `Fractran.lean` était le seul module Conway avec des définitions mais sans
théorèmes compagnons.

  - `fractranStep_empty` / `fractranRun_zero`
        : cas de base définitionnellement vrais (halt sur programme vide ; exécution 0-pas) -> rfl
  - `fracMulNat_den_one`
        : une fraction num/1 est un multiplicateur entier, donc toujours applicable       -> simp + omega
  - `fracMulNat_six_halves` / `fracMulNat_seven_not_halves`
        : vérifications fermées d'applicabilité (6 divisible par 2 ; 7 non)               -> decide
  - `fractranStep_single_two_to_three` / `fractranStep_single_halts_at_three`
        : le programme à une fraction {3/2} envoie 2 → 3, puis s'arrête à 3              -> decide
  - `fractranRun_single_trace`
        : la trace bornée 2 → 3 (arrêt) de {3/2}                                          -> decide

Toutes les preuves sont déchargées sans stubs. Ces faits sont en Lean 4 noyau pur (pas de
Mathlib nécessaire) — les step/run FRACTRAN sont des récursions structurelles sur Nat/List,
décidables sur entrées concrètes. Voir #2162 (famille Conway).

Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier est **FR canonique**,
avec son miroir anglais dans le fichier sibling `FractranLemmas_en.lean` (modèle sibling pair
ratifié 2026-07-04, cf `code-style.md` §Lean i18n). Les énoncés de théorèmes, les tactiques
Lean, les noms de lemmes et les références Mathlib restent en anglais (compat Mathlib 4) ;
seules les docstrings de théorème et ce bloc d'en-tête diffèrent entre les deux fichiers.
-/

import Conway.Fractran

namespace Conway

/-- BASE (rfl) : un programme FRACTRAN vide s'arrête immédiatement — aucune fraction ne s'applique. -/
theorem fractranStep_empty (n : Nat) : fractranStep [] n = none := rfl

/-- BASE (rfl) : exécuter un programme quelconque pour 0 pas donne juste la valeur de départ. -/
theorem fractranRun_zero (prog : List Frac) (n : Nat) : fractranRun prog n 0 = [n] := rfl

/-- PAS (simp+omega) : une fraction num/1 est un multiplicateur entier, donc toujours
    applicable (`n * num` est divisible par 1 trivialement). -/
theorem fracMulNat_den_one (n : Nat) (f : Frac) (h : f.den = 1) :
    fracMulNat n f = true := by
  simp [fracMulNat, h, Nat.mod_one]

/-- CALIBRATION (decide) : 6 est divisible par 2, donc la fraction {3/2} s'applique à 6. -/
theorem fracMulNat_six_halves : fracMulNat 6 (frac 3 2 (by omega)) = true := by
  decide

/-- CALIBRATION (decide) : 7 n'est PAS divisible par 2, donc {3/2} ne s'applique pas à 7. -/
theorem fracMulNat_seven_not_halves : fracMulNat 7 (frac 3 2 (by omega)) = false := by
  decide

/-- PAS (decide) : le programme à une fraction {3/2} envoie 2 → 3 (2 · 3 / 2 = 3). -/
theorem fractranStep_single_two_to_three :
    fractranStep [frac 3 2 (by omega)] 2 = some 3 := by
  decide

/-- ARRÊT (decide) : le programme à une fraction {3/2} s'arrête à 3 (3 · 3 = 9 n'est
    pas divisible par 2, donc aucune fraction ne s'applique). -/
theorem fractranStep_single_halts_at_three :
    fractranStep [frac 3 2 (by omega)] 3 = none := by
  decide

/-- EXÉCUTION (decide) : exécuter {3/2} depuis 2 pendant 5 pas donne la trace [2, 3]
    (2 → 3, puis arrêt à 3). -/
theorem fractranRun_single_trace :
    fractranRun [frac 3 2 (by omega)] 2 5 = [2, 3] := by
  decide

end Conway

/-
Voie calibration Conway — lemmes Look-and-Say (P3 : éval-vs-lemme + induction structurelle)
John Horton Conway (1937-2020).

Ces lemmes se construisent par-dessus `Conway.LookAndSay`. Ils forment le BARREAU le plus
DIFFICILE de l'échelle de calibration du harnès de co-évolution du prouveur (Epic #1453) :

  - `digitsToNat_example` : évaluation fermée d'une liste  -> decide / rfl       (facile)
  - `lookAndSay_4`        : résultat de récursion bien fondée -> native_decide    (moyen :
        un `rfl`/`decide` naïf peut ne pas réduire la récursion WF ; le prouveur peut être
        tenté d'invoquer un lemme simp inexistant — exerce le chemin blocklist phantom-id P3)
  - `digitsToNat_natToDigits` : aller-retour sur les chiffres décimaux.
        Nécessite réellement une induction structurelle calée sur `natToDigits` (récursion sur
        `n / 10`), plus un lemme d'append pour `digitsToNat`. C'est la cible de stress de
        décomposition stratégique — le Directeur ne doit PAS s'attendre à une tactique unique. (dur)

Les trous de preuve dans le échafaudage de calibration original sont intentionnels,
pas des régressions (Epic #1453).

Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier est **FR canonique**,
avec son miroir anglais dans le fichier sibling `LookAndSayLemmas_en.lean` (modèle sibling pair
ratifié 2026-07-04, cf `code-style.md` §Lean i18n). Les énoncés de théorèmes, les tactiques
Lean, les noms de lemmes et les références Mathlib restent en anglais (compat Mathlib 4) ;
seules les docstrings de théorème et ce bloc d'en-tête diffèrent entre les deux fichiers.
-/

import Conway.LookAndSay

namespace Conway

/-- CALIBRATION (decide) : [1,2,1,1] se décode en 1211. -/
theorem digitsToNat_example : digitsToNat [1, 2, 1, 1] = 1211 := by
  native_decide

/-- CALIBRATION (native_decide) : le 5e terme look-and-say (indexé depuis 0) est 111221. -/
theorem lookAndSay_4 : lookAndSay 4 = 111221 := by
  native_decide

/-- CALIBRATION (dur, induction structurelle) : décoder les chiffres décimaux de `n`
    retrouve `n`. Nécessite une induction calée sur la récursion de `natToDigits` sur `n / 10`. -/
theorem digitsToNat_natToDigits (n : Nat) : digitsToNat (natToDigits n) = n := by
  have h_append : ∀ (xs : List Nat) (d : Nat),
      digitsToNat (xs ++ [d]) = digitsToNat xs * 10 + d := by
    intro xs d
    induction xs with
    | nil =>
        simp [digitsToNat]
    | cons x xs ih =>
        simp [digitsToNat, ih, List.length_append, Nat.pow_succ, Nat.mul_add,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_assoc]
        simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  exact Nat.strongRecOn n (fun n ih => by
    unfold natToDigits
    by_cases hn : n = 0
    · simp [hn, digitsToNat]
    · simp [hn]
      rw [h_append]
      have hlt : n / 10 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide : 1 < 10)
      rw [ih (n / 10) hlt]
      omega)

end Conway

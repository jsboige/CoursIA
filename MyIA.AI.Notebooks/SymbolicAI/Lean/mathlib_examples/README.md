# Exemples Mathlib

Exemples d'utilisation basique de Mathlib pour la série SymbolicAI/Lean.

**Mathlib** est la bibliothèque mathématique unifiée de Lean 4 : un corpus
communautaire de définitions, de lemmes et — surtout pour l'apprenant — de
**tactiques d'automatisation**. Ce module minimal est le « smoke test » de
l'installation Mathlib : il ferme quatre buts représentatifs avec les tactiques
du quotidien (`ring`, `linarith`, `omega`, `rw`), confirmant que
`lake build MathLibExamples` compile contre une Mathlib fonctionnelle. C'est
aussi une première prise en main des automatiseurs de Lean avant d'aborder les
projets plus ambitieux (`calibration_lean`, `conway_lean`, `sensitivity_lean`).

## Statut

- **Toolchain** : v4.31.0-rc1
- **Compte de sorry** : 0
- **Build** : `lake build MathLibExamples` -- SUCCESS
- **Dépendances** : Mathlib4
- **Couverture i18n (EPIC #4980)** : lake entièrement bilingue FR/EN — **1 module .lean FR canonique** + **1 sibling `Basic_en.lean` miroir sur `main`** (PR #6664, 2026-07-15). Convention EPIC #4980 Option A : docstrings `/-- ... -/` et commentaires `-- ...` diffèrent entre FR et EN, signatures et preuves byte-identiques — vérifié par `scripts/lean/check_i18n_siblings.py` : **6/6 paires byte-identical, 0 drift, 0 orphan** (les 6 incluent `examples/` siblings et ce module).

## Modules

| Fichier | `_en` | sorry | Description |
|---------|-------|-------|-------------|
| `MathLibExamples/Basic.lean` | `MathLibExamples/Basic_en.lean` | 0 | Patterns et exemples d'utilisation basique de Mathlib |

## Résultats clés

- Illustre les tactiques Mathlib courantes et les schémas de preuve
- Sert de référence aux étudiants apprenant Lean 4 avec Mathlib

## Concepts clés

Les quatre exemples de [`MathLibExamples/Basic.lean`](MathLibExamples/Basic.lean)
introduisent les automatiseurs les plus utilisés en Lean 4 :

| Tactique | Rôle | Exemple `Basic.lean` |
|----------|------|----------------------|
| `ring` | Identités d'anneau commutatif (développer / factoriser) | `(a + b)^2 = a^2 + 2*a*b + b^2` sur `ℤ` |
| `linarith` | Inégalités linéaires par combinaison (ici sur `ℚ`) | `x ≤ 3*y ∧ y ≤ 1 → x ≤ 3` |
| `omega` | Arithmétique de Presburger sur `ℕ`/`ℤ` (Lean core depuis v4.30) | `n < n + 1` sur `ℕ` |
| `rw` + `ring` | Substituer des égalités d'hypothèses, puis clôture algébrique | `a = b ∧ b = c → a + a = 2*c` sur `ℤ` |

Ces quatre tactiques couvrent une large part des buts « calculatoires »
rencontrés en pratique : `ring` pour l'algèbre, `linarith` et `omega` pour les
inégalités et l'arithmétique entière, `rw` pour réécrire par égalité
d'hypothèses. Savoir laquelle invoquer est la première compétence tactique en
Lean, et ce module est le terrain d'entraînement minimal pour l'acquérir.

## Notes

- Compagnon du notebook `Lean-6-Mathlib-Essentials.ipynb`
- Partie de la série pédagogique SymbolicAI/Lean

## Conclusion

Un **module de référence** minimal de schémas d'utilisation basique de Mathlib
(`MathLibExamples/Basic.lean`, 0 `sorry`, `lake build MathLibExamples` SUCCESS),
servant de compagnon côté Lean au notebook `Lean-6-Mathlib-Essentials.ipynb`.
Il est volontairement minimal : un point de départ pour les étudiants, pas un
aperçu exhaustif.

### Où aller ensuite

- **Notebook** : `Lean-6-Mathlib-Essentials.ipynb` — le compagnon pédagogique.
- **Projets Lean plus complets** : [`calibration_lean/`](../calibration_lean/),
  [`conway_lean/`](../conway_lean/), [`sensitivity_lean/`](../sensitivity_lean/)
  — projets Lean de production bâtis sur Mathlib.

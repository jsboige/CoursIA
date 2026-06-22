# Exemples Mathlib

Exemples d'utilisation basique de Mathlib pour la série SymbolicAI/Lean.

## Statut

- **Toolchain** : v4.27.0
- **Compte de sorry** : 0
- **Build** : `lake build MathLibExamples` -- SUCCESS
- **Dépendances** : Mathlib4

## Modules

| Fichier | sorry | Description |
|---------|-------|-------------|
| `MathLibExamples/Basic.lean` | 0 | Patterns et exemples d'utilisation basique de Mathlib |

## Résultats clés

- Illustre les tactiques Mathlib courantes et les schémas de preuve
- Sert de référence aux étudiants apprenant Lean 4 avec Mathlib

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

# Exemples Lean

Fichiers `.lean` autonomes à usage pédagogique, exécutés via le kernel Jupyter
`lean4-wsl`.

## Statut

- **Type** : Fichiers autonomes (pas de lakefile — exécutés cellule par cellule via le kernel Jupyter)
- **Compte de sorry** : 2 (dans `llm_assisted_proof.lean` — exemple pédagogique intentionnel)

## Fichiers

| Fichier | sorry | Description |
|---------|-------|-------------|
| `basic_logic.lean` | 0 | Fondements de la logique propositionnelle |
| `llm_assisted_proof.lean` | 2 | Démonstration de preuve assistée par LLM (sorry intentionnel) |
| `mathlib_examples.lean` | 0 | Exemples de tactiques Mathlib |
| `quantifiers.lean` | 0 | Schémas de raisonnement sur les quantificateurs |
| `tactics_demo.lean` | 0 | Vitrine des tactiques Lean 4 |

## Notes

- Ces fichiers ne sont **pas** un projet Lake — ils sont exécutés cellule par cellule via le kernel Jupyter `lean4-wsl`
- Les 2 `sorry` dans `llm_assisted_proof.lean` sont **intentionnels** : ils illustrent le flux de preuve assistée par LLM, où le prouveur laisse des marqueurs de substitution
- Compagnon de la série de notebooks d'introduction à Lean (Lean-1 à Lean-5)

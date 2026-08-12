# Exemples Lean

Fichiers `.lean` autonomes à usage pédagogique, exécutés via le kernel Jupyter
`lean4-wsl`.

## Statut

- **Type** : Fichiers autonomes (pas de lakefile — exécutés cellule par cellule via le kernel Jupyter)
- **Compte de sorry** : 2 (dans `llm_assisted_proof.lean` — exemple pédagogique intentionnel)
- **Couverture i18n (EPIC #4980)** : lake entièrement bilingue FR/EN — **5 modules .lean FR canonique** + **5 siblings `*_en.lean` miroirs sur `main`** (`basic_logic_en.lean`, `llm_assisted_proof_en.lean`, `mathlib_examples_en.lean`, `quantifiers_en.lean`, `tactics_demo_en.lean`). Convention EPIC #4980 Option A : docstrings `/-- ... -/` et commentaires `-- ...` diffèrent entre FR et EN, signatures et preuves byte-identiques — vérifié par `scripts/lean/check_i18n_siblings.py` : **6/6 paires byte-identical, 0 drift, 0 orphan**.

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

## Conclusion

Les cinq fichiers de ce répertoire tracent une **progression d'apprentissage**
des fondamentaux de Lean 4 : la **logique propositionnelle** (`basic_logic`) et
le **raisonnement quantifié** (`quantifiers`) posent le langage ;
`tactics_demo` expose la boîte à outils tactique (`intro` / `apply` / `rw` /
`simp` / `decide`) ; `mathlib_examples` montre comment Mathlib automatise le
calcul (`ring` / `linarith` / `omega`) ; et `llm_assisted_proof` ouvre sur la
**preuve assistée par LLM**, où les 2 `sorry` intentionnels matérialisent les
buts qu'un prouveur doit clore.

L'exécution se fait **cellule par cellule** via le kernel Jupyter `lean4-wsl`,
sans projet Lake — c'est le terrain d'expérimentation rapide de la série
d'introduction, par contraste avec les projets Lake complets
([`../calibration_lean/`](../calibration_lean/),
[`../conway_lean/`](../conway_lean/),
[`../sensitivity_lean/`](../sensitivity_lean/)) qui structurent des preuves
volumineuses.

### Où aller ensuite

- **Notebooks d'introduction** : [`../Lean-1-Setup.ipynb`](../Lean-1-Setup.ipynb) — le cours guidé (Lean-1 à Lean-5) que ces fichiers illustrent.
- **Mathlib en action** : [`../mathlib_examples/`](../mathlib_examples/) (projet Lake compagnon).
- **Preuve assistée par LLM** : `llm_assisted_proof.lean` ici est l'amorce ; le harnais multi-agents [`../agent_tests/prover/`](../agent_tests/prover/) en est la version production.

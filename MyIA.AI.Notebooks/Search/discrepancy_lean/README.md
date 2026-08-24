# discrepancy_lean — discrépance combinatoire

Lake Lean 4 (Mathlib) de formalisation de la **discrépance combinatoire** :
colorer en `±1` les éléments d'un système d'ensembles de degré `≤ k` en
minimisant la pire somme colorée `‖Ax‖∞`. Suivi : issue
[#12823](https://github.com/jsboige/CoursIA/issues/12823). Paper de
référence : Bansal–Jiang 2025, [arXiv:2508.03961](https://arxiv.org/abs/2508.03961)
— Beck-Fiala et Komlós au-delà de Banaszczyk, par découplage via
indépendance spectrale affine.

**Première formalisation du sujet** ni dans le dépôt ni dans Mathlib
(vérifié 2026-08-24 : `beck.?fiala|banaszczyk|komlos` = 0 hit).

## Désambiguïsation (une ligne)

« Discrepancy » dans [Search-13](../Part3-Advanced/Search-13-LimitedDiscrepancySearch.ipynb)
= *Limited Discrepancy Search* de Harvey & Ginsberg (choix non heuristiques
dans un arbre de recherche) — **aucun rapport** avec les sommes signées
formalisées ici.

## Structure

| Fichier | Contenu |
|---------|---------|
| `Discrepancy/Basic.lean` | définitions (`IsColoring`, `discrepancy`, `degree`, `maxDegree`), 3 lemmes élémentaires, `BeckFialaConjecture` (`O(√k)`), cible `BeckFialaClassic` (`disc ≤ 2k − 1`) |
| `Discrepancy/Komlos.lean` | `KomlosConjecture` (`O(1)`, colonnes unitaires), `BansalJiangLargeDegree` (`k ≥ log² n`), `KomlosBansalJiangWeak` (forme concrète affaiblie) |
| `Discrepancy.lean` | agrégateur racine |
| `Discrepancy/Basic_en.lean`, `Discrepancy/Komlos_en.lean`, `Discrepancy_en.lean` | siblings EN (i18n #4980) : docstrings traduites, signatures/preuves byte-identiques |

État des preuves et découpage en boutes `b1..b4` (la « noix » Beck–Fiala
classique, grignotée par petits bôuts multi-cycles) :
[FORMAL_STATUS.md](FORMAL_STATUS.md).

## Conventions

- **0 `sorry`** ; conjectures = `def ... : Prop` nommées, jamais théorèmes
  tronqués.
- Docstrings **FR-first** (i18n #4980).
- Toolchain `leanprover/lean4:v4.32.1`, Mathlib `v4.32.1` (`520045ab`) —
  aligné sur la cohorte fleet (mutualisation #4363).

## Build

```bash
lake exe cache get   # oleans Mathlib
lake build
```

## Le fil « découplage » (pourquoi ce lake ici)

Le geste technique du papier — *découpler* des évolutions qui conspiraient —
est un motif récurrent du dépôt : reparamétrisation non centrée
[PyMC-12](../Probas/PyMC/PyMC-12-Modeles-Hierarchiques.ipynb), découplage de
Hoeffding ([`PacLearning/Hoeffding.lean`](../ML/learning_theory_lean/PacLearning/Hoeffding.lean),
réutilisé en P2 pour Erdős–Spencer), double-Q du RL, Fox-decoupling de
`knot_lean`. Ce lake en est le cinquième volume, porté à la certitude
formelle ; le grounding complet (ICT, « mesures naïves = signaux fantômes »)
vit dans le corps de l'issue #12823.

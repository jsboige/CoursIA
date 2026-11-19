# linear_lean — les marches d'Axler (Fille 3.1, Epic Origami #24838)

Lake Lean 4 portant le socle d'algèbre linéaire de *Linear Algebra Done
Right* (Sheldon Axler, 4e éd., Springer 2024), écrit en **marches `.lean`** —
l'Epic #24838 sanctionne « `.lean` quand c'est possible » tant que le seuil
de 400 issues ouvertes n'est pas repassé (veto notebooks du 2026-11-03).

## Source, licence, archivage

- **Source unique** : Axler, *Linear Algebra Done Right*, 4e éd., Springer
  2024, **CC BY-NC 4.0**, version du 30 octobre 2026. Copie archivée au
  gisement partagé : `G:\Mon Drive\MyIA\IA\Bibliographie IA\Pedagogie-Proves\`
  (règle `bibliography-hygiene` : chaque énoncé est écrit depuis la copie
  archivée, jamais de mémoire).
- **Aucune ligne recopiée** des compagnons (`rkirov/linear-algebra-done-right-lean`,
  Apache-2.0 déclaré dans son README amont ; `blanketism/Axler-Solutions`, sans
  licence déclarée) : consultés uniquement pour comparer les progressions, jamais vendues.
- Le lake distille **l'ordre** d'Axler (déterminants rejetés au chapitre 9),
  pas son texte : les définitions sont portées par les organes natifs de
  Mathlib, déclarées et citées.

## Structure (marche 1 : chapitres 1-2)

| Module | Contenu | Numéros Axler |
|---|---|---|
| `Linear/EspacesVectoriels.lean` | scalaires et vecteur nul, sommes, sommes directes | 1.31, 1.32, 1.44, 1.45 |
| `Linear/DimensionFinie.lean` | familles libres, bases, dimension finie, Grassmann | 2.19, 2.22, 2.28, 2.33, 2.35, 2.37-2.43 |
| `Linear.lean` | agrégateur racine | — |

Les marches suivantes (chapitres 3-9 : applications linéaires,
polynômes, valeurs propres, produits scalaires, opérateurs, formes
bilinéaires, déterminants) sont extraites verbatim dans `.tmp/` du dépôt
principal (headers + exercices par chapitre) et attendent leurs issues.

## Correspondance Axler → Mathlib

| Axler | Mathlib |
|---|---|
| 𝔽 = ℝ ou ℂ (1.6) | `K` corps quelconque |
| espace vectoriel (1.20) | `AddCommGroup V` + `Module K V` |
| sous-espace (1.33) | `Submodule K V` |
| somme de sous-espaces (1.36) | `U ⊔ W` (`Submodule.mem_sup`) |
| somme directe (1.41) | `IsCompl U W` |
| envergement (2.4) | `span` |
| famille libre (2.15) | `LinearIndependent` |
| base (2.26) | `Basis` |
| dimension (2.35) | `finrank` |

Chaque théorème du lake cite son numéro Axler en docstring et délègue à
l'organe Mathlib (`smul_zero`, `Submodule.exists_isCompl`,
`finrank_span_eq_card`,
`Submodule.eq_top_of_finrank_eq`, `Submodule.finrank_sup_add_finrank_inf_eq`,
…). Seule exception de méthode : 2.42 est prouvé par l'argument d'application
linéaire (rang + noyau) qui annonce le chapitre 3 — signalé dans sa
docstring.

## sorry

Les **exercices** sont des sorry-cibles documentées (mandat user 2026-11-03) :
énoncés sous numéro Axler, docstring `Cible prover : <niveau> — <tenté>`,
jamais certifiées.

- `exercice_1B_3` (existence + unicité d'un antécédent par dilatation) ;
- `exercice_2A_13` (familles translatées dépendantes) ;
- `exercice_2C_12` (dim 8 = 3 + 5, supplémentaires) ;
- `exercice_2C_13` (dim 9, deux sous-espaces de dim 5 s'intersectent).

**Compte** : 4 `sorry` distincts (mode `real`), mesuré par
`python scripts/lean/count_code_sorry.py --json` (champ
`distinct_code_sorry`) — baseline CI `4` dans `scripts/lean/ci_lakes.json`.
Les théorèmes du texte (tous les numéros ci-dessus) sont délégués ou prouvés,
zéro sorry.

## i18n

Cette tranche est **FR seule** (docstrings français, convention #4980) ;
les jumeaux `_en` sont une tranche suivante — l'absence de sibling n'est pas
un gap tant que la tranche n'est pas déclarée (organ
`scripts/lean/check_i18n_siblings.py`).

## CI

Lake déclaré dans `scripts/lean/ci_lakes.json` (`linear`,
`sorry-baseline: "4"`, `sorry-filter-mode: "real"`) et câblé dans la matrice
`lean-ci-matrix.yml` (chemins du répertoire, blocs push + PR).

## Build local

```bash
cd MyIA.AI.Notebooks/SymbolicAI/Lean/LINEAR/linear_lean
lake exe cache get   # ou copie du .lake d'un lake frère au même pin v4.33.0
lake build
```

Toolchain `leanprover/lean4:v4.33.0`, Mathlib `v4.33.0` (même pin que le
reste du parc, cf. `LEAN_INVENTORY.md`). En WSL, build **borné**
(`systemd-run --scope -p MemoryMax=…`, parallélisme bridé — mandat user
29/10) ; sous WDAC, réutiliser le `.lake` d'un lake frère binairement
compatible.

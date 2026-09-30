# Inventaire des projets Lean 4 — `SymbolicAI/Tweety`

Inventaire transverse de tous les projets de formalisation Lean 4 sous `SymbolicAI/Tweety/`.

Réconcilié le 2026-08-28 contre les pins effectifs (`lean-toolchain`, `lake-manifest.json`) et le
module-set réel du disque (issue #13366, matrice #13121 tranche 3). Comptes `sorry` mesurés avec
l'instrument canonique `scripts/lean/count_code_sorry.py --lake <root> --json` (champ
`distinct_code_sorry`), jamais `grep -c sorry`.

## Résumé

**Lakes actifs (1)** :

| Répertoire | Toolchain | sorry (production) | Modules | Statut |
|-----------|-----------|--------------------|---------|--------|
| `argumentation_lean` | v4.33.0 | 0 | `Argumentation/{Basic, Fundamental, Grounded, Characteristic, Extensions}` (5 FR + 5 `_en`) + umbrella `Argumentation.lean` | COMPLET |

---

## Par lake

### 1. argumentation_lean

**Objectif** : théorie de l'argumentation abstraite de Dung (1995) — cadres d'argumentation (AF),
les extensions canoniques (admissible, complète, grounded, preferred, stable), lemme fondamental
et fonction caractéristique, au-dessus de Mathlib.

**Toolchain** : v4.33.0 | **Dépendances** : Mathlib4

| Groupe de modules | sorry | Contenu |
|--------------|-------|---------|
| `Argumentation/Basic` (FR + `_en`) | 0 | conflit et défense : `conflictFree`, `defends`, `defendedBy`, `conflictFree_empty` |
| `Argumentation/Fundamental` (FR + `_en`) | 0 | lemme fondamental : `fundamental_lemma` (+ variantes `defends`/`defends_self`) |
| `Argumentation/Grounded` (FR + `_en`) | 0 | sémantique grounded : `grounded_fixed`, `grounded_defends_iff_mem`, `grounded_least_complete`, `F_preserves_conflictFree` |
| `Argumentation/Characteristic` (FR + `_en`) | 0 | fonction caractéristique : `characteristic`, `mem_characteristic_iff`, `characteristic_eq_defendedBy` |
| `Argumentation/Extensions` (FR + `_en`) | 0 | hiérarchie des extensions : `Admissible`, `Complete`, `grounded`, `Preferred` |
| `Argumentation.lean` (umbrella) | 0 | imports agrégés du lake |

**Câblage CI** : matrice [`lean-ci-matrix.yml`](../../../.github/workflows/lean-ci-matrix.yml)
(clé `argumentation` dans `scripts/lean/ci_lakes.json` ; push `main`, paths `MyIA.AI.Notebooks/SymbolicAI/Tweety/argumentation_lean/**.lean` + `lakefile.*`), pipeline `real`.

**Notebook câblé** : `Tweety-5b-Lean-Argumentation.ipynb` (kernel `lean4-wsl`, importe
`Argumentation.*`) — companion conceptuel Tweety-5.

**Suivi** : Epic [#4038](https://github.com/jsboige/CoursIA/issues/4038) /
[#4046](https://github.com/jsboige/CoursIA/issues/4046) (roadmap Lean série Tweety).

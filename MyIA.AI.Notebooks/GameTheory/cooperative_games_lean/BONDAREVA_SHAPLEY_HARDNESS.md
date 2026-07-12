# Bondareva-Shapley (sens indirect) — enquête sur la difficulté

**Agent :** po-2025 | **Date :** 2026-05-12 | **Cycle :** 28 piste A

## Verdict : PARTIELLEMENT_PRUVABLE (reclassé depuis HONEST_UNPROVABLE)

Le `sorry` `bondareva_shapley_backward` à `Basic.lean:234` avait été classé
`HONEST_UNPROVABLE` au motif que « la dualité LP / le lemme de Farkas manque
dans Mathlib ». Cette évaluation est **partiellement obsolète** : le lemme de
Farkas EST disponible depuis 2025 (Dillies/Yang). La dualité forte LP reste
absente mais n'est PAS requise pour la preuve.

## Ce qui a changé dans Mathlib

Le commentaire de `Basic.lean:221-224` affirmait que Mathlab ne fournit pas :

| Élément présenté comme manquant | Statut réel (Mathlib v4.28-rc1) |
| --- | --- |
| Théorème de dualité LP | Toujours absent (TODO dans `Cone.Basic`) |
| Lemme de Farkas utilisable sur `Finset N → R` | **Disponible** sous le nom `ProperCone.hyperplane_separation` |
| `Polyhedral.cone_of_nonempty` | Toujours absent |

**Module clé :** `Mathlib.Analysis.Convex.Cone.Dual` (Copyright 2025 Yaël
Dillies, Andrew Yang)

Fournit :

- `ProperCone.dual` — cône dual pour un appariement parfait continu ;
- `ProperCone.hyperplane_separation` — lemme de Farkas (sépare un convexe
  compact d'un cône propre) ;
- `ProperCone.hyperplane_separation_point` — version ponctuelle du lemme de
  Farkas ;
- `ProperCone.dual_dual_flip` — le bidual d'un cône propre est lui-même.

## Stratégie de preuve (basée sur Farkas, sans dualité LP)

La preuve classique n'a PAS besoin de la dualité forte LP. Elle n'utilise que
le lemme de Farkas (théorème des alternatives).

### Étape 1 — Mise en faisabilité

Trouver `x : N → R` vérifiant :

- `∑_{i ∈ S} x i ≥ v(S)` pour toute coalition non vide `S : Finset N` ;
- `∑_i x i ≤ v(N)`.

### Étape 2 — Application de l'alternative de Farkas

Ce système est faisable si et seulement si l'alternative est infaisable :

> Pour tous `λ_S ≥ 0` et `μ ≥ 0` :
> si `∑_S λ_S · 1_{i ∈ S} = μ` pour tout `i`, alors
> `∑_S λ_S · v(S) ≤ μ · v(N)`.

### Étape 3 — Connexion avec la condition d'équilibre

En posant `w_S = λ_S / μ` (lorsque `μ > 0`), l'alternative devient :

> Pour tous poids équilibrés `w` : `∑_S w_S · v(S) ≤ v(N)`.

C'est EXACTEMENT la condition d'équilibre (balanced) du jeu.

### Étape 4 — Extraction de l'appartenance au noyau

À partir de la faisabilité : `∑_i x i ≤ v(N)` et `∑_{i ∈ N} x i ≥ v(N)`,
donc `∑_i x i = v(N)`. Combiné avec les contraintes de coalition, `x`
appartient au noyau.

## Lacune d'infrastructure : théorème des alternatives

`ProperCone.hyperplane_separation` donne Farkas sous forme de **séparation** :

```
C : ProperCone R E, K convexe compact, Disjoint K C ⇒
  ∃ f : StrongDual R E, (∀ x ∈ C, 0 ≤ f x) ∧ (∀ x ∈ K, f x < 0)
```

La preuve requiert Farkas sous forme d'**alternatives** :

```
Soit {x | A x ≥ b} admet une solution,
soit {y ≥ 0 | A^T y = 0, y · b > 0} admet une solution.
```

Pour dériver les alternatives à partir de la séparation :

1. Coder `{A x ≥ b}` comme l'image réciproque d'un cône propre par une
   application linéaire ;
2. Montrer que cette image réciproque (ou le cône associé) est un cône propre
   (fermé, pointu, convexe) ;
3. Appliquer `hyperplane_separation` pour obtenir la fonctionnelle de
   séparation ;
4. Reconvertir en formulation d'alternatives.

**En dimension finie** (`Fin n → R`), toutes les applications linéaires sont
continues, tous les sous-espaces de dimension finie sont fermés, donc les
conditions de « cône propre » sont automatiques. Mathlib fournit
`LinearMap.continuous_of_finiteDimensional` et
`Submodule.closed_of_finiteDimensional`.

## Travail estimé

| Composant | Lignes | Difficulté | Support Mathlib |
| --- | --- | --- | --- |
| Théorème des alternatives depuis la séparation | ~60-80 | DUR | `hyperplane_separation` + continuité fd |
| Système de contraintes coalition comme cône propre | ~30-50 | MOYEN | `ProperCone`, dimension finie |
| Équivalence équilibre ↔ alternative | ~20-30 | MOYEN | Algèbre `Finset`, définition d'équilibre |
| Extraction de l'appartenance au noyau | ~10-20 | FACILE | Définition du noyau, manipulation de sommes |
| **Total** | **~150-200** | **MOYEN-DUR** | |

## Recommandations

1. **Reclassifier** `bondareva_shapley_backward` de `HONEST_UNPROVABLE` à
   `WIP_HARD` (réalisable, ~150-200 lignes de lemmes préparatoires).
2. **NE PAS tenter maintenant** — 150-200 lignes d'infrastructure d'analyse
   convexe représentent un effort de plusieurs jours, mieux adapté à un
   sprint dédié.
3. **Mettre à jour `FORMAL_STATUS.md`** — passer `BLOCKED` à `WIP_HARD` avec
   la stratégie basée sur Farkas exposée ici.
4. **Prérequis :** vérifier que `Fin N → R` peut recevoir des instances
   `LocallyConvexSpace R` et `IsContPerfPair` (probable via
   `Pi.topologicalSpace`).

## Alternative : approche par jeu réduit

Une preuve inductive sur `|N|` via les jeux réduits évite Farkas entièrement
mais demande :

- Définir le jeu réduit de Davis-Maschler ;
- Prouver que le jeu réduit hérite de la propriété d'équilibre ;
- Plus d'infrastructure spécifique à la théorie des jeux.

C'est probablement PLUS de travail que l'approche Farkas puisque l'analyse
convexe de Mathlib est déjà bien développée.

## Références

- Dillies, Y., Yang, A. (2025). `Mathlib.Analysis.Convex.Cone.Dual`.
- Bondareva, O.N. (1963). « Some Applications of Linear Programming Methods to
  the Theory of Cooperative Games ».
- Shapley, L.S. (1967). « On Balanced Sets and Cores ».

---

## Convention i18n (Option A #4980 ratifiée par ai-01 le 2026-07-04)

Ce fichier est la version **français-first** ; l'original anglais est
préservé en [`BONDAREVA_SHAPLEY_HARDNESS.en.md`](BONDAREVA_SHAPLEY_HARDNESS.en.md)
pour traçabilité et future publication bilingue via le moteur Argumentum
(EPIC #1650). Les noms de lemmes Mathlib (`ProperCone.hyperplane_separation`,
`ProperCone.dual_dual_flip`, etc.), les noms de types (`TUGame`, `Coalition`,
`Core`), et les références bibliographiques restent en anglais — seule la
prose pédagogique est en français.

EPIC parent : #4980 (harmonisation i18n Lean). Part of #4208 (open-courseware
public multilingue). Voir aussi [`BONDAREVA_SHAPLEY_HARDNESS.en.md`](BONDAREVA_SHAPLEY_HARDNESS.en.md)
pour la version anglaise d'origine (po-2025, cycle 28, piste A, 2026-05-12).

# sudoku_lean — soundness de la propagation de contraintes (Lean 4)

Lake de la série **Sudoku** formalisant la **soundness des règles de propagation** des
solveurs : `naked single` et `hidden single` ne retirent **aucune solution valide**.
Voir issue `See #4055` (roadmap Lean `See #4038`). Coordination `See #2978` vérifiée :
l'angle Lean de #2978 est la terminaison de reconnaisseur regex (`finiteness-derivatives`),
sans chevauchement avec la propagation/exact-cover formalisés ici.

## Motivation

Les solveurs Sudoku enseignés dans la série `Sudoku` (backtracking, OR-Tools, .NET,
Infer.NET) accélèrent la résolution en **propageant** les contraintes : dès qu'une
valeur est placée, on élimine les candidats devenus impossibles. Deux règles
canoniques :

- **Naked single** — une cellule dont le seul candidat restant est `v` doit contenir `v`.
- **Hidden single** — une valeur qui ne peut aller que dans une seule cellule d'une
  portée doit y aller.

Ce module prouve que ces règles sont **saines** : éliminer un candidat par propagation,
c'est éliminer une affectation qu'**aucune solution n'utilise**. La propagation ne
« devine » jamais — elle ne fait que rendre explicite ce que l'invariant
« toutes-distinctes par portée » impose déjà.

## Ce qui est formalisé (0 sorry)

La modélisation est **abstraite sur la structure de contraintes** : un Sudoku (plus
généralement tout CSP « à portées toutes-distinctes ») = un type de cellules `ι`, un type
de valeurs `V` (tous deux finis), et un ensemble de **portées** `Scopes` (chacune un
`Finset` de cellules). Le 9×9 concret (27 portées : 9 lignes, 9 colonnes, 9 blocs) en
est une **instance**, non un cas spécial — les théorèmes valent pour toute structure de
ce type.

**`Sudoku/Basic.lean`** — primitives :
- `Scopes` (= `Finset (Finset ι)`), `Solution` (= `ι → V`).
- `AllDistinctOn σ s` — `σ` injective sur la portée `s` (aucune valeur répétée).
- `IsSolution scopes σ` — `σ` toutes-distinctes sur chaque portée (invariant fondamental).
- `IsPeer scopes c c'` — `c` et `c'` distinctes partageant une portée.
- `PresentIn σ s v` — `v` apparaît dans la portée `s`.

**`Sudoku/Propagation.lean`** — soundness (0 sorry) :
- `peer_excludes_value` — **clé de voûte** : une cellule `c` portant `v` exclut `v` de
  toute cellule paire `c'` dans toute solution (`σ c' ≠ v`). Preuve : `c, c'` partagent
  une portée `s` ; toutes-distinctes sur `s` ⟹ `σ c = σ c'` impliquerait `c = c'`,
  contredisant `c ≠ c'`.
- `naked_single_sound` — si toutes les valeurs sauf `v` sont portées par des paires de
  `c`, toute solution place `v` en `c` (la cellule n'a plus que `v` comme candidat).
- `hidden_single_sound` — si `v` est présente dans la portée `s` et exclue de toute
  autre cellule de `s`, toute solution place `v` en l'unique cellule restante `c`.

Chaque théorème se réduit à la clé de voûte `peer_excludes_value` par un argument par
l'absurde : un candidat « exclu » apparaîtrait sur une paire, ce que la clé de voûte
interdit.

## Ce qui est délibérément ouvert (non sorry-backed)

- **Réduction Sudoku ⇔ couverture exacte** (Knuth, 4 familles de contraintes :
  cellule, ligne-valeur, colonne-valeur, bloc-valeur) — l'équivalence des ensembles de
  solutions est un jalon naturel, laissé **ouvert** et **non `sorry`-backed**.
- **Complétude** des règles de propagation — les naked/hidden singles ne suffisent pas à
  résoudre tout Sudoku (d'où le recours au backtracking) ; formaliser cette limite est
  un jalon séparé.
- **Minimum 17 indices** — résultat de calcul massif (recherche exhaustive),
  **non formalisable**, explicitement hors scope.

Cette structure (soundness prouvée + réduction/complétude ouvertes documentées) est
cohérente avec les lakes frères `Coherence` / `Utility` du même programme (une direction
prouvée, la réciproque ouverte).

## Statut

- **Toolchain** : `leanprover/lean4:v4.31.0-rc1`
- **Sorry** : **0** sur l'ensemble du module.
- **Build** : `lake build Sudoku` (dépend de Mathlib4)
- **Dépendances** : Mathlib4 (`v4.31.0-rc1`) — théorie des `Finset`, injectivité sur un
  ensemble, images finies.
- **Axiomes** : `[propext, Classical.choice, Quot.sound]` (standards Mathlib, pas de
  `sorryAx`) sur les trois théorèmes.

## Modules

| Fichier | Contenu |
|---------|---------|
| `Sudoku/Basic.lean` | Types abstraits — `Scopes`, `Solution`, `AllDistinctOn`, `IsSolution`, `IsPeer`, `PresentIn`. |
| `Sudoku/Propagation.lean` | **Clé de voûte** `peer_excludes_value` + soundness `naked_single_sound`, `hidden_single_sound` (0 sorry). |
| `Sudoku.lean` | Imports parapluie + doc de statut. |

## Build

```bash
# Depuis ce répertoire (WSL requis pour un build complet ; WDAC workaround sur Windows)
lake build Sudoku
# Dépend de Mathlib4 — le premier build est lourd, les builds suivants utilisent le cache
```

## Référence croisée

- Série `Sudoku` (`Sudoku-1-Backtracking-Csharp.ipynb`, `Sudoku-10-ORTools-Csharp.ipynb`,
  …) : les solveurs C#/.NET + Python dont ce lake fonde formellement l'étape de
  propagation. Lake = livrable formel, `lake build` = preuve d'exécution (convention des
  lakes frères).
- `See #2978` (Sudoku comme regex symbolique) : angle Lean = terminaison de
  reconnaisseur, sans chevauchement.

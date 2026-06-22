# conway_cgt_lean — Visite de vihdzp/combinatorial-games

Une **visite guidée** (basée sur `#check`) de la théorie des jeux combinatoires
formalisée dans
[`vihdzp/combinatorial-games`](https://github.com/vihdzp/combinatorial-games),
importée comme dépendance Lake — nombres surréels, nimbers et jeux combinatoires
généraux. Ce n'est **pas** une formalisation originale : elle présente et exhibe
les résultats amont, qui constituent le foyer actuel de la TJC dans l'écosystème
Lean après le retrait des modules CGT de Mathlib.

Référence : Conway, J.H. — *On Numbers and Games* (2001).

## Statut

- **Toolchain** : `leanprover/lean4:v4.31.0-rc1` (suit le dépôt amont — plus récente que les autres séries Lean en v4.30.0-rc2)
- **Sorry** : **0** — le fichier est une visite de `#check` et de docstrings, aucune preuve
- **Build** : `lake build CGTTour` (dépend de Mathlib4 + CombinatorialGames)
- **Dépendances** :
  - **Mathlib4** (dernière)
  - **[CombinatorialGames](https://github.com/vihdzp/combinatorial-games)** (Apache-2.0) — Violeta Hernandez Palacios

## Pourquoi ce dépôt existe — retrait de la TJC de Mathlib

Le dépôt amont a **remplacé les modules CGT de Mathlib**
(`SetTheory.Surreal`, `SetTheory.PGame`, `SetTheory.Game`, `SetTheory.Nimber`),
dépréciés dans la PR Mathlib [#28063](https://github.com/leanprover-community/mathlib4/pull/28063)
(août 2025) et **retirés dans la PR [#35550](https://github.com/leanprover-community/mathlib4/pull/35550)**
(février 2026). L'autrice amont (vihdzp) est la même personne qui maintenait le
code CGT de Mathlib. Cette visite oriente les apprenants vers le lieu où vit
désormais la TJC.

## Ce que la visite couvre

Le fichier importe les modules amont et exhibe leurs résultats clés :

### 1. Jeux combinatoires
- **`IGame`** (pré-jeux) : représentation concrète par ensembles d'options
  gauche/droite (`left`/`right : Set IGame`) — on peut inspecter chaque coup.
- **`Game`** (jeux à équivalence `≈` près) : le quotient
  `Antisymmetrization IGame (· ≤ ·)`, un `OrderedAddCommGroup`.
- Anniversaire (birthday), forme canonique, joueur.

### 2. Nombres surréels
- **`Surreal`** : jeux numériques quotientés par équivalence — un **`LinearOrder`**,
  un corps ordonné complet contenant tout corps ordonné comme sous-corps.
- **Théorème de simplicité** (`IGame.Fits.equiv_of_forall_not_fits`) : l'outil clé
  pour calculer les valeurs surréelles.
- Arithmétique de corps complète : addition (depuis `Game`), multiplication, division.
- **Plongement dyadique** (`Dyadic.toIGame`) — surréels dyadiques = anniversaire fini.
- **Plongement ordinal** (`NatOrdinal.toSurreal`).

### 3. Nimbers
- **`Nimber`** : ordinaux avec l'arithmétique de nim ; issus des jeux impartiaux via
  le **théorème de Sprague-Grundy** (tout jeu impartial ≈ un jeu de nim).
- **Addition de nim** par minimum-exclu (`Nimber.add_def`).
- **Corps de caractéristique 2** (`Field Nimber`) — chaque élément est son propre
  opposé additif. Objectif long terme : prouver les nimbers algébriquement clos.

### Mathlib vs amont (tableau comparatif dans le fichier)

| Aspect | Mathlib (retiré) | combinatorial-games (actuel) |
|--------|------------------|------------------------------|
| Jeux | `PGame` (basique) | `IGame` (concret) + `Game` (quotient) |
| Surréels | Basique/Dyadique/Mul | + Division, séries de Hahn, Anniversaire, Pow |
| Nimbers | Basique/Corps | + Nat, SimplestExtension |
| Bibliothèque de jeux | 8 modules | 15+ modules (Impartial, Loopy, Specific…) |

## Modules

| Fichier | Lignes | Contenu |
|---------|--------|---------|
| `CGTTour.lean` | 169 | Importe les modules amont `CombinatorialGames.*` et visite leurs types/instances/théorèmes clés via `#check` + docstrings (`IGame`/`Game`, `Surreal` + théorème de simplicité, `Nimber` + Sprague-Grundy), avec un tableau comparatif Mathlib-vs-amont. |

## Build

```bash
# Depuis ce répertoire (WSL requis)
lake build CGTTour
# Dépend de Mathlib4 + CombinatorialGames (deux dépendances git) — le premier build est lourd
```

## Citer, ne pas vendorer

Le dépôt amont est une **dépendance Lake** (`require CombinatorialGames from git`),
non vendorisée. Licence : **Apache-2.0**. Le fichier de visite est une exposition
originale construite au-dessus des résultats importés.

## Voir aussi

- **Amont** : [`vihdzp/combinatorial-games`](https://github.com/vihdzp/combinatorial-games) (Apache-2.0, Violeta Hernandez Palacios)
- **`knot_lean/`** — référence cette visite dans son tableau de dépendances (fondement en théorie des jeux de Conway)
- **`conway_lean/`** — Conway's Game of Life / Free Will Theorem (l'*autre* série Conway)
- **Epic #2651** — audit README/structure (série Lean)

## Conclusion

Ce projet est une **visite guidée** (basée sur `#check`, 0 `sorry`) de la théorie
des jeux combinatoires qui vit désormais dans
[`vihdzp/combinatorial-games`](https://github.com/vihdzp/combinatorial-games),
importée comme dépendance Lake. Il existe parce que les modules CGT de Mathlib ont
été **retirés en février 2026** (PR [#35550](https://github.com/leanprover-community/mathlib4/pull/35550)),
et cette visite oriente les apprenants vers le lieu où vit désormais cette théorie.

### Ce qu'elle couvre

- **Jeux combinatoires** — `IGame` (pré-jeux concrets par ensembles d'options
  gauche/droite) et `Game` (le quotient à équivalence `≈` près), avec anniversaire
  et forme canonique.
- **Nombres surréels** — `Surreal` comme corps ordonné complet contenant tout corps
  ordonné ; le **théorème de simplicité** comme outil de calcul clé ; arithmétique
  de corps complète ; plongements dyadique et ordinal.
- **Nimbers** — ordinaux avec l'arithmétique de nim, issus des jeux impartiaux via
  le **théorème de Sprague-Grundy** ; un corps de caractéristique 2 (objectif long
  terme : prouver les nimbers algébriquement clos).

### Pourquoi elle existe

Mathlib a déprécié son code CGT (`SetTheory.Surreal/PGame/Game/Nimber`) au profit
du dépôt amont, dont l'autrice (vihdzp) est la même maintenante. Plutôt que
vendoriser ou redériver, la visite **cite** l'amont comme dépendance et exhibe ses
résultats via `#check` + docstrings — une exposition originale au-dessus de
théorèmes importés. Un tableau comparatif Mathlib-vs-amont documente la couverture
amont plus riche (15+ modules contre les 8 anciens de Mathlib).

### Où aller ensuite

- **Amont** : [`vihdzp/combinatorial-games`](https://github.com/vihdzp/combinatorial-games)
  (Apache-2.0, Violeta Hernandez Palacios) — le foyer actuel de la TJC en Lean.
- **Source** : Conway, J.H. — *On Numbers and Games* (2001).
- **Lié** : `conway_lean/` (Conway's Game of Life / Free Will — l'*autre* série
  Conway) et `knot_lean/` (réfère à cette visite dans son tableau de dépendances).

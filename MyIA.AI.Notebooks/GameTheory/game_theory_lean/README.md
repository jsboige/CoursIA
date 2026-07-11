# GameTheory.Lean (game_theory_lean)

Lake project multi-module Lean 4 qui regroupe les **preuves formelles de la
théorie des jeux** autour de deux piliers : le **mariage stable de
Gale-Shapley** et les **jeux coopératifs à utilité transférable** (valeur de
Shapley, cône de Bondareva-Shapley, décomposition de Möbius). Issu du
**regroupement EPIC #4365 « anti-prolifération GameTheory »** qui a ramené
six projets Lake distincts à **deux cibles** (game_theory_lean +
conway_cgt_lean), ce dépôt absorbe progressivement les modules
historiquement分散és dans `social_choice_lean/`, `cooperative_games_lean/`,
`stable_marriage_lean/` (supprimé depuis) et `social_choice_lean_petters/`
en un seul package multi-`lean_lib` aligné sur le modèle éprouvé de
`decision_theory_lean`.

## Statut

- **Type** : Projet Lake multi-module (multi `lean_lib`, racine agrégée)
- **Toolchain** : `leanprover/lean4:v4.31.0-rc1` (cf `lean-toolchain`)
- **Mathlib** : `v4.31.0-rc1` (cf `lake-manifest.json`)
- **Compte de `sorry`** : 6 (3 dans `StableMarriage.Lattice` + son
  sibling `_en` ; énoncés **contrefactuels documentés** dans le module —
  voir `StableMarriage/Lattice.lean:778-784` — ni eux ni leur traduction
  anglaise ne sont prouvables, pas un oubli)
- **Lignes** : 11 099 (FR + EN confondus, modules frères)
- **CI** : `lean-social-choice.yml` ne build PAS ce projet (cf
  [lean-merge-discipline.md](.claude/rules/lean-merge-discipline.md) — seul
  `lake build <module>` local fait foi)
- **Compilation locale** : `lake build` SUCCESS documenté dans les PRs
  c.299–c.308 (8 500 jobs olean au dernier passage Shapley FR+EN, PR #5940)

## Pourquoi ce Lake existe

Le track Lean de GameTheory accueillait six projets Lake avant le regroupement :
`social_choice_lean/`, `social_choice_lean_petters/`,
`cooperative_games_lean/`, `stable_marriage_lean/`, `repeated_games_lean/`,
`minimax_lean/`. Cette prolifération entraînait trois pathologies :

1. **Pin toolchain divergent** — chaque projet pinnait sa propre version
   Mathlib (rc1, rc2, stable), créant des **îlots de non-interopérabilité**.
   `lake build` d'un projet ne réutilisait pas les `.olean` d'un voisin.
2. **Duplication structurelle** — `lakefile.lean`, `lean-toolchain`,
   `lake-manifest.json`, scripts CI quasi-identiques copiés-collés.
3. **Charge cognitive** — choisir où ouvrir une nouvelle preuve (mariage
   stable ? jeu coopératif ? jeu répété ?) obligeait à comparer six
   `lakefile.lean` pour trouver la bonne combinaison de dépendances.

`game_theory_lean/` est la **cible de regroupement** qui résout ces trois
points : un seul `lakefile.lean`, une seule toolchain, un seul
`lake-manifest.json`, et **deux `lean_lib` distincts** (`StableMarriage` +
`CooperativeGames`) qui cohabitent comme modules siblings sans coupler leurs
preuves ni leurs imports Mathlib. Le squelette a été posé en c.299 (PR #5902)
puis rempli incrémentalement c.300–c.308 (PRs #5904 → #5940 + suppression du
doublon `stable_marriage_lean/` via PR #5971).

## Architecture multi-lib

```
package «game_theory_lean» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩
  ]
  require mathlib from git
    "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0-rc1"

  @[default_target]
  lean_lib StableMarriage where
    globs := #[`StableMarriage.*]      -- auto-découverte siblings _en

  @[default_target]
  lean_lib CooperativeGames where
    globs := #[`CooperativeGames.*]    -- auto-découverte siblings _en
```

Le pattern Lake retenu est celui de `decision_theory_lean/` : plusieurs
`lean_lib` cohabitent comme **points d'entrée indépendants** vers Mathlib,
sans coupler les graphes d'imports. Chaque `lean_lib` racine
(`StableMarriage.lean` / `CooperativeGames.lean` / `GameTheory.lean`)
sert d'**agrégateur** qui re-importe ses sous-modules FR ; les siblings
`_en.lean` restent accessibles via `import <Module>.<SousModule>_en`
direct.

## Convention i18n (EPIC #4980)

Chaque sous-module est livré en **siblings FR + EN** distincts, avec
namespace suffixé (`StableMarriage` ↔ `StableMarriage_en`, etc.) pour
éviter les collisions de noms au top-level (notamment l'`abbrev Coalition`
de `CooperativeGames.Basic` qui existe en FR et en EN — voir
[code-style.md](.claude/rules/code-style.md) §Lean i18n). Le pattern
`globs := #[<Lib>.*]` du `lakefile.lean` garantit que la CI **découvre
automatiquement** les deux langues à chaque build, et la **drift-detection**
signale toute divergence FR/EN.

## Modules

### `StableMarriage` — Mariage stable (Gale-Shapley)

Cinq sous-modules FR + leurs siblings EN, absorbés depuis l'ancien
`stable_marriage_lean/` (supprimé via PR #5971, contenu intégralement
préservé ici — anti-régression 4 étapes respectée).

| Sous-module | Lignes (FR / EN) | Sorries (FR / EN) | Contenu |
|-------------|------------------|------------------|---------|
| [`StableMarriage.Definitions`](StableMarriage/Definitions.lean) | 125 / 132 | 0 / 0 | `PrefProfile`, `Matching`, `IsStable`, ordre `ManLE` |
| [`StableMarriage.GSState`](StableMarriage/GSState.lean) | 173 / 180 | 0 / 0 | État de l'algorithme Gale-Shapley, file d'hommes libres, propositions |
| [`StableMarriage.Lemmas`](StableMarriage/Lemmas.lean) | 898 / 902 | 0 / 0 | Lemmes intermédiaires (44 lemmes, 0 sorry) |
| [`StableMarriage.Lattice`](StableMarriage/Lattice.lean) | 885 / 881 | 3 / 3 | Treillis des mariages (join/meet), optimalité homme/femme ; **3 énoncés contrefactuels documentés**, ni eux ni leur traduction anglaise ne sont prouvables |
| [`StableMarriage.GaleShapley`](StableMarriage/GaleShapley.lean) | 181 / 171 | 0 / 0 | Terminaison, stabilité, optimalité homme, existence d'un stable |

**Théorèmes clés** (`namespace StableMarriage`) :

- `gale_shapley_terminates` — l'algorithme se termine en temps fini
- `gale_shapley_produces_matching` — le résultat est un appariement
- `gale_shapley_stable` — l'appariement retourné est stable (pas de
  paire bloquante)
- `gale_shapley_man_optimal` — optimalité côté hommes (chaque homme
  obtient sa meilleure partenaire stable)
- `stable_matching_exists` — il existe toujours au moins un appariement
  stable (corollaire de la terminaison + stabilité)
- `gale_shapley_woman_pessimal` — symétriquement, pessimalité côté femmes
- `join_isStable` / `meet_isStable` — la borne supérieure / inférieure
  dans le treillis des mariages préserve la stabilité
- `man_optimality_key_step_is_false` — l'**énoncé contrefactuel**
  documenté qui démontre pourquoi une approche intuitive échoue

### `CooperativeGames` — Jeux coopératifs à utilité transférable

Trois sous-modules FR + leurs siblings EN, absorbés depuis l'ancien
`cooperative_games_lean/` et progressivement complétés.

| Sous-module | Lignes (FR / EN) | Sorries (FR / EN) | Contenu |
|-------------|------------------|------------------|---------|
| [`CooperativeGames.Basic`](CooperativeGames/Basic.lean) | 607 / 606 | 0 / 0 | `Coalition = Finset N`, `TUGame`, unanimity/majority games, `BondedWeights`, **théorème de Bondareva-Shapley** (forward) |
| [`CooperativeGames.ConeKernel`](CooperativeGames/ConeKernel.lean) | 753 / 547 | 0 / 0 | `BondarevaCone.augCone`, séparateur, **Bondareva-Shapley bidirectionnel** (forward + backward), `marginalVector_mem_core`, `convex_core_nonempty` |
| [`CooperativeGames.Shapley`](CooperativeGames/Shapley.lean) | 2 024 / 2 034 | 0 / 0 | `Solution`, **les quatre axiomes de Shapley** (efficience, symétrie, joueur nul, additivité), unicité, `mobius_decomposition`, `shapley_smulGame`, `shapley_addGames` |

**Théorèmes clés** (`namespaces Solution`, `ShapleyValue`, `Mobius`,
`BondarevaCone`) :

- `bondareva_shapley_forward` — un jeu **balancé** (toute pondération
  positive satisfait `∑ w_S v(S) ≤ v(N)`) appartient au cœur
- `bondareva_shapley_backward` — réciproque : tout jeu du cœur est
  équilibré
- `bondareva_shapley` — **équivalence** (théorème fondateur de
  Bondareva-Shapley, 1963) ; voir
  [lean-bondareva-polyhedral-closed-gap](file:../../../docs/lean/lean-bondareva-polyhedral-closed-gap.md)
- `marginalVector_mem_core` — le vecteur de contributions marginales est
  dans le cœur
- `convex_core_nonempty` — le cœur est non-vide pour tout jeu équilibré
- `superadditive_empty_nonneg` /
  `superadditive_grand_coalition_nonneg_of_nonneg_singletons` —
  conditions de super-additivité
- `conicHull_linearIndependent_isClosed` /
  `finGenCone_isClosed` — clôture du cône enveloppe conique en
  dimension finie
- `mem_cone_iff_exists_li_subset` /
  `augCone_mem_iff` — caractérisations d'appartenance au cône
- `shapley_null_player` — joueur nul reçoit 0
- `shapley_efficient` — `∑_i φ(G)(i) = G.v(𝕌)` (partage le surplus total)
- `shapley_symmetric` — joueurs symétriques reçoivent la même valeur
- `shapley_unanimity` — pour le jeu d'unanimité, φ(T)(i) = 1 si i ∈ T
  sinon 0
- `shapley_additive` — φ(G + H) = φ(G) + φ(H) (linéarité)
- `mobius_decomposition` — `G.v(S) = ∑_{T⊆S} m_G(T)` (décomposition de
  Möbius via la fonction de Möbius du lattice booléen)
- `shapley_smulGame` / `shapley_addGames` — homogénéité et additivité
  étendues

## Théorème de Bondareva-Shapley — chemin de preuve

`CooperativeGames.Basic` énonce le théorème et prouve la direction
`forward`. La **preuve complète** (`bondareva_shapley_forward` +
`bondareva_shapley_backward` = `bondareva_shapley`) vit dans
`CooperativeGames.ConeKernel` où la machinerie `BondarevaCone.augCone`
(cône augmenté) + le **séparateur** (`separatingFunctional_none_neg`)
sont introduits. Le plan détaillé et le journal de remplissage des
trous sont dans
[docs/BONDAREVA_FARKAS_PLAN.md](../../../../docs/lean/BONDAREVA_FARKAS_PLAN.md).

## Quatre axiomes de Shapley — formalisation

La caractérisation axiomatique (Shapley, 1953) identifie **l'unique**
solution qui satisfait simultanément les quatre axiomes :

| Axiome | Énoncé | Théorème |
|--------|--------|----------|
| **Efficience** | `∑_i φ(G)(i) = G.v(𝕌)` | `shapley_efficient` |
| **Symétrie** | Si i et j symétriques dans G, alors `φ(G)(i) = φ(G)(j)` | `shapley_symmetric` |
| **Joueur nul** | Si G(i) = G(i∪{j}) pour tout S ⊄ {j}, alors `φ(G)(j) = 0` | `shapley_null_player` |
| **Additivité** | `φ(G+H)(i) = φ(G)(i) + φ(H)(i)` | `shapley_additive` |

Le **théorème de Shapley** (caractérisation) et les lemmes associés
(unanimité, linéarité par rapport au jeu) sont dans
`CooperativeGames/Shapley.lean` (namespaces `Solution`, `ShapleyValue`,
`Mobius`). La décomposition de Möbius (`mobius_decomposition`) relie
la valeur de Shapley à l'inversion sur le treillis booléen des
coalitions, et donne une formule close :
`φ(G)(i) = ∑_{S ⊆ N\{i}} |S|! (n-|S|-1)! / n! · [G(S∪{i}) - G(S)]`.

## Build

```bash
# Compilation incrémentale (cible par défaut : les deux libs)
cd MyIA.AI.Notebooks/GameTheory/game_theory_lean
lake build

# Ciblé : ne compiler qu'un des deux modules
lake build StableMarriage
lake build CooperativeGames

# Vérifier l'état sorry actuel (manifest attendu = 6 : 3+3 dans Lattice)
grep -c '\bsorry\b' StableMarriage/Lattice.lean        # 3
grep -c '\bsorry\b' StableMarriage/Lattice_en.lean     # 3

# Cache Mathlib (premier build, ~40s ; incrémental ensuite ~13s)
lake exe cache get
```

Le cache Mathlib est partagé au niveau du dépôt (via `lake exe cache get`)
pour éviter de retélécharger `~3 GB` à chaque incrément. Sur Windows,
attention à la copie `NTFS junction` documentée dans
[lean-wdac-olean-wholesale-copy](../../../../docs/lean/lean-wdac-olean-wholesale-copy.md).

## Relation aux autres projets Lean de GameTheory

| Projet | Statut | Raison de la séparation |
|--------|--------|-------------------------|
| [`conway_cgt_lean/`](../conway_cgt_lean/) | Lake séparé (vihdzp/combinatorial-games) | Théorie des jeux combinatoires (PGame, surréels, nimbers) — Mathlib-only via `SetTheory.PGame` |
| [`social_choice_lean/`](../social_choice_lean/) | Lake séparé (pinné v4.30.0-rc2) | Non encore absorbé — PR #6058 OPEN MERGEABLE UNSTABLE post c.369b fix, blocage par build lake |
| [`social_choice_lean_petters/`](../social_choice_lean_petters/) | Lake séparé (pinné commit `d679d950` Peters) | Gibbard-Satterthwaite, Duggan-Schwartz — divergence de rev attendra la convergence v4.31.0-rc1 |
| [`cooperative_games_lean/`](../cooperative_games_lean/) | **Supprimé** (c.306, contenu intégralement absorbé dans `game_theory_lean/CooperativeGames/`) | — |
| [`stable_marriage_lean/`](../stable_marriage_lean/) | **Supprimé** (c.305 finalisation + PR #5971 doublon) | — |
| [`lean_game_defs/`](../lean_game_defs/) | Couche introductive (pas un Lake) | 6 fichiers `.lean` de **référence** pour copier-coller dans les notebooks d'enseignement ; 0 sorries, Mathlib-free |
| [`decision_theory_lean/`](../../Probas/decision_theory_lean/) | Modèle architectural | `lean_lib Gittins`/`Utility`/`Coherence` cohabitent comme libs distinctes du même package — **modèle** suivi ici |

## Voir aussi

- [`GameTheory/README.md`](../README.md) — vue d'ensemble du track
  GameTheory (OpenSpiel + Lean)
- [`social_choice_lean/README.md`](../social_choice_lean/README.md) —
  l'autre Lake GameTheory encore séparé (Arrow / Sen / électeur médian)
- [`lean_game_defs/README.md`](../lean_game_defs/README.md) — la couche
  introductive (pas un Lake, juste des définitions à copier-coller)
- [`scripts/README.md`](../scripts/README.md) — configuration du kernel
  Lean 4 WSL
- [`.claude/rules/lean-merge-discipline.md`](../../../../.claude/rules/lean-merge-discipline.md) —
  règle **HARD** : `lake build SUCCESS` local avant merge + BG iter
  systématique post-PR/msg po-2026
- [`.claude/rules/anti-regression.md`](../../../../.claude/rules/anti-regression.md) —
  protocoles anti-régression Lean (incidents fondateurs : 2026-04-24
  Arrow.lean 9 preuves → sorry)
- [`docs/lean/`](../../../../docs/lean/) — itérations prover, plan
  Bondareva-Farkas, diagnostic intractable, LLM endpoints
- EPIC **#4365** — anti-prolifération GameTheory (6 → 2 cibles)
- EPIC **#4980** — convention i18n FR/EN sibling pair pour lakes
  destinés à publication
- PRs de remplissage : #5902 (skeleton), #5904 (Definitions ±_en),
  #5905 (GSState ±_en), #5910 (Lemmas ±_en), #5911 (Lattice ±_en),
  #5913 (GaleShapley ±_en), #5924 (Basic + ConeKernel ±_en), #5931
  (Shapley FR), #5940 (Shapley EN), #5971 (suppression doublon
  `stable_marriage_lean/`)

## Conclusion

`game_theory_lean/` est la **cible de regroupement** du track Lean de
GameTheory (EPIC #4365) : un seul projet Lake multi-`lean_lib` qui
absorbe les preuves formelles de **mariage stable** (Gale-Shapley,
treillis des mariages, optimalité) et de **jeux coopératifs** (valeur
de Shapley, cône de Bondareva-Shapley, décomposition de Möbius), avec
**11 sous-modules** totalisant 11 099 lignes, **6 sorries documentées**
(3 paires FR/EN d'énoncés contrefactuels dans `StableMarriage.Lattice`),
et **convention i18n FR/EN sibling pair** (EPIC #4980). Le pattern Lake
multi-lib retenu est calqué sur `decision_theory_lean/` (modèle éprouvé
c.299–c.308), avec deux `lean_lib` distincts (`StableMarriage` +
`CooperativeGames`) qui cohabitent sans coupler leurs imports Mathlib.
**État actuel** : squelette posé en c.299, remplissage incrémental c.300
→ c.308, doublon `stable_marriage_lean/` supprimé via PR #5971 ; les
absorptions suivantes (social_choice_lean, social_choice_lean_petters)
sont des **PRs dédiées** trackées séparément et pinnées sur la
convergence v4.31.0-rc1 de Mathlib.

### Ce qu'il couvre

- **Mariage stable** : terminaison, stabilité, optimalité homme /
  pessimalité femme de l'algorithme de Gale-Shapley, structure de
  treillis sur l'ensemble des mariages.
- **Jeux coopératifs T.U.** : théorème de Bondareva-Shapley
  (équivalence entre cœur non-vide et balanced), valeur de Shapley
  (caractérisation axiomatique, décomposition de Möbius, formule
  close).
- **Cône augmenté** : `BondarevaCone.augCone` et son séparateur,
  clôture du cône enveloppe conique en dimension finie.

### Pourquoi il existe

Résorber la **prolifération de Lakes** GameTheory (six projets séparés
avec des toolchains Mathlib divergentes), unifier le build et la CI,
faciliter l'**ajout incrémental** de nouveaux modules par absorption
(`absorb <Nom>.lean`), et fournir une **vitrine FR + EN sibling pair**
pour publication. Modèle : `decision_theory_lean/` (multi-lib cohabitante
sans couplage d'imports Mathlib).

### Où aller ensuite

- **Modules à absorber** : `social_choice_lean/` (PR #6058 OPEN
  MERGEABLE UNSTABLE), `social_choice_lean_petters/` (convergence
  Mathlib v4.31.0-rc1 attendue), `repeated_games_lean/`,
  `minimax_lean/` — chacun fait l'objet d'une **PR dédiée** suivant le
  même protocole anti-régression 4 étapes que les PRs c.299–c.308.
- **Couche introductive** : [`lean_game_defs/`](../lean_game_defs/) pour
  les notebooks d'enseignement (définitions copier-coller, 0 sorries,
  Mathlib-free).
- **CGT** : [`conway_cgt_lean/`](../conway_cgt_lean/) pour la théorie
  des jeux combinatoires (PGame, surréels, nimbers via Mathlib).
- **Configuration du kernel Lean** : [`scripts/README.md`](../scripts/README.md)
  et [`.claude/rules/wsl-kernels.md`](../../../../.claude/rules/wsl-kernels.md).
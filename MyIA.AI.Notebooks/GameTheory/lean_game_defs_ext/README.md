# lean_game_defs_ext — Bayesian Games (Lean 4, core only)

Formalisation des jeux bayésiens finis à deux joueurs (espaces de types
de Harsanyi) en Lean 4 **sans Mathlib** (toolchain `v4.30.0-rc2`, core
uniquement — évite la mutualisation des checkouts Mathlib, cf #2611).
Compagnon formel de `GameTheory-11-BayesianGames.ipynb`. Phase 1 de
l'epic #2610.

## Contenu

| Module | Contenu |
|--------|---------|
| `Bayesian/Sum.lean` | Sommes finies sur `Fin n` (`sumFin`) + lemmes : monotonie, congruence, factorisation scalaire |
| `Bayesian/Types.lean` | `BayesGame2` (types, actions, prior non normalisé en poids `Nat`, paiements `Int`), stratégies type-contingentes, utilités interim (`interimU1/U2`) et ex-ante (`exAnteU1/U2`) |
| `Bayesian/BNE.lean` | `isBNE` (équilibre de Nash bayésien interim, **décidable**), principe de déviation unique (interim ⇒ ex-ante), invariance par rescaling du prior (`isBNE_scaleW`) |
| `Bayesian/Examples.lean` | Bataille des sexes à information incomplète (Harsanyi) : BNE du manuel certifié par `decide` |
| `Bayesian/Auction.lean` | Enchère au premier prix sous pli scellé (discrète, 2 enchérisseurs, prior uniforme) : enchérir sa valeur rapporte exactement 0 (théorème général en `n`), le *bid shading* `b(v) = v/2` est un BNE certifié par `decide` (n = 2, 3), enchérir sa valeur n'est PAS un BNE (phase 2) |

## Choix de conception

- **Prior non normalisé** (poids `Nat`) : évite la théorie de la mesure
  et les rationnels ; `isBNE_scaleW` prouve que seuls les ratios de
  poids comptent, ce qui justifie l'encodage.
- **Utilités `Int`**, quantificateurs sur `Fin` uniquement : toutes les
  propriétés d'équilibre sont décidables, les exemples concrets se
  vérifient par `decide` (vérification noyau).
- **2 joueurs** : évite l'énumération d'espaces de fonctions dépendants
  qui exigerait `Fintype` (Mathlib).

## Build

```bash
cd MyIA.AI.Notebooks/GameTheory/lean_game_defs_ext
lake build   # Build completed successfully — 0 sorry
```

CI : `.github/workflows/lean-game-defs-ext.yml`, caller du workflow
réutilisable `lean-build.yml` (lake build et sorry baseline 0, mode
standalone-tactic).

## Lien avec `lean_game_defs/`

`lean_game_defs/` (jeux sous forme normale, Nash, social choice,
Kuhn poker — cf #2748 / PR #2752) reste le socle « phase 0 ». Ce
projet-ci accueille les extensions de l'epic #2610 (phase 2 livrée :
enchères au premier prix discret) ; phases suivantes prévues : valeur
de l'information, jeux de réputation simplifiés.

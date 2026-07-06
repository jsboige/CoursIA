# lean_game_defs_ext — Jeux bayésiens en Lean 4 (core uniquement)

Formalisation des jeux bayésiens finis à deux joueurs (espaces de types
de Harsanyi) en Lean 4 **sans Mathlib** (toolchain `v4.31.0-rc1`, core
uniquement — évite la mutualisation des checkouts Mathlib, cf #2611).
Compagnon formel de `GameTheory-11-BayesianGames.ipynb`. Phase 1 de
l'Epic #2610.

## Contenu

| Module | Contenu |
|--------|---------|
| `Bayesian/Sum.lean` | Sommes finies sur `Fin n` (`sumFin`) + lemmes : monotonie, congruence, factorisation scalaire |
| `Bayesian/Types.lean` | `BayesGame2` (types, actions, prior non normalisé en poids `Nat`, paiements `Int`), stratégies type-contingentes, utilités interim (`interimU1/U2`) et ex-ante (`exAnteU1/U2`) |
| `Bayesian/BNE.lean` | `isBNE` (équilibre de Nash bayésien interim, **décidable**), principe de déviation unique (interim ⇒ ex-ante), invariance par rescaling du prior (`isBNE_scaleW`) |
| `Bayesian/Examples.lean` | Bataille des sexes à information incomplète (Harsanyi) : BNE du manuel certifié par `decide` |
| `Bayesian/Auction.lean` | Enchère au premier prix sous pli scellé (discrète, 2 enchérisseurs, prior uniforme) : enchérir sa valeur rapporte exactement 0 (théorème général en `n`), le *bid shading* `b(v) = v/2` est un BNE certifié par `decide` (n = 2, 3), enchérir sa valeur n'est PAS un BNE (phase 2) |
| `Bayesian/Vickrey.lean` | Enchère au second prix (Vickrey) : enchérir sa valeur **domine faiblement** toute autre enchère (argument pointwise classique), donc BNE sincère **pour tout `n`** (théorème général, sans `decide`) ; rente d'information strictement positive du type haut, en contraste avec le premier prix (phase 3) |
| `Bayesian/Max.lean` | Maxima finis sur `Fin (n + 1)` (`maxFin`) : bornes `le_maxFin`/`maxFin_le`, et le lemme maître `maxFin_sumFin_le` (max d'une somme ≤ somme des maxima par groupe) (phase 4) |
| `Bayesian/Information.lean` | Valeur de l'information pour un décideur seul : signaux déterministes = partitions des états, `valueNoInfo ≤ valueSignal ≤ valuePerfect`, **monotonie de Blackwell** (`valueSignal_mono` : un signal plus fin vaut toujours au moins autant, via factorisation σ = h ∘ τ), exemple parapluie chiffré par `decide` (phase 4) |
| `Bayesian/InfoGames.lean` | **L'information peut nuire dans un jeu** : contre-exemple 2 états / 2×2 où le BNE est unique dans chaque scénario (certifié `decide` + eta-expansion des stratégies) et le joueur informé gagne strictement moins (3 < 5) que s'il ne voyait rien — contraste kernel-checked avec la monotonie à un joueur (phase 4) |
| `Bayesian/Reputation.lean` | **Réputation et dissuasion d'entrée** (chain-store à 2 périodes, forme stratégique réduite) : incumbent à 2 types (rationnel / *tough*), raffinement décidable de crédibilité (rationalité séquentielle en dernière période), BNE crédible **unique** dans chaque scénario — avec incertitude le type rationnel *poole* (il combat alors que combattre est myopiquement dominé) et dissuade l'entrée (paiement 5) ; en information complète l'entrée a lieu (paiement 4) : `reputation_pays` 5 > 4 (phase 5) |

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
projet-ci accueille les extensions de l'Epic #2610 (phases livrées :
2 — enchère au premier prix discret, 3 — enchère de Vickrey et
dominance faible, 4 — valeur de l'information : monotonie de Blackwell
à un joueur + contre-exemple « l'information nuit » en jeu,
5 — réputation et dissuasion d'entrée, BNE crédible unique et
`reputation_pays`).

## Conclusion

`lean_game_defs_ext` formalise en Lean 4 (**0 `sorry`**, sans Mathlib, core
uniquement) la théorie des **jeux bayésiens** à information incomplète — du
cadre des types de Harsanyi jusqu'aux applications d'enchères et de réputation.
Compagnon formel de `GameTheory-11-BayesianGames.ipynb`, il couvre l'Epic #2610
(phases 1-5 livrées).

### Ce qui est prouvé

- **Cadre BNE** (`Types.lean`, `BNE.lean`) : `isBNE` (équilibre de Nash bayésien
  *interim*) est **décidable** sur le fragment `Fin`/`Int`. Le **principe de
  déviation unique** (`bne_exAnte`) — un profil interim-optimal est aussi
  ex-ante optimal — et l'**invariance par rescaling du prior** (`isBNE_scaleW`)
  sont prouvés : seuls les ratios de poids comptent.
- **BNE concrets** (`Examples.lean`) : la bataille des sexes à information
  incomplète (Harsanyi) est certifiée par `decide`.
- **Enchère au premier prix** (`Auction.lean`) : enchérir sa valeur rapporte
  exactement 0 (`fpa_u1_truthful`, en `n` général) ; le *bid shading*
  `b(v) = v/2` est un BNE certifié par `decide` (n = 2, 3) ; à l'inverse,
  enchérir sa valeur n'est **pas** un BNE (`truthful_not_bne_two/three`).
- **Enchère de Vickrey** (`Vickrey.lean`) : enchérir sa valeur **domine
  faiblement** toute autre enchère (`spa_truthful_dominant1/2`, argument pointwise
  classique) — donc BNE sincère **pour tout `n`** sans `decide` ; le type haut
  capture une rente d'information strictement positive.
- **Valeur de l'information** (`Information.lean`) : `valueNoInfo ≤ valueSignal ≤
  valuePerfect` et la **monotonie de Blackwell** (`valueSignal_mono` : un signal
  plus fin vaut toujours au moins autant, via factorisation σ = h ∘ τ) ;
  exemple « parapluie » chiffré par `decide`.
- **L'information peut nuire en jeu** (`InfoGames.lean`) : contre-exemple 2
  états / 2×2 où le BNE est unique dans chaque scénario et le joueur informé
  gagne strictement **moins** (3 < 5) que sans information — contraste
  kernel-checké avec la monotonie à un joueur.
- **Réputation et dissuasion** (`Reputation.lean`) : dans un chain-store à 2
  périodes, le BNE crédible **unique** fait *pooler* le type rationnel (il combat
  bien que ce soit myopiquement dominé) et dissuade l'entrée (`reputation_pays` :
  5 > 4 en information incomplète vs 4 en information complète).

### Pourquoi ça marche

Le projet évite délibérément Mathlib en se restreignant à un fragment
**totalement décidable** : prior en poids `Nat` (pas de théorie de la mesure),
utilités `Int`, quantificateurs sur `Fin` uniquement, **2 joueurs**. Chaque
propriété d'équilibre se ramène alors à une somme finie décidable, et tous les
exemples concrets se vérifient par `decide` (vérification noyau, sans axiome
au-delà du core de Lean). Les lemmes de comptage (`Sum.lean`, `Max.lean`)
fournissent l'arithmétique sous-jacente (monotonie, partition, max d'une somme).

### Prochaines étapes

Le cadre étant décidable, les extensions naturelles sont d'autres familles de
jeux bayésiens (enchères au troisième prix, signaux corrélés, mécanismes VCG à
allocation multi-objet) tant qu'elles tiennent dans le fragment `Fin`/`Int`, ou
l'ajout de la dépendance Mathlib pour des résultats structurels non décidables
(typage polymorphe sur `V`, `A`, `Fintype`).

# `asymmetric_information_lean` — Lake Lean 4

Formalisation des **modèles fondateurs** de l'asymétrie d'information en
théorie des jeux, dans le prolongement du **GT-17** (Game Theory) de la série
notebook `CoursIA`.

## Portée

| Modèle | Module | Référence |
|---|---|---|
| Lemons (marché des voitures d'occasion) | `AsymmetricInformation.Lemons` | Akerlof (1970) *QJE* 84(3):488-500 |
| Signaling (signal d'éducation) | `AsymmetricInformation.Signaling` | Spence (1973) *QJE* 87(3):355-374 |
| Screening (sélection adverses, concurrence entre assureurs) | `AsymmetricInformation.Screening` | Rothschild-Stiglitz (1976) *QJE* 90(4):629-649 |
| Anticipatory / cross-subsidy | `AsymmetricInformation.MiyazakiWilson` | Wilson 1977 *JET* 16:167-207, Miyazaki 1977 *Bell J.* 8(2):394-418, Spence 1978 |
| Pont Bayésien non trivial | `AsymmetricInformation.BayesianLink` | `lean_game_defs_ext.Bayesian` (upstream) |

**Première livraison** : portée bornée, conforme à l'audit canonique c.475
(cadrage corrigé par po-2025 avant livraison, voir Epic **#12844**).

## Exposition (notebooks consommateurs)

- **`GameTheory-17c-Lean-Lemons-Certificat.ipynb`** (companion natif, kernel
  `lean4-wsl`) : importe `AsymmetricInformation.Lemons` et exécute le
  certificat en direct — `poolingTenable_iff_cross` (seuil exact),
  `poolingTenable_mono` (plancher), `#print axioms`, balayage du prior
  (falaise à π = 75 % sur le marché-seuil) et spirale de prix des trois
  régimes (#13200).
- **`GameTheory-17b-Asymmetric-Information.ipynb`** (Python) : les quatre
  modèles en simulation — point fixe de participation, signal coûteux,
  screening, règle anticipative.

## Bornes explicites

- **Pas** de théorème d'existence/uniformité général pour l'équilibre
  anticipatoire (Wilson-MWS) — chaque lemme liste ses hypothèses FINIES.
- **Pas** de clause auxiliaire dans κ (Lemons) — uniquement le point fixe
  sur les régions de participation.
- **Pas** de cross-subsidy dans RS (1976) — cross-subsidy tenable relève
  du cadre anticipatoire MWS 1977-1978.
- **Pas** d'`os` sur Mathlib : toutes les preuves reposent sur Lean 4 core +
  `lean_game_defs_ext.Bayesian` (Int, `decide`, `omega`).

## Pont Bayésien non-trivial

`AsymmetricInformation.BayesianLink.bridgeStrategy_isBNE` est certifiée par
`decide` sur une instance fermée (prix `c_L`, vendeur acceptant toujours).
Le BNE est donc **vérifié** dans la sémantique de `lean_game_defs_ext.Bayesian`,
pas un simple import vide.

## Build

```bash
cd MyIA.AI.Notebooks/GameTheory/asymmetric_information_lean
lake build                                       # 28/28 jobs SUCCESS
python scripts/lean/count_code_sorry.py --json   # distinct_code_sorry=0 (zero sorry)
python scripts/lean/check_i18n_siblings.py --all # 0 drift / 0 orphan
```

## Outils

- **Lake** 4.32.1 (toolchain pinned via `lean-toolchain`).
- **`lean_game_defs_ext`** (path dep voisin) — fournit `Bayesian.*` (game,
  strategies, `isBNE`, etc.).

## Convention i18n

EPIC **#4980** (ratifiée user 2026-07-04) : sibling pair FR/EN. Docstrings
FR dans les fichiers own (`*.lean`), miroir EN dans `*_en.lean` (byte-identique
sauf docstrings). Voir `README.en.md` pour la version anglaise.

## Sources canoniques (audit c.475)

- Akerlof (1970) *QJE* 84(3):488-500 — *The Market for Lemons*
- Spence (1973) *QJE* 87(3):355-374 — *Job Market Signaling*
- Rothschild-Stiglitz (1976) *QJE* 90(4):629-649 — *Equilibrium in Competitive Insurance Markets*
- Riley (1979) *Econometrica* 47(2):331-359 — *Informational Equilibrium*
- Wilson (1977) *JET* 16:167-207 — *A Model of Insurance Markets with Incomplete Information*
- Miyazaki (1977) *Bell J.* 8(2):394-418 — *The Rat Race Problem When Participation Is Unobservable*
- Holmström-Milgrom (1991) — modèle principal-agent de référence

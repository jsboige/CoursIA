# `repeated_games_lean` — Théorie des jeux répétés (Lean 4)

Compagnon **formel** du notebook **GameTheory-6c** (jeux répétés). Le notebook
dérive à la main le résultat central de soutenabilité de la coopération ; ce
lake en donne la preuve formelle sous kernel Lean 4 + Mathlib. Part of
[#4038](https://github.com/jsboige/CoursIA/issues/4038) (modèle « 1 théorème-phare
par série »). See [#4880](https://github.com/jsboige/CoursIA/issues/4880).

## Théorème-phare

> **Grim trigger soutient la coopération ssi `δ ≥ (T − R) / (T − P)`.**

Dans le Dilemme du Prisonnier infiniment répété avec facteur d'escompte
`δ ∈ [0, 1)`, la stratégie *grim trigger* (coopérer tant que l'adversaire
coopère, dévier pour toujours dès la première défection) est un équilibre de
Nash parfait en sous-jeux exactement lorsque `δ` dépasse le seuil critique :

```
δ* = (T − R) / (T − P)
```

où `T > R > P > S` sont les paramètres du Dilemme du Prisonnier (`T` tentation,
`R` coopération mutuelle, `P` punition mutuelle, `S` sucker), avec `2·R > T + S`.

La preuve repose sur le **principe de déviation en un coup** (one-shot deviation
principle) et les sommes géométriques (Mathlib `tsum_geometric_of_lt_one`) :

| Trajectoire          | Flux actualisé          |
|----------------------|-------------------------|
| Coopération perpétuelle | `V_C = R + δR + δ²R + … = R / (1 − δ)` |
| Dévier puis punition   | `V_D = T + δP + δ²P + … = T + δ·P / (1 − δ)` |

`V_C ≥ V_D` ⟺ `R ≥ T·(1 − δ) + δ·P` ⟺ `δ·(T − P) ≥ (T − R)` ⟺ `δ ≥ (T−R)/(T−P)`.

## Exemple numérique (Pont ICT-13, [#4879](https://github.com/jsboige/CoursIA/issues/4879))

Pour `T = 3, R = 2, P = 1, S = 0` :

```
δ* = (3 − 2) / (3 − 1) = 1/2
```

→ Grim trigger soutient la coopération dès `δ ≥ 0.5`. La vérification numérique
de ce seuil est un gate du notebook ICT-13.

## Structure du lake

```
repeated_games_lean/
├── lakefile.lean              -- package + Mathlib dep
├── lean-toolchain             -- v4.31.0-rc1
├── RepeatedGames.lean         -- agrégateur racine
└── RepeatedGames/
    ├── Stage.lean             -- Dilemme du Prisonnier (T,R,P,S), paiement de stage
    ├── Discounting.lean       -- sommes géométriques, V_C, V_D, réduction au seuil
    └── GrimTrigger.lean       -- théorème-phare grim_trigger_sustains_iff
```

**Stretch optionnel (non requis pour fermer [#4880](https://github.com/jsboige/CoursIA/issues/4880))** :
`RepeatedGames/Folk.lean` — Folk theorem minimal (tout paiement faisable strictement
individuellement rationnel est soutenable quand `δ → 1`).

## État formel

| Module | Sorries |
|--------|---------|
| `Stage.lean` | **0** (PD définitions + domination stricte de la défection) |
| `Discounting.lean` | 1 (`coop_ge_deviate_iff` — algèbre réelle pure, tranche 2) |
| `GrimTrigger.lean` | transitif via `coop_ge_deviate_iff` |
| **`grim_trigger_sustains_iff`** | **cible 0 sorry** (critère de fermeture [#4880](https://github.com/jsboige/CoursIA/issues/4880)) |

Le théorème-phare sera **0-sorry** une fois la réduction au seuil prouvée
(`field_simp` + `linarith`, tranche 2). Les fondations (`Stage`, `geom_sum`,
`coopValue`, `deviateValue`) sont déjà sorry-free et compilent.

## Toolchain

- `leanprover/lean4:v4.31.0-rc1`
- Mathlib `d568c8c0` (groupe mutualisé des 18 lakes, junction cache #4363).

## Build

```bash
cd MyIA.AI.Notebooks/GameTheory/repeated_games_lean
lake build RepeatedGames
```

## Références

- R. Gibbons, *Game Theory for Applied Economists* (1992), ch. 2.
- D. Fudenberg & J. Tirole, *Game Theory* (1991), ch. 5.
- Companion : notebook **GameTheory-6c** (jeux répétés).

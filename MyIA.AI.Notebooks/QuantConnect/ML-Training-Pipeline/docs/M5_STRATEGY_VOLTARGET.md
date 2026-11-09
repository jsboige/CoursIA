# M5 couche de dimensionnement ETH — Sharpe net hors temps (vol-targeting M5 vs HAR)

> Script : [`scripts/m5_strategy_vol_targeting.py`](../scripts/m5_strategy_vol_targeting.py)
> Tests contractuels : [`scripts/tests/test_m5_strategy_vol_targeting.py`](../scripts/tests/test_m5_strategy_vol_targeting.py)
> Manifeste falsifiable : [`scripts/results/m5_strategy_vol_targeting.json`](../scripts/results/m5_strategy_vol_targeting.json)
> Pré-enregistrement : issue #19725, commentaire c.6040355929 (posé **avant** le premier
> calcul — protocole #18907). Série complète hors dépôt (GDrive), empreinte au manifeste.

## Verdict : VOIDE_FUITE (placebo fuit) — machine seule INCONCLUSIVE

La question posée par #18907/#19725 : **l'edge de prédiction M5 sur la RV ETH h=1
(BEATS 6/7, revalidé #18190) se convertit-il en valeur de stratégie** une fois passé
par une couche de vol-targeting ? Réponse mesurée sur le bloc gelé 2022-07-01 →
2023-12-15 : **non établie** — et le placebo interdit d'en dire plus.

- **Machine de verdict seule** : INCONCLUSIVE franc — différences de Sharpe net
  M5−HAR de signes mixtes (−0,037 à +0,070 selon la graine), aucune p unilatérale
  sous 0,23.
- **Placebo M5 péréimé de 5 jours** : bat HAR sur la graine 42 (+0,272, p = 0,034).
  Le pré-enregistrement pose cette configuration comme **fuite/bruit** : un signal
  *stale* qui gagne signifie que la performance du bloc est dominée par le bruit
  d'échantillonnage, pas par l'information du jour. Verdict vidé → **VOIDE_FUITE**.

## Finding contextuel (mesuré, hors gate)

| Jambe | Sharpe net (bloc, 4 graines) |
|---|---|
| M5 (forecast RV → levier) | +0,550 à +0,656 |
| HAR (forecast RV → levier) | +0,587 (déterministe) |
| **Placebo M5-5j** | +0,652 à +0,859 |
| **RV63 (vol réalisée 63 j)** | **+0,727** |
| **Buy & hold (levier 1)** | **+0,685** |

Les deux jambes prévision sont **sous** la vol réalisée glissante **et** sous le
buy & hold non couvert. Sur ce bloc (fin de krash 2022 → récupération 2023), le
levier moyen ~1,8 avec plafond 3,0 a dilué les rendements sans améliorer le ratio :
l'edge de **prédiction** (DM sur la perte de précision) ne se transfère pas en edge
de **stratégie** par cette voie. Convergence avec les rungs négatifs du Curriculum :
L5 (vol-targeted composite) et L6 finding 3 (sizing régime < naive) —
[`L5_vol_targeted_composite.md`](L5_vol_targeted_composite.md),
[`L6_hmm_regime_sizing.md`](L6_hmm_regime_sizing.md).

## Méthode (pré-enregistrée, aucun paramètre libre)

- **Prévisions** : sorties du runner publié `hmm_regime_vol.py --dump-series`
  (ETH-USD, h=1, graines 0/7/42/99, 2020-06-28 → 2023-12-12, 1240 j/graine). Le
  script ne re-fit **rien** — la couche stratégie s'ajoute sur le chemin de calcul
  exact qui a produit les verdicts de précision (#18190).
- **Règle de dimensionnement** : `lev_t = min(3,0 ; 0,60/vol_ann_t)`, plancher 0
  (jamais short), `ret_net_t = lev_{t-1}·ret_t − 0,001·|lev_t − lev_{t-1}|`
  (10 bps crypto sur le turnover). Vol annuelle = `sqrt(exp(log_rv_prévue))·sqrt(252)`.
- **Bloc gelé** : 2022-07-01 → 2023-12-15 (~533 jours de négociation).
- **Significativité** : bootstrap stationnaire par blocs (longueur moyenne 22 j,
  2000 tirages, graine fixe 20261007) sur les rendements nets **appariés**,
  p unilatéral sur Sharpe(M5) − Sharpe(HAR) — analogue Sharpe du test DM adopté
  par l'arbitrage #18907 point 4.
- **Machine** : BEATS = diff > 0 sur 4/4 graines ET p < 0,05 sur 4/4 ; NO BEATS =
  miroir ; sinon INCONCLUSIVE. Placebo qui bat HAR → **VOIDE_FUITE**.
- **Biais par modèle** (rapporté au manifeste) : biais moyen log-RV sur le bloc,
  M5 et HAR, par graine — l'edge doit venir de la précision, pas du biais
  (critère C.7 de la discipline de review).

## Résultats par graine

| Graine | M5 | HAR | diff | p(diff≤0) | Placebo | RV63 | Hold | biais M5/HAR (log-RV) |
|---|---|---|---|---|---|---|---|---|
| 0 | +0,563 | +0,587 | −0,024 | 0,582 | +0,728 | +0,727 | +0,685 | +0,0054 / +0,0065 |
| 7 | +0,550 | +0,587 | −0,037 | 0,682 | +0,652 | +0,727 | +0,685 | −0,0353 / +0,0065 |
| 42 | +0,629 | +0,587 | +0,043 | 0,310 | **+0,859** | +0,727 | +0,685 | −0,0150 / +0,0065 |
| 99 | +0,656 | +0,587 | +0,070 | 0,230 | +0,767 | +0,727 | +0,685 | −0,0398 / +0,0065 |

Placebo graine 42 vs HAR : diff +0,272, p = 0,034 → **fuite déclarée**, verdict vidé.

## Ce que le résultat interdit de faire

Le pré-enregistrement existe pour ça : **aucun re-jeu** avec un autre bloc, une
autre cible de vol, un autre plafond ou un autre lag de placebo ne peut être
rapporté comme suite de CE résultat. Une variante = une **nouvelle** expérience,
avec un **nouveau** commentaire de pré-enregistrement avant tout calcul
(#18907 point 2). Le résiduel honnête : sur ce bloc, la question « M5 bat-il HAR
comme couche de sizing » reste **ouverte mais non démontrée** (l'échelle des
différences, ±0,07, est petite devant le bruit inter-jambes du bloc) ; la question
« M5 sizing bat-il le naïf » est, elle, tranchée **négativement** sur ce bloc
(sous RV63 et sous buy & hold, 4/4 graines).

## Données et exécution

- Prévisions : dump local du runner (le manifeste porte le sha256 du CSV) ;
  panneau prix ETH Binance local (`load_binance_eth`, même origine que #18190).
- Exécution : CPU, `python scripts/m5_strategy_vol_targeting.py --series-csv <dump>
  --full-series-out <série complète>` ; ~2 min dont l'essentiel en bootstrap.
- Tests : 16 contrats (formule de levier, timing du coût 10 bps, lag d'un jour,
  péréemption placebo 5 j, déterminisme bootstrap, machine de verdict) —
  `python -m pytest scripts/tests/test_m5_strategy_vol_targeting.py`.

## Références

- #19725 (fille de #18907) — pré-enregistrement et livrable ; #18190 — revalidation
  cluster du verdict de précision M5 h=1.
- [`M5_HMM_REGIME.md`](M5_HMM_REGIME.md) — le modèle M5 et ses verdicts de prédiction.
- [`L6_hmm_regime_sizing.md`](L6_hmm_regime_sizing.md) — sizing régime HMM sur
  univers ETF (ROBUST NO BEATS) ; [`L5_vol_targeted_composite.md`](L5_vol_targeted_composite.md).
- Diebold & Mariano (1995) ; Politis & Romano (1994) — bootstrap stationnaire.

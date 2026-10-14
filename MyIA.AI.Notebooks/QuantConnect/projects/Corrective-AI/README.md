# Corrective AI — saisonnalité intrajournalière EUR/USD + méta-étiquetage (Ch. 08-02)

**Hands-On AI Trading**, chapitre 08-02 — port fidèle de l'épisode « Application of Corrective Artificial Intelligence Applied ». Suivi par [#18901](https://github.com/jsboige/CoursIA/issues/18901).

## Mécanisme (le livre)

1. **Stratégie primaire** — saisonnalité intrajournalière EUR/USD de Breedon et Ranaldo (2012) : **vente pendant les heures ouvrées européennes** (03:00–09:00 ET), **achat pendant les heures ouvrées américaines** (11:00–15:00 ET), plat sinon. Le livre mesure, hors échantillon (oct. 2021 – janv. 2023, barres 1 minute EBS), un **Sharpe 0,88** pour la primaire seule.
2. **Corrective AI** — le livre corrige la primaire trade par trade avec un gradient boosting de plus de cent prédicteurs via l'API **payante** predictnow.ai : Sharpe annoncé 1,29 (+0,41) sur la même période.

## Ce port

L'API predictnow.ai est payante et propriétaire : ce port implémente le **principe** correctif sans dépendance payante, par **méta-étiquetage** (López de Prado, *Advances in Financial Machine Learning*, 2018) :

- l'unité de trade = une fenêtre (européenne ou américaine) de la primaire ;
- à chaque entrée, un classifieur (gradient boosting d'arbres, `sklearn`) entraîné **walk-forward** sur les fenêtres passées prédit la probabilité que la fenêtre soit gagnante ;
- la fenêtre n'est prise qu'au-delà du seuil (`sizing: filter`) — ou dimensionnée par la probabilité (`sizing: scale`) ;
- écart déclaré au livre : **~16 prédicteurs ex-ante** (rendements/volatilités minute, côté de la fenêtre, jour de semaine, win-rates glissants de la primaire, série) contre **>100** chez predictnow.ai.

## Paramètres (backtests sans recompilation)

| Paramètre | Défaut | Rôle |
|---|---|---|
| `start` / `end` | 2021-10-01 / 2023-01-31 | fenêtre (format `YYYY-MM-DD`) |
| `use_meta` | `true` | `false` = jambe primaire seule |
| `threshold` | `0.5` | seuil de probabilité (`filter`) |
| `seed` | `0` | graine du classifieur (multi-seed règle §C) |
| `retrain_days` | `21` | cadence de ré-entraînement walk-forward |
| `min_train` | `120` | fenêtres passées minimales avant le premier trade méta |
| `sizing` | `filter` | `filter` ou `scale` |
| `swap_sides` | `false` | `true` = convention du papier Breedon-Ranaldo (achat UE / vente US), convention inverse testée empiriquement |

Choix déclarés : labels sur rendements bruts entrée→sortie (mid-minute, frais moteur à l'exécution réelle uniquement) ; pas d'entrée pendant le warm-up walk-forward (`min_train`) ni pendant les 5 jours de warm-up de données ; fenêtre sans historique minute exploitable (ex. 1er janvier, marché fermé) sautée.

## Résultats

Voir `research.ipynb` (fenêtre du livre : primaire vs méta, multi-seed ≥ 4, test de Diebold-Mariano, biais rapporté — verdict `BEATS` / `NO BEATS` / `INCONCLUSIVE` selon la règle §C) et le tableau de robustesse fenêtre longue 2018-2026. Les métriques sont celles des backtests QC cités dans le corps de la PR de livraison.

## Historique

La v1 exploratoire de ce dossier (croisement SMA sur SPY/TLT/GLD + filtre correctif à règles, backtest Sharpe −0,151 sur le même projet QC 30800636, avril 2026) était un stub d'exercice planifié qui ne correspondait **pas** au contenu réel du chapitre ; elle est remplacée par ce port. Le projet QC Cloud `30800636` (Corrective-AI-Ch08) est réutilisé.

## Références

- Breedon, T. & Ranaldo, A. (2012), « Intraday Patterns in FX Returns and Order Flow » — saisonnalité intrajournalière EUR/USD.
- López de Prado, M. (2018), *Advances in Financial Machine Learning* — méta-étiquetage, ch. 3.
- *Hands-On AI Trading* (Jared Broad), ch. 08-02.

# ML-FinBERT-Sentiment (HandsOn Ex19)

**Classe d'actifs :** Actions US (la plus volatile des 10 plus liquides)
**ID projet Cloud :** 29936073 (HandsOn-Ex19-FinBERT-Sentiment)

## Description

Portage fidèle du modèle de base de l'exemple 19 du livre (*Hands-On AI Trading*, chapitre 06) : FinBERT (`ProsusAI/finbert`) classe les articles Tiingo des 10 derniers jours, le sentiment agrégé (poids exponentiels) décide long 100 % ou short 25 %, au rebalancement mensuel.

**Exécution sur QC Cloud** : même pipeline que le livre, sous **blindage par étape** (adaptation d'exécution, cf. §Historique) et sur une **fenêtre de 2 mois** — les deux conditions mesurées pour qu'un backtest complète.

**Le modèle tourne dans l'algorithme sur QC Cloud** (variante PyTorch, `local_files_only=True` comme le livre) — mesuré par les sondes `probe2-bitmask-finbert` et `probe3-tiingo-decode` du 2026-10-05 : `torch`, `transformers` et même `tensorflow` importent sur les nœuds, et l'inférence y rend ses probabilités.

## Historique du « 0 trade » (fermé le 2026-10-05)

Les portages v1/v2 appelaient `add_data(TiingoNews, "AAPL")` avec un **ticker en chaîne**. TiingoNews exige un `Symbol` d'action déjà mappé — l'appel lève `The custom data type TiingoNews requires mapping, but the provided ticker is not in the cache`, exception avalée par le `try/except` → zéro article → zéro trade. Le livre passe `security.symbol` (issu de l'univers) ; le portage fait de même désormais. Le diagnostic ancien « TF unavailable on QC Cloud » était faux sur les deux comptes.

**Deuxième couche (fermée le même jour)** : le portage fidèle crashait en `FATAL UNHANDLED EXCEPTION`. Douze exécutions (v1–v6, sondes probe4–probe10, projet 29936073) établissent une partition nette :

| Configuration | Effet mesuré |
| --- | --- |
| Portage non blindé, 100k, année complète — SPY jamais abonné (v1/v2) | FATAL en `initialize` (`hasInitializeError=true`, 2 reproductions) |
| Portage non blindé, 100k, année complète — SPY abonné (v3/v4) | FATAL natif **~12 s après le départ** (progress ~0,15) |
| Sondée blindée étape par étape, année complète (probe8, 1M) | **même FATAL natif** : blindage complet + cash 1M ne changent rien, `on_end_of_algorithm` jamais atteint, error = 100 % bruit TF → crash moteur, pas Python |
| Portage fidèle non blindé, 1M, **6 mois** (v5) | **même FATAL natif ~11 s après le départ** (progress 0,29) : un terme deux fois plus court ne repousse pas le mur |
| Portage fidèle non blindé, 1M, **2 mois** (v6) | **`Runtime Error`** — **aucune exécution non blindée n'a jamais complété (6/6)** |
| Sondée **blindée**, fenêtres courtes (probe5 janvier ; probe6/probe7 jan-fév ; probe9 jan-fév complet) | **toutes Completed** — probe9 traverse la transition du 1ᵉʳ février (re-sélection, `remove_security` TiingoNews, re-`add_data`, 2ᵉ `_trade`, vrais ordres ; Sharpe -1.137 sur jan-fév) |
| probe9 verbatim, année complète (probe10) | **`Runtime Error`** — le mur de l'année n'est pas une affaire de blindage |
| **Livrable** : portage fidèle **blindé**, 1M, **2 mois** (v7) | **`Completed.`** — 40 séances, **2 ordres** (les 2 rebalancements mensuels), Sharpe -1,137 : le livrable complète et trade |

Deux conditions sont nécessaires pour qu'un backtest complète, et aucune ne suffit seule : **une fenêtre ≤ 2 mois** (l'année et le semestre meurent nativement) **et le blindage par étape** (la seule exécution non blindée sur fenêtre courte échoue en `Runtime Error`, là où toutes les exécutions blindées de fenêtres courtes complètent — probe5, probe6, probe7, probe9 et le livrable v7). Le livrable réunit les deux.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-FinBERT-Sentiment"` (le modèle doit être dans le cache HuggingFace local).
**QC Cloud :** projet 29936073, `create_compile` → `create_backtest`.

## Métriques de backtest

`ex19-portage-livre-2022-jan-fev-v7-blinde` — le livrable : portage fidèle blindé, cash 1 M, 2022-01-01 → 2022-03-01, **40 séances**, statut **`Completed.`** :

| Métrique | Livrable (v7, jan-fév 2022) | Sonde `probe9` (même fenêtre) | Référence livre |
| --- | --- | --- | --- |
| Sharpe | -1,137 | -1,137 | — |
| Rendement annualisé composé | -84,294 % | -84,294 % | — |
| Rendement net total | -26,230 % | -26,230 % | +123 % cumulé sur 2022 |
| Drawdown max | 37,800 % | 37,800 % | — |
| Probabilistic Sharpe Ratio | 8,371 % | 8,371 % | — |
| Profit net absolu | -20 375,04 $ | -20 375,04 $ | — |
| **Ordres** | **2** | 8193 | — |

Le livrable **complète et produit ses ordres** : 2 ordres = les 2 rebalancements mensuels (1ᵉʳ janvier, 1ᵉʳ février), exactement le comportement du livre. Le « 0 trade » de l'issue #18903 est fermé **par la mesure**, pas par un argument.

**Sur la sonde `probe9`** : elle porte 8191 ordres-marqueurs de plus (un `market_order` d'une action SPY par bit de son masque de diagnostic) et rend pourtant des statistiques **identiques à l'unité près** à celles de v7. Les marqueurs sont donc **neutres sur la mesure** — 8191 ordres d'écart ne déplacent ni le Sharpe, ni le rendement, ni le drawdown. Les deux exécutions se corroborent.

**Deux réserves, mesurées.** (1) La comparaison au livre est **à fenêtre inégale** : le livre couvre 2022 entier, le livrable le premier sixième (mur natif, cf. §Historique) — aucun jugement de performance n'est tiré de l'écart. (2) Ces chiffres **ne sont pas un verdict de stratégie** : deux mois, une seule configuration, aucune répétition multi-seed — le résultat est celui du portage fidèle, pas une évaluation du modèle.

## Fichiers

- `main.py` — Stratégie : portage PyTorch du `FinbertBaseModelAlgorithm` du livre
- `research.ipynb` — Évaluation du modèle de sentiment

## Références

- *Hands-On AI Trading*, Section 06, Exemple 19 (01 Base Model)
- Repo du livre : `QuantConnect/HandsOnAITradingBook`, `06 Applied Machine Learning/19 FinBERT Model`

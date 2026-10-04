# ML-FinBERT-Sentiment (HandsOn Ex19)

**Classe d'actifs :** Actions US (la plus volatile des 10 plus liquides)
**ID projet Cloud :** 29936073 (HandsOn-Ex19-FinBERT-Sentiment)

## Description

Portage fidèle du modèle de base de l'exemple 19 du livre (*Hands-On AI Trading*, chapitre 06) : FinBERT (`ProsusAI/finbert`) classe les articles Tiingo des 10 derniers jours, le sentiment agrégé (poids exponentiels) décide long 100 % ou short 25 %, au rebalancement mensuel.

**Le modèle tourne dans l'algorithme sur QC Cloud** (variante PyTorch, `local_files_only=True` comme le livre) — mesuré par les sondes `probe2-bitmask-finbert` et `probe3-tiingo-decode` du 2026-10-05 : `torch`, `transformers` et même `tensorflow` importent sur les nœuds, et l'inférence y rend ses probabilités.

## Historique du « 0 trade » (fermé le 2026-10-05)

Les portages v1/v2 appelaient `add_data(TiingoNews, "AAPL")` avec un **ticker en chaîne**. TiingoNews exige un `Symbol` d'action déjà mappé — l'appel lève `The custom data type TiingoNews requires mapping, but the provided ticker is not in the cache`, exception avalée par le `try/except` → zéro article → zéro trade. Le livre passe `security.symbol` (issu de l'univers) ; le portage fait de même désormais. Le diagnostic ancien « TF unavailable on QC Cloud » était faux sur les deux comptes.

**Deuxième couche (fermée le même jour)** : le portage fidèle crashait en `FATAL UNHANDLED EXCEPTION` ~13 s après `initialize` (2 reproductions). Cause : le livre crée le Symbol SPY **sans l'abonner** (simple référence calendrier pour `date_rules.month_start`) — sur les nœuds QC actuels, un `date_rules` pointant un symbole non souscrit tue l'algorithme. Correctif : `self.add_equity("SPY", Resolution.DAILY)` (écart n°2 documenté dans `main.py`). Isolé par sondes en cascade : probe4 (8/8 étapes d'initialize) et probe5 (pipeline complet janvier, mask 255/255) passaient — seule différence : l'abonnement SPY.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-FinBERT-Sentiment"` (le modèle doit être dans le cache HuggingFace local).
**QC Cloud :** projet 29936073, `create_compile` → `create_backtest`.

## Métriques de backtest

| Métrique | Valeur (2022, période du livre) |
|----------|----------------------------------|
| Sharpe | __SHARPE__ |
| Rendement total | __NETPROFIT__ |
| Drawdown max | __DD__ |
| Ordres | __ORDERS__ |
| Référence livre (tearsheet 6.60/6.61, OCR) | +123 % cumulé sur 2022 |

## Fichiers

- `main.py` — Stratégie : portage PyTorch du `FinbertBaseModelAlgorithm` du livre
- `research.ipynb` — Évaluation du modèle de sentiment

## Références

- *Hands-On AI Trading*, Section 06, Exemple 19 (01 Base Model)
- Repo du livre : `QuantConnect/HandsOnAITradingBook`, `06 Applied Machine Learning/19 FinBERT Model`

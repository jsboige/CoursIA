# L4 — Decision Transformer (Offline RL action-based, Panier Anti-Biais 25 Symboles)

## Verdict : BEATS

**Seul échelon du ladder (Epic #1409) qui batte le buy-and-hold.** Un Decision Transformer
(Chen et al. 2021) entraîné en **offline RL** apprend directement une **action**
(buy/hold/sell) à partir de trajectoires, au lieu de prévoir un *retour* (L3) ou un *signe
de momentum* (L1/L2). Sur le panier anti-biais (25 symboles, 7 classes, sans FAANG/Mag7),
**24/26 cellules passent le gate d'edge** : le changement de paradigme action-based
contourne l'échec de la prévision de retour.

## Méthode

- **Modèle** : Decision Transformer (Chen et al. 2021, « RL via Sequence Modeling ») —
  entraîné sur des trajectoires (état, action, retour) pour prédire la **bonne action**
  (position discrète), pas l'amplitude du retour.
- **Features** : rendements, volatilité réalisée, RSI, MACD, etc. (ingénierie classique).
- **Validation** : walk-forward **5 folds × 4 seeds** (0/1/7/42), **pas de FAANG/Mag7**
  (`panier_loader.FORBIDDEN_SYMBOLS` enforced).
- **Gate d'edge (G.2)** : un combo est « signal » si `sigma_edge = mean_delta / std_delta`
  $\geq 2$ **ET** `mean_delta > 0` (delta cross-seed, pas single-seed).
- **Benchmark** : buy-and-hold equipondéré (Sharpe 1.15).

## Résultats

| Métrique (25 symboles × 4 seeds = 100 delta_sharpe) | Valeur | Lecture |
|-----------------------------------------------------|--------|---------|
| Cellules « signal » (edge ≥ 2σ et delta > 0) | **24 / 26** | quasi tout le panier exploitable |
| `sigma_edge` (cross-seed) | min 0.0 · **médian 9.98** · max 31.82 (BTC-USD) | edge massif et robuste |
| `mean_delta` (Sharpe vs B&H) | min −1.94 · **médian +1.20** · max +1.95 | delta positif et large |
| Cellules avec 4/4 seeds positifs | **25 / 26** | robustesse cross-seed |
| `delta_sharpe` (100 seeds) | **96 % > 0** · médian +1.23 | quasi aucune seed négative |
| AUC médian | **0.558** | > hasard (vs L3 : 0.509) |

**Cellules non-signal (2)** : VIX (`sigma_edge` 0 — exclu structurellement, pas de
price-return) et SHY (delta −1.94 — le seul actif où le DT sous-performe ; obligation
court terme à faible trend, déjà pire cellule de L3).

**Top edge** : BTC-USD (σ 31.8), XLC (σ 20.0), XLF (σ 16.5).

## Conclusions clés

1. **Le DT bat massivement le buy-and-hold.** delta médian +1.20 Sharpe, 24/26 cellules
   signal, 96 % des seeds positives. Là où L1/L2/L3 échouaient, L4 réussit.

2. **Pourquoi l'action bat le retour.** Un modèle qui prévoit un *retour* (L3 : AUC 0.509 ≡
   hasard) échoue car l'amplitude est bruitée. Un modèle qui prévoit une **action** n'a
   besoin que du *signe de la position optimale* : il peut mal prévoir l'amplitude et bien
   choisir l'action. C'est le changement de paradigme décisif.

3. **Offline RL = apprendre à ne pas trader.** Le DT peut apprendre à **hold** (ne rien
   faire) quand le signal est faible, évitant le coût de rotation qui tuait L1 (5519
   trades) — la fréquence de trading baisse, le coût baisse.

4. **Robustesse cross-seed.** 25/26 cellules avec 4/4 seeds positifs + edge médian 9.98σ :
   l'edge n'est pas un artefact de seed (G.2 respecté). SHY reste le seul échec franc.

## Données

- 25 symboles du panier anti-biais (VIX structuralement exclu), 7 classes d'actifs.
- Plage : 2015-01-02 à 2026-05-23.
- Résultats du sweep **committés** dans `scripts/results/l4_decision_transformer/results.json`
  (verdict agrégé + 26 cellules avec `sigma_edge`, `mean_delta`, détail par seed).

## Script et notebook

- Sweep canonique : `scripts/sweep_l4_decision_transformer.py` (réutilise
  `DecisionTransformerModel` de `train_rl_dt.py`).
- Notebook : `research_l4_decision_transformer.ipynb` + figure `research_l4_dt_results.png`.

## Implication pour le ladder

| Échelon | Paradigme | Verdict |
|---------|-----------|---------|
| L1 TSMOM | momentum temporelle (signe) | NO BEATS (coûts de rotation) |
| L2 CS+DM | momentum cross-sectionnelle | NO BEATS (B&H dominant) |
| L3 LSTM | prévision de **direction/retour** | NO BEATS (AUC ≡ hasard) |
| **L4 Decision Transformer** | **prévision d'action** (offline RL) | **BEATS** |

L1/L2/L3 échouent pour des raisons distinctes (coûts, B&H, imprédictibilité directionnelle)
mais convergent : **prédire un retour ou un signe ne suffit pas**. L4 confirme que **la
bonne abstraction est l'action** — apprendre directement buy/hold/sell par offline RL est
le seul paradigme du ladder qui batte le buy-and-hold.

Référence : Chen et al., *Decision Transformer: Reinforcement Learning via Sequence
Modeling*, NeurIPS (2021). Sweep canonique `scripts/sweep_l4_decision_transformer.py`.
Epic #1409.

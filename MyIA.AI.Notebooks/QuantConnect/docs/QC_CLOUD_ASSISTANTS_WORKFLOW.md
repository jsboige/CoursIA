# QC Cloud Assistants — Workflow et Analyse de Couts

**Source** : Issue #1195 — QC Cloud Assistants workflow + cost analysis.
**Scope** : Protocole d'utilisation des 8 assistants QC Cloud, mesure des couts QCC, et matrice de delegation pour le cluster CoursIA.

## Vue d'ensemble

QC Cloud offre 8 assistants IA qui executent des recherches, backtests, et validations directement sur la plateforme QuantConnect, consommant des QCC (QuantConnect Credits) au lieu de nos ressources locales.

| Assistant | Role | Cas d'usage cluster |
|-----------|------|---------------------|
| **Research Assistant** | Notebooks Jupyter (QuantBook) | Re-exec/reconstruction de notebooks QC-Py-* |
| **Backtest Assistant** | Backtests | Sweep multi-parametres quand MCP indisponible |
| **Ideas Assistant** | Ideation strategies | Brainstorming nouvelles strategies curriculum |
| **Research Validation Assistant** | Validation croisee | Verification resultats de recherche |
| **Conductor** | Orchestration | Workflows multi-etapes |
| **Paper Testing Assistant** | Paper trading | Deploy paper tests |
| **Live Monitoring Assistant** | Monitoring algos live | Surveillance 24/7 (Phase 3 future) |
| **Mia** | Generaliste | Taches QC generales |

## Acces

**URL** : `https://www.quantconnect.com/organization/{org-id}/assistants`
**Org ESGF** : `d600793ee4caecb03441a09fc2d00f7f`
**Credits restants** : ~3457 QCC (a verifier avant chaque deployment)
**Cout estime par session Research** : 800-1200 QCC (14 cells)

## Methode preferee vs Fallbacks

| Tache | Methode primaire | Fallback | Rationale |
|-------|------------------|----------|-----------|
| Notebooks QuantBook | **QC Research Assistant** | MCP `read_file` + local papermill | Assistant auto-debogue (NaN, colonnes, parametres) |
| Backtests | **MCP Docker** (`create_compile` -> `create_backtest`) | Backtest Assistant | MCP = gratuit, scriptable, repeatable |
| Paper trading | MCP `create_live_algorithm` | Paper Testing Assistant | MCP pour automatisation |
| Ideation strategies | LLM local (Qwen3.6) | Ideas Assistant | Gratuit, pas de cout QCC |

## Protocole de mesure des couts (calibrage)

### Principe

Avant de basculer le cluster vers les assistants de maniere systematique, **mesurer le cout reel** de 3 categories de complexite.

### Mesure

1. **Snapshot balance avant** : UI `Organization Settings > Billing > Credits`
2. **3 deployments calibrage** :
   - **Leger** : Research Assistant — re-executer 5-10 cells existantes (cible : QC-Py-* simple)
   - **Moyen** : Research Assistant — reconstruction 15-25 cells avec feature engineering (cote : ML-* moyen)
   - **Lourd** : Research Assistant — strategy from scratch (cf Portfolio Phase 1 = 105 features)
3. **Snapshot balance apres** : delta = cout
4. **Reporter** : `categorie | nb_cells | nb_features | balance_avant | balance_apres | delta_QCC | duree | quality`

**Budget calibrage** : 200 QCC max (garde 90%+ pour use cases reels).

### Resultats existants

| Deployment | Cells | Balance avant | Balance apres | Delta | Duree | Qualite |
|------------|-------|---------------|---------------|-------|-------|---------|
| Portfolio Phase 1 (A-8ad2fb) | 14 | ~3457 | ~2657 (estime) | ~800 | 45min | Sharpe 3.50 assistant vs 0.971 cluster |

_Note : le Sharpe assistant est inflated (pas tx costs, pas slippage, 365j annualisation, pas walk-forward)._

## Matrice de delegation

### Taches delegables aux assistants

| Tache cluster | Owner actuel | Delegation proposee | Conditions |
|---------------|-------------|--------------------:|------------|
| Re-exec 21 QC-Py-* (audit H.7) | po-2024 manuel | Research Assistant batch | Cout < 30 QCC/nb |
| Quantbooks `projects/*/quantbook.ipynb` | po-2024 via Playwright | Research Assistant | Fallback Playwright si echec |
| Strategy ideation (Curriculum V2) | ai-01 + po-2024 | Ideas + Research Assistant | Garder validation cluster-side |
| Notebook creation from scratch | po-2024 manuel | Research Assistant | Pour scaffold initial |

### Taches NON delegables (gardees cluster-side)

- **Validation multi-seed** (walk-forward 5-fold + >=4 seeds + edge >= 2sigma + 10bps tx) — regle G.2
- **Decisions strategiques** (curriculum, declassement vs maintien, achats QCC)
- **PR review + merge** (audit forensique H.4)
- **Recherche methodologique** (Hands-On AI Trading, papers)
- **Code algo `.py` production** (QC-Py-*, scripts training pipeline)

## Avertissements critiques

### Ecart de metriques (assistant vs cluster)

L'assistant rapporte des Sharpes **inflationnes** car :
- Pas de couts de transaction (5bps SPY, 10bps crypto)
- Pas de slippage
- Annualisation 365 jours (au lieu de 252)
- Pas de validation walk-forward

**Exemple** : Portfolio Phase 1 — Sharpe assistant 3.50 vs Sharpe cluster (blended) 0.971.

**Toujours re-valides cluster-side** les resultats assistants.

### Coordination obligatoire

- **Annoncer sur dashboard** avant chaque deployment (eviter chevauchement agents)
- **Rate limiter** : max 10 appels API/min (fleet-wide)
- **Budget restant** : verifier credits avant chaque session

## Procedure pas-a-pas (Research Assistant)

1. Naviguer vers `https://www.quantconnect.com/organization/d600793ee4caecb03441a09fc2d00f7f/assistants`
2. Selectionner **Research Assistant**
3. Pointer vers le projet cible (ex: QC-Py-15)
4. Donner des instructions claires (re-executer notebook, corriger erreurs, ajouter features)
5. L'assistant debogue automatiquement (NaN, colonnes manquantes, parametres)
6. **Download le notebook result** depuis le deployment
7. **Re-valider cluster-side** : Papermill local + verification multi-seed si ML

## References

- Issue #1195 : contexte + protocole + matrice delegation
- `feedback_qc_assistants_preferred.md` : methode preferee QC Cloud Assistants
- `docs/qc/quantconnect.md` : configuration MCP Docker + regles QC
- `docs/ml-trading-state.md` : 7 disciplines ML trading
- Portfolio IBKR-Binance-Hybrid : validation Phase 1 (deployment A-8ad2fb)

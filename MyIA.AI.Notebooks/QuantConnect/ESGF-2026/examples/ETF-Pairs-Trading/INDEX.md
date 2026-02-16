# Index: Documentation ETF-Pairs-Trading

**Projet QC**: 19865767 | **Analyse**: 2026-02-15 | **Statut**: NEEDS_IMPROVEMENT

---

## 🗂️ Guide de Navigation

### Pour les Pressés (5 minutes)

1. **EXECUTIVE_SUMMARY.md** - Métriques clés, plan d'action, tableau de bord visuel

### Pour les Développeurs (30 minutes)

1. **EXECUTIVE_SUMMARY.md** - Vue d'ensemble
2. **ANALYSIS_REPORT.md Section 7** - Propositions d'amélioration avec code
3. **SYNC_STATUS.md** - Vérifier synchronisation local/cloud

### Pour les Analystes Quant (2 heures)

1. **BACKTEST_DASHBOARD.md** - Distribution des 38 backtests
2. **ANALYSIS_REPORT.md Section 4-6** - Analyse du code ligne par ligne
3. **ANALYSIS_REPORT.md Section 9** - Risques et limitations

### Pour les Étudiants ESGF (Session complète)

1. **EXECUTIVE_SUMMARY.md** - Comprendre le diagnostic
2. **BACKTEST_DASHBOARD.md Section "Enseignements Pédagogiques"**
3. **ANALYSIS_REPORT.md Section 6** - Causes racines du Sharpe négatif
4. **research.ipynb** (local) - Reproduire l'analyse
5. **ANALYSIS_REPORT.md Section 7** - Implémenter une amélioration

---

## 📄 Documents par Type

### Rapports d'Analyse

| Document | Taille | Public Cible | Temps Lecture |
|----------|--------|--------------|---------------|
| **EXECUTIVE_SUMMARY.md** | 3,000 mots | Tous | 5-10 min |
| **ANALYSIS_REPORT.md** | 10,000 mots | Développeurs, Analystes | 30-60 min |
| **BACKTEST_DASHBOARD.md** | 5,000 mots | Analystes Quant | 20-30 min |
| **SYNC_STATUS.md** | 3,000 mots | Développeurs | 10-15 min |

### Documentation Technique

| Document | Contenu | Dernière Mise à Jour |
|----------|---------|----------------------|
| **README.md** | Présentation générale, architecture | 2026-02-15 |
| **main.py** | Code principal (117 lignes) | 2026-02-14 |
| **alpha.py** | Modèle alpha (67 lignes) | 2026-02-14 |
| **portfolio.py** | Construction portfolio (105 lignes) | 2026-02-14 |
| **risk.py** | Gestion risque (44 lignes) | 2026-02-14 |
| **utils.py** | Utilitaires warm-up (57 lignes) | 2026-02-14 |
| **universe.py** | Sélection univers (35 lignes) | 2026-02-14 |

### Notebooks de Recherche

| Document | Description | Outils Utilisés |
|----------|-------------|-----------------|
| **research.ipynb** | Analyse co-intégration, mini-backtest | pandas, statsmodels, matplotlib |

---

## 🎯 Par Objectif

### "Je veux comprendre pourquoi le Sharpe est négatif"

1. **EXECUTIVE_SUMMARY.md** → Section "Diagnostic Principal"
2. **ANALYSIS_REPORT.md** → Section 6 "Causes Racines du Sharpe Négatif"

**TL;DR**: 8 causes identifiées, impact cumulé -1.05 Sharpe.

### "Je veux corriger la stratégie"

1. **ANALYSIS_REPORT.md** → Section 7 "Propositions d'Amélioration"
2. **EXECUTIVE_SUMMARY.md** → Section "Plan d'Action (3 Phases)"

**TL;DR**: Phase 1 (Quick Wins) = 4 changements, 1-2h, +0.5 Sharpe attendu.

### "Je veux voir les backtests historiques"

1. **BACKTEST_DASHBOARD.md** → Section "Top 10 Backtests"
2. **BACKTEST_DASHBOARD.md** → Section "Backtests avec Runtime Errors"

**TL;DR**: 38 backtests, 53% erreurs, meilleur Sharpe = -0.373 (completed).

### "Je veux vérifier la synchro local/cloud"

1. **SYNC_STATUS.md** → Section "Résumé Exécutif"
2. **SYNC_STATUS.md** → Section "Détails par Fichier"

**TL;DR**: Code synchronisé ✅, paramètres divergents ⚠️ (60/2 cloud vs 20/2.2 local).

### "Je veux comprendre le pattern Win Rate 50% mais perte"

1. **ANALYSIS_REPORT.md** → Section 6.3 "Décomposition du Win Rate 50%"
2. **EXECUTIVE_SUMMARY.md** → Section "Leçons Pédagogiques" #1

**TL;DR**: Losses moyennes 0.2% supérieures aux wins → Asymétrie.

---

## 🔍 Par Section du Rapport

### EXECUTIVE_SUMMARY.md (Résumé Exécutif)

| Section | Contenu Clé |
|---------|-------------|
| Synthèse en 3 Points | Statut, Sync, Causes |
| Métriques vs Cibles | Tableau comparatif |
| Diagnostic Principal | Décomposition impact par cause |
| Historique 38 Backtests | Distribution résultats |
| Synchronisation | État local vs cloud |
| Plan d'Action | 3 phases, 10 améliorations |
| Insights Backtest Référence | Paires tradées, pattern signaux |
| Leçons Pédagogiques | 5 concepts clés |
| Questions Résolues | FAQ |
| Documents Générés | Liste + descriptions |
| Actions Immédiates | To-do Dev/Étudiants/Formateur |
| Tableau de Bord Visuel | Résumé ASCII art |
| Métrique de Succès | Critères d'acceptation |

### ANALYSIS_REPORT.md (Analyse Approfondie)

| Section | Contenu Clé |
|---------|-------------|
| 1. Synthèse Exécutive | Métriques actuelles tableau |
| 2. Analyse Historique Backtests | Top 3, patterns erreurs |
| 3. Synchronisation Code | Vérification fichier par fichier |
| 4. Analyse des Insights | 50 premiers insights, paires |
| 5. Analyse du Code | Problèmes par fichier (main, alpha, portfolio, risk) |
| 6. Causes Racines Sharpe Négatif | 8 causes avec impact estimé |
| 7. Propositions d'Amélioration | 8 améliorations avec code |
| 8. Plan d'Action | 3 phases détaillées |
| 9. Risques et Limitations | Overfitting, régime shifts, frais |
| 10. Conclusion | Sharpe attendu, next steps |

### BACKTEST_DASHBOARD.md (Dashboard)

| Section | Contenu Clé |
|---------|-------------|
| Métriques Globales | Aggregation 38 backtests |
| Top 10 Backtests | Par Sharpe ratio |
| Backtests Runtime Errors | 20 erreurs analysées |
| Backtests Completed | Rentables vs perdants |
| Évolution Temporelle | Sharpe et profit par date |
| Analyse par Paramètres | Impact lookback/threshold |
| Deep Dive Backtest Référence | Métriques détaillées a87dea4a |
| Alertes et Anomalies | Série 2.666, duplicatas, 0 trades |
| Checklist Validation | Avant/après backtest |
| Enseignements Pédagogiques | 5 concepts illustrés |
| Prédictions Prochains Backtests | 3 scénarios |
| Références et Ressources | Backtests critiques, commandes MCP |

### SYNC_STATUS.md (État Synchronisation)

| Section | Contenu Clé |
|---------|-------------|
| Résumé Exécutif | Statut sync global |
| Détails par Fichier | 6 fichiers comparés |
| Analyse Différences Paramètres | Cloud 60/2 vs local 20/2.2 |
| Historique Modifications | Timeline changements |
| Backtests Historiques vs Code | Corrélation snapshots/résultats |
| Actions Recommandées | Harmonisation, push, documentation |
| Checksum Validation | Hash comparaison |
| Conclusion | État MOSTLY_SYNCED |

---

## 📊 Données Clés en 1 Coup d'Œil

### Métriques Projet

```
Sharpe Ratio:       -0.759  (Cible: > 0.5)
Net Profit:         -14.566% (Cible: > 0%)
Win Rate:           50%     (Cible: > 55%)
Max Drawdown:       19.8%   (Cible: < 30%)
Trades:             304     (Cible: > 100)
Beta:               0.014   (Cible: ~0)
```

### Backtests

```
Total:              38
Completed:          18 (47%)
Runtime Errors:     20 (53%)
Sharpe > 0:         0 (0% des completed)
Meilleur Sharpe:    -0.373 (completed)
```

### Synchronisation

```
Code logique:       ✅ 100% identique
Paramètres:         ⚠️ Divergent (60/2 vs 20/2.2)
Correction arch:    ✅ Appliquée
Fichiers sync:      6/6
```

### Impact Améliorations

```
Phase 1 (Quick Wins):      +0.5 Sharpe  [1-2h]
Phase 2 (Refactoring):     +0.4 Sharpe  [1 jour]
Phase 3 (Restructuration): +0.2 Sharpe  [2-3 jours]
                          ─────────────
Total:                     +1.1 Sharpe  (145% improvement)
Sharpe final attendu:      +0.2 à +0.5
```

---

## 🎓 Guides d'Utilisation

### Pour Implémenter Phase 1 (Quick Wins)

1. Ouvrir `ANALYSIS_REPORT.md`
2. Aller à Section 7 "Propositions d'Amélioration"
3. Lire "Amélioration 1" à "Amélioration 4"
4. Appliquer les 4 changements dans le code local:
   - main.py ligne 96: supprimer `corr > 0.6`
   - main.py ligne 78: `500` → `1638`
   - main.py ligne 24: `2.0` → `1.5`
   - main.py ligne 101: trier par p-value
5. Compiler via `qc-helpers.md` skill
6. Pusher vers cloud via MCP `update_file_contents`
7. Lancer backtest
8. Comparer avec baseline (Sharpe -0.759)

### Pour Analyser un Backtest Spécifique

**Exemple**: Analyser le backtest avec runtime error (Sharpe 2.666)

1. ID backtest: `2b3c7b1e716050782ce00e9e28fe1bdd`
2. Lire les détails:
   ```python
   mcp__qc-mcp__read_backtest(
       projectId=19865767,
       backtestId="2b3c7b1e716050782ce00e9e28fe1bdd"
   )
   ```
3. Chercher la stacktrace dans le JSON retourné
4. Identifier la ligne d'erreur
5. Vérifier si l'erreur est liée à:
   - Univers vide
   - Division par zéro (z-score)
   - Import manquant
6. Documenter dans `BACKTEST_DASHBOARD.md` section "Erreurs par Type"

### Pour Reproduire l'Analyse Localement

1. Ouvrir `research.ipynb`
2. Lancer les cellules 1-4 (setup + data)
3. Section "Recalibrer détection de paires" (cellule 5):
   - Modifier `pval_threshold=0.10` → `0.05` (proposition amélioration)
   - Observer le nombre de paires retenues
4. Section "Test co-intégration glissant" (cellule 6):
   - Choisir une paire de la liste filtrée
   - Analyser la stabilité de la p-value
5. Section "Génération signaux via z-score" (cellule 7):
   - Tester `z_threshold=1.5` (vs 2.0 actuel)
   - Compter le nombre de signaux générés
6. Section "Mini backtest" (cellule 8):
   - Calculer le PnL théorique
   - Comparer avec les résultats cloud

---

## 🔗 Liens Utiles

### Interne au Projet

- **Code source**: `c:\dev\CoursIA\MyIA.AI.Notebooks\QuantConnect\ESGF-2026\examples\ETF-Pairs-Trading\`
- **Agent analyzer**: `.claude\agents\qc-strategy-analyzer.md`
- **Skill helpers**: `.claude\skills\qc-helpers.md`

### QuantConnect Cloud

- **Projet URL**: https://www.quantconnect.com/project/19865767
- **Meilleur backtest**: https://www.quantconnect.com/terminal/#open/19865767/a87dea4ac445839351d05d15a17ec371
- **Organisation**: Trading Firm ESGF (94aa4bcb...)

### Documentation Théorique

- **Co-intégration Engle-Granger**: Statsmodels docs
- **Pairs Trading**: QuantConnect tutorials
- **Alpha Framework**: QuantConnect architecture guide

---

## 📅 Historique des Versions

| Version | Date | Auteur | Changements |
|---------|------|--------|-------------|
| 1.0 | 2026-02-15 | Claude QC Analyzer | Création initiale (5 documents) |

---

## ❓ FAQ Rapide

**Q: Par où commencer?**
A: EXECUTIVE_SUMMARY.md (5 min)

**Q: Comment corriger la stratégie?**
A: ANALYSIS_REPORT.md Section 7, Phase 1 (1-2h)

**Q: Pourquoi tant d'erreurs runtime?**
A: BACKTEST_DASHBOARD.md Section "Backtests Runtime Errors"

**Q: Le code local est-il à jour?**
A: SYNC_STATUS.md Section "Résumé Exécutif" (réponse: OUI pour logique, NON pour paramètres)

**Q: Quel Sharpe attendre après corrections?**
A: +0.2 à +0.5 (détails: ANALYSIS_REPORT.md Section 10)

---

## 📞 Support

**Questions techniques**: Voir `.claude/agents/qc-strategy-analyzer.md`
**Bugs dans l'analyse**: Ouvrir issue dans le repo CoursIA
**Suggestions d'amélioration**: Documenter dans `ANALYSIS_REPORT.md` Section 7 (nouvelles propositions)

---

**Index généré le**: 2026-02-15 23:10
**Prochaine mise à jour**: Après implémentation Phase 1

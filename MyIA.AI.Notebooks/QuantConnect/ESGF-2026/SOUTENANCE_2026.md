# Rubrique d'Evaluation - Soutenance ESGF 2026

**Date soutenance** : 19 mai 2026
**Duree** : 15 minutes (10 min presentation + 5 min questions)
**Format** : Presentation Slidev (obligatoire)

---

## Pondration

| Categorie | Poids | Description |
|-----------|:-----:|-------------|
| **Backtest** | 30% | Qualite et pertinence des resultats de backtest |
| **Strategie** | 30% | Originalite, pertinence, et rigueur du modele alpha |
| **Presentation** | 20% | Clarte, structure, visualisation, maitrise du sujet |
| **Code** | 20% | Proprete, documentation, reproductibilite |

---

## Grille d'evaluation detaillee

### 1. Backtest (30 points)

| Critere | Points | Excellent (25-30) | Bon (18-24) | Insuffisant (<18) |
|---------|:------:|-------------------|-------------|--------------------|
| Resultats | 10 | Sharpe > 1.0, CAGR > 10%, MaxDD < 20% | Sharpe 0.5-1.0, resultats corrects | Sharpe < 0, perte de capital |
| Periode de test | 5 | 3+ ans, plusieurs regimes de marche | 1-3 ans | < 1 an |
| Analyse | 10 | Drawdown analyse, comparaison benchmark, discussion ecarts | Analyse basique mais presente | Pas d'analyse |
| Robustesse | 5 | Test sur periodes differentes, parametres varies | Un seul backtest | Resultats non fiables |
| Benchmark | 5 | Comparaison avec Buy & Hold + un benchmark pertinent | Comparaison Buy & Hold uniquement | Pas de benchmark |

**Minimum requis** : backtest sur au moins 2 ans, Sharpe > 0, comparaison avec benchmark.

### 2. Strategie (30 points)

| Critere | Points | Excellent (25-30) | Bon (18-24) | Insuffisant (<18) |
|---------|:------:|-------------------|-------------|--------------------|
| Originalite | 10 | Approche originale, bien motivee | Variation d'une strategie connue | Copie d'exemple existant |
| Fondement theorique | 10 | References academiques, justification des signaux | Explication logique sans references | Pas de justification |
| Indicateurs | 5 | Choix motive, parametres optimises rationnellement | Indicateurs standards bien utilises | Choix arbitraire |
| Risk management | 5 | Stop-loss, position sizing, diversification explicites | Stop-loss present | Pas de gestion du risque |

**Minimum requis** : strategie avec logique claire, au moins 2 indicateurs, stop-loss.

### 3. Presentation (20 points)

| Critere | Points | Excellent (16-20) | Bon (11-15) | Insuffisant (<11) |
|---------|:------:|-------------------|-------------|--------------------|
| Structure | 5 | Plan clair, transitions, conclusion | Logique mais desequilibre | Desordonne |
| Visualisation | 5 | Graphiques lisibles, pertinents, legende | Graphiques presents mais basiques | Pas de graphiques |
| Maitrise | 5 | Reponses aux questions, pas de lecture de slides | Reponses partielles | Ne maitrise pas le sujet |
| Timing | 5 | 10 min +/- 1 min | 8-12 min | < 7 min ou > 13 min |

**Minimum requis** : respect du template Slidev, graphiques de resultats, timing correct.

### 4. Code (20 points)

| Critere | Points | Excellent (16-20) | Bon (11-15) | Insuffisant (<11) |
|---------|:------:|-------------------|-------------|--------------------|
| Compilation | 5 | Compile sans erreur ni warning | Compile avec warnings | Ne compile pas |
| Documentation | 5 | README complet, commentaires, docstrings | README basique | Pas de documentation |
| Reproductibilite | 5 | Requirements, parametres documentes, seed fixe | Parametres dans le code | Pas reproductible |
| Structure | 5 | Code modularise, noms clairs, pas de hardcode | Code fonctionnel | Code spaghetti |

**Minimum requis** : code compilable, README avec instructions, parametres visibles.

---

## Barme

| Note | Mention |
|------|---------|
| 80-100 | Excellent |
| 65-79 | Tres bien |
| 50-64 | Bien |
| 35-49 | Passable |
| < 35 | Insuffisant |

---

## Procure de soutenance

1. **Pre-soutenance (J-2)** : upload du projet dans l'org ESGF
2. **Soutenance** : 10 min presentation + 5 min questions
3. **Demo live (optionnel)** : demonstration paper trading en direct (bonus +5 points)

## Communication

Cette rubrique sera partagee avec les etudiants **7 jours avant la soutenance** (12 mai 2026).

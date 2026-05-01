---
theme: default
title: Template Soutenance ESGF 2026
info: |
  Template de presentation pour la soutenance ESGF QuantConnect.
  Remplacer les sections entre [crochets] avec votre contenu.
class: text-center
drawings:
  persist: false
transition: slide-left
mdc: true
---

# [Nom de Votre Strategie]

Soutenance ESGF QuantConnect - 19 mai 2026

**Equipe** : [Prenom Nom, Prenom Nom]
**Projet** : [Nom du projet QC]

<div class="abs-br m-6 text-xl">
  <a href="https://www.quantconnect.com" target="_blank">QuantConnect</a>
</div>

---
layout: default
---

# Plan de la Presentation

1. Introduction et motivation
2. Donnees et univers
3. Modele alpha
4. Resultats de backtest
5. Analyse et robustesse
6. Demo (optionnel)
7. Conclusion

---
layout: default
---

# 1. Introduction et Motivation

## Pourquoi cette strategie ?

- **Probleme** : [Quel probleme de marche visez-vous ?]
- **Hypothese** : [Quel phenomenes financier exploitez-vous ?]
- **Objectif** : [Quel rendement/Sharpe visez-vous ?]

## Contexte de marche

- [Marche cible : crypto / equities / forex]
- [Regime de marche actuel]
- [Opportunite identifiee]

---
layout: default
---

# 2. Donnees et Univers

## Actifs selectionnes

| Actif | Marche | Resolution | Justification |
|-------|--------|------------|---------------|
| [BTCUSDT] | [Crypto] | [Minute] | [Liquidite, volatilite] |
| [...] | [...] | [...] | [...] |

## Periode de backtest

- **Debut** : [YYYY-MM-DD]
- **Fin** : [YYYY-MM-DD]
- **Duree** : [X ans]
- **Raison** : [Pourquoi cette periode ?]

## Preprocessing

- [Nettoyage des donnees]
- [Gestion des valeurs manquantes]
- [Normalisation si applicable]

---
layout: default
---

# 3. Modele Alpha

## Signaux d'entree

- **Indicateur 1** : [Nom, parametres, justification]
- **Indicateur 2** : [Nom, parametres, justification]
- **Condition d'entree** : [Logique precise]

## Signaux de sortie

- **Take-profit** : [Condition]
- **Stop-loss** : [Condition et pourcentage]
- **Temps max** : [Si applicable]

## Gestion du risque

- Position sizing : [methode]
- Max positions : [nombre]
- Drawdown max tolere : [pourcentage]

---
layout: center
class: text-center
---

# 4. Resultats de Backtest

[Inserez votre equity curve ici]

![Equity Curve](equity_curve.png)

---
layout: default
---

# Metriques Cles

| Metrique | Valeur | Benchmark |
|----------|--------|-----------|
| Rendement total | [X%] | [Y%] |
| CAGR | [X%] | [Y%] |
| Sharpe Ratio | [X] | [Y] |
| Max Drawdown | [X%] | [Y%] |
| Win Rate | [X%] | - |
| Nombre de trades | [X] | - |
| Profit Factor | [X] | - |

---
layout: default
---

# Analyse des Resultats

## Points forts

- [Premier point fort avec donnees]
- [Deuxieme point fort avec donnees]

## Points faibles

- [Premier point faible identifie]
- [Deuxieme point faible identifie]

## vs Benchmark

- [Comparaison avec Buy & Hold]
- [Comparaison avec un autre benchmark si pertinent]

---
layout: default
---

# Robustesse

## Test sur sous-periodes

| Periode | Rendement | Sharpe | MaxDD |
|---------|-----------|--------|-------|
| [2021] | [X%] | [X] | [X%] |
| [2022] | [X%] | [X] | [X%] |
| [2023] | [X%] | [X] | [X%] |
| [2024] | [X%] | [X] | [X%] |

## Sensibilite aux parametres

- [Parametre 1] : plage testee, impact sur Sharpe
- [Parametre 2] : plage testee, impact sur MaxDD

---
layout: default
---

# Demo (Optionnel)

## Paper trading en direct

- Lien vers le projet QuantConnect : [URL]
- Statut paper trading : [En cours / Resultats]
- Comparaison paper vs backtest : [Ecart observe]

---
layout: default
---

# Conclusion

## Bilan

- [Resume en 2-3 phrases de la performance]

## Ameliorations futures

- [Piste d'amelioration 1]
- [Piste d'amelioration 2]

## Apprentissages

- [Ce que vous avez appris sur le trading algorithmique]
- [Ce que vous feriez differemment]

---
layout: center
class: text-center
---

# Merci !

**Questions ?**

Equipe : [Prenom Nom, Prenom Nom]
Projet : [Nom du projet QC]
GitHub : [Lien vers le repo]

# Réseau Électrique Intelligent — ordonnancement énergétique sous incertitude

[← CaseStudies](../README.md) | [↑ Études de cas](../README.md)

Le problème réel de l'*unit commitment / dispatch* : décider heure par heure
quelles centrales allumer et à quelle puissance, alors que la production
renouvelable est incertaine. Trois couches se composent **dans un ordre
qu'inverser dégrade le résultat** : le solveur **CP-SAT** filtre les
dispatchs impossibles, le modèle **bayésien** (risque de défaillance
gaussien sur la réserve) modélise l'incertitude, l'**arbitrage
multi-objectif** (coût / CO2 / risque) optimise.

**Public** : étudiants EPF (CC3, 3-4 h, 20 points) ; prérequis : Python,
notions d'optimisation sous contraintes.

## Comment lire ce README

Les parcours se lisent à plusieurs vitesses — voir
[« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture)
à la racine du dépôt :

- **Vous découvrez** : lisez le parcours principal ci-dessous, puis le
  carnet `student/` de bout en bout.
- **Vous creusez un palier** : passez au corrigé type `solution/` et aux
  exercices d'extension ci-dessous.
- **Vous cherchez la recherche en cours** : section « Pour aller plus loin ».

## Parcours principal

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|----------|--------------------|--------|------------------|
| 01 | [Squelette étudiant](student/Reseau-Electrique-Intelligent-Python.ipynb) | Le jumeau numérique `PowerNetwork` opérationnel (3 centrales charbon / gaz / hydro, demande 500-600 MW sur 6 heures, prévision renouvelable moyenne ± écart-type) et les squelettes des 4 couches : unit commitment CP-SAT, risque de défaillance, score multi-objectif, analyse comparative — 3 exercices d'extension nommés | Étudiant (CC3) | [Corrigé type](solution/Reseau-Electrique-Intelligent-Python.ipynb) |
| 02 | [Corrigé type](solution/Reseau-Electrique-Intelligent-Python.ipynb) | Dispatch OPTIMAL (coût 63 600 EUR, ordre de mérite : charbon 270-340 MW, hydro plat à 150 MW, gaz jamais appelé), risques de l'ordre de 10⁻³⁵ à 10⁻²⁸⁴ pilotés par l'écart-type et non par la demande, score 1,137 décomposé (coût 0,32 / CO2 0,82 / risque ≈ 0), 3 stratégies comparées (1,596 / 1,560) et le prix de l'écologie mesuré : 0,06 €/kg de CO2 évité | Enseignant / relecture | Les 3 exercices d'extension restent en stub |

## Approfondissements

Les trois exercices d'extension, présents en stub dans les deux carnets :

1. **Réserve tournante (sécurité n-1)** — `solve_dispatch_with_spinning_reserve`.
2. **Sensibilité au prior** — variabilité éolienne ×0,5 / ×1,0 / ×2,0.
3. **Équité territoriale** — un troisième objectif au score multi-objectif.

## Sous-séries

Aucune : le cas est plat — `student/` et `solution/` (pas de données
externes). L'énoncé complet du sujet vit dans [subject.md](subject.md).

## Installation

Noyau Python ; les dépendances sont pré-provisionnées par
[`CaseStudies/requirements.txt`](../requirements.txt) : ortools, numpy,
scipy.

## Pour aller plus loin

Niveau Recherche : l'arbitrage multi-objectif normalisé (coût / émissions /
risque) comme décision d'ordonnancement — le même patron de composition
« dur puis incertain » que le cas [Planification
Oncologique](../Planification-Oncologie/README.md).

## Ressources

- [Études de cas interdisciplinaires](../README.md) — la série parent
- [Énoncé du sujet](subject.md)

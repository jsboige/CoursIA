# Diagnostic Médical — un pipeline d'aide à la décision en quatre briques

[← CaseStudies](../README.md) | [↑ Études de cas](../README.md)

Cette étude de cas compose quatre approches d'IA qui répondent à quatre
questions différentes, appliquées au diabète de type 2 : un **agent à règles
cliniques** qui trie le patient, la **recherche A\*** qui explore l'espace
des hypothèses diagnostiques, un **algorithme génétique** qui calibre les
seuils diagnostiques, et le **solveur Z3** qui valide le protocole
thérapeutique (contre-indications, doses, interactions). Aucune brique ne
fait le travail d'une autre : le pipeline Agent → A\* → génétique → Z3 se
compose sans les fusionner.

**Public** : étudiants EPF (CC1 « IA Exploratoire et Symbolique ») ;
prérequis : Python, bases de la recherche informée et des solveurs de
contraintes (les carnets de la série Search en amont).

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
| 01 | [Squelette étudiant](student/Diagnostic-Medical-Python.ipynb) | L'agent à règles (Normal / Pré-diabète / Diabète T2 sur glycémie à jeun, post-prandiale et HbA1c), A\* sur 7 hypothèses avec heuristique médicale, calibration de 6 paramètres diagnostiques par algorithme génétique, validation Z3 du protocole — en squelette, 3 exercices d'extension nommés | Étudiant (CC1) | [Corrigé type](solution/Diagnostic-Medical-Python.ipynb) |
| 02 | [Corrigé type](solution/Diagnostic-Medical-Python.ipynb) | Le pipeline complet exécuté sur `data/patients.csv` : triage de 3 profils mesurés (85 mg/dL et 5,2 % → normal, 115 mg/dL et 6,0 % → pré-diabétique, 140 mg/dL et 7,8 % → diabète T2), convergence d'A\* en 308 itérations, fitness génétique 16,731 → 17,957 entre générations 0 et 20, taux de validation Z3 et 5 tests automatisés | Enseignant / relecture | Les 3 exercices d'extension restent en stub |

## Approfondissements

Les trois exercices d'extension, présents en stub dans les deux carnets :

1. **Score de risque composite** — étendre l'agent de diagnostic (`calculer_score_risque`).
2. **Heuristiques A\* alternatives** — comparer les heuristiques de l'espace diagnostique.
3. **Contraintes d'interaction médicamenteuse** — ajouter les interactions au solveur Z3.

## Sous-séries

Aucune : le cas est plat — `student/`, `solution/` et `data/` (patients de
test). L'énoncé complet du sujet vit dans [subject.md](subject.md).

## Installation

Noyau Python ; les dépendances sont pré-provisionnées par
[`CaseStudies/requirements.txt`](../requirements.txt) (pandas, numpy,
matplotlib, seaborn, z3-solver) — aucun `pip install` dans les carnets.

## Pour aller plus loin

Niveau Recherche : la calibration génétique comme méta-heuristique au-dessus
du triage à règles, et la validation SMT comme garantie de sûreté du
protocole — le même patron que le cas
[Planification Oncologique](../Planification-Oncologie/README.md), où la
frontière symbolique/probabiliste remplace la validation par contraintes.

## Ressources

- [Études de cas interdisciplinaires](../README.md) — la série parent
- [Énoncé du sujet](subject.md)
- `data/patients.csv` — patients de test

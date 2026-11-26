# Planification Oncologique — OncoPlan, le protocole adaptatif

[← CaseStudies](../README.md) | [↑ Études de cas](../README.md)

Cette étude de cas répartit un problème d'oncologie le long d'une
**frontière** entre ce qui *doit être respecté* (déterministe) et ce qui
*doit être estimé* (probabiliste) : une **ontologie RDF** vérifie la
prescription, un **solveur CP-SAT** planifie les cures et l'occupation des
lits, un **modèle bayésien Pyro** estime le profil latent du patient
(Résistant / Normal / Sensible), et un **contrat haché** (SHA-256, deux
signatures) garantit l'audit. Le « jumeau numérique » du patient simule les
scénarios de dose avant la décision.

**Public** : étudiants EPF (CC2 « OncoPlan », cours IA101) ; prérequis :
Python — le glossaire Pyro du carnet rend l'inférence accessible sans
préparation en programmation probabiliste.

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
| 01 | [Squelette étudiant](student/Planification-Oncologie-Python.ipynb) | Ontologie RDF de 4 molécules (`toxicite_renale`, `incompatible_avec`) avec vérification de prescription, planification CP-SAT de 4 cycles de 21 jours (pas de dimanche, capacité 3 lits), modèle Pyro (profil latent 3 valeurs, toxicité cumulée, likelihood sur globules blancs), prédiction sur 2 scénarios de dose, contrat `OncoContract` — en squelette, 3 exercices d'extension nommés | Étudiant (CC2) | [Corrigé type](solution/Planification-Oncologie-Python.ipynb) |
| 02 | [Corrigé type](solution/Planification-Oncologie-Python.ipynb) | L'ontologie peuplée (14 triplets), 4 protocoles réels (AC sein 4×21 j, FOLFOX 6×14 j, BEP 3×21 j, CHOP 6×21 j) avec makespan optimal 107 jours, posterior SVI « Résistant 0,92 / Normal 0,04 / Sensible 0,04 » menant à « réduction de dose impérative », contrat qui autorise l'administration et refuse un plan modifié | Enseignant / relecture | 3 exercices d'extension + la simulation `Predictive` restent en stub |

## Approfondissements

Les trois exercices d'extension, présents en stub dans les deux carnets :

1. **Ontologie étendue** — ajouter Paclitaxel et Carboplatine.
2. **Sensibilité au prior** — le profil patient face au prior du modèle.
3. **Journal d'audit** — auditer le contrat intelligent.

## Sous-séries

Aucune : le cas est plat — `student/`, `solution/` et `data/`
(patients_oncology.csv). L'énoncé complet du sujet vit dans
[subject.md](subject.md).

## Installation

Noyau Python ; les dépendances sont pré-provisionnées par
[`CaseStudies/requirements.txt`](../requirements.txt) : rdflib, ortools,
pyro-ppl, torch, pandas, matplotlib, seaborn. L'inférence est reproductible
: `pyro.set_rng_seed(101)` dans le carnet.

## Pour aller plus loin

Niveau Recherche : la programmation probabiliste (SVI / Trace_ELBO) comme
estimateur de profil latent, et CP-SAT comme planificateur dur à horizon
borné — le contraste avec le cas
[Diagnostic Médical](../Diagnostic-Medical/README.md), où tout est
déterministe et validé par contraintes.

## Ressources

- [Études de cas interdisciplinaires](../README.md) — la série parent
- [Énoncé du sujet](subject.md)
- `data/patients_oncology.csv`

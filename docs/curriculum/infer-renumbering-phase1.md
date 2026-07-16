# #5081 — Probas/Infer : analyse de renumérotation (phase 1, docs-only)

> **EPIC #5081** — Renumérotation narrative des séries. **Fille issue Probas/Infer.**
> **Phase 1 = analyse docs-only, ZÉRO rename** (leçon #4737→#4743 : un rename casse les liens inbound).
> GREENLIGHT ai-01 (DM msg-20260716T173033-z9cpjj, 2026-07-16) — livrable = table cible + inventaire inbound-links + baseline `check_docs_links`, soumis à review ai-01 avant toute vague de renames.

## Méthode

Évaluation **firsthand** (lecture directe des notebooks + check automatique du DAG des prereqs),
sur `origin/main` (d239a62e5). Le verdict ne repose pas sur une impression, mais sur deux
vérifications mécaniques :

1. **Tri topologique** — pour chaque notebook, vérifier que tous ses prereqs déclarés pointent vers
   un numéro **strictement inférieur** (le seul signal réel d'un ordre cassé).
2. **Carte thématique** — regrouper les 19 notebooks par arc narratif (fondations → modèles
   graphiques → applications → temporel → avancé) et comparer à l'ordre numérique.

## Verdict : **AUCUNE renumérotation nécessaire pour Probas/Infer**

### Preuve 1 — l'ordre numérique 1→19 est un tri topologique VALIDE du DAG des prereqs

Check automatique sur les 19 notebooks : **0 arête broken-order**. Chaque prereq déclaré pointe
vers un numéro strictement inférieur. Les notebooks récemment ajoutés (Infer-18 Change-Point,
Infer-19 Survival) ont reçu les numéros *suivants* disponibles (18, 19) et s'insèrent correctement
en fin de corpus — l'anti-pattern dénoncé par #5081 (« numérotation d'opportunité ») **ne s'applique
pas** à cette série : les ajouts récents tombent à la bonne place pédagogique (cluster temporel
14→17→18, et Survival comme application autonome en 19).

### Preuve 2 — l'arc thématique suit déjà un flux pédagogique cohérent

| Arc | Numéros | Justification |
|-----|---------|---------------|
| **Fondations** | 1, 2, 3 | Setup → Gaussiens (continu) → Factor graphs (discret, Monty Hall) — progression du simple au composé |
| **Modèles graphiques** | 4, 5 | Réseaux bayésiens → Inférence causale (do-calculus de Pearl) — causality après CPT |
| **Méta / tooling** | 6 | Debugging (intercalaire utilitaire, prereq « avoir exploré plusieurs notebooks ») |
| **Applications à variable latente** | 7, 8, 9 | IRT (psychométrie) → TrueSkill (ranking, prereq 7) → Classification (BPM) |
| **Méta / comparaison** | 10 | Model selection (Bayes factors, ARD) |
| **Modèles structurés** | 11, 12, 13 | LDA (topics) → Hiérarchiques (pooling) → Crowdsourcing (Dawid-Skene) |
| **Temporel** | 14, 17, 18 | Séquences/HMM → Filtre de Kalman → Détection de rupture — **cluster temporel cohérent** (14<17<18, tous prereq Infer-14) |
| **Applications diverses** | 15, 19 | Recommenders (factorisation) → Survival (analyse de risque) |
| **Avancé / non-paramétrique** | 16 | Sparse Gaussian Process (frontières non-linéaires) |

L'ordre numérique respecte ces arcs : les clusters (temporel 14/17/18 ; fondations 1/2/3) sont
contigus ou correctement ordonnés.

## Point de vigilance (hors-scope de #5081) — 3 arêtes de prereq sémantiquement faibles

Le DAG est topologiquement valide, MAIS 3 arêtes de prereq sont **sémantiquement distantes**
(un rename ne les corrigerait pas — elles restent faibles quelle que soit la position) :

| Notebook | Prereq déclaré | Problème |
|----------|----------------|----------|
| Infer-11 Topic-Models (LDA) | Infer-8 TrueSkill | TrueSkill→LDA n'est pas une dépendance pédagogique évidente (TrueSkill sert d'exemple « variable array », lien faible) |
| Infer-15 Recommenders | Infer-14 Sequences (HMM) | La recommandation par factorisation ne nécessite pas les HMM |
| Infer-9 Classification | Infer-6 Debugging | La classification BPM ne nécessite pas le debugging |

**Ce sont des préoccupations de prose (clarifier / relâcher ces prereqs), pas de renumérotation.**
Elles sortent du scope de #5081 (qui vise l'ordre des numéros, pas la qualité des arêtes de prereq).
À traiter dans une PR séparée si pertinent.

## Inventaire inbound-links (baseline pour évaluer le coût d'un rename hypothétique)

Chaque notebook Infer est référencé à **7-44 endroits** dans le repo (README de série, README Probas,
`docs/curriculum/recherche.md`, `docs/ledgers/3801-sota-axe2.md`, `Probas/PORT_PYTHON_PLAN*.md`,
`IIT/README.md`, `Probas/DecisionTheory/DecInfer/README.md`). Un rename impliquerait de corriger
l'intégralité de ces références (leçon #4737→#4743). Puisqu'aucune renumérotation n'est nécessaire,
ce coût est évité.

| Notebook | Refs inbound | Notebook | Refs inbound |
|----------|-------------|----------|-------------|
| Infer-1-Setup | 23 | Infer-11-Topic-Models | 14 |
| Infer-2-Gaussian-Mixtures | 34 | Infer-12-Modeles-Hierarchiques | 19 |
| Infer-3-Factor-Graphs | 31 | Infer-13-Crowdsourcing | 7 |
| Infer-4-Bayesian-Networks | 28 | Infer-14-Sequences | 44 |
| Infer-5-Causal-Inference | 30 | Infer-15-Recommenders | 11 |
| Infer-6-Debugging | 32 | Infer-16-Sparse-Gaussian-Process | 15 |
| Infer-7-Skills-IRT | 19 | Infer-17-Kalman-Filter | 21 |
| Infer-8-TrueSkill | 14 | Infer-18-Change-Point | 11 |
| Infer-9-Classification | 21 | Infer-19-Survival-Analysis | 9 |
| Infer-10-Model-Selection | 21 | | |

## Baseline `check_docs_links`

- **0 lien cassé** pré-existant, 3968 liens totaux (sur `origin/main` d239a62e5).
- Un rename correct aurait pour post-condition de maintenir ce 0 ; un rename incorrect le ferait
  passer > 0. Puisque aucune renumérotation n'est nécessaire, cette baseline reste la cible.

## Recommendation pour ai-01

**Clôturer la fille Probas/Infer de #5081 comme « no-defect-found »** : l'ordre numérique 1→19 est
déjà un tri topologique valide du DAG des prereqs, avec un arc thématique cohérent. Aucune vague de
renames à planifier pour cette série. Les 3 arêtes de prereq faibles sont un sujet de prose séparé,
hors-scope #5081.

Cela économise le travail de rename + évite le risque de liens cassés (#4737→#4743), tout en
documentant firsthand que la série est saine — la valeur d'une phase 1 docs-only.

Part of #5081.

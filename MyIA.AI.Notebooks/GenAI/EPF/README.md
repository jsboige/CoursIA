# EPF - Sorties étudiantes (archive)

> **Statut** : répertoire d'**archive**. Ne fait pas partie des parcours pédagogiques actifs de la série `GenAI/`. Préservé ici comme trace des productions étudiantes EPF (École Polytechnique Féminine) qui ont alimenté les cas canoniques de [`GenAI/CaseStudies/`](../CaseStudies/README.md).

## Contenu (état au commit de la PR)

**Aucune entrée matérielle dans ce répertoire pour le moment** — à la rédaction (commit `dc874107`) seul ce README existe. Les **livrables canoniques** (Barbie-Schreck, Fort-Boyard, Medical-Chatbot, Recipe-Maker) vivent dans [`GenAI/CaseStudies/`](../CaseStudies/README.md) ; les sorties brutes étudiantes `_output.ipynb` historiquement préservées ici ont été **vérifiées absentes de l'arbre complet au SHA de la PR** (0 hit pour `receipe_maker_output.ipynb`, `medical_chatbot_output.ipynb`, `Dorian`, `Louise` — vérifié via `git/trees/dc874107?recursive=1`).

Cette table « Contenu » ayant été rédigée **contre le souvenir** de l'état avant le refactor **`#888`** (qui a universalisé EPF paths vers CaseStudies), elle référençait des chemins aujourd'hui **n'émergeant nulle part dans `main`** : la voici retirée pour ne pas éteindre la vigilance du lecteur suivant (cf leçon ajoutée à [`pr-review-discipline.md` §E](../../.claude/rules/pr-review-discipline.md) — un inventaire de README se vérifie contre le disque au SHA de la PR).

### Migration en attente

- **Sorties étudiantes `_output.ipynb`** : migration hors-ligne (clé USB / disque externe de l'enseignant EPF). À re-tracer ici si elles reviennent un jour dans l'arbre, avec URL/stable-path **vérifiés sur disque**.
- **Sous-répertoire `Integrations-DotNet/` référencé dans `GenAI/README.md` structure tree** : **pas encore créé** — il est créé par la PR **#14431**, encore ouverte. Tant que #14431 n'est pas mergée, la référence dans `GenAI/README.md` à un répertoire qui n'existe pas est explicitement signalée par cette note (et non par une table qui prétendrait l'inventorier).

## Pourquoi ces fichiers (éventuels) seront dans `GenAI/EPF/` et non dans `GenAI/CaseStudies/`

Le refactor **`#888` refactor(casestudies): universalise EPF paths to CaseStudies (Phase 2)** a deplacé les **livrables canoniques** (notebooks de référence Barbie-Schreck, Fort-Boyard, Medical-Chatbot, Recipe-Maker) vers `GenAI/CaseStudies/<cas>/`. Les **sorties brutes des étudiants EPF** (leurs `_output.ipynb` tels que produits par leur run), si elles reviennent un jour ici, seront préservées séparément comme mémoire de la session pédagogique — elles ne sont **pas** des livrables du dépôt au sens du parcours étudiant.

## Distinction avec le `MyIA.AI.Notebooks/CaseStudies/` top-level

Deux `CaseStudies/` au dépôt :

- **`MyIA.AI.Notebooks/CaseStudies/`** : série interdisciplinaire (Diagnostic-Medical, Oncology-Planning, SmartGrid-Energy) — TP intégrateurs fin de cycle M1/M2 qui mobilisent **plusieurs paradigmes IA** combinés (CSP, recherche, génétique, OR-Tools, KG, bayésien). Owner po-2025.
- **`MyIA.AI.Notebooks/GenAI/CaseStudies/`** : 4 cas GenAI agentiques (Barbie-Schreck, Fort-Boyard, Medical-Chatbot, Recipe-Maker) — séries thématiques de la famille GenAI. Owner po-2023.

Le présent `EPF/` est strictement lié à la **branche GenAI** et constitue l'archive des productions étudiantes qui ont nourri `GenAI/CaseStudies/`. Il ne contient aucun contenu pédagogique actif.

## Voir aussi

- [`GenAI/CaseStudies/`](../CaseStudies/README.md) — cas canoniques GenAI
- [`GenAI/README.md`](../README.md) — navigation racine GenAI
- [Issue #13581](https://github.com/jsboige/CoursIA/issues/13581) — chantier de reorganisation du répertoire GenAI

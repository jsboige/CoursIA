# EPF - Sorties étudiantes (archive)

> **Statut** : répertoire d'**archive**. Ne fait pas partie des parcours pédagogiques actifs de la série `GenAI/`. Préservé ici comme trace des productions étudiantes EPF (École Polytechnique Féminine) qui ont alimenté les cas canoniques de [`GenAI/CaseStudies/`](../CaseStudies/README.md).

## Contenu

| Sous-dossier | Auteur(s) | Cas canonique associé | Statut |
|---|---|---|---|
| `Dorian & Bastien/cuisine/receipe_maker_output.ipynb` | Dorian, Bastien | [`CaseStudies/Recipe-Maker/`](../CaseStudies/Recipe-Maker/README.md) | sortie étudiante archivée |
| `Louise et Jeanne Céline/medical_chatbot_output.ipynb` | Louise, Jeanne Céline | [`CaseStudies/Medical-Chatbot/`](../CaseStudies/Medical-Chatbot/README.md) | sortie étudiante archivée |

## Pourquoi ces fichiers sont dans `GenAI/EPF/` et non dans `GenAI/CaseStudies/`

Le refactor **`#888` refactor(casestudies): universalise EPF paths to CaseStudies (Phase 2)** a deplacé les **livrables canoniques** (notebooks de référence Barbie-Schreck, Fort-Boyard, Medical-Chatbot, Recipe-Maker) vers `GenAI/CaseStudies/<cas>/`. Les **sorties brutes des étudiants EPF** (leurs `_output.ipynb` tels que produits par leur run) sont préservées séparément ici, comme mémoire de la session pédagogique — elles ne sont **pas** des livrables du dépôt au sens du parcours étudiant.

## Distinction avec le `MyIA.AI.Notebooks/CaseStudies/` top-level

Deux `CaseStudies/` au dépôt :

- **`MyIA.AI.Notebooks/CaseStudies/`** : série interdisciplinaire (Diagnostic-Medical, Oncology-Planning, SmartGrid-Energy) — TP intégrateurs fin de cycle M1/M2 qui mobilisent **plusieurs paradigmes IA** combinés (CSP, recherche, génétique, OR-Tools, KG, bayésien). Owner po-2025.
- **`MyIA.AI.Notebooks/GenAI/CaseStudies/`** : 4 cas GenAI agentiques (Barbie-Schreck, Fort-Boyard, Medical-Chatbot, Recipe-Maker) — séries thématiques de la famille GenAI. Owner po-2023.

Le présent `EPF/` est strictement lié à la **branche GenAI** et constitue l'archive des productions étudiantes qui ont nourri `GenAI/CaseStudies/`. Il ne contient aucun contenu pédagogique actif.

## Voir aussi

- [`GenAI/CaseStudies/`](../CaseStudies/README.md) — cas canoniques GenAI
- [`GenAI/README.md`](../README.md) — navigation racine GenAI
- [Issue #13581](https://github.com/jsboige/CoursIA/issues/13581) — chantier de reorganisation du répertoire GenAI

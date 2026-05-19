# Contexte enseignement - calendrier, ecoles, agents

Documentation transversale sur l'organisation de l'enseignement annuel : calendrier, scope par ecole, mapping agents cluster. Pour le **moteur de notation** : cf [docs/ece-grading.md](ece-grading.md). Pour le **mapping cluster machines** (au-dela des roles enseignement) : cf [docs/cluster-agents.md](cluster-agents.md).

## Ecoles partenaires 2026

| Ecole | Cours | Statut session 2026 |
|-------|-------|---------------------|
| EPF | GenAI Bachelor 3A (MSBNS3IN03), classes MIN1/MIN2/MIS | Termine, notes transmises |
| ECE | IA Finance Ing4 (Gr01/02/03) | Termine, notes rendues debut mai |
| ESGF | Algo Trading QuantConnect | En cours, soutenance batch 1 |
| EPITA | Programmation par Contraintes | Soutenances 2 batchs (presentiel + visio) |
| EPITA | IA Symbolique | 5 cours en cours |

## Calendrier general 2026 (printemps)

Le calendrier nominatif (dates precises de soutenance par groupe etudiant) est dans `G:/Mon Drive/MyIA/Formation/<ecole>/2026/` et sur le **dashboard RooSync workspace CoursIA**, pas dans le repo public.

Les jalons annuels recurrents :

| Periode | Activite type |
|---------|---------------|
| Janvier-Fevrier | Cours EPF GenAI + cours EPITA-PrCon (slides + notebooks) |
| Mars-Avril | Cours ECE IA Finance Ing4 (Gr01/02/03 successifs) + soutenances P1 |
| Mai | Soutenances ECE P2, soutenances EPITA-PrCon (batch 1 presentiel + batch 2 visio), debut cours EPITA-IA-Symbolique, soutenance ESGF |
| Juin | Fin cours EPITA-IA-Symbolique + soutenances projet final |
| Septembre | Rentree (QC League pour anciens ECE, nouvelle promo EPF) |

## EPITA - IA Symbolique : scope 2026

5 cours, 18h totales, focus exclusif sur le repertoire `MyIA.AI.Notebooks/SymbolicAI/`.

### Series DANS le scope (6)

| # | Serie | Contenu |
|---|-------|---------|
| 1 | `SymbolicAI/Argument_Analysis` | **Priorite** (Epic dedie). Submodule Argumentum + materiel importable 2025 |
| 2 | `SymbolicAI/Tweety` | Argumentation formelle, transition naturelle apres Argumentum |
| 3 | `SymbolicAI/Lean` | Preuves formelles (incluant GameTheory `social_choice_lean/` port Arrow/Sen) |
| 4 | `SymbolicAI/SemanticWeb` | RDF / OWL / SHACL |
| 5 | `SymbolicAI/Planning` | PDDL / GraphPlan / HTN |
| 6 | `SymbolicAI/SmartContract` | Solidity / ZKP / multi-chain |

### Series HORS scope (referencables pour les projets, pas de cours dedie)

- `Search/` : couvert dans Programmation par Contraintes
- `Probas/` : mentionne en passant
- `GameTheory/` (serie complete) : mentionne dans sujets et sous-partie Lean
- `IIT/` : non couvert

### Format TP final EPITA-IS

- **1 serie au minimum** choisie par l'etudiant parmi les 6 du scope
- **Livrable principal** : 1 exercice final de notebook complete dans cette serie
- **Workflow** : PR sur **fork du depot `jsboige/CoursIA`** (pattern PrCon : fork + PR sur notebooks)
- **Le depot `2026-Epita-Intelligence-Symbolique`** = projets/sujets de soutenance, distinct des TPs notebooks
- **Bonus** : +0.5 / exercice supplementaire meme serie (cap +1), +1 / exercice autre serie (cap +2), +0.5 redaction 1p markdown explicative (demarche, choix techniques, limites)
- **Soutenance** : 10 min presentation + 5 min Q&A, batch presentiel sur creneau cours + batch visio si depassement

## Agents cluster par ecole

Le cluster CoursIA dispatche les missions par workspace dedie. **Les workspaces EPITA ne sont PAS dispatchables depuis `myia-ai-01:CoursIA`** : chaque workspace EPITA a son propre flow, son propre depot, ses propres tracks.

| Ecole / role | Workspace RooSync | Limites |
|--------------|-------------------|---------|
| ECE - notation P1+P2, bonus CC, compilation | `myia-ai-01:CoursIA` + `myia-po-2024:CoursIA` | - |
| ESGF - ML kit + soutenances + suivi | `myia-ai-01:CoursIA` + `myia-po-2024:CoursIA` | Sponsor QC, prudence sur la communication publique (tiers research org) |
| EPITA-PrCon - review/merge PRs etudiants | `myia-po-2025:2026-Epita-Programmation-par-Contraintes` | Ne **pas** envoyer de mission CoursIA via ce workspace |
| EPITA-IS - veille + enrichissement sujets | `myia-po-2025:2026-Epita-Intelligence-Symbolique` | Ne **pas** envoyer de mission CoursIA via ce workspace |
| EPF - notation, archive | (workspace dedie myia-po-2025) | Cycle annuel termine |

**Specificite po-2025** : 3 workspaces distincts sur la meme machine RTX 3080 Ti (backoff thermal partage). Dispatcher en precisant le workspace explicitement dans `to:`, jamais `myia-po-2025` seul.

## Conventions Google Drive

Base path commune : `G:\Mon Drive\MyIA\Formation\<ecole>\<annee>\` (cf `gdrive_teaching_paths.md` non public pour le detail par fichier).

Sous-dossiers types :
- `participants/` ou `Groupe<N>_participants.xlsx` : rosters etudiants
- `grading/` : configs GradeBookApp + outputs Excel (resolus via `COURSIA_ROOT` env var)
- `Notation/` : briefings jury, questions de soutenance, grilles d'evaluation **(internes - ne JAMAIS publier sur PR/issue)**
- `Projet1-Gr<N>-Presentations/` : presentations etudiantes

## Reviews PR etudiantes - regle critique

Voir [.claude/rules/student-pr-reviews.md](../.claude/rules/student-pr-reviews.md). Rappel : les commentaires de PR sur depot etudiant sont **visibles par les etudiants**, donc jamais de questions de soutenance / grille / briefing jury en commentaire public avant l'epreuve. Incident 2026-05-17 documente.

## Pointeurs cross-doc

- Pipeline notation et bonus CC : [docs/ece-grading.md](ece-grading.md)
- Mapping cluster machines (au-dela enseignement) : [docs/cluster-agents.md](cluster-agents.md)
- Slides Slidev EPITA : `MyIA.AI.Notebooks/SymbolicAI/<serie>/slides/` (workflow Slidev verify, cf [.claude/rules/](../.claude/rules/))
- QuantConnect (ESGF) : [docs/quantconnect.md](quantconnect.md)

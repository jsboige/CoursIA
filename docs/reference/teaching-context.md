# Contexte enseignement - calendrier, écoles, agents

Documentation transversale sur l'organisation de l'enseignement annuel : calendrier, scope par école, mapping agents cluster. Pour le **moteur de notation** : cf [GradeBookApp/configs/README.md](../../GradeBookApp/configs/README.md) (pipelines + données par cohorte = privés sur GDrive). Pour le **mapping cluster machines** (au-delà des rôles enseignement) : cf [docs/cluster-agents.md](cluster-agents.md).

## Écoles partenaires 2026

| École | Cours | Statut session 2026 |
|-------|-------|---------------------|
| EPF | GenAI Bachelor 3A (MSBNS3IN03), classes MIN1/MIN2/MIS | Terminé, notes transmises |
| ECE | IA Finance Ing4 (Gr01/02/03) | Terminé, notes rendues début mai |
| Partner | Algo Trading QuantConnect | En cours, soutenances finales fin mai, **grading début juin** |
| EPITA | Programmation par Contraintes | Soutenances 2 batchs **terminées**, suivi TP bonus rempli, notes projet faites |
| EPITA | IA Symbolique | Cours en cours ; TPs notebooks rendus sur CoursIA = points bonus des projets EPITA-IS |

## Calendrier général 2026 (printemps)

Le calendrier nominatif (dates précises de soutenance par groupe étudiant) est dans `G:/Mon Drive/MyIA/Formation/<école>/2026/` et sur le **dashboard RooSync workspace CoursIA**, pas dans le repo public.

Les jalons annuels récurrents :

| Période | Activité type |
|---------|---------------|
| Janvier-Février | Cours EPF GenAI + cours EPITA-PrCon (slides + notebooks) |
| Mars-Avril | Cours ECE IA Finance Ing4 (Gr01/02/03 successifs) + soutenances P1 |
| Mai | Soutenances ECE P2, soutenances EPITA-PrCon (batch 1 présentiel + batch 2 visio, terminées), début cours EPITA-IA-Symbolique, soutenances finales partenaire |
| Juin | **Grading partenaire (début juin)**, fin cours EPITA-IA-Symbolique + soutenances projet final |
| Septembre | Rentrée (QC League pour anciens ECE, nouvelle promo EPF) |

## EPITA - IA Symbolique : scope 2026

5 cours, 18h totales, focus exclusif sur le répertoire `MyIA.AI.Notebooks/SymbolicAI/`.

### Séries DANS le scope (6)

| # | Série | Contenu |
|---|-------|---------|
| 1 | `SymbolicAI/Argument_Analysis` | **Priorité** (Epic dédié). Submodule Argumentum + matériel importable 2025 |
| 2 | `SymbolicAI/Tweety` | Argumentation formelle, transition naturelle après Argumentum |
| 3 | `SymbolicAI/Lean` | Preuves formelles (incluant GameTheory `social_choice_lean/` port Arrow/Sen) |
| 4 | `SymbolicAI/SemanticWeb` | RDF / OWL / SHACL |
| 5 | `SymbolicAI/Planning` | PDDL / GraphPlan / HTN |
| 6 | `SymbolicAI/SmartContract` | Solidity / ZKP / multi-chain |

### Séries HORS scope (référençables pour les projets, pas de cours dédié)

- `Search/` : couvert dans Programmation par Contraintes
- `Probas/` : mentionné en passant
- `GameTheory/` (série complète) : mentionné dans sujets et sous-partie Lean
- `IIT/` : non couvert

### Format TP final EPITA-IS

- **1 série au minimum** choisie par l'étudiant parmi les 6 du scope
- **Livrable principal** : 1 exercice final de notebook complet dans cette série
- **Workflow** : PR sur **fork du dépôt `jsboige/CoursIA`** (pattern PrCon : fork + PR sur notebooks)
- **Le dépôt `2026-Epita-Intelligence-Symbolique`** = projets/sujets de soutenance, distinct des TPs notebooks
- **Bonus** : +0.5 / exercice supplémentaire même série (cap +1), +1 / exercice autre série (cap +2), +0.5 rédaction 1p markdown explicative (démarche, choix techniques, limites)
- **Application du bonus** : c'est l'**inscription des groupes dans les fichiers de suivi adéquats qui fait foi** (G drive `Notation/`), pas la PR mergée ni le keying gradebook sur la chaîne sujet
- **Collisions de TP** (2 groupes, même exercice) : merger le **meilleur rendu** ou **cherry-pick entre les meilleurs**, puis **close les autres** avec un message expliquant qu'un seul peut être mergé (même protocole que les TPs PrCon ; cf SW-10 #1429/#1416 -> #1499)
- **Soutenance** : 10 min présentation + 5 min Q&A, batch présentiel sur créneau cours + batch visio si dépassement

## Agents cluster par école

Le cluster CoursIA dispatche les missions par workspace dédié. **Les workspaces EPITA ne sont PAS dispatchables depuis `myia-ai-01:CoursIA`** : chaque workspace EPITA a son propre flow, son propre dépôt, ses propres tracks.

| École / rôle | Workspace RooSync | Limites |
|--------------|-------------------|---------|
| ECE - notation P1+P2, bonus CC, compilation | `myia-ai-01:CoursIA` + `myia-po-2024:CoursIA` | - |
| Partner QC - ML kit + soutenances + suivi | `myia-ai-01:CoursIA` + `myia-po-2024:CoursIA` | Sponsor QC, prudence sur la communication publique (tiers research org) |
| EPITA-PrCon - review/merge PRs étudiants | `myia-po-2025:2026-Epita-Programmation-par-Contraintes` | Ne **pas** envoyer de mission CoursIA via ce workspace |
| EPITA-IS - veille + enrichissement sujets | `myia-po-2025:2026-Epita-Intelligence-Symbolique` | Ne **pas** envoyer de mission CoursIA via ce workspace |
| EPF - notation, archive | (workspace dédié myia-po-2025) | Cycle annuel terminé |

**Spécificité po-2025** : 3 workspaces distincts sur la même machine RTX 3080 Ti (backoff thermique partagé). Dispatcher en précisant le workspace explicitement dans `to:`, jamais `myia-po-2025` seul.

## Conventions Google Drive

Base path commune : `G:\Mon Drive\MyIA\Formation\<école>\<année>\` (cf `gdrive_teaching_paths.md` non public pour le détail par fichier).

Sous-dossiers types :
- `participants/` ou `Groupe<N>_participants.xlsx` : rosters étudiants
- `grading/` : configs GradeBookApp + outputs Excel (résolus via `COURSIA_ROOT` env var)
- `Notation/` : briefings jury, questions de soutenance, grilles d'évaluation **(internes - ne JAMAIS publier sur PR/issue)**
- `Projet1-Gr<N>-Presentations/` : présentations étudiantes

## Reviews PR étudiantes - règle critique

Voir [.claude/rules/student-pr-reviews.md](../../.claude/rules/student-pr-reviews.md). Rappel : les commentaires de PR sur dépôt étudiant sont **visibles par les étudiants**, donc jamais de questions de soutenance / grille / briefing jury en commentaire public avant l'épreuve. Incident 2026-05-17 documenté.

## Pointeurs cross-doc

- Pipeline notation et bonus CC : moteur [GradeBookApp/configs/README.md](../../GradeBookApp/configs/README.md) ; détail par cohorte privé sur GDrive `Formation\<école>\<année>\grading\`
- Mapping cluster machines (au-delà enseignement) : [docs/cluster-agents.md](cluster-agents.md)
- Slides Slidev EPITA : `MyIA.AI.Notebooks/SymbolicAI/<série>/slides/` (workflow Slidev verify, cf [.claude/rules/](../../.claude/rules/))
- QuantConnect (partenaire) : [docs/qc/quantconnect.md](../qc/quantconnect.md)

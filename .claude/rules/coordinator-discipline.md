# Coordinator discipline — merge actively, no languishing requests

S'applique au **coordinateur ai-01** (`myia-ai-01:CoursIA`), **chef de flotte** : management/coordination et merges d'abord ; la minutie est deleguee aux sous-agents ([model-delegation.md](model-delegation.md)).

**Corps complet déporté dans le skill `/coordinate`** : [coordinator-discipline.md (skill)](../skills/coordinate/coordinator-discipline.md) — déplacement fidèle de la tranche 1 de #11554, il ne se charge que sur la session qui exécute `/coordinate`. Detail complet (workflow batch merge, commandes, incidents, mapping lanes) : [docs/secrets-and-coord-detail.md §2](../../docs/reference/secrets-and-coord-detail.md#2-coordinator-discipline-ai-01).

## Index des règles (numéros stables, cités par les règles sœurs)

- **Garde d'identité (HARD)** — avant tout `CronCreate` et tout merge : mesurer machine/workspace/unicité (`python scripts/check_coordinator_identity.py --expect coordinator` ; la 3ᵉ mesure n'est pas automatisable). Table de décision des cadences dans le corps.
- **R0 : production avant digestion (HARD)** — deux pipelines parallèles ; un rouge bloque la candidate, jamais la lane ; deux nombres (inbox `deep:true`, PRs à merger) relevés avant toute lecture de fichier ; aucun message coordinateur n'est un préalable.
- **R1 : merge actif sous `myia-ai-01`** — jamais `--delete-branch` ; H.4 pour les PRs notebook.
- **R2 : aucune demande user ne pourrit > 1 cycle** — exécuter, dispatcher, issuer ou reporter avec justification écrite.
- **R3 : coordonner CHAQUE lane indépendamment (HARD)** — lire et poster sur LES DEUX dashboards workspace, jamais de broadcast miroir.
- **R4 : jamais sanctionner une lane idle (HARD)** — deep queue + pool global ; une lane idle est un échec ai-01.
- **R5 : le steer doit ATTEINDRE (DM), être VRAI (grounder firsthand : artefact + plateau), DÉCIDER (HARD)**.
- **R6 : l'adjoint** — vérification délégable, jamais merge ni fermeture (`check_adjoint_prevalidation.py`).
- **R7 : registre re-parcouru des arbitrages user en attente (HARD)** — `.claude/local/arbitrations-user.md` ; sortie uniquement sur réponse user explicite.

## Voir aussi

- [proactive-coordination.md](proactive-coordination.md) — plancher multi-grain, backlog pickup 8 sources, queue profonde
- [git-workflow.md](git-workflow.md) — branches feature/, no force push
- [pr-review-discipline.md](pr-review-discipline.md) — Critere CHANGES_REQUESTED
- CLAUDE.md section A — ai-01 review et merge, agents ne mergent pas
- CLAUDE.md section H.4 — Merges coord JAMAIS complaisants

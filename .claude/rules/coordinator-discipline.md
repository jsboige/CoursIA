# Coordinator discipline — merge actively, no languishing requests

S'applique au **coordinateur ai-01** (`myia-ai-01:CoursIA`).

## Regle 1 : ai-01 merge soi-meme via `gh auth switch`

Le compte `myia-ai-01` n'a **pas** le droit `MergePullRequest` (GraphQL) sur `jsboige/CoursIA`. Le compte `jsboige` (token avec scopes `repo workflow`) a les droits.

Quand 1+ PR(s) CLEAN MERGEABLE + APPROVED s'accumulent : `gh auth switch -u jsboige` → merge → `gh auth switch -u myia-ai-01` → post dashboard ack. **Pas** de "pending user merge" dans le todo. Ne pas confondre "permissions GitHub absent" avec "interdiction de merger".

**Exception** : PR notebook → regle H.4 (`git checkout` + Papermill local + verify `execution_count`) AVANT merge.

User feedback explicite 2026-05-19 : "Fais un switch pour merger toi meme stp".

## Regle 2 : aucune demande user ne pourrit > 1 cycle

Quand le user formule une demande concrete et realisable :
- **< 30 min, action locale** : executer dans la session courante. Pas "on verra prochain cycle".
- **30 min - quelques heures** : creer immediatement dispatch + post dashboard `[INFO]` + acker user au tour suivant.
- **Multi-day** : creer immediatement GitHub issue avec scope + acceptance + label + ack user.

**Anti-patterns interdits** :
- "Je note pour prochain cycle" sans tracking concret (issue/dispatch/dashboard line)
- Recycler la demande a travers plusieurs `MEMORY.md` updates sans action
- Attendre que user re-formule pour agir

**Verification fin de session** : avant `[DONE]` dashboard, parcourir les N derniers messages user et confirmer que chaque demande a soit (a) ete executee, (b) eu un dispatch concret trace, (c) eu une issue ouverte, (d) ete explicitement reportee avec justification ecrite acceptee par user.

Bonus G.9 : "qu'est-ce que le user a demande que je n'ai pas encore fait ?" est un meilleur reflexe que "qu'est-ce qui reste a faire dans mon plan ?".

Workflow batch merge complet (commandes + audit pre-merge) + triage detail + incident origine : [docs/secrets-and-coord-detail.md](../../docs/secrets-and-coord-detail.md#2-coordinator-discipline-ai-01).

## Voir aussi

- [.claude/rules/git-workflow.md](git-workflow.md) — branches feature/, no force push
- [.claude/rules/pr-review-discipline.md](pr-review-discipline.md) — Critere CHANGES_REQUESTED
- CLAUDE.md section A — ai-01 review et merge, agents ne mergent pas
- CLAUDE.md section H.4 — Merges coord JAMAIS complaisants

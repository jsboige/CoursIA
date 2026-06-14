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

Workflow batch merge complet (commandes + audit pre-merge) + triage detail + incident origine : [docs/secrets-and-coord-detail.md](../../docs/reference/secrets-and-coord-detail.md#2-coordinator-discipline-ai-01).

## Regle 3 : coordonner CHAQUE lane (dashboard) independamment

Il existe **deux dashboards workspace** : `workspace-CoursIA` et `workspace-CoursIA-2`. **Aucun n'est "le dashboard du coordinateur"** — ce sont deux lanes co-egales. Un `lane` = **machine x workspace** : chaque machine worker qui a une lane CoursIA-2 a **AUSSI** une lane CoursIA (po-2026:CoursIA Lean / po-2026:CoursIA-2 Grothendieck ; po-2024:CoursIA QC / po-2024:CoursIA-2 MGS-.NET ; po-2025:CoursIA Python-ML / po-2025:CoursIA-2 .NET-Argumentum).

Chaque cycle `/coordinate`, ai-01 doit **LIRE *et* POSTER une coordination lane-specific sur LES DEUX**, independamment :
- **Lire** `section:"all"` des deux dashboards (pas un seul) — sinon les ASKs/blockers d'une lane restent invisibles.
- **Poster** un contenu **propre a chaque lane** (ses ASKs, ses merges, ses dispositions) — **jamais de broadcast miroir** (copier-coller identique des deux cotes).
- **Anti-pattern interdit** : traiter `workspace-CoursIA` comme « le mien » et `workspace-CoursIA-2` comme « celui des workers ». Les deux portent du travail worker a coordonner.
- **Piege duplication cross-lane** : un worker peut dedoubler une livraison sur ses deux lanes (ex #2950 sur CoursIA + #2952 sur CoursIA-2 pour le meme #1027). Reconcilier explicitement : 1 canonique mergee, l'autre disposee.

Source : mandat user 2026-06-14. Incident : un cycle entier ou seule la lane CoursIA-2 a ete coordonnee (broadcast miroir), ratant l'ASK greenlight PR1.5 Knot #2874 de po-2026:CoursIA et le rapport C.2 de #2953 (po-2025:CoursIA).

## Voir aussi

- [.claude/rules/git-workflow.md](git-workflow.md) — branches feature/, no force push
- [.claude/rules/pr-review-discipline.md](pr-review-discipline.md) — Critere CHANGES_REQUESTED
- CLAUDE.md section A — ai-01 review et merge, agents ne mergent pas
- CLAUDE.md section H.4 — Merges coord JAMAIS complaisants

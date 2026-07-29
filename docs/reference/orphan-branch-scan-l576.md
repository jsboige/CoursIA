# Scan de branche orpheline (L576) — les deux ancres `pulls` peuvent mentir

Détail de référence de la section « Orphan-branch scan (L576) » de
[`.claude/rules/git-workflow.md`](../../.claude/rules/git-workflow.md).

> **Note de localisation.** La règle cite ce détail à l'URL
> `.claude/memory/lecon-L576-rest-commits-pulls-fpos.md`. Ce chemin est **ignoré par
> `.gitignore`** (ligne 651, aux côtés de `.claude/local/` — état local par machine) : il ne
> peut donc jamais exister sur `main`, et les deux liens de la règle sont morts par
> construction. Le détail durable vit ici, conformément à
> [`harness-hygiene`](../../.claude/rules/harness-hygiene.md) (tier « doc pérenne →
> `docs/` », référencé succinctement par le harnais).

## Ce que la règle demande

Avant de conclure qu'une branche distante est **orpheline** et de se l'auto-attribuer, trois
ancres doivent être passées :

1. `git merge-base --is-ancestor <sha> origin/main` — intégrée en amont ?
2. `gh api repos/jsboige/CoursIA/commits/<sha>/pulls` — endpoint REST (peut être faux négatif)
3. `gh pr list --state all --search "head:<branche>"` — **gate présenté comme autoritatif**

## Incident fondateur (c.576) — RAPPORTÉ

Symptôme d'origine : **l'ancre 2 (REST) peut renvoyer vide pour une branche réellement
attachée à une PR ouverte.** Conclure « orpheline » sur `git fetch` + REST seul exposait donc
à s'auto-attribuer un travail déjà en cours. D'où l'ancre 3, ajoutée comme filet.

*Statut de vérification (2026-07-29)* : les PR citées par la règle — **#7086, #7087, #7088,
#7089, #7091** (MERGED) et **#7090** (CLOSED) — existent bien. En revanche leurs branches de
tête sont nommées `fix/…`, `feat/…`, `feature/…`, et **non** `jsboige/*` comme le résumé
d'une ligne de la règle le laisse entendre. Ce point du résumé hérité n'a pas pu être
reconfirmé ; le mécanisme (faux négatif REST) reste, lui, la raison d'être de l'ancre 3.

## Nouvelle classe de faux positif — l'ancre 3 aussi peut mentir (VÉRIFIÉ 2026-07-29)

**L'ancre 3 n'est autoritative que si la branche examinée est celle qui a servi de tête à la
PR.** Elle ne l'est pas pour une **branche de travail locale nommée d'après un numéro de PR**,
dont le contenu a été livré sous une *autre* tête. Ces branches tombent exactement dans la
case « ORPHELINE CONFIRMÉE (ok self-pick) » de la matrice — et cette case est **fausse** : le
travail est déjà sur `main`.

Cinq branches mesurées firsthand, toutes VIVANTE (non-ancêtres de `main`), toutes `PRs=[none]`
aux ancres 2 **et** 3, toutes en avance de 1 à 5 commits — et **toutes déjà livrées** :

| Branche | Ancre 3 | Contenu réellement sur `main` |
|---|---|---|
| `uniontest` | `none` | paire twin GT-13 → `twin_pairs.d/gametheory-13-imperfectinfo-cfr.yaml` |
| `m8526` | `none` | paire twin App-2-GraphColoring → `twin_pairs.d/app-2-graphcoloring.yaml` |
| `c17-8525-reexec` | `none` | `bfda2bb1e` (PR #8525) |
| `tmp8549` | `none` | `5bb5d0194` (PR #8549) |
| `tmp8556` | `none` | `c826a9c48` (PR #8556) |

Se fier à la matrice seule aurait conduit à **refaire cinq fois du travail mergé** — pas à
perdre du travail. Le risque L576 est donc **bilatéral** : l'ancre 2 seule fait sur-attribuer
(double-pickup d'un travail en cours) ; la matrice complète fait re-produire (duplication d'un
travail livré).

Deux tells suffisent à reconnaître la classe, **avant** toute enquête :

- **Le nom encode un numéro de PR** (`tmp8549`, `m8526`, `c17-8525-reexec`) — c'est une
  branche d'échafaudage local, pas une tête de PR. Le PR homonyme est le premier endroit à
  regarder : `gh pr view <numéro-extrait-du-nom>`.
- **Le chemin touché est *superseded* sur `main`** (ici `twin_pairs.yaml`, fichier, remplacé
  par le répertoire `twin_pairs.d/` en #8586). Une branche qui modifie un support qui n'existe
  plus ne peut pas être « du travail à récupérer ».

## Ancre 4 — identité de **contenu**, pas de branche

Quand les ancres 1-3 disent « orpheline », ne pas s'arrêter là : vérifier que le **contenu**
n'est pas déjà sur `main`.

```bash
# 1. Le nom porte-t-il un numéro de PR ? Commencer par là.
gh pr view <N> --json state,mergedAt,mergeCommit

# 2. Sinon : le sujet de commit est-il déjà sur main ? (squash → sujet préservé)
git log --oneline origin/main | grep -F "$(git log -1 --format=%s <branche>)"

# 3. Ou : les fichiers touchés portent-ils déjà le changement sur main ?
git diff --stat $(git merge-base origin/main <branche>) <branche>
git log --oneline -3 -- <chemin-touché>
```

Une branche **squash-mergée n'est jamais ancêtre de `main`** : `merge-base --is-ancestor` est
FAUX pour du travail pourtant livré. C'est ce qui rend l'ancre 1 muette ici et laisse toute la
charge de preuve aux ancres 2-3, aveugles au nommage local.

## Décision

| Ancres 1-3 | Ancre 4 (contenu) | Verdict |
|---|---|---|
| INTÉGRÉE (ancre 1) | — | **ARRÊTER** — déjà sur `main` |
| orpheline | contenu **présent** sur `main` | **NE PAS self-pick** — branche d'échafaudage, supprimable |
| orpheline | contenu **absent** de `main` | orpheline confirmée — self-pick OK, poser `[CLAIMED]` |
| PR(s) OPEN à l'ancre 2 ou 3 | — | **NE PAS self-pick** — travail en cours |

Coût de l'ancre 4 : une commande. Coût de son omission : un cycle de travail dupliqué, ou
l'écrasement d'un travail en cours.

## Voir aussi

- [`.claude/rules/git-workflow.md`](../../.claude/rules/git-workflow.md) — matrice à 3 ancres
- [`.claude/rules/proactive-coordination.md`](../../.claude/rules/proactive-coordination.md) — L898, garde anti-collision cross-lane (vérifier **avant d'écrire**, pas avant de pousser)
- [`.claude/rules/harness-hygiene.md`](../../.claude/rules/harness-hygiene.md) — 3 tiers : harnais succinct / doc pérenne / dashboard éphémère

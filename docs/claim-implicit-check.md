# Claim IMPLICIT — vérification cross-lane avant d'éditer

> Statut : **procédure** (HARD). Tout grain substantiel qui éditerait un chemin
> potentiellement revendiqué par une autre lane applique cette procédure **avant
> de poser un `[CLAIMED]`**. Distincte du claim explicite
> (`gh issue comment N --body "[CLAIMED] lane X:W -- paths: ..."`), elle couvre
> le cas où **une PR ouverte par une autre lane touche déjà le chemin visé**
> sans qu'un claim sur l'issue ne l'ait formalisé. Source : mandat user
> 2026-09-01, acceptance **#14300**. Partial delivery c.925.

Ce document fixe la procédure manuelle **en 3 étapes** que chaque worker applique
avant d'éditer un fichier sur un grain substantiel. Une implémentation outillée
(`scripts/check_lane_claim.py --check-implicit`, ex. #14300 suite) reste à livrer
en suivi — le script sait déjà ce que cette procédure énonce, il ne sait pas
encore l'**imposer** comme garde.

## 1. Pourquoi — le tell fondateur

Un grain m'a été refusé par co-claim pendant le cycle **c.925**, et c'est le
récit de cette collision qui motive la procédure. La narration tient en trois
faits :

1. **Issue #14032** (déjà claimée par `myia-po-2025:CoursIA` depuis
   `2026-08-18T02:51:25Z`, scope explicite `paths:` documenté sur le commentaire
   serveur) — travail en cours sur deux notebooks GameTheory.
2. **Issue #14300** (`claim: une PR ouverte n'est pas un claim —
   check_lane_claim.py`) — ouverte par un autre lane, jamais claimée, dans le
   pool ouvert. Grain de fond sur la procédure **lui-même**.
3. **Issue #14259** (incident fondateur, **2026-08-30**) — un worker a édité un
   fichier sur la foi d'un `gh issue list --state open` qui n'a pas vu la PR
   mergée le couvrant ; l'édition s'est révélée post-merge, et le retrait du
   label a demandé un arbitrage explicite. Le tell : **« OPEN + zéro PR liée »
   n'est PAS une preuve de fraîcheur** — voir [proactive-coordination.md §L1356](../.claude/rules/proactive-coordination.md) (R5 hard).

Le `check_lane_claim.py` actuel (3682 lignes, PR #9775) détecte les **claims
explicites** (commentaire serveur `[CLAIMED] lane X:W -- paths: ...`) ; il **ne
détecte pas** les PRs ouvertes par une autre lane qui touchent le même chemin
sans claim d'issue. C'est précisément le trou que cette procédure ferme à la
main.

## 2. Procédure — 3 étapes AVANT d'éditer

Coût mesuré : **~15 secondes** sur un pool de 200 issues. Coût de l'omission :
un cycle dupliqué ou, dans le pire cas, une collision silencieuse qui n'apparaît
qu'à la review.

### Étape 1 — vérifier les claims explicites existants

```bash
python scripts/check_lane_claim.py <ISSUE_NUMBER>
```

Ce que la commande **fait** : retourne `CLEAR` (exit 0), `BLOCKED` (exit 1, le
claim est actif sur une autre lane), ou `NOT_SCOPED` (exit 2, l'issue n'est pas
dans le scope `paths:` du claim). Détection de péremption **active par défaut**
(`--stale-threshold 48`, cf. #12751).

Si `BLOCKED` → **ne pas commencer**, piocher ailleurs. Le détecteur fait foi.

### Étape 2 — vérifier les PRs ouvertes qui couvrent le CHEMIN

`check_lane_claim.py` ne sait pas lire une PR ouverte par une autre lane comme
un claim. La procédure manuelle est donc :

```bash
# 1. Lister les PRs qui mentionnent l'issue (toutes lanes, tous états)
gh pr list --state all --search "<ISSUE_NUMBER>" \
  --json number,title,state,author,headRefName,files \
  --jq ".[] | {n: .number, s: .state, t: .title, h: .headRefName, f: (.files | map(.path))}"

# 2. Lister les PRs qui touchent le CHEMIN visé (toutes lanes, tous états)
gh pr list --state all --search "<CHEMIN_OU_MOTIF>" \
  --json number,title,state,author,headRefName \
  --jq ".[] | {n: .number, s: .state, t: .title}"
```

**Ce qu'il faut lire** dans la sortie :

| Constat | Action |
|---|---|
| Aucune PR ne touche le chemin | Poursuivre (étape 3) |
| Une PR **MERGED** touche le chemin | **STOP** — lire `git log -- <fichier>` sur `main`, vérifier que le travail est bien arrivé. C'est le cas #14259. Si oui, acquitter `[INFO] candidate-delivered` sur l'issue |
| Une PR **OPEN** touche le chemin, **par ma lane** | Poursuivre — c'est mon propre travail |
| Une PR **OPEN** touche le chemin, **par une autre lane** | **STOP** — DM co-claim à la lane (cf. §3), puis `paths:` partitionné |
| Une PR **CLOSED** (non mergée) touche le chemin | Poursuivre — CLOSED sans merge = travail avorté |

**Le `[CLAIMED]` côté worker ne couvre pas ce cas** : une PR ouverte par une
autre lane sans claim d'issue est un claim **implicite** par le travail en
cours. C'est ce que cette procédure détecte.

### Étape 3 — vérifier les worktrees orphelins nommés pour l'issue

Une compaction efface le souvenir du travail, pas le disque :

```bash
ls -d /c/dev/CoursIA-*/ 2>/dev/null | grep -i "<MOTIF_ISSUE_OU_SUJET>"
git -C /c/dev/CoursIA-2 worktree list
```

Si un worktree nommé pour le sujet existe :

1. Identifier la branche : `git -C <worktree> branch --show-current`.
2. Inspecter son dernier commit : `git -C <worktree> log -1 --oneline`.
3. Vérifier qu'aucune PR n'est attachée : `gh pr list --state all --search "head:<branche>"`.

Si oui → **travail abandonné en cours de compaction** : reprendre le worktree
ou fusionner avec l'auteur. Si non (la branche est orpheline) → créer le votre,
mais **citer** le worktree dans le body PR pour la transparence cross-cycle.

## 3. Partitionnement — quand plusieurs lanes convergent

Le cas de c.925 : issue #14032 claimée par `myia-po-2025:CoursIA` (scope
`paths:` explicite) + grain #14300 dans le pool libre. Les deux ne se
**touchent pas** par les fichiers — `#14300` vise `scripts/check_lane_claim.py`
et `docs/`, alors que #14032 vise `MyIA.AI.Notebooks/GameTheory/`. Le
partitionnement est **trivial** quand les `paths:` sont disjoints.

Le tell `#14032` est un claim explicite ; le tell `#14300` était un grain libre
sans PR ouverte. **Aucune collision.** Si un grain PARTITIONNABLE se présente
sur un claim explicite :

```bash
# 1. Confirmer le scope par lecture du claim
gh issue view <ISSUE_CLAIMED> --comments --json comments \
  --jq ".comments[] | select(.body | test(\"\\[CLAIMED\\]\")) | .body"

# 2. Vérifier que le grain n'intersecte pas le scope
python scripts/check_lane_claim.py <ISSUE_CLAIMED> --paths "<MES_GLOB_PATTERNS>"
#   --paths disjoint de son scope → NOT_SCOPED (exit 2)
#   --paths intersectant son scope → BLOCKED (exit 1)
```

Si `NOT_SCOPED` → poser un `[CLAIMED-AMEND] lane <self> -- paths:
<mon_scope_partitionne>` sur **la même issue**, ou ouvrir une issue de suivi
qui n'intersecte pas. Détail de la clause `paths:` matchable :
[docs/reference/lane-claim-detail.md](reference/lane-claim-detail.md#forme-canonique-de-la-clause-paths-10597-10958-11064-12052) (référence).

Si la collision est **non partitionnable** (même fichier, même section) →
DM co-claim à l'autre lane, attendre réponse avant d'éditer. C'est l'organe
cross-lane de cette procédure — le `[CLAIMED]` ne résout rien si l'autre lane
n'a pas eu le temps de répondre.

## 4. Anti-patterns

| Anti-pattern | Pourquoi c'est un piège | Alternative |
|---|---|---|
| `gh issue list --state open` seul | Ne voit pas les **PRs mergées** qui couvrent l'issue en rider. Tell fondateur #14259 | Étape 2 avec `--state all --search "<N>"` |
| `git merge-base --is-ancestor` seul | Un squash-merge efface l'ascendance ; `is_ancestor` retourne `false` alors que la PR est MERGED | Étape 2 avec `gh pr list --state all` |
| Croit qu'un worktree orphelin = travail abandonné | Le worker peut être en compaction, sa branche peut être attachée à une PR OPEN | Étape 3 + `gh pr list --state all --search "head:<br>"` |
| Édite puis pose `[CLAIMED]` | L'édition a déjà eu lieu ; si collision, retour arrière coûteux (commit revert + re-travail sur la bonne branche) | Appliquer cette procédure **avant** d'éditer |
| Croit qu'un claim **explicite** sur une issue suffit | Une autre lane peut avoir une PR ouverte touchant le **chemin** sans claim d'issue | Étape 2 systématique — claim implicite ≠ claim explicite |

## 5. Suivi — implémentation outillée

L'acceptance **#14300** demande l'ajout d'un mode `--check-implicit` à
`scripts/check_lane_claim.py` qui automatiserait les étapes 1-2. C'est un
grain substantiel (~200-300 lignes, header docstring + nouvelle branche dans
le dispatch + tests fixtures) **non couvert** par cette PR partielle c.925.

Une PR de suivi ouvrira le mode :

```bash
python scripts/check_lane_claim.py <ISSUE> --check-implicit --paths "<GLOB>"
#   CLEAR (exit 0)        : aucun claim explicite, aucune PR OPEN sur le chemin
#   BLOCKED (exit 1)      : claim explicite actif d'une autre lane
#   IMPLICIT (exit 3)     : aucune claim explicite, mais PR OPEN d'une autre lane
#   DELIVERED (exit 4)    : PR MERGED sur le chemin (= grain déjà livré)
#   NOT_SCOPED (exit 2)   : disjoint (cf. partitionnement §3)
```

Le nouvel exit code `IMPLICIT` rend visible **uniquement** ce que la procédure
manuelle détecte aujourd'hui. C'est ce que cette PR ne fait pas — elle documente
la procédure, sans l'outiller. Une fois outillée, ce document sera réécrit
pour renvoyer à la commande unique, et le mode manuel deviendra un fallback
d'audit.

## 6. Voir aussi

- [proactive-coordination.md §L898](../.claude/rules/proactive-coordination.md) — collision guard **avant d'ÉCRIRE**, pas avant de pousser.
- [proactive-coordination.md §L1356](../.claude/rules/proactive-coordination.md) — preflight claim `--state all`, jamais `--state open` seul.
- [lane-claim-protocol.md](../.claude/rules/lane-claim-protocol.md) — règle HARD `[CLAIMED]` côté worker, partitionnement `paths:`, organe `scripts/check_lane_claim.py`.
- [proactive-coordination-detail.md](reference/proactive-coordination-detail.md) — backlog pickup, pool global, never-idle.
- **Issue #14300** — acceptance partielle (cette PR) ; suivi outillage `--check-implicit`.
- **Issue #14259** — incident fondateur, tell « OPEN + zéro PR liée n'est pas une preuve de fraîcheur ».
- **Issue #14032** — exemple vécu c.925, claim explicite partitionné sans collision.

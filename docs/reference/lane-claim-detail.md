# Lane claim protocol — détail (référencé depuis `.claude/rules/lane-claim-protocol.md`)

Documentation détaillée du protocole de claim cross-lane. Le **règle succincte** vit dans [`.claude/rules/lane-claim-protocol.md`](../../.claude/rules/lane-claim-protocol.md) ; ce fichier porte le **contexte, les incidents, les déviations sémantiques et le tie-break**.

S'applique à tous les agents du cluster CoursIA (workers `po-*` + coordinateur `ai-01`), sur les deux workspaces. Source : mandat user 2026-08-06 (« mieux differencier les lanes CoursIA et CoursIA-2 pour eviter les collisions malheureusement trop courantes ») + sign-off user 2026-08-07 (session directe vscode).

## Pourquoi le dashboard ne peut PAS être le registre de verrous

- Le `[CLAIMED]` dashboard est **siloté par lane** : invisible depuis l'autre workspace pendant la fenêtre décision → push, exactement là où naissent les collisions (`gh pr list` ne voit que le travail déjà poussé).
- Le dashboard **auto-condense et archive** : un verrou ramassé par le GC n'est pas un verrou.
- Les stamps rédigés en corps de message **mélangent heure locale et UTC** (incident : `00:52` CEST suffixé `Z` → ordre des claims inversé, arbitrage failli être rendu à l'envers).

L'issue GitHub ferme les trois d'un coup : locus **unique cross-lane par construction**, timestamp **serveur UTC non falsifiable** (`createdAt`), **jamais condensée**.

**Référence croisée** : issue **#9774** (diagnostic complet + mandat) · PR **#9775** (organe `check_lane_claim.py`) · commit `7cec13a3f`.

## Forme canonique de la clause `paths:` (#10597, #10958, #11064, #12052)

La clause `paths:` est parsée par `_extract_paths_clause` dans `scripts/check_lane_claim.py`. **Quatre règles** la rendent matchable — toute déviation fabrique un scope mort et fait passer la claim en epic-wide (fail-CLOSED : un claim cassé n'est PAS permissif, il bloque toutes les autres lanes).

| Forme | Canonique | Cassé | Issue |
| --- | --- | --- | --- |
| Annotation tiret | `paths: a/**, b/** -- 2026-08-11T18:10Z` | `paths: a/**, b/**2026-08-11T18:10Z` (pas de ` -- `) | #10958 |
| Annotation parenthèse | `paths: a/** (Phase 2, tranche A)` | parenthèse NON séparée par espace = caractère légitime préservé | #12052 |
| Accolades | `paths: search-{6,8,9}-*.yaml` (fnmatch n'a pas `{a,b}`) | `paths: search-{a,b-*.yaml` (accolade non fermée) | #10597 |
| `--paths` CLI | `gh issue comment N --body-file body.md --paths g1 --paths g2` | `--paths ` seul avec valeur vide | #11064 |

**Règles de syntaxe (toutes obligatoires)** :

1. **Globs séparés par des virgules.** Pas de `;`, pas de retour à la ligne.
2. **Aucune parenthèse dans la liste de globs.** Annotation parenthétique = espace + ouvrante ` (`, tronquée au premier séparateur (#12052). Une parenthèse COLLÉE (sans espace) est un caractère de filename légitime, préservée intacte.
3. **Annotation éventuelle après un ` -- ` délimité par des espaces** (ou ` — `, ` – `), sur la MÊME ligne.
4. **Accolades fermées** et expandables (`{a,b,c}` → 3 globs frères). Une accolade non fermée = `unparseable_scope`, claim portée epic-wide par défaut.
5. **Chaque glob contient au moins un `/`** OU un métacaractère fnmatch (`*`, `?`, `[seq]`, `[!seq]`). Un mot isolé sans slash ni métacaractère est un fragment de prose — `_unparseable_scope_in` (#12052) le signale dans le JSON d'audit pour que la lane déclarante puisse le corriger. Sans slash ni métacaractère, fnmatch traite le fragment comme un nom de fichier LITERAL (qui ne matche rien en pratique).

**Référence organe** : `scripts/check_lane_claim.py:_extract_paths_clause` + `scripts/tests/test_check_lane_claim.py::test_paths_clause_*`. **Référence diagnostic** : issue **#12052** (parenthèse + prose), #10958 (annotation tiret), #10597 (accolades), #11064 (`--paths`).

## Déviation sémantique — un glob bien formé qui ne matche aucun fichier suivi (#12740)

La garantie fail-CLOSED de la ligne 28 (rule) tient pour les déviations **syntaxiques**. Elle ne tient pas pour la déviation **sémantique** — un glob syntaxiquement correct mais qui nomme un chemin inexistant (ex. `paths: scripts/notebook_tools/check_code_in_markdown.py` alors que le fichier réel est `detect_code_in_markdown_cells.py`, incident #12620 : deux lanes ont livré le même fichier réel).

Politique choisie (option **b**, signaler sans re-bloquer) : on NE rouvre PAS le fail-open #10958 — un claim actif dont tout le scope est mort reste porté epic-wide (un claim cassé n'est pas permissif) — mais `check_lane_claim.py` ajoute un champ JSON `dead_scope_globs` (lane-keyed, agrégé sur TOUS les événements de claim, y compris relâchés) pour que le typo soit visible à un sweep JSON, et non seulement sur le stderr que le gate/le picker ne consomment pas. Le cas légitime du fichier pas encore créé (grain Lean, nouveau notebook) reste couvert sans geler la lane : la cible s'écrit avec un métacaractère de répertoire (`scripts/notebook_tools/*markdown*`).

## Identité de lane et collisions intra-lane (#14323)

Le protocole indexe l'exclusion mutuelle sur la **lane** (`machine:workspace`), pas sur le processus Claude Code. C'est intentionnel : un claim de sa propre lane doit permettre une reprise après compaction ou réveil. Cette propriété repose toutefois sur une prémisse opérationnelle désormais explicite : **une seule session active par lane**.

Deux processus simultanés sous la même lane — par exemple un cron qui se déclenche pendant une session interactive, ou deux réveils qui se chevauchent — présentent la même identité à `check_lane_claim.py`. Le garde ne peut pas les distinguer : chacun interprète le claim existant comme sa propre reprise. Le mode `--paths` a la même limite, puisqu'il signale les intersections portées par une lane différente.

### Portée exacte de `CLEAR`

`CLEAR` garantit seulement qu'**aucune autre lane** ne détient un claim actif intersectant le grain ou les chemins demandés. Il ne garantit pas :

- qu'aucun autre processus ne travaille sous la même lane ;
- qu'une PR ou un worktree de la même lane n'est pas déjà en cours ;
- que la session appelante est l'auteur du claim observé.

Les gardes L898 (`git worktree list`, PRs ouvertes par branche/sujet/chemin) restent donc complémentaires, mais ils ne remplacent pas la prémisse : un travail intra-lane non poussé peut être invisible aux deux.

### Décision : restaurer la prémisse, ne pas étendre le marqueur

La voie retenue est **un agent actif par lane**, appliquée au niveau des schedulers et des sessions : laisser finir ou arrêter la session existante avant d'en démarrer une autre sous le même couple `machine:workspace`. En cas de chevauchement constaté, les deux processus cessent d'éditer, comparent leur périmètre, puis conservent un seul propriétaire actif.

L'alternative `[CLAIMED] lane <L> agent <session-id>` n'est pas retenue. Elle alourdirait un format déjà partagé par les issues, le picker et le merge-gate, tout en transformant chaque reprise après compaction en problème d'identité et chaque `RELEASED` manquant en blocage intra-lane. La règle d'exploitation rétablit l'invariant avec moins d'état et sans migration du parseur.

**Référence** : issue #14323 — diagnostic de l'angle mort intra-lane et lien avec les crons chevauchés.

## Tie-break — l'issue l'emporte, l'override s'écrit (#10223)

Les deux collisions du 2026-08-09 (#10169 puis #10161) ont révélé deux non-écrits qu'on écrit ici noir sur blanc. Un organe débloquant les enforce désormais : `.github/workflows/lane-claim-guard.yml` (`check-lane-claim-required`).

**Claim-issue > claim-dashboard, même quand le dashboard est antérieur.** Un `[CLAIMED]` sur l'issue bat un `[CLAIMED]` dashboard **indépendamment de l'horodatage**, pour les trois raisons mécaniques du § ci-dessus (silotage, condensation, stamps locaux) — pas par punition. Sur #10169, ~12 minutes d'avance au dashboard n'ont pas suffi : seul le claim d'issue était au locus cross-lane. Le `createdAt` serveur fait foi.

**Override coordinateur permis, mais écrit sur l'issue.** Le coordinateur garde le droit de merger contre un claim détenu quand la substance le justifie — mais il **perd la possibilité de le faire sans l'écrire**. L'arbitrage est porté par le marqueur `[OVERRIDE] lane <machine:workspace>` (commentaire d'issue), qui accorde le claim à la lane nommée et clot celui des autres dans le reducteur de `check_lane_claim.py` (Tâche 2 de #10223). Une réparation à la main après coup (ce qui a été fait sur #10169) est précisément le geste que cette clause rend inutile : le gate `check-lane-claim-required` reste rouge tant que l'override n'est pas écrit.

## Ce que cette règle ne fait pas

Elle ne sanctionne aucune lane : dans l'incident fondateur, les deux workers avaient passé leurs gardes correctement — le **signal** était défaillant, pas leur discipline. Lever un claim = commentaire explicite (`[RELEASED]` ou livraison de la PR) ; un claim d'une lane morte > 48 h sans commit ni PR se ré-arbitre par le coordinateur, pas par auto-service.

## Partitionnement par fichier (#10419, #11755)

Le coordinateur partitionne explicitement par fichier dès que plusieurs lanes convergent sur une même cible (précédent : `HashlifeCorrectness.lean` partitionne P4-mpr / murs SW-SE / MarginFragment entre trois lanes sur #6724). Le partitionnement s'écrit mécaniquement depuis #10419 : un `[CLAIMED]` portant une clause `paths:` ne bloque qu'une lane dont le scope **intersecte** le sien (fnmatch). Deux lanes aux scopes **disjoints** sur une même issue-parapluie (cas nominal d'un audit multi-instances type #10382, une lane par notebook) sont donc libres en parallèle.

Sans la clause, le `[CLAIMED]` reste **epic-wide** (bloque toutes les autres lanes -- sémantique héritée, préservée). L'organe lit le scope depuis le commentaire d'issue ET, en complément, depuis le `--paths` du caller ; la disjointness n'est honorée que quand **les deux** claims déclarent un scope.

## Claim stale — détection de péremption (#12751)

`check_lane_claim.py` détecte la péremption **active par défaut** (`--stale-threshold 48`). Un claim d'une lane morte > 48 h sans commit ni PR peut être repris par une autre lane en postant un nouveau `[CLAIMED]`. L'ancien comportement (toute claim active bloque) s'obtient explicitement par `--no-stale`.

## Lectures croisées

- `.claude/rules/lane-claim-protocol.md` — règle succincte (auto-chargé)
- `.claude/rules/proactive-coordination.md` — L898 collision guard (complémentaire : PRs déjà poussées) ; règle 5 pool global
- `.claude/rules/coordinator-discipline.md` — R3 lanes indépendantes, R5 steer qui ATTEINT
- `.claude/rules/variation-protocol.md` — le tag `Grain:`/`lane` que `check_lane_claim.py` sait extraire (#9485 single-reader)
- `scripts/check_lane_claim.py` — organe de détection
- `scripts/tests/test_check_lane_claim.py` — suite de tests
- Issue #9774 (diagnostic + mandat) · PR #9775 (organe) · Issue #10223 (gate bloquant `lane-claim-guard.yml` + marqueur `[OVERRIDE]`)
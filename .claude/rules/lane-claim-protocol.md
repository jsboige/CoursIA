# Lane claim protocol — le claim vit sur l'issue GitHub, pas sur le dashboard

S'applique a **tous les agents** du cluster CoursIA (workers `po-*` + coordinateur `ai-01`), sur les deux workspaces. Source : mandat user 2026-08-06 (« mieux differencier les lanes CoursIA et CoursIA-2 pour eviter les collisions malheureusement trop courantes ») + sign-off user 2026-08-07 (session directe vscode). Diagnostic complet + incident fondateur (#9764 livree deux fois par deux lanes irreprochables) : issue **#9774**. Organe : **#9775** (`scripts/check_lane_claim.py`, merge 7cec13a3f).

## Pourquoi le dashboard ne peut PAS etre le registre de verrous

- Le `[CLAIMED]` dashboard est **silote par lane** : invisible depuis l'autre workspace pendant la fenetre decision → push, exactement la ou naissent les collisions (`gh pr list` ne voit que le travail deja pousse).
- Le dashboard **auto-condense et archive** : un verrou ramasse par le GC n'est pas un verrou.
- Les stamps rediges en corps de message **melangent heure locale et UTC** (incident : `00:52` CEST suffixe `Z` → ordre des claims inverse, arbitrage failli etre rendu a l'envers).

L'issue GitHub ferme les trois d'un coup : locus **unique cross-lane par construction**, timestamp **serveur UTC non falsifiable** (`createdAt`), **jamais condensee**.

## Regle HARD — cote worker

1. **Avant d'EDITER un fichier** pour un grain rattache a une issue #N : verifier les claims — `python scripts/check_lane_claim.py N` — la detection de peremption est **active par defaut** (`--stale-threshold 48`, cf. #12751) ; l'ancien comportement (toute claim active bloque) s'obtient explicitement par `--no-stale`. (ou `gh issue view N -c`). Un `[CLAIMED]` d'une **autre lane** non leve → ne pas commencer, piocher ailleurs. Le check precede l'**edition**, pas le push (L898 durci : le pre-push est deja trop tard — c'est le cout du correctif ecrit en double).
2. **Poser son claim sur l'issue** : `gh issue comment N --body "[CLAIMED] lane <machine:workspace> — <intention en une ligne>"`. Pas de timestamp dans le corps : le `createdAt` serveur fait foi.
   - **Amender le scope d'un claim déjà posé** : `[CLAIMED-AMEND] lane <machine:workspace> -- paths: <scope corrigé COMPLET>` (même ligne). Sémantique #13022 : événement **open remplaçant** — le reducer ordonné par `createdAt` fait que l'amend remplace le claim précédent de la lane. La ligne doit porter l'**union complète** (pas le delta seul) ; un amend **sans** clause `paths:` repasse le claim en **epic-wide** (fail-CLOSED, cf [test suite](../../scripts/tests/test_check_lane_claim.py)). Incident fondateur : #11703 (amend d'union no-op pour l'organe, double livraison évitée de justesse par un re-[CLAIMED] canonique).
3. **Tout timestamp redige est en UTC explicite.** Le suffixe `Z` sur une heure locale est proscrit. En cas de conflit, l'ordering par `createdAt` serveur **l'emporte toujours** sur un stamp de corps.
4. Le dashboard **garde le recit de cycle** (`[CLAIMED]` informatif y reste bienvenu) ; il **cesse d'etre le registre de verrous** — seul le commentaire d'issue fait foi cross-lane.

## Regle HARD — cote coordinateur (ai-01)

5. **Poser le `[CLAIMED]` au dispatch** (commentaire d'issue au nom de la lane servie), sans attendre que le worker le pose au demarrage : la fenetre decision → claim est celle du coordinateur a couvrir.
6. **Partitionner explicitement par fichier** des que plusieurs lanes convergent sur une meme cible (precedent : `HashlifeCorrectness.lean` partitionne P4-mpr / murs SW-SE / MarginFragment entre trois lanes sur #6724). Le partitionnement s'ecrit mecaniquement depuis #10419 : un `[CLAIMED]` portant une clause `paths:` ne bloque qu'une lane dont le scope **intersecte** le sien (fnmatch). Deux lanes aux scopes **disjoints** sur une meme issue-parapluie (cas nominal d'un audit multi-instances type #10382, une lane par notebook) sont donc libres en parallele. Syntaxe : `[CLAIMED] lane <machine:workspace> -- paths: glob1, glob2`. Sans la clause, le `[CLAIMED]` reste **epic-wide** (bloque toutes les autres lanes -- semantique heritee, preservee). L'organe lit le scope depuis le commentaire d'issue ET, en complement, depuis le `--paths` du caller ; la disjointness n'est honoree que quand **les deux** claims declarent un scope.
7. **Lire les DEUX dashboards avant de provisionner** (rappel R3 [coordinator-discipline.md](coordinator-discipline.md)) — necessaire mais insuffisant seul : il ne couvre pas la fenetre inter-cycle, d'ou les points 5-6.

## Forme canonique de la clause `paths:` (#10597, #10958, #11064, #12052)

La clause `paths:` est parsee par `_extract_paths_clause` dans `scripts/check_lane_claim.py`. **Quatre regles** la rendent matchable — toute deviation fabrique un scope mort et fait passer la claim en epic-wide (fail-CLOSED : un claim casse n'est PAS permissif, il bloque toutes les autres lanes).

| Forme | Canonique | Casse | Issue |
| --- | --- | --- | --- |
| Annotation tiret | `paths: a/**, b/** -- 2026-08-11T18:10Z` | `paths: a/**, b/**2026-08-11T18:10Z` (pas de ` -- `) | #10958 |
| Annotation parenthese | `paths: a/** (Phase 2, tranche A)` | parenthese NON separee par espace = caractere legitime preserve | #12052 |
| Accolades | `paths: search-{6,8,9}-*.yaml` (fnmatch n'a pas `{a,b}`) | `paths: search-{a,b-*.yaml` (accolade non fermee) | #10597 |
| `--paths` CLI | `gh issue comment N --body-file body.md --paths g1 --paths g2` | `--paths ` seul avec valeur vide | #11064 |

**Regles de syntaxe (toutes obligatoires)** :

1. **Globs separes par des virgules.** Pas de `;`, pas de retour a la ligne.
2. **Aucune parenthese dans la liste de globs.** Annotation parenthétique = espace + ouvrante ` (`, tronquée au premier séparateur (#12052). Une parenthese COLLEE (sans espace) est un caractère de filename légitime, préservée intacte.
3. **Annotation éventuelle apres un ` -- ` délimité par des espaces** (ou ` — `, ` – `), sur la MEME ligne.
4. **Accolades fermées** et expandables (`{a,b,c}` → 3 globs frères). Une accolade non fermée = `unparseable_scope`, claim portée epic-wide par défaut.
5. **Chaque glob contient au moins un `/`** OU un métacaractère fnmatch (`*`, `?`, `[seq]`, `[!seq]`). Un mot isolé sans slash ni métacaractère est un fragment de prose — `_unparseable_scope_in` (#12052) le signale dans le JSON d'audit pour que la lane déclarante puisse le corriger. Sans slash ni métacaractère, fnmatch traite le fragment comme un nom de fichier LITERAL (qui ne matche rien en pratique).

**Référence organe** : `scripts/check_lane_claim.py:_extract_paths_clause` + `scripts/tests/test_check_lane_claim.py::test_paths_clause_*`. **Référence diagnostic** : issue **#12052** (parenthèse + prose), #10958 (annotation tiret), #10597 (accolades), #11064 (`--paths`).

**Conséquence croisée du scope mort — réserver une cible pas encore créée (#12905)** : la levée epic-wide de la déviation sémantique ci-dessus verrouille l'issue **entière**, y compris pour des lanes au scope vivant et prouvablement disjoint (#12844 mesuré : lane A scopée sur le notebook GT-17b existant, bloquée par le claim `asymmetric_information_lean/**` d'une lane B posé avant la création du chemin — la reproduction fondatrice). Le verdict BLOCKED **nomme** désormais ce mécanisme : annotation `DEAD-SCOPE LOCK` (#12927, test `test_12905_dead_scope_blocker_names_epic_wide_lock`) qui cite la lane bloqueuse, ses globs morts et les trois échappatoires (worktree à jour / `[RELEASED]` + priorité en prose / `[OVERRIDE]` coordinateur). **Pratique pour une cible qu'on s'apprête à créer** (nouveau lake, nouveau répertoire — le cas nominal d'une annonce de travail à venir) : écrire la priorité **en prose** dans le claim, sans clause `paths:` sur le chemin vide, et poser la clause quand le chemin porte son premier fichier suivi. C'est le contournement appliqué sur #12844 le jour même : `[RELEASED]` du claim au scope mort + priorité en prose, re-posé en `[CLAIMED] ... paths:` dès la création du lake.

**Déviation sémantique — un glob bien formé qui ne matche aucun fichier suivi (#12740)** : la garantie fail-CLOSED de la ligne 28 tient pour les déviations **syntaxiques**. Elle ne tient pas pour la déviation **sémantique** — un glob syntaxiquement correct mais qui nomme un chemin inexistant (ex. `paths: scripts/notebook_tools/check_code_in_markdown.py` alors que le fichier réel est `detect_code_in_markdown_cells.py`, incident #12620 : deux lanes ont livré le même fichier réel). Politique choisie (option **b**, signaler sans re-bloquer) : on NE rouvre PAS le fail-open #10958 — un claim actif dont tout le scope est mort reste porté epic-wide (un claim cassé n'est pas permissif) — mais `check_lane_claim.py` ajoute un champ JSON `dead_scope_globs` (lane-keyed, agrégé sur TOUS les événements de claim, y compris relâchés) pour que le typo soit visible à un sweep JSON, et non seulement sur le stderr que le gate/le picker ne consomment pas. Le cas légitime du fichier pas encore créé (grain Lean, nouveau notebook) reste couvert sans geler la lane : la cible s'écrit avec un métacaractère de répertoire (`scripts/notebook_tools/*markdown*`).

## Tie-break — l'issue l'emporte, l'override s'ecrit (#10223)

Les deux collisions du 2026-08-09 (#10169 puis #10161) ont revele deux
non-ecrits qu'on ecrit ici noir sur blanc. Un organe debloquant les enforce
desormais : `.github/workflows/lane-claim-guard.yml` (`check-lane-claim-required`).

8. **Claim-issue > claim-dashboard, meme quand le dashboard est anterieur.**
   Un `[CLAIMED]` sur l'issue bat un `[CLAIMED]` dashboard **independamment de
   l'horodatage**, pour les trois raisons mecaniques du § ci-dessus (silotage,
   condensation, stamps locaux) — pas par punition. Sur #10169, ~12 minutes
   d'avance au dashboard n'ont pas suffi : seul le claim d'issue etait au locus
   cross-lane. Le `createdAt` serveur fait foi.
9. **Override coordinateur permis, mais ecrit sur l'issue.** Le coordinateur
   garde le droit de merger contre un claim detenu quand la substance le
   justifie — mais il **perd la possibilite de le faire sans l'ecrire**.
   L'arbitrage est porte par le marqueur `[OVERRIDE] lane <machine:workspace>`
   (commentaire d'issue), qui accorde le claim a la lane nommee et clot celui
   des autres dans le reducteur de `check_lane_claim.py` (Tache 2 de #10223).
   Une reparation a la main apres coup (ce qui a ete fait sur #10169) est
   precisement le geste que cette clause rend inutile : le gate
   `check-lane-claim-required` reste rouge tant que l'override n'est pas ecrit.

## Ce que cette regle ne fait pas

Elle ne sanctionne aucune lane : dans l'incident fondateur, les deux workers avaient passe leurs gardes correctement — le **signal** etait defaillant, pas leur discipline. Lever un claim = commentaire explicite (`[RELEASED]` ou livraison de la PR) ; un claim d'une lane morte > 48 h sans commit ni PR se re-arbitre par le coordinateur, pas par auto-service.

## Voir aussi

- [proactive-coordination.md](proactive-coordination.md) — L898 collision guard (complementaire : PRs deja poussees) ; regle 5 pool global
- [coordinator-discipline.md](coordinator-discipline.md) — R3 lanes independantes, R5 steer qui ATTEINT
- [variation-protocol.md](variation-protocol.md) — le tag `Grain:`/`lane` que `check_lane_claim.py` sait extraire (#9485 single-reader)
- Issue #9774 (diagnostic + mandat) · PR #9775 (organe) · Issue #10223 (gate bloquant `lane-claim-guard.yml` + marqueur `[OVERRIDE]`)

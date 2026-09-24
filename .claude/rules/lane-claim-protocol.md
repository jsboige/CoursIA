# Lane claim protocol — le claim vit sur l'issue GitHub, pas sur le dashboard

S'applique à tous les agents du cluster CoursIA (workers `po-*` + coordinateur `ai-01`), sur les deux workspaces. **Détail** : [docs/reference/lane-claim-detail.md](../../docs/reference/lane-claim-detail.md) — incident fondateur #9774, organe PR #9775, déviations sémantiques #12740, tie-break #10223.

## Règle HARD — côté worker

1. **Avant d'ÉDITER un fichier** pour un grain rattaché à une issue #N : vérifier les claims — `python scripts/check_lane_claim.py N` (détection de péremption **active par défaut** `--stale-threshold 48`, cf. #12751). Un `[CLAIMED]` d'une **autre lane** non levé → ne pas commencer, piocher ailleurs. Le check précède l'**édition**, pas le push (L898 durci).
2. **Poser son claim sur l'issue** : `gh issue comment N --body "[CLAIMED] lane <machine:workspace> — <intention en une ligne>"`. Pas de timestamp dans le corps : le `createdAt` serveur fait foi.
   - **Amender le scope** : `[CLAIMED-AMEND] lane <machine:workspace> -- paths: <scope corrigé COMPLET>` (même ligne). Sémantique #13022 : événement **open remplaçant**. Un amend **sans** clause `paths:` repasse la claim en **epic-wide** (fail-CLOSED, cf. #11703 incident fondateur).
3. **Tout timestamp rédigé est en UTC explicite.** Le suffixe `Z` sur une heure locale est proscrit. En cas de conflit, l'ordering par `createdAt` serveur **l'emporte toujours** sur un stamp de corps.
4. Le dashboard **garde le récit de cycle** (`[CLAIMED]` informatif y reste bienvenu) ; il **cesse d'être le registre de verrous** — seul le commentaire d'issue fait foi cross-lane.

## Prémisse d'identité — une lane = un agent actif (HARD, #14323)

Le protocole suppose **un seul agent actif par couple `machine:workspace`**. Un second processus (cron chevauché, session interactive parallèle) sous la même lane est indiscernable du premier : `check_lane_claim.py` traite leur claim commun comme une reprise légitime.

- `CLEAR` signifie uniquement **« aucune autre lane ne bloque ce grain ou ces chemins »**. Il ne prouve ni « aucun autre processus travaille », ni « aucun travail de ma propre lane n'est en cours ».
- La voie retenue est de **restaurer cette prémisse opérationnelle** : un cron/session actif par lane, sans ajouter d'identité de processus au format de claim.
- Avant de démarrer une seconde session sous la même lane, arrêter ou laisser finir la première. Si un chevauchement est découvert, ne pas éditer : coordonner les deux sessions et conserver un seul propriétaire actif.

Le détail et les alternatives écartées sont consignés dans [lane-claim-detail.md](../../docs/reference/lane-claim-detail.md#identité-de-lane-et-collisions-intra-lane-14323).

## Règle HARD — côté coordinateur (ai-01)

5. **Poser le `[CLAIMED]` au dispatch** (commentaire d'issue au nom de la lane servie), sans attendre que le worker le pose au démarrage : la fenêtre décision → claim est celle du coordinateur à couvrir.
6. **Partitionner explicitement par fichier** dès que plusieurs lanes convergent sur une même cible (précédent : `HashlifeCorrectness.lean` sur #6724). Syntaxe : `paths: glob1, glob2` — sans clause, le claim reste **epic-wide**. Détail partitionnement : [docs/reference/lane-claim-detail.md](../../docs/reference/lane-claim-detail.md#partitionnement-par-fichier-10419-11755).
7. **Lire les DEUX dashboards avant de provisionner** (R3 [coordinator-discipline.md](coordinator-discipline.md)) — nécessaire mais insuffisant seul : il ne couvre pas la fenêtre inter-cycle, d'où les points 5-6.

## Forme canonique de la clause `paths:` (résumé)

Quatre règles la rendent matchable — toute déviation = scope mort = epic-wide (fail-CLOSED) :

| Forme | Canonique | Cassé |
| --- | --- | --- |
| Annotation tiret | `paths: a/**, b/** -- 2026-08-11T18:10Z` | pas de ` -- ` |
| Annotation parenthèse | `paths: a/** (Phase 2, tranche A)` | parenthèse collée (sans espace) = filename légitime préservé |
| Accolades | `paths: search-{6,8,9}-*.yaml` (fnmatch n'a pas `{a,b}`) | accolade non fermée |
| `--paths` CLI | `gh issue comment N --body-file body.md --paths g1 --paths g2` | `--paths ` seul avec valeur vide |

**Détails, table étendue, déviations sémantiques (#12740), références organe** : [docs/reference/lane-claim-detail.md](../../docs/reference/lane-claim-detail.md#forme-canonique-de-la-clause-paths-10597-10958-11064-12052).

## Voir aussi

- [proactive-coordination.md](proactive-coordination.md) — L898 collision guard ; règle 5 pool global
- [coordinator-discipline.md](coordinator-discipline.md) — R3 lanes indépendantes, R5 steer qui ATTEINT
- [variation-protocol.md](variation-protocol.md) — le tag `Grain:` que `check_lane_claim.py` sait extraire
- [docs/reference/lane-claim-detail.md](../../docs/reference/lane-claim-detail.md) — **détail complet**
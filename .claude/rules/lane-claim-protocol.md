# Lane claim protocol — le claim vit sur l'issue GitHub, pas sur le dashboard

S'applique a **tous les agents** du cluster CoursIA (workers `po-*` + coordinateur `ai-01`), sur les deux workspaces. Source : mandat user 2026-08-06 (« mieux differencier les lanes CoursIA et CoursIA-2 pour eviter les collisions malheureusement trop courantes ») + sign-off user 2026-08-07 (session directe vscode). Diagnostic complet + incident fondateur (#9764 livree deux fois par deux lanes irreprochables) : issue **#9774**. Organe : **#9775** (`scripts/check_lane_claim.py`, merge 7cec13a3f).

## Pourquoi le dashboard ne peut PAS etre le registre de verrous

- Le `[CLAIMED]` dashboard est **silote par lane** : invisible depuis l'autre workspace pendant la fenetre decision → push, exactement la ou naissent les collisions (`gh pr list` ne voit que le travail deja pousse).
- Le dashboard **auto-condense et archive** : un verrou ramasse par le GC n'est pas un verrou.
- Les stamps rediges en corps de message **melangent heure locale et UTC** (incident : `00:52` CEST suffixe `Z` → ordre des claims inverse, arbitrage failli etre rendu a l'envers).

L'issue GitHub ferme les trois d'un coup : locus **unique cross-lane par construction**, timestamp **serveur UTC non falsifiable** (`createdAt`), **jamais condensee**.

## Regle HARD — cote worker

1. **Avant d'EDITER un fichier** pour un grain rattache a une issue #N : verifier les claims — `python scripts/check_lane_claim.py N` (ou `gh issue view N -c`). Un `[CLAIMED]` d'une **autre lane** non leve → ne pas commencer, piocher ailleurs. Le check precede l'**edition**, pas le push (L898 durci : le pre-push est deja trop tard — c'est le cout du correctif ecrit en double).
2. **Poser son claim sur l'issue** : `gh issue comment N --body "[CLAIMED] lane <machine:workspace> — <intention en une ligne>"`. Pas de timestamp dans le corps : le `createdAt` serveur fait foi.
3. **Tout timestamp redige est en UTC explicite.** Le suffixe `Z` sur une heure locale est proscrit. En cas de conflit, l'ordering par `createdAt` serveur **l'emporte toujours** sur un stamp de corps.
4. Le dashboard **garde le recit de cycle** (`[CLAIMED]` informatif y reste bienvenu) ; il **cesse d'etre le registre de verrous** — seul le commentaire d'issue fait foi cross-lane.

## Regle HARD — cote coordinateur (ai-01)

5. **Poser le `[CLAIMED]` au dispatch** (commentaire d'issue au nom de la lane servie), sans attendre que le worker le pose au demarrage : la fenetre decision → claim est celle du coordinateur a couvrir.
6. **Partitionner explicitement par fichier** des que plusieurs lanes convergent sur une meme cible (precedent : `HashlifeCorrectness.lean` partitionne P4-mpr / murs SW-SE / MarginFragment entre trois lanes sur #6724).
7. **Lire les DEUX dashboards avant de provisionner** (rappel R3 [coordinator-discipline.md](coordinator-discipline.md)) — necessaire mais insuffisant seul : il ne couvre pas la fenetre inter-cycle, d'ou les points 5-6.

## Ce que cette regle ne fait pas

Elle ne sanctionne aucune lane : dans l'incident fondateur, les deux workers avaient passe leurs gardes correctement — le **signal** etait defaillant, pas leur discipline. Lever un claim = commentaire explicite (`[RELEASED]` ou livraison de la PR) ; un claim d'une lane morte > 48 h sans commit ni PR se re-arbitre par le coordinateur, pas par auto-service.

## Voir aussi

- [proactive-coordination.md](proactive-coordination.md) — L898 collision guard (complementaire : PRs deja poussees) ; regle 5 pool global
- [coordinator-discipline.md](coordinator-discipline.md) — R3 lanes independantes, R5 steer qui ATTEINT
- [variation-protocol.md](variation-protocol.md) — le tag `Grain:`/`lane` que `check_lane_claim.py` sait extraire (#9485 single-reader)
- Issue #9774 (diagnostic + mandat) · PR #9775 (organe)

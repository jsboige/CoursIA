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
6. **Partitionner explicitement par fichier** des que plusieurs lanes convergent sur une meme cible (precedent : `HashlifeCorrectness.lean` partitionne P4-mpr / murs SW-SE / MarginFragment entre trois lanes sur #6724). Le partitionnement s'ecrit mecaniquement depuis #10419 : un `[CLAIMED]` portant une clause `paths:` ne bloque qu'une lane dont le scope **intersecte** le sien (fnmatch). Deux lanes aux scopes **disjoints** sur une meme issue-parapluie (cas nominal d'un audit multi-instances type #10382, une lane par notebook) sont donc libres en parallele. Syntaxe : `[CLAIMED] lane <machine:workspace> -- paths: glob1, glob2`. Sans la clause, le `[CLAIMED]` reste **epic-wide** (bloque toutes les autres lanes -- semantique heritee, preservee). L'organe lit le scope depuis le commentaire d'issue ET, en complement, depuis le `--paths` du caller ; la disjointness n'est honoree que quand **les deux** claims declarent un scope.
7. **Lire les DEUX dashboards avant de provisionner** (rappel R3 [coordinator-discipline.md](coordinator-discipline.md)) — necessaire mais insuffisant seul : il ne couvre pas la fenetre inter-cycle, d'ou les points 5-6.

## Tie-break — l'issue l'emporte, l'override s'ecrit (#10223)

Les deux collisions du 2026-08-09 (#10169 puis #10161) ont revele deux
non-ecrits qu'on ecrit ici noir sur blanc. Un organe debloquant les enforce
desormais : `.github/workflows/lane-claim-guard.yml` (`check-lane-claim-required`).

8. **Claim-issue > claim-dashboard, meme quand le dashboard est anterieur.**
   Un `[CLAIMED]` sur l'issue bat un `[CLAIMED]` dashboard, **independamment
   de l'horodatage**. La raison est mecanique, pas punitive : le dashboard est
   silote par lane (invisible cross-workspace pendant la fenetre decision ->
   push), auto-condense (un verrou ramasse par le GC n'est pas un verrou), et
   ses stamps melent heure locale et UTC (cf §ci-dessus). Sur #10169, po-2026
   avait ~12 minutes d'avance sur le dashboard workspace-CoursIA — et a perdu
   contre le claim d'issue de po-2025, parce que seul ce dernier etait au locus
   cross-lane. Le `createdAt` serveur de l'issue fait foi ; un stamp dashboard
   anterieur ne l'invalide pas.
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

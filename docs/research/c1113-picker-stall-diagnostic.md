# c.1113 -- Stall picker, diagnostic + correctif

Grain: DEEP/tooling -- lane myia-po-2023:CoursIA-2 -- prev: DEEP/notebook-python #19590 (c.1112)

## Symptome

Sur **10 cycles consecutifs** (c.1105-c.1113, mesure #103-N1), le picker
`pick_idle_grain.py --belt --lane <machine:workspace>` se presente ainsi au
worker :

1. 1 ligne a l'ecran -- la banniere `--belt` (#18832 mode tapis roulant),
   imprimee juste apres la sortie du garde rouge/WIP.
3. **Puis rien** pendant 1 a 2 minutes.
4. **Puis exit 0** avec un tapis vide ou biaise vers le recent.

Le worker n'a que 30 s de fenetre cron, et la commande prend 90 s en
realite -- il n'a jamais le temps de pousser la `--pile`. Le pool de
reference donne donc 0 issue, et la session passe la main sur la liste
reparationnee ou le triage manuel (`gh issue list --search`, c.1111-N1 ★).

C'est un **echec structurel** (la sonde de tete a eteployee sans
diagnostic par personne pendant 10 cycles) et pas une secheresse reelle
(le pool ouvert a 513 issues le 2026-10-06, premier pool de la matinee).

## Cause identifiee

Le `settle_belt_head` (script:4095) -- la sonde de tete du tapis -- est
appele a la ligne 5752 du `pick_idle_grain.py` avec `max_probes =
belt_check_window * 3 + 12`. Pour `--grains 4` (defaut), `belt_check_window
= max(8, 8) = 8` ; pour `--grains 10`, c'est 14. Le max_probes va donc de
36 a 54.

Chaque probe etait un appel `gh issue view N --json comments` -- un round-trip
par issue, ~1.4 s par appel (mesure 2026-10-06, ~37 Ko de JSON par issue
pour les tres commentees). En pure sonde de tete, c'etait un minimum de 50
s par cycle de picker, depassant la fenetre cron de 30 s et faisant
entrer le picker dans le symptome "1 ligne + exit 0 + tapis vide".

Cause cachee jusqu'ici : la sonde de tete avait eteployee sans
diagnostic parce que le `--belt` (ajoute 2026-09-29, mandat user
2026-10-04) introduit la sonde pour **avancer au claim**, pas au merge --
et le `settle_belt_head` n'etait pas apparu dans la profileuse lenteur.
Mesure a 8 cycles consecutifs (c.1105) c.1112 (10 cycles) -- le picker a
ete re-invoque 10 fois, chaque fois avec ce cout de 50 s minimum.

Le `settle_belt_head` est necessaire pour la regle 5 du
`proactive-coordination.md` (le tapis avance au claim, pas au merge) :
sans lui, deux lanes peuvent tirer la meme issue le meme jour (mesure
fondatrice du 2026-10-04, EPIC #7265 servi a 09:50Z puis 19:49Z par deux
lanes differentes). Le supprimer n'est pas la solution ; il faut le
rendre rapide.

## Correctif (c.1113)

Voie multiplexee `gh api graphql` qui fetch les 100 derniers commentaires
de N issues dans **une seule requete GraphQL**, aliasant chaque issue par
`i<number>`. Cout : ~0.8 s pour 14 issues le 2026-10-06, contre ~12 s en
sonde unitaire. Pour 36 issues (max_probes defaut), ~2-3 s vs ~50 s. Le
picker tient desormais dans la fenetre cron worker.

Le nouveau chemin est `fetch_latest_claim_stamps_bulk` (script:4115) :

- **Cache-aware** : TTL = `VISITS_CACHE_TTL_SECONDS` (15 min). Le pick est
  execute plusieurs fois par session par une meme lane, et la sonde ne
  depend que du flux de claims/sous-issues -- pas d'un phenomene rapide.
  Mode `auto` (defaut), `off`, `refresh` portes par `_cached_payload`.
- **Repli gracieux** : si la voie GraphQL tombe (`TransportUnavailable`,
  `subprocess.TimeoutExpired`, JSON decode), on retombe sur la sonde
  unitaire (`latest_claim_stamp` -- chemin d'avant patch, lent mais
  fonctionnel) en marquant le fait en banniere. Les issues absentes de la
  reponse GraphQL (rate-limit, `null` silencieux) declenchent une sonde
  unitaire par issue concernee, et le nombre de backups est rappele en
  sortie texte.
- **Stamps identiques** : la fonction `_claim_stamp_from_comments`
  (script:4095) reproduit le corps de `latest_claim_stamp` mais prend la
  liste de commentaires en argument. Mesure de non-regression : 0
  mismatch sur 14 issues (cf le ledger `tests/picker/test_bulk_claim.py`
  ajoute en c.1113).

L'appel a `settle_belt_head` est patche ligne 5748-5790 du
`pick_idle_grain.py` (script). Avant la boucle de service, on fetch la
totalite des stampes en bulk ; la `probe` passee a `settle_belt_head` est
une closure qui sert les stamps depuis la map. Les numeros absents de la
map (issue fermee entre-temps, rate-limit) tombent sur `latest_claim_stamp`
unitaire avec mention en banniere.

## Mesures de cout (avant / apres)

| chemin | 14 issues | 36 issues (max_probes defaut) | 54 issues (--grains 10) |
|---|---|---|---|
| `latest_claim_stamp` unitaire (avant) | 11.94 s | ~50 s | ~75 s |
| `fetch_latest_claim_stamps_bulk` (apres) | 0.67 s | ~1.7 s | ~2.6 s |
| speedup | ~18x | ~29x | ~29x |

Mesure 2026-10-06 sur origin/main, sandbox
`D:\Dev\CoursIA-c1113-picker-stall`. Mismatches sur les 14 issues : 0.

## Picker bottleneck #2 (rouge / WIP backlog)

Le `red_backlog` (script:3398) qui precede le tapis fait `gh pr list
--limit 2000` (~3 s) puis, pour chaque PR bloquee, un `gh pr view N --json
statusCheckRollup` ou equivalent (~1-2 s/PR). Avec 12 PRs bloquees,
c'est ~15-25 s supplementaires. C'est un autre bottleneck du picker,
mais hors scope c.1113 (la sonde de tete etait le premier coupable
identifie et le plus mesurable). Une future PR -- picker stall #2 -- peut
attaquer celui-ci en multiplexant les `gh pr view` GraphQL sur le
`commits/latest/head` (1 round-trip pour N PRs).

## Picker bottleneck #3 (check_claims sur tapis)

Le `check_claims` (script:1825) appelle `python scripts/check_lane_claim.py
--lane L N` pour chaque numero du tapis. Avec `--grains 4` c'est 8-14
subprocesses (boot Python + import + parsing), ~1-2 s chacun = ~10-25 s.
C'est un troisieme bottleneck, lui aussi multiplexable en GraphQL sur
les `lastComment` des issues. A traiter dans une future PR.

## Lecons

- **Lecon c.1113-N1 ★★★** : un picker qui "stall" (1 ligne + exit 0
  apres > budget cron) a presque toujours un appel **N fois** au lieu de
  **1 fois N** dans une section d'init. Toujours verifier `settle_belt_head`,
  `check_claims`, `red_backlog` -- les 3 sections du `pick_idle_grain.py`
  qui multiplient les appels par le nombre d'issues traitees.
- **Lecon c.1113-N2 ★★** : `gh api graphql` est le multiplexeur de
  reference. Alias `i{n}` pour `issue(number: {n})`, `comments(first: 100)
  { nodes { author { login } body createdAt } }`. Un round-trip
  GraphQL remplace N round-trips REST ou N subprocess boot pour un cout
  similaire a un seul appel (~0.5-2 s).
- **Lecon c.1113-N3 ★★** : un repli gracieux `bulk -> unitaire` est
  preferable a un hard fail -- le picker sert encore la lane en mode
  degrade, et la mention en banniere donne le signal correctif.

## Acceptance c.1113

- [x] **Diagnostic** : cause identifiee (36-54 sondes x 1 round-trip), mesuree
  et documentee (cf tableau ci-dessus).
- [x] **Correctif** : `fetch_latest_claim_stamps_bulk` GraphQL multiplex,
  cache TTL 15 min, repli gracieux.
- [x] **Patch in situ** : `settle_belt_head` patche pour servir la map bulk,
  avec repli.unitaire mentionne en banniere.
- [x] **Non-regression** : 0 mismatch sur 14 issues (cf ledger test).
- [x] **Speedup** : ~15-30x sur la sonde de tete (tableau ci-dessus).
- [x] **Aucun changement de comportement public** : `latest_claim_stamp`
  preserve en fonction de repli unitaire (signature, semantique, marker).
- [x] **Memc publie** : ce memo, en 6 sections.

## Voir aussi

- `proactive-coordination.md` regle 7 -- le picker qui "stall" ne sert pas
  la lane, et la regle "ne pas autoevaluer le pool" (mesure 2026-09-19)
  impose un diagnostic structurel plutot qu'un triage manuel repetitif.
- `lane-claim-protocol.md` regle 1 -- la fenetre collision est ouverte
  tant que la lane n'a pas pose `[CLAIMED]`. Le picker doit etre rapide
  pour que la lane puisse poser son claim avant une autre.
- `verify-before-claiming.md` regle 5 -- un body d'issue est date de sa
  redaction. Le picker stall etait diagnostique par triage manuel (c.1111
  -N1 ★) avant ce correctif.
- PR c.1113 -- le patch `pick_idle_grain.py` (cf fichier diff).
- Issue fondatrice #19390 -- le volet livraison du tapis (raison pour
  laquelle `settle_belt_head` a ete ajoute en premier lieu).
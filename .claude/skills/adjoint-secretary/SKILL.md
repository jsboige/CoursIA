---
name: adjoint-secretary
description: Cycle 30 min du secrétaire vérificateur myia-po-2026:CoursIA-3. Consigne l'état de coordination sur workspace-CoursIA-3, porte les aller-retours DM avec les workers, et émet des dossiers de preflight sur les tranches assignées par l'adjoint titulaire.
---

# Secrétaire vérificateur — myia-po-2026:CoursIA-3

Cycle court (30 min, cadence cron haiku) du secondataire de l'adjoint titulaire (`myia-po-2025:CoursIA-2`). Le dashboard `workspace-CoursIA-3` est le lieu d'organisation à trois : titulaire, secrétaire, coordinateur (`myia-ai-01:CoursIA`).

Cette commande est réservée au slot `myia-po-2026:CoursIA-3` et ne doit jamais être remplacée par `/coordinate`, `/coordinate-adjoint` ou `/continue`.

## Mandat fondateur (user 2026-09-21)

> « Tu es celui des 3 coordinateurs le plus actif, avec ton cron plus fréquent que les autres et ton modèle nettement plus rapide. Mets à jour tes mémoires et ton harnais pour ne plus rester stalled comme ça. Tu es celui qui doit faire circuler l'information pour que tout se débloque. »

## Rôle et frontière HARD

Le secrétaire vérificateur DÉCHARGE l'adjoint titulaire. Il peut :

- **consigner** sur `workspace-CoursIA-3` : les décisions rendues, les tells fondateurs, les blockers actifs, l'état des vagues de dossiers — l'état de coordination lisible par les trois parties ;
- **porter les aller-retours DM** avec les workers : relais des dispatchs du titulaire (le titulaire arbitre, le secrétaire notifie et collecte les réponses), relances de nits, collecte des preuves post-fix ;
- **vérifier de façon bornée** : re-mesurer les HOLD, re-stamper les dossiers périmés, émettre des `[ADJOINT PREFLIGHT]` sur les **tranches de PRs explicitement assignées** par le titulaire (répartition publiée sur `workspace-CoursIA-3`) ;
- **attester en tierce** les PRs portées par la lane titulaire (l'auto-attestation lui est refusée par le gate — le secrétaire est un 2e attestataire aux côtés de po-2024/po-2027).

Restent au titulaire (`myia-po-2025:CoursIA-2`, cf [coordinate-adjoint](../coordinate-adjoint/SKILL.md)) :

- la synthèse pour ai-01 (le secrétaire prépare les éléments, le titulaire consolide et signe) ;
- la réponse aux ASK des lanes, les dispatchs de NOUVEAUX grains, les réparations de scope ;
- l'hygiène de `workspace-CoursIA-2`.

Restent au coordinateur (`myia-ai-01:CoursIA`) : merges, clôtures, reviews `APPROVED`/`CHANGES_REQUESTED`, marqueurs `[OVERRIDE]`, HOLD G-VAR, batch-close, PR étudiantes, arbitrages inter-lanes.

**Interdits du secrétaire** : merger, fermer une issue d'autrui, poster une synthèse au nom du titulaire, dispatcher un grain non assigné, toucher aux PR étudiantes.

## Cycle (30 min)

1. Lire `workspace-CoursIA-3` (section `all`) : consignes du titulaire, tranche assignée, messages du coordinateur.
2. Lire l'inbox RooSync non lue de `myia-po-2026:CoursIA-3`.
3. Traiter la tranche assignée : émission/re-stamp de dossiers selon les garde-fous ci-dessous.
4. Porter les aller-retours en attente (relais, relances, collectes) — un DM par worker, la sonnette sur le dashboard concerné.
5. Consigner sur `workspace-CoursIA-3` : ce qui a été vérifié (avec preuve), ce qui a changé, ce qui attend qui.
6. Finir par un rapport `[DONE][SECRETARY]` court (l'état, pas la chronique).

**Plafond : ~40 appels gh par cycle** (le mur du débit de la flotte est le rate limit GitHub partagé — 5 000/h **par utilisateur** `jsboige`, toutes lanes confondues, avec limite secondaire GraphQL ; un cycle haiku qui brûle le quota baisse le débit de tous).

## Doctrine Hub — décharger, pas attester (mandat user 2026-09-22)

**Le secrétaire dépense des tokens à la PLACE de l'adjoint et du coordinateur, pas EN PLUS d'eux.**

Le poste est apparu pour **soulager** ai-01 et le titulaire. Quand le secrétaire passe son cycle à émettre 6 dossiers `[ADJOINT PREFLIGHT]` qui ne servent qu'à prouver ce que chacun peut voir par `gh pr view`, il **augmente** la charge au lieu de la réduire. Le résultat : ai-01 et titulaire restent saturés, le secrétaire finit son cycle en ayant juste produit du SHA-matching.

**Verbatim user 2026-09-22** : « tu nous fait des sessions fines comme du papier à cigarette alors qu'on a toujours 300+ PRs en vol et que je te rappelle que ton rôle est de dépenser des tokens que l'adjoint et le coordinateur n'auront pas à dépenser. C'est tout l'inverse que tu fais, les 2 restent surchargés pendant que tu ne fais quasiment rien, et c'est inacceptable. »

### Hiérarchie des gestes (du plus utile au moins utile)

**Niveau 1 — Ce qui décharge vraiment les autres** (faire en priorité) :

1. **Push paquets nominatifs DM ai-01** : 30 PRs avec diff/auteur/âge/verdict exact-head → il merge en 1 passe (mesure fondatrice `ai01-c29-lot-secretaire-14` : 10/10 converties en merge vs 15/53 et 2/54 sans tri nominatif).
2. **Alerte titulaire sur CHANGES_REQUESTED à désamorcer** : 1 DM par PR en CHANGES_REQUESTED non levée avec motif exact → il sait exactement laquelle regarder.
3. **Push liste nominative PRs CONFLICT aux porteurs** : 1 commentaire PR par PR en CONFLICT pour qu'ils rebasent → ça débloque le merge sans intervention coordinateur.
4. **Surveillance quota GraphQL** : `gh api rate_limit` deep + tracker `{rest, graphql}` séparément. Alerter ai-01 si porte fermée.
5. **Surveillance runners saturation** : suivre les signalements de check rouge CI systemic, escalader en DM ai-01 quand 6+ PRs sont bloquées par la même cause.

**Niveau 2 — Ce qui peut être utile si le pool le demande** (à faire après le Niveau 1) :

6. **Dossiers `[ADJOINT PREFLIGHT]` nominatifs exact-head** : quand ai-01 ou titulaire **demande explicitement** un dossier sur une PR précise, ou quand un dispatch nominatif est posté dans l'inbox.
7. **Préfight B.0 / nits non levés** : lister dans un DM les PRs avec `check_unaddressed_nits.py rc=1` pour qu'ai-01 puisse décider lecture par lecture.

**Niveau 3 — À éviter** (le notaire) :

- Émettre 6 dossiers/salve/cycle en oldest-first quand personne ne les demande. **consomme du quota GraphQL** sans augmenter le taux de merge.
- PATCH/correction de dossiers périmés. Le delta de conversion est nul.
- Diagnostiquer en détail des motifs gate (DWELL, kernels drift) hors périmètre secrétaire.
- Cycle bloqué à re-gater 6 PRs pour avoir 4 READY + 2 BLOCKED — c'est le travail d'un bot, pas d'un hub.

### Critère de succès d'un cycle

**Un cycle est utile si et seulement si** ai-01 ou titulaire peut merger ou travailler sur **plus de PRs à la fin du cycle qu'au début**. Le hub fournit l'info en avance ; il n'atteste pas l'info après.

**Anti-pattern** : terminer un cycle avec « 4 READY + 2 BLOCKED posés » sans que la file de merge d'ai-01 n'ait bougé. **Le hub a augmenté la charge au lieu de la réduire.**

## Émission de dossiers — garde-fous obligatoires

Référence complète : [coordinate-adjoint §Émission de dossiers](../coordinate-adjoint/SKILL.md). Les quatre non-négociables :

1. **Instrument de mesure des checks (arbitrage ai-01 2026-09-21 + RECTIF 12:09Z)** : lire `commits/<sha>/check-runs` — **jamais** `actions/runs` (un `attempt=2` y garde l'ancien id plus petit : organe `dedupe_latest`, `scripts/pr_gate.py` l.537, mesure #11416). Dédup **obligatoire** (17 noms dupliqués mesurés sur #16263) par clé canonique `(started_at, id)` dans cet ordre — jamais `created_at`, jamais `id` seul — et **paginer** (`--paginate` : total_count 101 > per_page 100 mesuré sur #16263).
2. **Le gate en échec imprime sur STDOUT** : avant tout post de dossier, exiger (a) rc=0 du `--template`, (b) `head -1` du fichier = `[ADJOINT PREFLIGHT]`, (c) placeholders `REPLACE_WITH` présents dans le template source. `grep -c REPLACE_WITH = 0` est un **faux-OK** sur une ligne d'erreur `UNKNOWN -- ...`.
3. **Le gate ne lit pas l'état de merge** : un dossier READY exige la vérification `mergeable` côté attestant (`CONFLICTING` → BLOCKED conflit ; `UNKNOWN` → HOLD re-mesure).
4. **Dossier posé EN DERNIER** : toute prose postée après le dossier le périmé (surfaces-sha256). En fenêtre rate-limited GraphQL : fallback REST (`gh api repos/jsboige/CoursIA/issues/N/comments --input payload.json`, payload `{"body": "..."}` hors shell — `-f body=` interdit, `gh-posting-hygiene` HARD 1), template régénéré après la fenêtre.
5. **DWELL = minuteur, pas un défaut de contenu** : un rouge `PR gate: DWELL -- ... ecoule a <HH:MM>Z. Rien a corriger dans le code` ne se répare PAS par push (chaque push ré-arme le plancher 120 min depuis la nouvelle tête) ; un dossier BLOCKED qui le nomme est un livrable valide, le merge suit l'échéance. `gh pr update-branch` ne ré-arme PAS le plancher depuis #16149. Corollaire : `statusCheckRollup` ment sur ~20 % des candidates (mesuré ai-01 2026-09-21) — ne jamais en faire un verdict.
6. **Lane qualifiée AVANT émission** : vérifier que la lane du dossier figure dans `QUALIFYING_LANES` du gate (`scripts/check_adjoint_prevalidation.py` l.102-113) — une lane hors liste rend `NO-DOSSIER` quelle que soit la qualité des mesures (6 commentaires invalides mesurés cycles 1-2).

Un BLOCKED honnête est un livrable valide (le gate rend rc=3) ; ne jamais écrire READY pour être visible.

## Quota GitHub, classement des rouges et contrôles de fond (mesures des 2026-09-22 et 23)

1. **Le quota REST `core` est par utilisateur, pas par jeton.** Un 403 « API rate limit exceeded for **user ID** … » signifie que le compte `jsboige` est vide pour **toute la flotte**. Deux instruments mentent alors :
   - `gh api rate_limit` rend 5000 restants, car il lit le compteur du jeton ;
   - `gh auth status` affiche « token invalid ».

   Le reset se lit dans les en-têtes : `gh api -i <endpoint> | grep -i x-ratelimit`. Mesure fondatrice : un cycle secrétaire de plusieurs centaines d'appels a vidé le quota de la flotte pendant 22 min.
2. **Lister en masse = GraphQL paginé**, jamais du REST PR par PR. `pullRequests(states: OPEN, first: 100)` rend `headRefOid`, `mergeable` et la date du dernier commit : 3 appels pour ~290 PRs. Le REST (check-runs, organes) ne se dépense que sur la **tranche actionnable**.
3. **Un rouge se classe au log du job, pas au titre.**
   - La classe « `Always-on guards -- N organes, 1 checkout` » est l'**agrégat** des organes : « 1 checkout » décrit le job, pas la cause.
   - Mesure sur 7 jobs : 5 défauts de contenu (perimeter, `tag_required`, `prev:` qui pointe une issue) et 2 défauts d'infra.
4. **Rouge après `update-branch` : vérifier d'abord que la tête contient le correctif** avec `gh api repos/jsboige/CoursIA/compare/<fix_sha>...<head> --jq .status`.
   - `ahead` ou `identical` : le correctif est dans la tête, donc le rouge vient d'ailleurs (runner sans `gh` dans son PATH, « lost communication », XDIST-WATCHDOG). Le geste est un **rerun `--failed` du run enfant**.
   - Sinon : `update-branch`, sous le frein de la file CI.
5. **Un champ absent fait échouer le filtre** (fail-closed). Il ne doit jamais tomber dans une valeur sentinelle qui passe le filtre. Contre-exemple mesuré : `x.get("head_date") or "9"` a classé 53 PRs comme « poussées il y a moins de 30 min ».
6. **Le compteur `status=queued` porte des zombies** : environ 55 runs créés le 08-19 et le 09-13 n'ont jamais été servis. Le frein « file > 120 » se calcule sur les runs **créés dans les 2 dernières heures**, groupés par heure de création, jamais sur `total_count` brut.
7. **GraphQL à 0 fausse B.0** : `check_unaddressed_nits.py` rend rc=1 et `--template` rend rc=2 `UNKNOWN`, sans que les nits aient changé. Avant d'interpréter un rouge B.0, lire `gh api graphql -f query='{rateLimit{remaining resetAt}}'`.
8. **Relire le fil de fermeture d'ai-01 avant de pousser des verdicts de fond**. Un relevé GraphQL de `state` coûte un point et évite de poser des dossiers sur des PRs fermées. Les PRs de la campagne densité gelée (veto #17040) se cherchent **par titre** (`densité in:title`, `densite in:title`) : l'organe #17456 ne voit que le numéro #13410.
9. **Une PR REPAIR peut corriger le point du CR et détruire le notebook**. Compter, par cellule, les items de `source` sans `\n` final (dernier item exclu), base contre tête.
   - Si le compte monte fortement dans une cellule de **code**, les lignes ont été jointes : en Lean ou Python, le code devient commentaire et les outputs deviennent orphelins.
   - Mesure fondatrice : #16951 (0 -> 1467) et #16970 (0 -> 606), deux ré-accentuations dont le CR sur `prouvé` était bien traité.
   - Bisecter par commit pour nommer le fautif et le dernier sain, puis poser une réserve 🔴 et un DM au porteur et à ai-01.
   - 1 à 3 items en markdown sont des soft-wraps, donc du bruit.
10. **Un READY de plus d'une heure se re-gate avant d'être renvoyé à ai-01**. Une tête inchangée ne prouve pas un dossier vivant :
    - un stamp legacy meurt dès que ses checks bougent (« legacy stamps whose checks moved need one --template re-stamp ») ;
    - un commentaire posté après le dossier (`[RIPE-SIGNAL]`, review NanoClaw) change `surfaces-sha256` ou fait passer B.0 à rc=1.

    Un script qui compare seulement la tête du dossier à la tête de la PR rend un faux LIVE. Seul `python scripts/check_adjoint_prevalidation.py N` fait foi. Mesure du 2026-09-22 à 23:15Z : 0 READY vivant sur 8 posés entre 08:54 et 21:30, 7 sur 8 après re-stamp.
11. **Un READY `domain: pass` peut être faux : crible de fond mécanique avant tout paquet**. Le gate ne relit pas le fond. Comparer base et tête, cellule par cellule, sur quatre points :
    - sources effondrées (item 9) ;
    - sortie de code réduite de plus de 30 % ;
    - marqueurs de dégradation (`disponible : False`, `fallback`, `sautée`, `Traceback`) ;
    - identifiants Python accentués (tokenize `NAME`) : une passe d'accents qui renomme `self.verifier` en `self.vérifier` casse le code sans toucher au markdown.

    Mesure fondatrice : #16953, READY du titulaire à 23:17 avec `domain: pass`, alors qu'il cumulait des identifiants renommés et une ré-exécution sans clé (`True` devenu `False / fallback`). Le trou d'organe correspondant est suivi en #17468.
12. **Le crible de fond ne remplace ni le gate ni B.0 : les deux se relancent PR par PR avant chaque paquet**. Ordre :
    1. `check_adjoint_prevalidation.py N` rc=0 **et** `check_unaddressed_nits.py N` rc=0, dans le quart d'heure qui précède l'envoi. **Le gate ne relance pas B.0.**
    2. Re-stamp `--template` des dossiers morts. Le format neuf re-vérifie les checks latest-wins au lieu de les hacher, donc un seul re-stamp rend le dossier durable face aux reruns.
    3. Envoi du paquet.

    Mesure fondatrice du 2026-09-22 à 23:50Z : sur 32 READY envoyés après le seul crible de fond, 14 étaient NO-DOSSIER (stamps legacy dont les checks avaient bougé après le redémarrage d'un pool, et un `[RIPE-SIGNAL]` posté après le dossier) et 1 avait B.0 rc=1 (réserve NanoClaw sur une base non mergée). Après re-stamp : 30 sur 32 mergeables.

13. **Deux attestants ne stampent pas la même PR**. Un dossier posté par-dessus un dossier `--template` vivant change les surfaces et le périme. Un dossier composé à la main, sans `--template`, ne survit pas au premier check qui bouge. Les deux attestants peuvent ainsi s'annuler, et la PR sort de la file d'ai-01 avec **zéro** dossier valide. Avant chaque post, un appel `check_adjoint_prevalidation.py N` : s'il rend 0 sous une autre lane attestante, ne pas poster. Partager les PRs sur `workspace-CoursIA-3`, et générer toujours avec `--template`.

    Mesure fondatrice du 2026-09-23 (00:10Z, puis 00:21-00:30Z) : sur #17312, #17384, #17414 et #17423, le titulaire a posté par-dessus des dossiers secrétaire rc=0. Ses dossiers rendaient eux-mêmes rc=1 (« surfaces not fully attested »). Il a fallu re-stamper les quatre.
14. **Le crible par diff mot à mot ne voit pas les défauts en cellule code : diff par jetons obligatoire sur toute passe d'accents**. En cellule code, séparer ce qui a changé :
    - jetons de code, hors commentaires et chaînes : un identifiant renommé d'un seul côté donne une `NameError` au Run All ;
    - chaînes seulement : si la sortie est identique octet pour octet au merge-base, elle est périmée (C.2).

    Sur les chaînes et commentaires, chercher aussi les docstrings **anglaises** accentuées et les mots en **capitales** passés en casse de phrase (`PROUVE` devenu `Prouvé`). Une levée de réserve étroite (un seul motif, par exemple `donné`/`donne`) ne vaut pas pour toute la PR.

    Mesure fondatrice : #16986, #16987 et #16988, « preuve » par diff `donn*` seul, puis `[OVERRIDE]` d'ai-01 à 00:07Z. Le diff par jetons a trouvé ensuite :
    - sur #16988, `résultat = ...` suivi de `print(f"... {resultat} ...")`, soit une `NameError`, avec une sortie `True` héritée de main ;
    - sur #16987, `"""Exécute a bash command ..."""` ;
    - sur #16986, trois `#eval` modifiés sans ré-exécution.

15. **Rejouer un job ne rafraîchit pas sa base**. Un rerun garde le `GITHUB_SHA` de l'événement d'origine, donc la merge ref `Merge <head> into <base>` de ce moment-là. Un correctif mergé sur `main` après la création du run est invisible au rerun, quel que soit le nombre de tentatives. Mesure fondatrice : #17087, run créé à 20:30Z, attempt 3 rejouée à 23:41Z, base `2e564885f` sans #17415 (21:10Z) ; résultat : exit 127 et 8 échecs `test_guard_gauntlet` sur les slots po-2026, alors que le même test passe sur les slots ai-01. Le remède « rejouer » devient une loterie de slot. Avant de rejouer, lire la ligne `HEAD is now at … Merge X into Y` du log et vérifier `git merge-base --is-ancestor <sha du fix> Y`. Si le fix manque, seul un nouvel événement `pull_request` (push ou update-branch) le récupère : c'est une décision d'ai-01 sous le frein CI, pas un rerun de plus.

16. **Un re-stamp confronte le body au diff**. Le gate ne lit pas le scope. Avant de poser `scope: pass`, relever les chemins que le body cite comme livrés (verbes corrigé, modifié, remplacé, ajouté) et vérifier qu'ils sont dans `pulls/N/files`. Mesure fondatrice : #16701, stampé `scope: pass` à 00:35Z. Le body annonçait 4 fichiers `.claude/*` et une cellule de Video 03-3 ; le diff ne touchait que 4 fichiers `docs/`, `scripts/` et `translations/`. Le BLOCKED du titulaire, posé à 00:59Z, était juste. Un crible par chemins cités sort beaucoup de faux positifs (références, fichiers « non touché ») : chaque hit se lit dans son contexte. Un BLOCKED de substance posé par l'autre attestant n'est pas un double-stamp (item 13). On le vérifie, on relaie la réparation à la lane porteuse, et on re-stampe à tête inchangée une fois le body corrigé. **Avant tout stamp, lire le `verdict:` du dernier dossier posé** : le 23/09, un READY a écrasé sans lecture un BLOCKED fondé (#17409). Sur une PR qui touche du `.lean` ou `agent_tests/prover/`, vérifier que le body porte les lignes B.1 à B.3, même en non applicable, avec `count_code_sorry.py`. Deux READY ont été retirés pour ce motif (#16905, #17409).

17. **Une restauration « à l'identique » restaure aussi les défauts de position**. Restaurer une cellule depuis la merge-base reconduit sa place d'alors. Si elle était mal placée, elle l'est encore (§D.4bis : une lecture suit la cellule de code dont la sortie porte ses chiffres). Instrument : pour chaque cellule markdown ajoutée par le commit de restauration, chercher ses nombres (au moins deux chiffres) dans la sortie de la cellule de code qui précède. 0 hit signale une lecture déplacée ; on cherche alors quelle sortie porte ces nombres. Mesure fondatrice : #17461 `ef1e9110a`, `03-Embeddings [10]` (« 4282 paires uniques »). Ses chiffres sont dans [8], elle est placée après [9], dont la sortie est vide, et elle était déjà mal placée à la merge-base `39c65577e4`. Contrôle : #17463, 7 lectures sur 7 bien placées. Corollaire de l'item 15 : un workflow `pull_request` aux types par défaut (`secret-scan.yml`) n'est relancé ni par un rerun ni par une édition de body. Seuls `synchronize` et `reopened` recalculent la merge ref, et c'est ce qui fait tomber un rouge hérité de `main`.

18. **Vérifier une affirmation avant de composer le post, jamais dans la même chaîne**. Trois comportements se cumulent :
    - sous Git Bash, `git show origin/main:<chemin>` est réécrit en chemin Windows (`origin\main;.github\…`) et échoue ;
    - une boucle `for` dont chaque itération échoue rend 0 ;
    - une chaîne `… && gh api …/comments --input` poste donc une affirmation qu'aucune mesure n'a portée.

    Mesure fondatrice : la levée #16905 (5787472539) a été postée avec une ligne B.3 « vérifiée » alors que le scan avait échoué. La re-mesure (`MSYS_NO_PATHCONV=1`, `git grep -l … origin/main -- <dir>`) l'a confirmée après coup : 14 workflows, 0 hit. Parade : exporter `MSYS_NO_PATHCONV=1` pour toute commande `ref:chemin`, et faire la mesure et le post en deux appels séparés, en lisant la sortie de la mesure entre les deux.

19. **Toute commande réseau porte un `timeout`, et une seule chose à la fois**. Un `git fetch`, un `gh api` ou un gate qui attend le réseau sans borne suspend la session entière, et le cron meurt avec elle : le secrétaire disparaît sans prévenir, alors que son rôle est justement de faire circuler l'information. Mesure fondatrice : deux blocages dans la nuit du 22 au 23/09. Le second, sur une chaîne `git fetch` de deux refs de PR + `git show > fichier` + `cmp`, a duré de 01:50Z à 11:20Z. Pendant ce temps le titulaire a envoyé un WAKE, ai-01 a réassigné deux PRs (#17479, #17485), et les deux coordinateurs ont cessé d'écrire sur `workspace-CoursIA-3`. Parade :
    - préfixer `timeout 20` (réseau) ou `timeout 60` (gate, fetch lourd) à chaque commande, **et** passer le paramètre `timeout` de l'outil Bash ;
    - ne pas chaîner plusieurs fetch réseau dans un même appel : un appel, une attente réseau ;
    - écrire les sorties intermédiaires dans le scratchpad de session, jamais dans un chemin de racine (`/tmp_*`) ;
    - à la reprise après un blocage : réarmer le cron d'abord, poster un `[INFO]` sur `workspace-CoursIA-3` et répondre par DM au titulaire et à ai-01 **avant** de reprendre la file. Leur silence sur le dashboard est la conséquence de l'absence, pas un désintérêt.

20. **Classer un rouge de runner à l'annotation du check-run, pas à la durée**. Un `Scripts Tests (CPU)` rouge dont le step `Run tests` a `conclusion=null` n'a pas échoué sur un test : le runner est mort sous lui. La cause se lit dans `gh api repos/jsboige/CoursIA/check-runs/<job>/annotations` au niveau `failure` : « The self-hosted runner lost communication with the server » (vers 13 à 19 min) ou « Out of memory » (vers 4 à 8 min). Mesure fondatrice du 23/09 à 11:35Z : **19 des 33** rouges `Scripts Tests (CPU)` des PRs ouvertes, tous sur `myia-ai-01-wsl-*`, avec 12 pertes de communication et 7 OOM. Classés « timeout » ou « échec sans test nommé », ils envoyaient les lanes réparer des PRs saines (#17519 : skipif posé pour rien). Un tel rouge se remonte au propriétaire de l'infra et se lève **par un rerun après correction de l'hôte**. C'est l'inverse d'un rouge hérité de main (item 15).
21. **`gh api rate_limit` ment sur GraphQL : lire les en-têtes d'un vrai appel**. Le 23/09 à 11:40Z, `gh api rate_limit` rendait `graphql 5000/5000 used 0`, alors qu'au même instant `gh api graphql -i` renvoyait `X-Ratelimit-Remaining: 0`, `Used: 5000`, avec un reset à 11:55:59Z. Pendant cette fenêtre, `check_unaddressed_nits.py` plante sur `gh pr view --json comments,reviews,commits` et sort en **rc=1 avec un traceback**, ce qui est indiscernable d'un BLOCKED si l'on ne lit que le code de retour. Parade :
    - mesurer le quota par `gh api graphql -i -f query='query{rateLimit{remaining resetAt}}'` ;
    - avant de consigner un B.0 rc=1, vérifier que la sortie commence par `BLOCKED` et non par `Traceback` ;
    - avertir les trois dashboards (cross-post) avec l'heure du reset, puis reprendre les mesures après.
22. **Un advisory rouge interdit READY : le gate le compte dans `latest-wins-green`**. `check_adjoint_prevalidation.py` range tout check-run de la tête dans le prédicat, requis ou non (`GREEN_CONCLUSIONS = {success, skipped, neutral}`, l.141). Une PR `mergeable_state: unstable`, dont le seul rouge est un advisory comme `Markdown table syntax advisory (label, non-blocking)`, reste donc mergeable pour GitHub, mais son dossier ne peut pas porter `checks: latest-wins-green` sans être contredit. Mesure fondatrice : #16897 et #16785, le 23/09 à 11:58Z. Le dossier y est BLOCKED, et le paquet d'ai-01 doit nommer l'advisory en cause, pas un défaut de PR.
23. **Un exercice est une cellule code stub, pas un énoncé markdown**. `three-exercises-per-notebook` définit l'exercice comme une *cellule code avec stub* (`pass` / `return None` / `print("Exercice a completer")` / `result = None  # TODO`). Pour un notebook **neuf** (point 1), avant d'écrire `domain: pass`, vérifier que chaque `### Exercice N` est suivi d'une cellule `code`. Mesure fondatrice : #16785 (SL-14 AI Feynman) le 23/09. Les cellules 22 à 24 portaient trois énoncés, chacun suivi directement de markdown : 0 exercice au sens de la règle, alors que le dossier du 21/09 disait `domain: pass`. Réserve 🟡 `5794432303`. Instrument : lire la liste `cells` et, pour chaque en-tête d'exercice, le `cell_type` de la cellule suivante.
24. **Une PR CLEAN dont la base est une branche morte ne livre rien : mesurer la base avant `scope: pass`**. Le gate ne lit pas `baseRefName`. Une PR empilée dont la PR de base a été mergée (ou fermée) reste `CLEAN` et verte, mais son merge atterrit sur une branche que plus rien ne porte vers `main`. Instrument, pour toute base non-`main` : `gh pr list --state all --search "head:<baseRefName>"`. Base `MERGED` ou `CLOSED` → `scope: fail`, geste de lane : retarget vers la branche vivante (`gh pr edit N --base …`) si la PR de base a été mergée par commit de merge, `git rebase --onto origin/main <ancienne tête de base>` si elle a été squash-mergée (le squash réécrit les SHA : `compare main...<tête>` remonte alors les fichiers de la base). Mesure fondatrice du 23/09 à 12:14Z : 4 PR CLEAN sur 38 (#16987, #16988, #16989, #17429), dont une stampée `scope: pass`. Corollaire, même cycle : une levée qui cite un SHA absent des commits de la PR se vérifie par `commits/<sha>/branches-where-head` — deux fois (#16989, #17123), le correctif était resté sur une branche latérale. Si son parent est la tête de la PR et qu'il ne touche aucune source de cellule code, l'avance rapide `git push origin <sha>:refs/heads/<branche de la PR>` exécute l'intention déclarée de la lane (règle 0 de `proactive-coordination`) ; s'il touche une cellule code, la ré-exécution C.2 revient à la lane.
25. **Un PR gate rouge sur une cause redevenue verte ne se relève pas seul : rejouer le run du gate**. Le PR gate agrège les checks au moment de son run. Si le rouge qu'il nomme passe au vert ensuite, il garde son FAIL tant que le balayage horaire `pr-gate-stale-sweep.yml` (cron `7 * * * *`) ne l'a pas ré-agrégé, et GitHub sert ce cron en retard, parfois pas du tout. Détection : dernier PR gate en `FAILURE`, titre qui ne commence pas par `DWELL`, aucun autre check rouge ni en cours. Remède : `gh run rerun <run id du PR gate>`, qui ré-agrège à l'état courant. Pas de push, pas d'`update-branch` : les deux déclenchent une rafale CI pour rien. Le même geste lève une vague `DWELL` échue quand le balayage n'est pas passé. Mesure fondatrice du 23/09 : #17537 (Always-on guards rouge à 10:39Z, vert à 11:18Z, gate toujours FAIL à 12:30Z, dernier balayage servi à 11:30Z), rejoué à 12:34Z et READY dans la foulée ; #17530, même classe.
26. **Deux pièges du rejeu, et le balayage qui ne voit plus rien**.
    - **`--failed` refusé sur un run qui conclut `success`.** Un job PR gate peut échouer sans runner (`runner_name: null`, 0 étape, durée nulle) à l'intérieur d'un run dont la conclusion reste `success`. Le check-run garde alors le titre de sa tentative précédente (un DWELL périmé, par exemple). Dans ce cas, `gh run rerun <run> --failed` rend « cannot be retried ». Le geste qui marche est `gh run rerun --job <job id>`, où le job id est celui du check-run (`actions/jobs/<id>`). Lecture des check-runs d'une suite relancée : `filter=all`, car le défaut `latest` masque la jambe.
    - **Balayage à 0 PR.** Avant de compter sur le balayage pour lever un DWELL, lire son dernier run : si la ligne « open PRs inspected: » est à 0 ou très en dessous du pool ouvert, le balayage n'a rien vu. Ses appels check-runs échouent en silence (`2>/dev/null || continue`), probablement sur le quota GITHUB_TOKEN épuisé par la rafale de balayages déclenchés à chaque push, et il conclut `success` quand même (défaut porté par #17230/#17243). Les DWELL échus se lèvent alors à la main.
    - **Un READY rendu par le gate ne vaut pas candidature au merge pour une PR de la campagne densité #13410**, gelée par le veto #17040. On la cherche par corps (`See #13410`) autant que par titre (item 8), et on la sort du paquet.
    - Mesure fondatrice du 23/09 : #17497 (job 107199661705, attempt 2 échouée à 13:22Z en 0 s ; `--job` accepté à 13:31Z) ; balayages 35866395602 et 35867123056 à 0 PR, contre 101 à 13:05Z ; #16413 et #16694 listées READY à tort.
27. **Lever, relire, re-stamper : cinq pièges.**
    - **B.0 ne crédite une levée qu'en voix nue.** Quand la réserve et la levée sont postées sous le même login (`jsboige`), `_lift_eligible` ignore une levée dans trois cas :
      - elle commence par un préfixe de rôle, `**[SECRETARY]` compris : `_ROLE_PREFIX_RE` traite `**` comme de la décoration ;
      - elle commence par un préfixe de lane `[machine:workspace]` ;
      - son texte contient un marqueur de réserve : glyphe 🟡/🔴 nu, `**BLOCKED**` ou « contredit ».

      Forme sûre : « Levée de la réserve NNNN du secrétaire (lane …, tête `xxx`) : … ». Mesure fondatrice : les levées de #17503 et #17469 sont restées à B.0 rc=1 jusqu'au PATCH (5796372227, 5796372614).
    - **Une ré-exécution lancée sans le paramètre de référence écrase le run qu'elle prétend reproduire.** Si un notebook piloté par un flag papermill (`FORCE_RETRAIN`, `USE_CACHE`) est rejoué avec la valeur par défaut, ses sorties sont valides mais relèvent d'un autre régime : poids chargés du cache au lieu d'un entraînement. Tous les organes restent verts. Avant `domain: pass`, comparer `metadata.papermill.parameters` entre la base et la tête. Mesure fondatrice : #17521, réserve 🔴 5796278027.
    - **Une règle déjà livrée par une PR sœur se voit dans l'arbre de merge.** Deux PRs de harnais sur la même issue peuvent écrire la même prescription à deux endroits. `git merge-tree --write-tree origin/main <tête>` donne l'arbre qui résulterait du merge : y chercher la section ajoutée et son équivalent déjà présent sur main. Mesure fondatrice : #17289 contre #16879 (issue #16878), `git-workflow.md` l.43-52 contre l.61-80, réserve 🟡 5796479941.
    - **Un `[OVERRIDE]` d'ai-01 posté après un dossier BLOCKED appelle un re-stamp, et personne ne le signale.** Pour repérer ces cas en masse, une requête GraphQL paginée suffit. Elle relève, sur les PRs ouvertes, `reviews(last:5, author:"myia-ai-01")` et les derniers commentaires ; on compare ensuite la date du dernier OVERRIDE à celle du dernier `[ADJOINT PREFLIGHT]`. Un OVERRIDE posé par l'auteur de la PR ne compte pas : il faut alors une re-review de la persona. Mesure fondatrice du 23/09 : #17257 et #17213 sont redevenues READY sur re-stamp à tête inchangée. #16735 est une PR d'ai-01 : son OVERRIDE ne lève pas la réserve NanoClaw.
    - **Un heredoc non quoté exécute les backticks qu'il contient.** Un corps de commentaire contenant `` `papermill …` `` et écrit dans `<<EOF` lance la commande. Toujours écrire `<<'EOF'`. Mesure fondatrice : c.50, un corps de commentaire rédigé dans un heredoc non quoté a exécuté ses backticks au lieu de les poster.

28. **Figure, jumelles, levées : quatre relevés.**
    - **Une courbe tracée ne prouve pas un modèle qui apprend.** Une lane sans vision peut établir qu'une figure n'est pas un cadre vide (en comptant les pixels colorés), mais pas ce que la figure montre. Le secrétaire la **regarde** (`Read` sur le PNG extrait par `git show <tête>:<chemin>`), puis la croise avec les métriques imprimées. Trois signes concordants désignent un prédicteur constant : des courbes plates, une `Correlation: nan` (variance nulle des prédictions pour `np.corrcoef`) et une analyse par quantile vide. Dans ce cas, l'exactitude affichée est la fréquence de la classe majoritaire. Si la prose annonce une plage (« 0.02-0.08 »), c'est un point de merge : soit la prose déclare la limite, soit la cause est corrigée. Mesure fondatrice : #17521 `f3f2d90ba2`, ré-entraînement de 13 epochs, validation figée à 0,5736, main à `Correlation 0.0160`.
    - **Deux PRs d'une même lane sur le même notebook se mesurent en séquence.** Commande : `git merge-tree --write-tree origin/main A`, `commit-tree` de l'arbre obtenu, puis `merge-tree` de B sur ce commit. Un CONFLICT dans les deux ordres signifie que l'une des deux doit être remplacée ou fermée, et c'est ai-01 qui tranche. Au passage, un PNG de figure d'environ 2,5 Ko est un cadre vide. Mesure fondatrice : #16808 puis #17521 donnent un CONFLICT sur QC-Py-31 et sur `training_curves.png` (2 487 octets dans #16808).
    - **Une review persona ultérieure peut attester elle-même un point d'un CR antérieur.** Dans la table LIFT-READY, citer la phrase de la seconde review qui constate le correctif, plutôt que re-mesurer ce qu'elle a déjà mesuré. Mesure fondatrice : sur #17487, le CR2 Hermes constate que la jambe KaTeX du CR1 est annoncée et que math-render est vert.
    - **Un retarget ou un rebase rend le body périmé.** Après un changement de base, relancer `git diff --stat <nouvelle base> <tête>` et le comparer aux chiffres du body. Tant qu'ils divergent, laisser `domain` à `fail` dans le script de dossier : `domain: pass` ne dit rien du scope. Mesure fondatrice : #16987 annonce +4/-4, le diff contre la nouvelle base fait +676/−370.
29. **Deux relevés : un `SUCCESS` qui ment, un advisory qui tombe sur l'infra.**
    - **Un `SUCCESS` imprimé par la cellule ne prouve pas que la commande a abouti.** Un wrapper peut rendre `Exit code : 0` alors que la commande a écrit `error:`. Le crible des sorties (item 11) ne cherche donc pas seulement `Traceback` et `fallback`. Il cherche aussi `Aborting`, `error: external command`, `(aucune sortie)` et `0 verdicts`, puis compare base et tête **ligne par ligne** : un `7/7` devenu `0/7` ne se voit pas à la taille de la sortie, qui peut même grossir. Mesure fondatrice : #16987 `aa28e7e44e`, ré-exécution complète dans un paquet `.lake/packages/mathlib` sale. Cellules 38 et 42 : 0 verdict parsé sur 7. Cellule 46 : `Aborting` / `git exited with code 1`, puis `SUCCESS : les 3 modules Life compilent`. Le body venait d'être aligné sur le diff : la seule levée du body aurait fait passer la PR en READY.
    - **Un advisory rouge se lit au log avant d'être imputé à la PR.** Sur #17551, `Organ-duplication advisory (non-blocking)` était rouge, et l'item 22 interdit READY dans ce cas. Le log montrait une erreur GraphQL de `sticky-pull-request-comment` (« Something went wrong while executing your query »), pas un finding. Il fallait un `gh run rerun <id> --failed` **avant** le stamp : le job ré-écrit un commentaire collant, et ce commentaire périmerait un dossier posté avant lui.

## Consignation sur workspace-CoursIA-3

Le dashboard est la **mémoire de travail à trois**. Chaque consigne porte : quoi (décision/tell/blocker), preuve (comment ID, run ID, mesure), qui attend quoi. Les posts du coordinateur y font foi sur ses arbitrages ; ceux du titulaire sur l'assignation des tranches ; les vôtres sur l'état vérifié. Rien d'éphémère n'est consigné (ça vit dans les rapports de cycle), rien de durable n'est laissé hors dashboard (le secrétaire meurt avec sa session).

## Amélioration continue (mandat user 2026-09-21)

« Gardez sous le coude l'amélioration continue, et mettez à jour vos skills régulièrement. » Chaque tell fondateur mesuré en cycle (garde-fou manquant, anti-pattern, instrument faux) est consigné sur le dashboard **puis** reporté dans cette skill par PR dédiée — pas d'édition directe de `main`. Trois défauts muets à chercher en priorité : un instrument qui réimplémente un organe existant (`git grep` le geste dans `scripts/` avant d'écrire du jq de verdict), une absence observée sur un échantillon prise pour une propriété de l'API, une forme d'appel gh non canonique (`-f body=` interdit, `gh-posting-hygiene` HARD 1).

## Cron

Un seul cron session-only à 30 min portant `/adjoint-secretary`. Vérifier `CronList` avant tout réarmement ; les crons expirent automatiquement après 7 jours — un cron expiré = slot silencieusement idle.

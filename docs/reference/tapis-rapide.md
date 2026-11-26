# Tapis rapide — la voie légère du tirage des grains

> REFERENCE — vivante — dernière révision 2026-11-26

Issue : [#22983](https://github.com/jsboige/CoursIA/issues/22983). Code : `scripts/coordination/tapis_rapide.py`
(fonctions pures et CLI), `scripts/coordination/tapis_marqueurs.py` (lecture des marqueurs de fil, extraite
le 2026-11-14 pour tenir le plafond de lignes), `scripts/coordination/tapis_service.py` (la forme du service :
commande, procédure de conteneur, lecture de secours, sortie texte), `scripts/coordination/tapis_origami.py`
(parcage Origami, #26523), `scripts/coordination/tapis_reverif.py` (re-décision des fils tronqués, #27179),
`scripts/coordination/tapis_leger.py` (la voie légère du tirage, #27225), `scripts/coordination/tapis_fenetre.py`
(la fenêtre du pool classé et celle du fil, #27225), `scripts/coordination/gh_issues.py`
(la lecture ciblée des issues nommées, #27225), `scripts/coordination/tapis_seance.py`
(les séances de marqueurs : une livraison en ouvre une neuve, #27338),
`scripts/coordination/tapis_citations.py` (les citations des PRs ouvertes : le travail en cours compte
comme une visite, #27338), `scripts/coordination/belt_equite.py` (l'équité du dispatch : un grain déjà
servi ne passe pas devant les premières visites, #27338)
et `scripts/coordination/gh_bulk.py` (seul module qui lance `gh` ou `git`).

Le lot public livré par #27368 est porté par des modules dédiés, extraits pour que les tests visent le
chemin public lui-même : `scripts/coordination/tapis_public.py` (la suite exacte du chemin public),
`scripts/coordination/tapis_tete.py` (le numéro que la rotation sert en premier),
`scripts/coordination/tapis_avance.py` (l'avance du curseur, bornée au lot),
`scripts/coordination/tapis_entrelace.py` (l'alternance primaire/reprise),
`scripts/coordination/tapis_non_tente.py` (le grain proposé mais jamais qualifié),
`scripts/coordination/tapis_etat_schema.py` (le schéma de l'état d'ancre : classes, état neuf,
accesseurs) et `scripts/coordination/tapis_etat_commit.py` (le commit qui a écrit l'état : deux états
d'ancre ne sont comparables que s'ils viennent du même code).
Elle **remplace** `scripts/pick_idle_grain.py --belt` pour le tirage : depuis #26926, aucune sortie du tapis rapide ni de `check_lane_claim.py` ne renvoie plus au tapis lourd (240 s, grains non vérifiés), qui reste un outil de diagnostic.

## La commande

```bash
python scripts/coordination/tapis_rapide.py --lane <machine:workspace> [--grains 8] [--json]
       [--jours 45] [--cache-s 300] [--graine S] [--lecture <dossier>]
       [--voie {leger,lourd}]
```

**La voie par défaut est légère** (classement sur métadonnées, qualification du grain servi sur son **fil
complet**) depuis #27225 ; `--voie lourd` garde l'ancienne lecture du pool entier, et le rejeu `--lecture`
y reste. Voir « La bascule » plus bas.

Trois lectures groupées, quel que soit le nombre de candidats : les issues ouvertes (GraphQL, pages de 50,
12 derniers commentaires par issue), les PRs ouvertes (REST, pages de 100) et **un** `git log origin/main`
local sur `--jours` jours (45 par défaut : une livraison fermée hors d'une fenêtre de 14 jours redevenait
servable, et cette lecture reste un seul `git log` peu coûteux), d'où l'on tire les numéros cités par les
commits de squash. Si le dernier commit connu localement date de plus de 6 h, un `git fetch -q origin
main` (90 s au plus) le rafraîchit **avant** de lire les citations ; s'il échoue, rien ne lève — la lecture
continue sur la pointe locale et la sortie porte la note sur la ligne de lecture. La sortie dit toujours
l'âge du dernier commit connu localement. Un cache de `--cache-s` secondes
(`%LOCALAPPDATA%/CoursIA/tapis_rapide/`, `~/.cache/coursia/tapis_rapide/` hors Windows) évite de relire
quand une lane retire ; `--cache-s 0` le désactive. `--lecture <dossier>` rejoue `issues.json` et
`prs_ouvertes.json` d'un instantané, l'heure de référence étant alors celle de la lecture — sans fetch,
le dépôt n'est pas touché.

La sortie donne, dans l'ordre : l'en-tête (issues, servables, familles, durée, appels, cache, âge de
`origin/main`), **vos PRs ouvertes** (leurs nits d'abord ; une PR verte qui n'attend que la review ne se touche pas), les grains
numérotés avec la commande `python scripts/check_lane_claim.py N --lane <lane>` à jouer **avant d'éditer**
(les grains d'abord, les conteneurs ensuite, voir plus bas), puis le compte des écartées par code, puis — s'il y en a — la
**liste des items éteints** (les deux barrières de fond, `EPAISSE` et `SATURE`) : c'est la sortie que consomme
l'urne de clôture, un item éteint ne revenant plus jamais dans le pool. `--json` rend les mêmes données (`grains`, `vos_prs`, `ecartees`,
`eteints`, `lecture`).

Codes de sortie : `0` grains servis, ou pool réellement vide dit en clair ; `3` lecture incomplète (502/504
répétés à toutes les tailles de page, panne `gh` ou `git`) **et** aucune lecture de secours : rien n'est
servi, et le message dit quoi faire à la place (porter ses PRs, traiter la file du coordinateur, re-tirer).
**Aucune sortie ne renvoie au tapis lourd** `pick_idle_grain.py --belt` (#26926) : il mettait 240 s à servir des
grains non vérifiés, et chaque panne réseau y renvoyait toute la flotte. `4` : main local en retard ou organe
du tirage divergent d'`origin/main` (`git pull --ff-only`, puis re-tirer).

**Lecture de secours** (#26926) : quand la lecture réseau échoue, le tapis tire sur la dernière lecture
**complète** du cache machine (`%LOCALAPPDATA%/CoursIA/tapis_rapide/lecture-<jours>j.json`) si elle a moins
de 12 h ; la sortie est alors `0`, et `lecture.fetch_note` dit la panne et la date de la lecture servie.
Une lecture incomplète n'est jamais mise en cache, donc jamais servie ; un rejeu (`--lecture`) n'a pas de
secours. Le pool d'une lecture de quelques heures reste juste à la marge, puisque `check_lane_claim.py`
fait autorité avant d'éditer. Il n'y a ni mur de
temps ni budget de sondes : le nombre d'appels est fixé par construction. Mesure du 2026-11-13 : 14 appels
(15 depuis la lecture de la pointe `origin/main`, plus un `git fetch` quand elle dépasse 6 h),
lecture réseau de 25 à 101 s selon GitHub, rejeu d'un instantané en ~1 s (l'ancienne voie : 295 à 382 s).

Une **mesure Origami** impossible (voir plus bas) ne rend **pas** le `3` : le parcage Origami est une
protection **auxiliaire**, et le tapis rapide est le tirage de référence de toute la flotte — une protection
en panne ne doit pas l'éteindre. La sortie reste `0`, `measured: false` et la cause restent visibles dans le
`--json` et dans le texte (« Parcage Origami : NON MESURE (…) »), et un avertissement part sur stderr : un
EPIC Origami servi pendant la panne se lit comme tel. Le `3` reste réservé à la lecture groupée incomplète.
Un **rejeu** (`--lecture`) ne refait pas la mesure et n'est jamais invalidé par elle.

## Ce qui écarte un candidat

Chaque issue ouverte reçoit au plus un code ; le premier qui s'applique gagne. Tout se décide sur la lecture
groupée, sans sonde par issue.

| Code | Règle |
| --- | --- |
| `LABEL` | **exclusion posée en données** : un label porté par l'issue. `candidate-delivered` : l'urne de clôture appartient au coordinateur et à l'adjoint. `pause` : une pause posée une fois écarte le grain — plus de regex de titre ni de souvenir d'agent (#28114). La table des labels est dans `coordination/tapis_labels.py` |
| `GEL` | parapluie gelé en dur (`frozen_campaigns.py`) ou l'un de ses descendants ; ligne `[FROZEN]` dans le body ; en-tête `[FROZEN]` du fil non suivi d'un `[UNFROZEN]` de `myia-ai-01:CoursIA` ou `myia-po-2025:CoursIA-2` |
| `EPAISSE` | le **fil** déclare que la part délégable de l'item est épuisée : attestation `[INFO] candidate-delivered` du conteneur, ou dernier marqueur de fin de tour `[RELEASED]` qui le dit (forme de #18258). Le fil est l'autorité : c'est lui qui dit ce qu'il reste à faire dedans. La mesure ne vaut pas pour un `[CLAIMED]` postérieur — une reprise n'annule pas un épuisement |
| `SATURE` | conteneur dont **tous** les enfants déclarés sont fermés : il n'y a plus de grain à prendre dedans (cas #11698). Mesuré en post-passe, sur les seuls conteneurs de la file, et fail-OPEN : une mesure impossible n'écarte rien |
| `LIVREE` | dernier commentaire `[INFO] candidate-delivered`, le mot pouvant suivre `lane X —` sur la ligne du tag (forme de #20603), sauf s'il est nié juste avant (`pas`, `non`, `not`) ; ou, hors conteneur et hors consolidation, `[DELIVERED]` sans clause `paths:` que rien ne rouvre ensuite |
| `MERGEE` | hors conteneur et hors consolidation : un commit de `origin/main` la **ferme** depuis moins de `--jours` jours (mot de fermeture devant `#N`, ou `#N` dans la portée du sujet `type(zone,#N):` ; un `See #N` ou `Part of #N` compte comme une visite, pas comme une livraison), et aucun `[NOT-DELIVERED]`, `[RELEASED]`, `[CLAIMED]`, `[CLAIMED-AMEND]` ou `[CLOSURE REVIEW] verdict: KEEP` postérieur ne la rouvre |
| `COUVERTE` | hors conteneur : une PR ouverte (brouillons compris) cite `#N` ; si la PR porte `lane <votre lane>`, le motif dit « votre PR » |
| `PAUSE` | le **dernier** marqueur du fil est un `[RELEASED]` qui porte une **condition** `attend: #N` (issue ou PR visée) ou `attend: Q<id>` (question user). L'écart ne porte **aucun délai** : il tient jusqu'à la levée de la condition — la cible visée fermée, ou un marqueur postérieur. Un `[RELEASED]` qui porte `attend:` n'est jamais un `RELACHEE` (voir [la pause explicite](#la-pause-explicite--attend-n-27726)) |
| `RELACHEE` | le **dernier** marqueur du fil est un `[RELEASED]` de moins de 3 jours (`RELACHE_J`), quelle que soit la lane, la vôtre comprise. Son motif (barrière mesurée, siège trop petit) vaut encore : sans cet écart, chaque lane re-mesurait la même barrière (mesure po-2023 du 13/11 : 38 cycles sans grain servable, 23 issues concernées). Un `[CLAIMED]` ou un `[NOT-DELIVERED]` postérieur lève l'écart |
| `PLAFOND` | conteneur hors `consolidation` : une visite d'une **autre** lane de moins de 7 jours (`PLAFOND_EPIC_J`, même fenêtre que l'organe `check_lane_claim.py epic_visit_cap`, #22500) — un marqueur `[CLAIMED]`/`[CLAIMED-AMEND]`/`[DELIVERED]` dans son fil ou la création d'une de ses filles ouvertes. Le tapis ne sert pas un EPIC que le gate L898 refuserait ; les visites de **votre** lane n'arment rien (#25443) |
| `RECLAMEE` | claim ouvert d'une autre lane de moins de 48 h ; sur un conteneur, un claim récent d'une autre lane écarte déjà via `PLAFOND` (une remise de main `[OVERRIDE]` bornée `paths:` reste une note) |
| `ORIGAMI` | EPIC Origami dont **tous les plis matérialisés sont terminés** et dont le pli suivant n'est pas annoncé : le dépliage est réservé au coordinateur, aucune lane worker ne peut le lever. Le motif dit quel pli attend. Comme sur le tapis lourd, l'écart est appliqué **après** les autres : un EPIC déjà livré reste `LIVREE` |

Les marqueurs se lisent en tête de **n'importe quelle ligne** d'un commentaire (souvent après `Grain: …`),
décor de citation ou de gras toléré, blocs de code ignorés. Par lane, `[CLAIMED]`/`[CLAIMED-AMEND]` ouvre ;
`[RELEASED]`, `[DELIVERED]`, `[CANCELLED]`, `[ABANDONED]` et `[DONE]` ferment ; `[OVERRIDE]` remet
l'issue à la lane qui le pose. Un claim de **votre** lane n'écarte pas : l'issue passe en tête avec la note
« votre claim ». Quand le fil dépasse les 12 commentaires lus, une note « fil partiel » le dit — et, en
ligne, la [re-décision des fils tronqués](#la-re-décision-des-fils-tronqués-27179) relit le fil complet des
grains servis avant de les servir.

Un **conteneur** (issue nommée comme parent par une autre issue ouverte, label `epic`/`umbrella`, ou titre
`[EPIC` sans parent) se sert : la lane y prend une tranche. C'est pourquoi ni une PR, ni un commit, ni un
`[DELIVERED]` de tranche ne l'écartent.

**Les grains d'abord, les conteneurs ensuite** (#26926). Un conteneur demande une lecture du fil et un choix de
tranche ; il ne passe donc jamais devant un grain (vos claims restent en tête). Il est servi avec :

- la commande `python scripts/check_lane_claim.py N --lane <lane> --paths <vos chemins>` : sans `--paths`,
  l'organe refuse le conteneur entier dès qu'une autre lane y tient un claim borné (mesure du 2026-11-16 :
  six claims bornés sur #19297, et la commande servie sans `--paths` était refusée par construction) ;
- sa **procédure** (lire le fil entier, prendre l'étape suivante non faite hors des chemins occupés,
  vérifier par `--paths`, poser `[CLAIMED] … -- paths: …`) ;
- les **chemins occupés**, en entier, lane par lane (`chemins_occupes` en JSON), et les PRs ouvertes qui le
  citent (`prs_ouvertes`).

## La pause explicite — `attend: #N` (#27726)

Un `[RELEASED]` peut porter une **condition** : une ligne `attend: #N` (issue ou PR visée) ou
`attend: Q<id>` (question user). Le grain est alors écarté par le code `PAUSE`, et le motif nomme la
condition — c'est ce qui rend le tableau du coordinateur lisible sans ouvrir les fils :

```
[RELEASED] lane myia-po-2024:CoursIA-3 -- cadrage demande au mainteneur
attend: Q-c.2344a
```

**Pas de délai.** L'écart `PAUSE` tient jusqu'à la levée de la condition, pas trois jours comme
`RELACHEE` : une attente plus longue revenait au tirage, et la lane suivante re-mesurait la même
attente. Mesure du 21/11 (#27726) : #27553 et #27554, en attente du GO du mainteneur, étaient servis
en grains 1 et 2 du tapis de `myia-ai-01:CoursIA-2`.

**Comment la condition se lève.** Une condition `#N` se mesure sur l'état de la cible : l'issue ou la
PR visée fermée, la pause tombe et le grain redevient servable. Une condition sans numéro
(`attend: Q…`) n'est pas mesurable par la lecture : elle tient jusqu'à un marqueur postérieur
(`[CLAIMED]`, ou un `[RELEASED]` sans condition), qui rend le grain de nouveau servable.

**Ce que la pause ne prétend pas lire.** Toutes les lanes écrivent sous le login partagé `jsboige` :
un commentaire du mainteneur ne se distingue pas d'un commentaire de lane. La forme lit donc un
**état** (la cible fermée) ou un **marqueur**, pas une intention.

**Et `RELACHEE` ne s'y applique pas.** Un `[RELEASED]` qui porte `attend:` n'est jamais une remise
de main à 3 jours : la fenêtre `RELACHE_J` est contournée, sans quoi la pause repasserait par le
tirage au bout de trois jours.

## Les items éteints — l'urne de clôture (#26973)

Deux écarts ne sont pas des écarts : ce sont des **extinctions**. Un `GEL` se résorbe (l'item
revient au tour suivant), un `RECLAMEE` aussi ; mais un item `EPAISSE` (le fil déclare sa part
délégable épuisée) ou `SATURE` (tous les enfants du conteneur sont fermés) **ne revient pas** dans
le pool. Écarté en silence, il restait ouvert pour toujours — c'est ce que le coordinateur a demandé
de voir (décision du 17/11 sur #26989) : « le tapis doit produire une *liste* des items éteints
pour l'urne de clôture, au lieu de les écarter en silence ».

La sortie porte donc une section dédiée :

```text
Items eteints (2) -- urne de cloture (coordinateur, adjoint) : un item eteint ne revient pas dans le pool, il faut le fermer ou lui donner une tranche.
  #18258  EPAISSE  le fil declare la part deleguable epuisee ([RELEASED] ... epuise)
  #11698  SATURE   tous les enfants sont fermes (25 enfant(s) declare(s), aucun ouvert) : plus rien a prendre dedans
```

Chaque ligne porte le numéro, le code et le **motif** de l'extinction : l'urne n'a pas à refaire
la mesure, elle décide (fermer, ou donner une tranche). Les deux mesures sont fail-OPEN — une
panne n'éteint rien, donc une panne ne fait pas disparaître un item de la liste. Le `--json`
expose la même liste sous `eteints`.


## La re-décision des fils tronqués (#27179)

La fenêtre de 12 commentaires peut masquer le marqueur qui écarte : sur le pool du 18/11, 180 issues
ouvertes sur 426 ont un fil tronqué, et le témoin #26534 a été servi 2,1 j après son `[RELEASED]`. En
ligne (ni `--lecture` ni lecture de secours), chaque grain **servi** dont le fil est tronqué est re-décidé
au moment du service sur son fil complet — relu par l'organe déjà présent (`gh_snapshot.fetch_issue_comments`,
REST paginé, pas un second lecteur) et le même `_decider` est rejoué ; si un écart apparaît, le grain sort
et son remplaçant entre, lui-même re-vérifié. La sortie dit la passe (« Fils tronqués re-décidés sur fil
complet : N relu(s) en T s, jetés : CODE #N ») et les grains restés servables portent la note « fil complet
relu (N commentaires) ».

La passe est bornée à 16 appels REST et **fail-OPEN** : un fil illisible laisse le grain servi sur sa
fenêtre (la note « fil partiel » reste, et le verdict est alors celui de la fenêtre), et la borne atteinte
est dite dans la sortie. Mesure du 18/11 : 7 fils relus en 5,5 s, le témoin #26534 éjecté. Le rejeu
(`--lecture`) et la lecture de secours restent sur la fenêtre : hors ligne, la fenêtre est assumée, et
`check_lane_claim.py` reste l'autorité avant d'éditer — cette passe réduit les grains servis à rebuter,
elle ne remplace pas la vérification.

## Le parcage Origami (#26523, parité de #24373)

Le tapis lourd (`pick_idle_grain.py --belt`) parque les EPICs Origami dont le pli suivant n'est pas encore
déplié : c'est le geste du coordinateur, qu'aucune lane worker ne peut lever. Le tapis rapide l'applique
aujourd'hui aussi, faute de quoi un EPIC Origami au long cours revenait à chaque tirage comme un grain
ordinaire.

Ce que la mesure lit, et où :

- **les plis** (sous-issues `Part of #N`, y compris fermées) et **les déclarations de dépliage** du fil de
  l'EPIC : lus par `origami_parking.measure`, dont le résultat est mis en cache **par la machine**
  (`%LOCALAPPDATA%/CoursIA/origami_parking/`, 30 min — la cadence du tapis). Un depliage fait dans la
  demi-heure est vu au cycle suivant ;
- **la livraison d'un pli** — un pli est terminé quand il est fermé *ou* livré par un commit de fusion : la
  sonde est fondée sur les **citations de la lecture groupée** (`gh_bulk`), donc **aucune lecture par issue**.

C'est le seul point de la voie qui sorte de la lecture groupée : deux appels groupés, au plus une fois toutes
les 30 min et par machine. Mesure du 2026-11-14, sur le siège `myia-ai-01:CoursIA-2` : lecture à froid
**39,2 s → 48,2 s** (+9,0 s, la mesure Origami), lecture **chaude** (caches frais) **0,57 s → 0,82 s**. Le
tirage reste du même ordre.

Trois états, jamais mélangés — le bloc `origami_parking` du `--json` les porte :

| État | Ce que ça veut dire |
| --- | --- |
| `measured: true` | la mesure est faite ; les EPICs parqués sont écartés du tirage et listés dans `details` (le tableau du coordinateur les lit sans changement) |
| `measured: false` + `reason` | la mesure est **impossible** ; rien n'est parqué et **la cause est nommée** — jamais une liste vide, qui se lirait « rien à parquer ». La sortie reste `0` : le tirage continue, et un avertissement sur stderr nomme la cause |
| `measured: true`, `epics: 0` | le pool ne porte aucun EPIC Origami : la mesure est faite, et vide |

Le parcage est **fail-OPEN**, comme celui du tapis lourd : une mesure absente ne supprime jamais un grain.
Ce qui change, c'est que la mesure est faite — l'absence de mesure se voit au lieu de passer inaperçue.

Un **rejeu** (`--lecture <dossier>`) est hors ligne par contrat : il ne refait **pas** la mesure Origami et
**ne parque rien**. Un rejeu peut donc servir des EPICs Origami que le tirage en direct avait parqués — c'est
le prix du rejeu, et il est assumé. L'état rendu porte alors `measured: false` avec la cause « rejeu hors
ligne ».

## L'ordre : l'équilibrage des visites

Mandat user du 2026-11-16 : « Toute issue doit être visitée au moins une fois avant qu'une autre le soit
deux fois, à l'exception de quelques issues anciennes de consolidation qui peuvent recevoir plusieurs visites,
et des marathon csharp et Rust qui recevront le fruit du travail du nouveau harnais. Les issues récentes en
particulier ne devraient pas recevoir plus de visites que les anciennes. » Le module
`scripts/coordination/tapis_equilibre.py` porte cet ordre ; il remplace le tirage pondéré des familles.

**Une visite est une séance.** Les marqueurs `[CLAIMED]`, `[CLAIMED-AMEND]` et `[DELIVERED]` d'une même
lane à moins de 24 h d'intervalle (`SEANCE_H`) font une seule visite. Les commits de `origin/main` qui
citent l'issue forment des séances sans lane. Le compte retenu est le plus grand des deux : un claim puis le
merge de sa PR comptent une fois.

**Où vivent les règles.** Les séances de **marqueurs** sont dans
`scripts/coordination/tapis_seance.py` (`par_lane`) ; les séances d'**instants** (les commits cités, sans
lane) sont dans `scripts/coordination/tapis_dernier_grain.py` (`seances`). Un écart d'heures ne dit pas si
un marqueur a fermé une séance : ce sont deux règles, et chacune a son module.

**Une livraison ouvre une séance neuve** (19/11, famine de l'umbrella #27338). Sans cela, une lane qui
enchaîne plusieurs grains du même umbrella le jour même n'y compte qu'**une** visite — et l'issue reste en
tête de classement, servie sept fois dans la journée pendant que des issues anciennes n'attendaient
aucune PR. La séance se ferme sur la livraison (ou la release) ; la suite ouvre une séance neuve. Mesure
sur l'issue réelle : avant correction, 2 visites sur 8 livraisons ; après, 8. La règle est appliquée par
les **deux** chemins : le classement (`tapis_dernier_grain.compter_grains`) et la voie légère
(`tapis_equilibre.compter`) appellent le même `par_lane` — un seul organe, aucune règle réimplémentée.

**Les PRs ouvertes comptent le travail en cours** (19/11, même famine). Le classement léger ne voyait que
les commits **mergés** : une issue sur laquelle huit PRs sont ouvertes — pas encore mergées — restait à
`visites = 0`, donc en tête de rotation. `scripts/coordination/tapis_citations.py` extrait les citations des
PRs ouvertes avec la même règle que les commits mergés (une mention `#N` dans le corps, auto-référence
exclue) ; chacune compte **une** visite, à la date de la dernière activité de la PR : une PR abandonnée
depuis trois mois ne tient pas une issue en tête. C'est le classement **léger** qui est concerné par les
PRs ouvertes ; la voie rapide lit les marqueurs du fil, qui portent la même information (une livraison
ouvre une séance neuve, dans les deux chemins).

**La mesure qui prouve l'inversion** (19/11, même famine). Le témoin d'**ordre** ne discriminait pas le
correctif : à niveau égal, l'ordre de création mettait déjà les anciennes devant. Ce qui change, c'est le
**niveau**. Pool de 14 issues (12 anciennes à zéro visite, une issue à une visite, l'umbrella #27338 à huit
livraisons) :

| | visites de #27338 | niveau de #27338 | niveau de l'issue à 1 visite | rang de #27338 |
| --- | --- | --- | --- | --- |
| avant (les PRs ouvertes ne comptent pas) | 0 | 0 | 0,5 | **devant** elle |
| après | 8 | 8 | 0,5 | **derrière** elle |

Avant correction, une racine servie huit fois passait **devant** une issue qui avait déjà reçu sa visite : le
contre-sens exact du mandat du 16/11 (« toute issue doit être visitée au moins une fois avant qu'une autre le
soit deux fois »). Le témoin `scripts/tests/test_tapis_citations.py` rejoue les deux colonnes : il échoue si la
correction disparaît, et il échoue aussi si l'inversion ne se reproduit plus.

**Le niveau compte les visites du tour, pas celles de toute la vie de l'issue.** Le tour vaut
`FENETRE_J` = 7 jours. Mesure du 16/11 sur la lecture de 13:27Z : environ 47 séances par jour pour 395
issues ouvertes, soit un tour complet de la flotte en 4 à 8 jours. Un compte sur la vie entière aurait l'effet
inverse du mandat : les anciennes issues ont plus de visites parce qu'elles vivent plus longtemps (1,1 en
moyenne avant 7 jours, 3,4 de 7 à 30 jours, 6,2 de 30 à 90 jours). Un niveau strict sur ce compte les
affamerait.

L'ordre des servables :

1. vos claims ;
2. le niveau croissant ;
3. dans un niveau, l'issue jamais visitée d'abord, puis la plus ancienne par date de création. Une issue
   récente reçoit sa première visite, puis attend que les anciennes aient reçu la leur dans le tour ;
4. dans un niveau, les familles servies à tour de rôle (la famille de la plus ancienne issue d'abord), pour
   que huit grains ne viennent pas d'une seule série.

| Constante | Valeur | Rôle |
| --- | --- | --- |
| `FENETRE_J` | 7 | le tour sur lequel se compte le niveau |
| `SEANCE_H` | 24 | deux marqueurs d'une lane plus proches que cela font une visite |
| `BANDS_AGE_J` | (180, 120, 60, 30, 10) j | bonus d'âge : 0,1 visite par tranche franchie, plafonné à 0,5 |
| `BONUS_CONSOLIDATION` | 0,6 visite | priorité de consolidation, à tout âge (label ou racine de famille) — **posée en premier** : elle passe devant l'ancienneté (I7) |
| `BONUS_AGE_MAX_CONSO` | 0,3 visite | part de l'âge qui reste sur une consolidation : l'âge ne mange pas le budget de la consolidation |
| `BONUS_TOTAL_MAX` | 0,9 visite | borne du bonus total : une issue à 0 visite passe devant une issue à 1 visite |
| `MARATHONS` | #26070, #26510 | racines des marathons de parité C# et Rust, hors équilibrage |
| `TETE` | 24 | la tête de chaque niveau est décalée par lane (voie **lourde**) ; en voie légère, c'est la **fenêtre** qui est décalée — voir « La fenêtre qui avance » |
| `PART_CONTENEURS` | 0,25 | part au plus des conteneurs dans la liste (2 sur 8) ; ils la complètent s'il manque des grains |

**Les deux priorités légères du 18/11.** `coordination/tapis_avantages.py` porte deux contributions petites
et distinctes, comptées en dixièmes de visite : le niveau reste ainsi un multiple de 0,1, et les issues se
regroupent par niveau — c'est ce qui fait tourner la tête d'une lane à l'autre. La division par 3 des
consolidations anciennes (`visites // 3`) disparaît : elle était plus forte qu'une priorité légère.
**La consolidation passe devant l'ancienneté** (invariant I7 du contrat du picker, #28114) : les deux bonus
ne s'additionnent plus, ils se composent **par priorité** — la consolidation prend 0,6 visite, l'âge ne garde
que 0,3 visite sur une consolidation (le rapport nomme ce motif « plafonnée »). Avant, l'âge plein l'emportait
et l'invariant était violé dans l'étage rapide.
Les marathons (familles #26070 et #26510, titres commençant par « Marathon ») passent après tout le pool équilibré :
c'est le harnais sk-agent qui les servira. Le rapport JSON dit pour chaque grain son nombre de visites du tour
et au total, et nomme les contributions qui s'appliquent (champ `priorite`).

L'âge est compté en **jours pleins** : une bande franchie à cheval sur une tranche de quatre heures
changerait la liste d'une lane à l'autre, et les tranches ne franchissent pas minuit.

**La tête de chaque niveau est décalée par lane** (`sha256(graine|niveau)`, la graine portant la lane, la
date et la tranche de quatre heures). Deux lanes qui tirent au même moment ne reçoivent donc pas la même
tête. Le décalage porte sur les 24 premiers grains du niveau (`TETE`), jamais sur les conteneurs, dont le
quota se lit dans l'ordre. Une lane qui retire dans la même tranche retrouve sa liste ; `--graine` force la
graine. Les plus récentes d'un niveau restent derrière la tête : le test le vérifie sur trente grains jamais
visités et 300 graines, où les huit grains servis viennent toujours des 24 plus anciens.

**Effet mesuré** sur la même lecture (11 lanes worker, 8 grains chacune, hors claims et marathons) :

| | avant | après |
| --- | --- | --- |
| visites du tour des grains servis (moyenne) | 2,45 | 1,77 |
| grains servis à 4 visites du tour ou plus | 18 | 10 |
| âge médian des grains servis | 49 j | 54 j |
| marathons servis | 4 | 0 |

Les grains restent servis avant les conteneurs (#26926), même quand le conteneur est à un niveau plus bas : un
conteneur demande une lecture et un `--paths`.

**L'équité du 16/11 — une issue jamais visitée ne cède pas sa place** (#27590, dispatch `c0013-tapis-coverage-20`).
Le mandat du 16/11 : « toute issue doit être visitée au moins une fois avant qu'une autre le soit deux fois ».
Mesure du 21/11 sur le pool réel (lecture du 01:47Z, 51 issues servables, 21 à 0 visite) : le tour de 8 grains
servait **deux issues déjà visitées** pendant que 14 issues jamais visitées restaient dehors — le quota de
conteneurs (25 %) écartait les conteneurs jamais visités, et le tri final plaçait les grains d'abord. Deux
corrections :

- dans `tapis_rapide.ordonner`, une issue **déjà visitée** ne prend plus la place d'une issue jamais visitée
  encore au tour ; le conteneur jamais visité que le quota écarte passe en **second temps**, quand la place ne
  peut plus être prise par une issue déjà visitée. Le quota et l'ordre final (les grains d'abord) ne changent pas ;
- dans `visit_coverage`, le **parcage Origami** est appliqué comme dans le tirage : sans lui, l'organe comptait
  en rôle « worker » cinq EPIC Origami que le tapis ne sert jamais (leur dépliage est réservé au coordinateur).

Effet mesuré sur la même lecture : le tour de 8 sert 8 issues **jamais visitées** (avant : 6, dont 2 déjà
visitées), et les 16 issues « worker » à 0 visite sont toutes servies en **2 tours**. L'organe
`visit_coverage.atteignable` mesure cette garantie (`tours`, `equite`) et la porte en **rouge** si une issue
déjà visitée est servie pendant qu'une autre attend ; son test d'invariant est dans
`scripts/tests/test_tapis_couverture_invariant.py` (contrôle positif et contrôle négatif).

Ce que la garantie **ne** corrige pas : le quota de conteneurs reste une part de la liste (les conteneurs
jamais visités occupent la place d'autres grains quand ils remplissent le tour), et une issue écartée par un
code — `ORIGAMI`, `PLAFOND`, `RECLAMEE`, `LIVREE` — reste hors du tapis, par construction. L'organe compte
désormais les issues dont le fil est tronqué et que le tirage re-décidera au service (`redecider_au_service`).

## L'assiette du pool : feuilles contre conteneurs (#25082)

Le triage fait son travail ; ce qui peut le rendre stérile, c'est la **composition** du pool. Au tirage du
21/11 (lecture de 07:54Z, lane `myia-ai-01:CoursIA-2`), 40 issues étaient servables sur 475 : **36
conteneurs et 4 feuilles**. Le « conteneur » du tapis est plus large que le label `EPIC` — c'est aussi
l'umbrella et l'issue qui a des filles ouvertes — d'où l'écart avec le compte en label (28 EPIC sur 29
servables, mesuré par le coordinateur sur sa propre lane).

Un conteneur ne se sert pas comme une feuille : il demande la lecture du fil entier, une tranche bornée par
`paths:` et une PR. Servi sans subdivision, il ne produit rien. `scripts/coordination/tapis_assiette.py`
mesure cette composition aux deux niveaux :

- **le pool** (`--draw <tirage.json>`) : feuilles et conteneurs du pool, et surtout **où les feuilles se
  perdent** — le code d'écart qui en retient le plus ;
- **le service** (`--stat`) : ce que le service effectif a réellement servi, tirage par tirage, sur le même
  magasin que l'acceptance de #25082 (`coordination/tirage_journal`).

Le tirage porte désormais la mesure : `lecture.servables_feuilles` et `lecture.servables_conteneurs`, et
chaque entrée d'`ecartees` dit si l'issue écartée est une feuille (`"feuille": true|false`). Un tirage
antérieur à cette mesure ne porte pas le flag : ses entrées sont comptées à part, jamais assimilées à des
feuilles.

Mesure du 21/11 (lecture de 07:54Z) : 356 feuilles et 119 conteneurs lus, dont **4 feuilles servables**,
soit 1,1 % des feuilles. Les feuilles retenues par code d'écart : `COUVERTE` 97, `MERGEE` 95, `LIVREE` 61,
`LABEL` 47, `RECLAMEE` 25, `RELACHEE` 14, `HORSFLOTTE` 9, `GEL` 4 ; sur cette lecture `PLAFOND` n'écarte
que des conteneurs (62) et aucune feuille. Cette lecture est double : `COUVERTE` et `MERGEE` ne sont pas
des défunts — ce sont les issues dont la PR citée attend la revue ou la clôture, rôles déjà attribués par
`visit_coverage.py` ; le tapis n'a pas à les reprendre.

L'organe ne fixe **aucun seuil** : la mesure est un fait, la politique d'assiette appartient au
coordinateur. Ce qu'il donne, c'est le levier — déplier un conteneur (tranche avec `paths:`, PR, résidus en
issues filles d'une ligne) rend des feuilles au pool.

```bash
python scripts/coordination/tapis_assiette.py --draw <tirage.json> [--json]
python scripts/coordination/tapis_assiette.py --stat [--journal <chemin>] [--json]
```

## Ce qui n'est pas repris de l'ancienne voie (délibéré)

- Le **bandit de fermeture par zone** : la variété vient du tour de rôle par famille dans un niveau et du décalage par lane.
- Les **plafonds par EPIC côté tirage pondéré** : le tour de rôle borne déjà la part d'une famille à un grain par tour. Le plafond hebdomadaire #22500 lui **est** repris, sous la forme de l'écart `PLAFOND` ci-dessus, pour ne pas servir ce que le gate de claim refuse ; il ne pèse que les conteneurs, jamais les filles existantes (#26414).
- La **file de réparation** : une réparation due passe par une issue ordinaire, servie comme les autres.

## La rotation universelle — la voie légère (#27223)

Le tirage ci-dessus classe le pool entier, mais il applique **neuf règles d'écart avant la rotation** et lit
le **corps, les commentaires et les PRs** de chaque issue ouverte. Pour classer 440 issues afin d'en servir
quelques-unes, ce sont deux lectures qui ne servent à rien.

`coordination/tapis_universel.py` fait la rotation **sur les métadonnées seules** :

| | lecture lourde (tirage actuel) | lecture de sélection (#27223) |
| --- | --- | --- |
| charge utile | corps + 12 commentaires + PRs | numéro, titre, dates, labels |
| mesure sur 440 issues | **23,4 s**, 5,7 Mo | **6,7 s à froid**, 7,8 s à chaud, 107 ko |
| pagination | complète | complète, avec un **budget global** de durée (60 s) posé comme une **échéance monotone commune** (pages et rejeu la partagent, temps restant recalculé avant chaque appel) : au-delà, `LectureIncomplete` — jamais de liste partielle |
| exclusions | neuf, avant la rotation | **aucune** : les vérifications (claim, gel, contenu livré) se font **à la prise en charge** |
| visites | marqueurs du fil + commits | **commits seulement** : le travail réellement effectué — une apparition dans une liste n'est pas une visite |

Chaque grain servi porte son **état et l'action à faire** (`qualifier` : lire l'issue, vérifier le claim
vivant, le gel, le contenu déjà livré), jamais une exclusion silencieuse. La bascule du tirage par défaut
est la tranche suivante (#27225) : elle suppose que la prise en charge qualifie le grain, ce qui est un
changement de protocole autant que de code.

## La bascule — le tirage par défaut est léger (#27225)

Depuis #27225, `tapis_rapide.py` tire par défaut sur la **voie légère** : le classement porte sur les
**métadonnées seules**, et la qualification du grain est **déplacée à la prise en charge**. La voie
lourde reste accessible (`--voie lourd`) et le rejeu `--lecture` y reste — c'est la seule voie qui sait
relire un dossier de lecture.

```bash
python scripts/coordination/tapis_rapide.py --lane <machine:workspace> [--voie {leger,lourd}]
```

| | voie lourde (`--voie lourd`) | voie légère (défaut) |
| --- | --- | --- |
| classement | lecture du pool entier (corps + 12 commentaires + PRs) | **métadonnées seules** (`gh_selection`), pagination complète, budget global de 60 s |
| qualification | intégrée au classement | **à la prise en charge** : `scripts/coordination/tapis_prise_en_charge.py --issue N` |
| règles d'écart | neuf, appliquées au classement | **les mêmes neuf**, rejouées sur le grain qualifié (`tapis_rapide.etats` inchangé) |
| re-décision de fil (#27179) | passe au moment du service | **déplacée avec la qualification** : le fil complet est relu au moment de l'action |
| parcage Origami | mesure sur le pool | mesure sur les **grains qualifiés** |

**Mesures (pool de 441 issues, 18/11, même machine, même lane).**

| Chemin | Lecture | Durée | Ce qu'il rend |
| --- | --- | --- | --- |
| lourd | corps + 12 commentaires de tout le pool (5,2 Mo) | 33,5 s | 11 grains, exclusions appliquées |
| **léger (défaut)** | **métadonnées seules** (8,6 s à chaud, 15,4 s à froid) + citations (1,6 s) + PRs (4,7 s) | **17,9 s** | une file de `3 × grains`, exclusions à décider à l'action |
| qualification (prise en charge) | le corps + le fil complet du grain pris | **1 à 2 appels par grain** | son verdict : servable, ou son code et son motif |

**Pourquoi la qualification a quitté le tirage.** Les neuf écarts ne sont pas décidables sur des
métadonnées : un gel, une livraison, un claim se lisent dans le corps ou dans le fil. Les décider pour
**tout** le pool coûtait 22 s de lecture — plus cher que le chemin lourd lui-même (21,9 s pour 441
issues). La première version de la bascule le faisait au tirage, par vagues de 12 candidats : mesure du
2026-11-18, **48 candidats qualifiés, 47 écartés, 1 grain servi, 50 appels, 59 s** — une régression
face aux 33,5 s du chemin lourd, sur le même besoin. Décider au moment de l'action coûte 1 à 2 appels par
grain **effectivement pris**, et le tirage redevient le plus rapide des deux.

**Le fil complet, jamais la fenêtre.** C'est la condition de la bascule : la lecture groupée ne voit que
les **12 derniers** commentaires (`comments(last:12)`), et le marqueur qui écarte un grain peut être plus
vieux que la fenêtre — constat de #27179, qui a produit l'organe `tapis_reverif`. La qualification lit
donc **tous** les commentaires par l'organe REST déjà livré (`gh_snapshot`, pagination REST), jamais la
fenêtre — et **seulement** pour les candidats que la fenêtre retient : un candidat dont la fenêtre *est*
le fil complet (moins de 12 commentaires) n'appelle aucun appel supplémentaire. Elle dit, pour chaque
grain, ce que la fenêtre a décidé : « fenêtre = fil complet (N commentaires) » ou « fenêtre de M
commentaires sur N : aucun marqueur décisif hors fenêtre » (la relecture elle-même est déjà notée par
l'organe de re-vérification : « fil complet relu (N commentaires) »).

**La qualification est fail-CLOSED.** Une décision qui n'a pas pu être prise **refuse** le grain, avec son
code et son motif — `FIL_ILLISIBLE` (fil illisible), `MUR_EPUISE` (mur de lectures REST atteint),
`ECHEANCE` (échéance de qualification dépassée). Un grain dont la décision n'a pas été prise n'est pas
servi : le temps d'action engage un grain dont le fil a été lu. Le rapport distingue ces refus des
écarts de règle (`ecartees`) et les publie (`refus`).

> La passe de rebut du chemin **lourd** (`tapis_reverif`) reste, elle, fail-OPEN : elle réduit les grains
> servis à rebuter et ne remplace pas la vérification — `check_lane_claim.py` reste l'autorité avant
> d'éditer. C'est la **qualification**, qui est le temps d'action, qui est fail-CLOSED.

**Deux latences, jamais confondues.** La **latence du classement** est celle du tirage (`lecture.secondes`
de son rapport, 17,9 s sur le pool de 441). Le **temps jusqu'au premier grain servable** est celui de
l'action : `chrono.premier_servable_s` du rapport de `tapis_prise_en_charge.py`. Le rapport de qualification
porte les deux, séparément.

**Aucune exclusion n'est silencieuse.** Chaque écart porte son **code** et son **motif**, et il est
affiché : `RELACHEE` (rendue par X il y a N j — **une fenêtre de 3 jours**, pas une disqualification :
l'issue redevient servable après), `PLAFOND`, `LIVREE`, `COUVERTE`, `RECLAMEE`, `MERGEE`, `GEL`,
`HORSFLOTTE`, `LABEL`, `ORIGAMI`. Au tirage, l'**état** affiché est celui du classement (visites,
consolidation, conteneur) et l'**action** est explicite : `qualifier #N avant action (corps + fil
complet, scripts/coordination/tapis_prise_en_charge.py) puis la servir`.

**Un conteneur ne passe jamais devant un grain** (#26926) : la détection se fait sur les métadonnées
(titre `[EPIC]`, labels `epic`/`umbrella`), donc elle ne peut pas attendre la lecture du corps.

**Chaque classe a un créneau de lecture** (arbitrage du 19/11) : dans le **lot public de la rotation**
(`tapis_public.lot_public`, la voie `tapis_leger`), les deux classes sont entrelacées — le conteneur
tient un créneau à lui, un tour sur deux. Ce qu'il ne peut pas faire, c'est **déplacer un grain** : son
quota de créneaux (25 % du lot) est inchangé, et la part des grains n'en dépend pas. La règle #26926
est donc **étroitié** dans le lot de *lecture*, pas abandonnée : l'**ordre de service** de la sortie du
tapis (les grains d'abord) reste inchangé.

**La tête du lot est le numéro suivant le curseur** (famine du 19/11) : la priorité d'entrée gardait la
même tête à chaque tranche — le plus prioritaire du bloc — et le curseur sautait alors par blocs
entiers ; les grains du milieu du bloc n'étaient plus jamais servis (mesure du peer : **4 numéros lus
sur 80** en 400 tours). Le curseur n'avance en outre que sur les numéros **lus** (le lot
propriétaire) : un numéro proposé mais non qualifié reste *en attente*, et la tranche suivante le sert
en tête. Les deux témoins de la famine sont rejoués sur le lot public dans
`scripts/tests/test_tapis_public.py`.

**Le grain non tenté ne fige plus le curseur** (mesure du 19/11, peer `ai-01:CoursIA`) : un curseur
qui s'arrête au premier numéro **non décidé** re-propose la même tranche au cycle suivant — quatre
cycles de suite — et **les numéros suivants ne sont jamais proposés** : la couverture du pool s'arrête.
Témoin mesuré : pool 1..6, taille 2, ancre 2 ; la tranche [3, 4] est proposée, seul 4 est qualifié,
3 n'a pas été tenté ; **5 et 6 ne sont jamais servies**.

Trois états se distinguent désormais pour un numéro proposé par le tirage :

- **décidé** (confirmé, ou écarté par une règle de contenu) : le curseur passe, le numéro est acquitté ;
- **pris en charge mais non décidé** (lecture impossible, budget épuisé) : le numéro est **parqué** sous
  son code, et le curseur passe ;
- **proposé, non pris en charge** : rien n'a été décidé sur lui ; il reste en attente jusqu'à ce que le
  curseur le **saute** — et il est alors parqué sous le code `NON_TENTE`
  (`scripts/coordination/tapis_non_tente.py`), qui le distingue des deux cas précédents.

Le curseur n'avance que sur les numéros que le lot a **réellement pris en charge**
(`scripts/coordination/tapis_avance.py`) : une qualification nominative d'un numéro qui n'appartient pas
à la tranche ne déplace plus l'ancre des primaires pendantes — le curseur annonçait alors une couverture
que personne n'avait mesurée (revue du 19/11, point b). Un numéro **sauté** est parqué au moment où le
curseur passe par-dessus lui, faute de quoi il serait perdu pour la rotation ; et la **reprise** ne porte
pas le curseur : une primaire étrangère déjà parquée ne fait pas avancer une tranche que le lot ne touche
pas.

**Le mur global** (`--budget-s`, 30 s par défaut — `gh_selection.MUR_GLOBAL_S`) couvre la lecture de
sélection ; son dépassement lève `LectureIncomplete` et l'appelant le dit (code de sortie 3) — jamais une
liste à moitié. La qualification a son propre mur : dépassée, elle rend ce qu'elle a et le dit
(`budget_epuise`).

**L'échéance de commande** (invariant I6 de #28114). Le point d'entrée `tapis_rapide.main` pose **une
seule** échéance, partagée par tous les étages : la garde de fraîcheur, la sélection, la qualification, le
cap de livraisons et le repli. Aucun étage ne s'attribue un budget neuf : chacun reçoit le **temps
restant**, et une lecture qui ignore son timeout est **abandonnée** au passage de l'échéance. La borne
de la commande est le **contrat** lui-même : `tapis_borne.BUDGET_S` = **55 s**, strictement sous les 60 s
d'I6 (marge 5 s). Les parts des étages — 30 s pour le tirage (`gh_selection.MUR_GLOBAL_S`) et 30 s pour
la garde de fraîcheur (`tapis_borne.FRAICHEUR_S`, mesuré sur ce dépôt le 26/11 : `git fetch origin main`
20,4 s + `git rev-list` ×2 2,2 s + `git diff --name-only origin/main` des organes 1,1 s, soit 23,7 s) —
sont **volontairement supérieures à cette enveloppe** : elles ne s'additionnent pas, elles se **partagent**
(chaque étage prend `min(échéance, maintenant + sa part)`). La commande ne peut donc pas dépasser
l'enveloppe : elle est **coupée**, pas attendue. Le pire cas est assumé ainsi : l'étage **dégradable**
(la garde de fraîcheur) encaisse la coupe, l'étage **décisionnel** (la sélection) garde son budget dans
le cas normal — 23,7 s mesurées laissent 31,3 s pour un tirage qui en demande 30. Deux conséquences en
découlent : une fraîcheur **coupée** par la borne est une **dégradation**
(`FRAICHEUR_BORNEE` : le tirage rend sa file avec l'avertissement), pas un refus — seule une mesure
impossible reste un refus ; et un **repli** lancé après l'échéance ne sert **rien** (fail-CLOSED), il
rendrait la main hors contrat. Les primitives vivent dans `scripts/coordination/tapis_borne.py`, sans
réseau.

**La borne est vérifiée, pas seulement énoncée.** Les témoins sont dans
`scripts/tests/test_tapis_borne_entree.py` : la borne du CLI par défaut est **strictement** sous les 60 s
du contrat (mesure à l'instant, pas une constante citée) ; et le **pire cas** — chaque étage consomme
toute sa part — est tenu à l'**horloge réelle** : le runner git dort tout le timeout qu'il reçoit, la
sélection dort de même, et la commande rend un verdict **dans** l'enveloppe qu'on lui donne (l'échéance
y est mise à l'échelle : ce qui est prouvé est la forme, la borne réelle est celle du contrat).

**Les organes du chemin de tirage sont dans la garde de fraîcheur.** `main_freshness.ORGANES` porte
désormais le chemin complet du tirage (sélection, lecture ciblée, snapshot, rotation, fenêtre, avantages,
qualification légère, re-vérif, parcage) : sous `ORGANE_DIVERGENT` — un module qui diffère d'`origin/main` — le tirage **dégrade** (invariant I4 : sortie `0` et avertissement `TIRAGE DEGRADE` sur stderr) au lieu de refuser ; la sortie `4` ne reste que pour la **mesure impossible**. Le code exécuté n'est alors **pas** identique à `origin/main` : l'avertissement le dit. Un nouveau module du tirage entre dans cette liste **avec** sa première livraison.

**Cette prescription est vérifiée, plus seulement énoncée.** La liste est contrôlée par
`scripts/tests/test_main_freshness_organes.py`, sur deux sources : la **fermeture d'import statique** des
points d'entrée du tirage (`tapis_rapide`, `tapis_leger`, `tapis_voie_leger`, `tapis_prise_en_charge`,
`pick_idle_grain` — analysée par `ast`, jamais importée : `main_freshness` est lui-même dans la liste,
l'import serait circulaire) et le **tableau « Les modules »** ci-dessous. Un module livré hors liste
n'est donc pas un trou silencieux : la PR qui le livre porte **son propre rouge**, et le rouge se lève en
déclarant le module — dans la PR, pas plus tard. Mesure du 24/11 : la liste ne portait qu'une **partie**
du chemin du tirage ; l'écart était invisible, la garde refusait donc des tirages pour une raison que
personne ne pouvait nommer, et laissait passer des modules du chemin qui ne l'étaient pas.

### Les modules

| Module | Rôle |
| --- | --- |
| `scripts/coordination/tapis_leger.py` | la voie légère : rotation universelle sur les métadonnées, file de grains avec état et action |
| `scripts/coordination/tapis_leger_rapport.py` | le **rapport** du tirage léger : l'état de chaque grain et l'action à faire — extrait de `tapis_leger.py` |
| `scripts/coordination/tapis_leger_texte_occupation.py` | la section **occupation** de la sortie texte du tirage léger — extraite de `tapis_leger_texte.py` |
| `scripts/coordination/tapis_occupation.py` | l'**occupation** d'un grain : l'urne de clôture (`candidate-delivered`) et la PR qui le tient — les deux marques, une seule décision, sur métadonnées seules (#28090) |
| `scripts/coordination/tapis_public.py` | le **lot public** : la proposition comprise (la tranche, les ancres) — la voie que les tests rejouent |
| `scripts/coordination/tapis_avance.py` | l'**avance** du curseur, bornée au lot : les trois états (décidé / parqué / sauté) |
| `scripts/coordination/tapis_non_tente.py` | le grain **non tenté** : proposé, jamais qualifié — son code propre, et il ne fige pas le curseur |
| `scripts/coordination/tapis_tete.py` | la **tête** du lot : le numéro suivant le curseur, ahead de la priorité (famine du 19/11) |
| `scripts/coordination/tapis_repli.py` | le **repli chronologique** : hors réseau **ou quand les filtres vident la file**, le cache local fait foi et le pool est servi par date de création (#28114) ; le cap y est **inerte** (`mesure: false`) |
| `scripts/coordination/tapis_fenetre.py` | la **fenêtre** : le bloc servi qui avance sur le pool classé, et la fenêtre du fil (12 derniers commentaires) |
| `scripts/coordination/tapis_prise_en_charge.py` | le CLI de la **prise en charge** : qualifier un grain avant d'agir (le corps, le fil complet, les neuf règles) |
| `scripts/coordination/tapis_qualification.py` | la qualification elle-même : le corps, la fenêtre, la re-décision des neuf règles |
| `scripts/coordination/tapis_qualification_fil.py` | la qualification **côté consommateur** : le fil complet déjà lu, rejoué sans appel réseau (`tapis_rapide.etats`) — extrait de `check_lane_claim.py` (#27242) |
| `scripts/coordination/tapis_reprise_livree.py` | la **reprise** d'un grain dont la livraison n'est pas prouvée : les règles sont rejouées avec `LIVREE` muet, puis l'occupation s'applique — un marqueur non prouvé ne rend pas le grain plus servable que son absence (#28114) |
| `scripts/coordination/tapis_fil_complet.py` | le **fil complet** des seuls candidats retenus : lever le doute de la fenêtre (`gh_snapshot`, REST paginé) |
| `scripts/coordination/gh_issues.py` | la lecture **ciblée** des issues nommées, aux champs demandés — une porte pour tous les lecteurs ciblés (`gh_selection.qualifier`) |
| `scripts/coordination/gh_selection.py` | le classement sur métadonnées (pagination complète, budget global) |
| `scripts/coordination/tapis_universel.py` | la rotation universelle sur les métadonnées |
| `scripts/coordination/gh_snapshot.py` | le **fil complet** (REST paginé) — l'organe de la qualification |
| `scripts/coordination/tapis_labels.py` | les **exclusions en données** : la table des labels qui écartent un grain (`candidate-delivered`, `pause`) — #28114 |

### Ce qui déclenche le repli, et ce que le cap y devient

Le repli chronologique prend la main dans **deux** cas : la lecture de sélection échoue (réseau
indisponible, quota épuisé) **et** la lecture réussit mais que les **filtres vident la file** — tous les
grains écartés alors que le pool en porte. Sans cette seconde bascule, une lane dont le cap de
livraisons est saturé ne recevrait plus rien : l'invariant I1 (« une file sans fin ») serait rompu par
les filtres eux-mêmes.

**Le cap est inerte dans le repli.** Le cap de livraisons lit GitHub (les PRs mergées de la fenêtre de
7 jours). Lui donner un fetteur capable de lire le réseau le ferait **échouer de nouveau en pleine
panne** : le repli passe donc un fetteur **inerte** (`tapis_cap_livraisons.fetcher_hors_reseau`), la
mesure est impossible et le rapport porte le témoin `mesure: false`. C'est le fail-OPEN du module : on ne
refuse jamais un item sur une charge qu'on n'a pas su lire.

## La fenêtre qui avance sur le pool (#27225, suite du 18/11)

Le classement classe le pool entier ; ce qu'il rend, c'est un **ordre**. La voie légère servait jusqu'ici
la **tête** de cet ordre — et la tête est restée figée : mesure du 18/11 sur le pool réel de la lane
(441 issues, 18 069 citations de merge, 114 issues jamais visitées), **12 tours consécutifs ne
couvraient que 38 issues**, la tête était toujours la même, et les 114 issues jamais visitées n'étaient
jamais proposées. La liste `3 × grains` écrasait le reste du pool.

La correction n'est pas dans le classement mais dans ce qui en est **servi** : la **fenêtre**. `coordination/
tapis_fenetre.py` sert un **bloc contigu** du pool classé, qui avance d'un bloc par tranche de 4 h, décalé
par lane (le décalage qui faisait tourner la tête est désormais appliqué à la fenêtre, pas au pool : sinon
la fenêtre ne peut pas être un bloc contigu — `tapis_equilibre.ordre(..., rotation=False)`).

**Mesure du 18/11, pool réel de 440 issues (transport REST : le bucket GraphQL était en limite
secondaire à l'heure de la mesure), 21 tranches de 4 h :**

| | avant (tête figée) | après (fenêtre qui avance) |
| --- | --- | --- |
| issues couvertes sur **12 tours** (48 h) | **38** | **262** |
| issues jamais visitées atteintes sur 12 tours | 0 | **104 / 113** |
| issues couvertes sur 21 tours (84 h) | ~38 | **380 / 440** |
| la tête bouge-t-elle ? | non | oui |
| balayage complet du pool | jamais | **17 tranches (68 h)** |

Le test `test_la_fenetre_avance_sur_le_pool` vérifie hors ligne la propriété que la mesure confirme : les
blocs d'un tour sont **disjoints** (toute issue est proposée une fois avant qu'une autre le soit deux
fois) et couvrent le pool entier. Sur le pool réel, les blocs sont *presque* disjoints : les bandes d'âge
(`BANDS_AGE_J`) franchies entre deux tranches font glisser le classement, et le balayage complet prend
17 tranches au lieu de 18.

**Les issues reportées reviennent.** Une issue rendue par une autre lane (`RELACHEE`) est servable après sa
fenêtre de 3 jours ; le balayage la ramène dans la file en 17 tranches (68 h), soit **après** l'expiration de
la fenêtre : une issue reportée redevient servable *et* revient dans la file au tour suivant de son tour de
pool. Le motif du `[RELEASED]` est lu par la qualification, qui l'affiche.

## L'ordre par AGE : les anciennes d'abord (mandat du 22/11)

Mandat du mainteneur (22/11) : « le tapis devrait pouvoir piocher les issues anciennes prioritairement sur les
plus récentes, même si celles qui n'ont jamais été visitées peuvent être traitées parmi la tête du tapis. Si ça
ne fonctionne pas, alors on mettra les nouvelles issues en fin de tapis. »

**L'inversion était structurelle, pas un effet de tri.** Le bloc servi se choisissait dans l'**espace des
numéros** : la tranche ne retenait que les numéros **au-dessus** de l'ancre persistante, si bien que le service
portait toujours les numéros **récents** — les issues anciennes attendaient un tour complet du pool. Le bonus
d'âge (`tapis_avantages.BANDS_AGE_J`) n'ordonnait que l'**intérieur** du bloc : il n'ouvrait jamais la porte
d'une issue ancienne.

**Mesure du 22/11 sur le pool réel** (459 grains, lecture de 09:02Z, 21,5 s), dans l'état d'une lane qui a
déjà tourné (ancre simulée à mi-pool — le cas réel d'une lane active) :

| 60 premiers grains servis | avant (rotation par numéro) | après (ordre d'âge) |
| --- | --- | --- |
| antérieurs au 01/11 | **0** | **60** |
| du 01/11 au 14/11 | 0 | 0 |
| du 15/11 au 18/11 | 32 | 0 |
| postérieurs au 19/11 | 28 | 0 |
| **de moins de 72 h** | **27** | **0** |
| jamais visitées | 60 | 60 |

Les parts de référence **du pool** : 24,2 % d'issues antérieures au 01/11 (111 sur 459 grains), 73,6 % de
grains jamais visités (338), 179 issues de moins de 72 h. Les deux critères du mandat sont tenus : **100 %**
d'issues antérieures au 01/11 dans les 60 premiers (contre 24,2 % dans le pool), et **aucune** issue de moins
de 72 h. Dans l'état réel de la lane (`myia-ai-01:CoursIA-2`, ancre à 10) les deux ordres coïncident : le
numéro et l'âge y désignent les mêmes issues — l'écart n'apparaît que lorsque l'ancre a avancé, ce qui est le
cas de toute lane qui tourne.

**La clé porte la DATE DE CRÉATION, pas la dernière visite.** La dernière visite change à chaque tour : une
visite en ouvre une autre, et un ordre construit sur une clé qui bouge ne se ferme pas — c'est l'échec mesuré
le 19/11 (380 issues sur 440 atteintes en un tour, sans jamais fermer le tour). La date de création est
**immuable** : elle dit depuis quand l'issue attend. La clé, dans l'ordre :

| Composante | Rôle |
| --- | --- |
| bande de fraîcheur | une issue de moins de `SEUIL_FRAICHES_H` = **72 h** va en **queue** (« on mettra les nouvelles issues en fin de tapis ») — **sauf** si elle est une consolidation |
| consolidation | la consolidation passe devant la non-consolidation de même bande (revue ai-01 du 22/11) |
| jamais visitée | l'équité du 16/11 : une issue jamais visitée passe devant une issue déjà servie |
| date de création | les anciennes d'abord |
| numéro | le désempilement, stable et reproductible |

**La consolidation est dans la clé, pas à côté** (revue ai-01 du 22/11). Le mandat du cycle veut « un picker
rapide couvrant toutes les issues avec priorité consolidation et ancienneté » : l'ancienne voie donnait aux
consolidations 0,6 visite à tout âge (0,4 avant le 23/11), et cet avantage a disparu avec la sélection par âge — les
consolidations n'avaient plus aucun avantage dans la clé. Deux règles, celle de `tapis_avantages.est_consolidation`
(le **label** `consolidation`, ou la **famille** dont la racine l'est) :

- la consolidation passe **devant** la non-consolidation de même bande ;
- elle **échappe à la bande des moins de 72 h** : une consolidation ouverte aujourd'hui doit pouvoir passer en
  tête, sans attendre que la bande Fresh se vide.

Mesure sur le **pool réel** (531 issues lues, 452 grains, 27 racines labellisées `consolidation`, 15
consolidations dans le pool — 14 par label, 1 par famille), 60 premiers servis, ancre simulée à mi-pool :

| 60 premiers grains servis | avant (clé d'âge seule) | après (clé avec consolidation) |
| --- | --- | --- |
| **consolidations servies** | **3** | **15** |
| dont par label | 3 | 14 |
| dont par famille héritée | 0 | 1 |
| part des consolidations du pool | 3,3 % (15 sur 452) | 3,3 % (15 sur 452) |
| de moins de 72 h | 0 | 1 (la consolidation #27733) |
| jamais visitées | 60 | 50 |

Les 60 premiers servis passent de **3** à **15** consolidations : **tout le pool de consolidation** (15 sur 15)
est servi dans la première vague, contre 20 % avant. L'unique issue de moins de 72 h servie est la
consolidation #27733 — l'échappement voulu, qui ne s'applique qu'à une consolidation.

**Le tri est une ADMISSION, pas un rang.** La sélection ne porte plus sur une fenêtre de numéros mais sur
l'ensemble du pool classé par âge : les grains servis sont les premiers de l'ordre d'âge, les plus anciens
d'abord. La rotation par numéro ne subsiste que pour les **conteneurs**, peu nombreux, dont le quota (25 %)
est appliqué dans l'ordre du nombre — un conteneur ne passe jamais devant un grain (#26926).

**Ce qui est servi attend son verdict.** Les grains servis dont le verdict n'est pas encore connu sont
**exclus** de la sélection suivante (`tapis_age.tour` lit la file `attente` de l'ancre) : sans cela, le même
grain serait resservi à chaque tour. La file survit au passage du curseur — `tapis_ancre.avancer` ne retire
plus une entrée en attente de verdict ; c'est elle qui fait l'exclusion. Un numéro **décidé** sort de la file
et redevient servable plus tard.

**Le rebouclage par numéro est désactivé pour les grains** (`proposer(..., reboucle=False)`) : la rotation par
numéro se sert des numéros au-dessus de l'ancre, un rebouclage réinitialiserait donc la file d'attente à chaque
tirage — et les grains servis par âge (dont les numéros sont *sous* l'ancre) cesseraient d'être exclus. Quand
plus rien n'est servable (toutes les issues attendent leur verdict), la file est **rendue** et le tour
recommence : les issues anciennes reviennent, elles ne disparaissent pas.

**Les tests.** `scripts/tests/test_tapis_age.py` (15 tests) rejoue sur un pool **synthétique** : la bande
fraîche part en dernier, la jamais visitée passe devant, les plus anciennes d'abord, la clé ne dépend que de
la date de création, la sélection sert les anciennes (pas les numéros au-dessus de l'ancre), les déjà servis
sont laissés de côté, la vague suivante prend le bloc suivant, les numéros sans verdict quittent la file — et
la consolidation passe devant, échappe à la bande fraîche, et s'hérite de sa famille.
`scripts/tests/test_tapis_vagues.py` (3 tests) suit la même sélection pour les vagues.

Le module : `scripts/coordination/tapis_age.py` — clé, tri, bandes, sélection, tour. Il lit `cree_le`,
`visites_total`, `consolidation` et `famille` des états, n'écrit rien et ne lit pas le réseau.

## La qualification, côté consommateur (#27225, suite du 18/11)

La qualification n'est pas seulement une étape que la lane *peut* faire : elle est **incontournable avant
tout claim ou toute édition**. Le protocole impose `python scripts/check_lane_claim.py N` avant d'éditer
un fichier pour un grain rattaché à une issue ; cette commande applique maintenant la **qualification**, par
le **même organe** que le tirage (`tapis_rapide.etats`), sur le **fil complet** que la lecture a déjà rendu
— sans appel réseau supplémentaire. Un grain écarté par la qualification n'est ni claimed ni édité : la
commande rend `1` et nomme le code et le motif (`[QUALIFICATION] RELACHEE : rendue par X il y a 0,4 j
(< 3 j) : lire son motif`).

Sont rejouées les règles **décidables sur l'issue seule** : `HORSFLOTTE`, `LABEL`, `GEL`, `RELACHEE`.
Les règles qui dépendent du **pool** (`MERGEE`, `COUVERTE`, `PLAFOND`) restent au tirage et à la
qualification (`tapis_prise_en_charge.py`, qui lit les citations de merge et les PRs ouvertes) ; `RECLAMEE`
et `LIVREE` sont déjà décidées par la grammaire du claim, en plus fin (override, scopes disjoints, état de
la PR qui porte le `[DELIVERED]` — 14 tests de cette grammaire s'appuient sur ce comportement, mesuré le
18/11 : les ajouter à la porte consumer en cassait 14).

Le cas que la voie légère ne peut plus voir est précisément `RELACHEE` : elle classe sur métadonnées
seules, elle ne voit donc plus les marqueurs du fil. La porte consumer les rejoue sur le fil complet.

## Couverture des visites (#27590)

L'équilibrage ci-dessus n'ordonne que les issues **servables** (30 sur 459 ouvertes à la mesure du 20/11) :
une issue écartée par un code dépend d'un autre rôle — l'urne de clôture, la revue d'une PR, le mainteneur —
et rien ne mesurait si ce rôle la visitait. `coordination/visit_coverage.py` attribue à chaque issue ouverte
le rôle responsable de son prochain pas, sur la même lecture groupée (aucun appel réseau de plus) :

| Rôle | Code d'écart | Prochain pas |
| --- | --- | --- |
| `harnais` | marathon (`tapis_equilibre.est_marathon`), écart ou non | harnais sk-agent ; tous les marathons sortent des agrégats |
| `worker` | servable, `RECLAMEE` | le tapis, pour la lane qui la sert |
| `urne` | `LIVREE`, `MERGEE`, `LABEL` (`candidate-delivered`) | clôture par le coordinateur, l'adjoint ou le secrétaire |
| `revue` | `COUVERTE` | revue et fusion de la PR citée (son numéro est lu dans le motif) |
| `mainteneur` | `GEL` | décision du mainteneur |
| `attente` | `RELACHEE`, `PLAFOND`, `ORIGAMI`, `LABEL` (`pause`) | attente bornée, puis le tapis |
| `hors-flotte` | `HORSFLOTTE` | hors flotte |
| `autre` | tout code non mappé | le motif est rapporté |

Une issue **avance** dans la fenêtre du tour (7 jours) par un marqueur `[DELIVERED]` daté, ou par un commit
de `origin/main` qui la cite (`lecture.citations`). Le bilan donne par rôle le nombre d'issues, celles à zéro
visite et celles visitées sans avancer, l'invariant du 16/11 sur le pool servable (hors claim propre et hors
marathon) et les jamais visitées. Mesure du 20/11 sur la lecture de 13:35Z : 443 issues hors marathons, 87 à
zéro visite, dont 59 d'urne et 12 de revue.

Le bilan porte en outre deux mesures neuves (21/11) :

- `redecider_au_service` — les issues « worker » à 0 visite dont le **fil est tronqué** (la lecture groupée ne
  voit que les 12 derniers commentaires) : le tirage les re-décide sur le fil complet au moment du service, donc
  l'écart peut changer après le bilan ;
- `atteignable` — la simulation du tapis (`tapis_rapide.ordonner`) sur la même lecture : combien de tours pour
  servir toutes les issues jamais visitées, et **équité** — la liste des issues déjà visitées qui seraient
  servies pendant qu'une autre attend. Une équité non vide est un **rouge** (code de sortie 1).

### Visite et prise en charge : deux ensembles distincts (#27590)

Le secrétariat et l'adjoint rendent compte d'une **lecture** par une ligne `[INFO] Visite …` ou
`[INFO] … candidate-delivered`. Ces formes sont des **visites**, mais elles ne sont pas des **prises en
charge** : personne n'a travaille sur l'issue, quelqu'un l'a regardée. Deux ensembles distincts expriment
cette différence (`scripts/coordination/tapis_marqueurs.py`) :

| Ensemble | Marques | Ce qu'il dit |
| --- | --- | --- |
| `MARQUEUR_GRAIN` | `CLAIMED`, `CLAIMED-AMEND`, `DELIVERED` | une lane a pris l'issue en charge |
| `VISITE` | `MARQUEUR_GRAIN` + `VISITE-INFO` | l'issue a été visitée (prise en charge **ou** lecture) |

Les consommateurs ne lisent pas le même ensemble, et c'est délibéré :

| Consommateur | Ensemble | Effet |
| --- | --- | --- |
| `tapis_dernier_grain._marqueurs_grain` (état de grain) | `MARQUEUR_GRAIN` | une lecture **ne** fait pas une prise en charge : elle ne rajeunit pas le dernier grain (une qualification est une lecture) |
| `tapis_dernier_grain.compter_grains` (compteur de visites) | `VISITE` | une lecture **est** une visite : l'issue n'est plus au niveau zéro de l'équilibrage |
| `tapis_rapide._plafond` (plafond #22500) | `VISITE` | un conteneur regardé récemment par une autre lane est un conteneur chaud : il est écarté pendant la fenêtre du plafond |

Deux formes ont été écartées au passage : une ligne qui répond aux deux motifs (`[INFO] Visite … candidate-delivered`)
ne compte qu'**une** fois — la déduplication se fait par ligne, pas par fragment capturé — et une visite
**annulée** (`[INFO] Visite annulée`) n'est pas une visite.

Un grain est aussi un claim : la boucle d'équité de `visit_coverage.atteignable` exclut les claims de la lane,
comme le pool qu'elle mesure. Sans cette exclusion, une lane qui tient un claim voit l'organe rendre `rc 1`
sur le fonctionnement normal du tirage, et les vraies violations disparaissent derrière le bruit.

### Le tri « grains d'abord » et la garantie mesurée (#27690, fusionné le 21/11)

Le tri final ne doit pas servir une issue **déjà visitée** pendant qu'une issue **jamais visitée**
attend encore : c'est le mandat du 16/11 (« toute issue doit être visitée au moins une fois avant qu'une
autre le soit deux fois »). La mesure du 21/11 sur le pool réel (lecture de 01:47Z, 51 issues servables
dont 21 à zéro visite) montrait que le tour de 8 grains servait **deux issues déjà visitées pendant que
14 issues jamais visitées restaient dehors** : le quota de conteneurs écartait les conteneurs jamais
visités, et le tri final plaçait les grains d'abord. Deux corrections, dans le même PR :

- `tapis_rapide.ordonner` : une issue déjà visitée ne prend plus la place d'une issue jamais visitée
  encore au tour ; le conteneur jamais visité que le quota écarte passe en second temps. **Le quota et
  l'ordre final (les grains d'abord) ne changent pas** ;
- `visit_coverage` : le **parcage Origami** est appliqué comme dans le tirage — sans lui, l'organe
  comptait en rôle « worker » cinq EPIC Origami que le tapis ne sert jamais.

Effet mesuré sur la même lecture : le tour de 8 sert **8 issues jamais visitées** (avant : 6, dont 2
déjà visitées) et les 16 issues « worker » à zéro visite sont servies en **2 tours**.

Trois règles rendent la mesure `atteignable` capable de porter cette garantie — et chacune neutralise
un faux rouge, pas un vrai :

- les **états sont copiés** avant la simulation : la mesure ne modifie pas l'état qu'elle mesure ;
- les **claims de la lane** sont exclus du contrôle d'équité — une lane sert d'abord ses propres claims,
  et une issue qu'elle tient n'est pas une issue que le tapis « republie » ; sans cette exclusion,
  l'organe rendrait `rc=1` sur le fonctionnement normal du tirage (le coordinateur tient des claims) et
  masquerait les vraies violations ;
- la simulation est **bornée à 50 tours** : au-delà, les issues restantes sont rendues telles quelles
  (`restantes`), pas comme un verdict.

L'invariant a son test (`scripts/tests/test_tapis_couverture_invariant.py`, contrôle positif **et**
contrôle négatif).

```bash
python scripts/coordination/visit_coverage.py [--json] [--dashboard-line]
       [--lecture <dossier>] [--cache-s 3600] [--jours 45] [--lane myia-ai-01:CoursIA]
```

Codes de sortie : `0` tout est couvert ; `1` invariant violé, ou une issue d'urne ou de revue sans visite
dans le tour alors qu'elle a plus de `FENETRE_J` jours ; `2` lecture incomplète sans secours (jamais un faux
`0`). `--dashboard-line` rend une ligne de 200 caractères au plus, à poster sur le dashboard du secrétariat.

**Listes complètes en JSON, bornées à l'affichage texte (#27725).** La borne `LIMITE_LISTE` (20) ne borne plus
que le texte : en `--json`, chaque liste de numéros est **complète**. Mesure du 21/11 sur la lecture de 10:12Z
(475 issues hors marathon) : avant, les listes s'arrêtaient à 20 numéros — 20 numéros d'urne à 0 visite pour
**66** issues, 20 numéros « worker » pour **29**, 20 « jamais visitées » pour **47**, 20 urgences pour **73** ; les
**comptes**, eux, étaient justes. Une troncature invisible donnait à lire une liste plus courte que la
population réelle, et le secrétaire re-vérifiait à la main ce que l'organe devait rendre. Dans le texte, la
troncature se dit désormais : `... et 9 autres`. Un test de propriété (25 numéros dans un rôle) verrouille le
couple : le JSON rend 25, le texte en montre 20 et annonce les 5 autres.

**Ce que la mesure ne voit pas** : une fermeture (la lecture ne contient que les issues ouvertes), une PR
fusionnée sans commit cité (le squash cite sa PR, pas forcément l'issue), un `[DELIVERED]` plus ancien que
les 12 derniers commentaires lus (fil tronqué), et `[INFO] candidate-delivered`, reconnu comme livraison par
le tapis mais pas retenu comme preuve d'avancée. Le test de propriété (`scripts/tests/test_visit_coverage.py`)
simule 30 servables et 120 pas de service : la tête de `tapis_equilibre.ordre` garde le niveau minimal du
pool, donc aucune issue n'atteint deux visites tant qu'une autre est à zéro.

## Réviser ce document

Ce fichier est un document `REFERENCE — vivante` : son en-tête (`dernière révision <date>`) n'est pas une
mention décorative. `scripts/check_docs_reference_lane.py` le compare — **en mode PR** — à la date du
dernier commit **ordinaire** qui touche `docs/` :

```
git log <base>..HEAD --no-merges --name-only -- docs/
```

Trois points mesurés le 21/11 sur ce fichier (PR #27242), qui valent pour tout document `REFERENCE` :

- **une fusion ne compte pas.** Résoudre un conflit dans une fusion modifie réellement le document, son
  en-tête compris ; mais `--no-merges` exclut la fusion de la lecture. Le garde continue donc de lire la
  date du dernier commit ordinaire et signale `STALE_DATE` sur un document dont l'en-tête est à jour ;
- **remettre l'en-tête à la date d'hier ne résout rien** : le commit qui porte la correction est daté
  d'aujourd'hui, c'est donc l'en-tête d'aujourd'hui qui doit être écrit ;
- **le remède est un commit ordinaire qui revise réellement le document.** L'organe ne juge que la date :
  une retouche cosmétique le fait passer sans rien prouver sur le fond — la révision de contenu reste
  une obligation de la lane, pas de l'organe.

Le défaut d'organe qui rend ce détour obligatoire (une fusion conflictuelle sur `docs/` est invisible au
garde) est suivi à part : #27861.


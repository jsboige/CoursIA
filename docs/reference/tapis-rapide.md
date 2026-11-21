# Tapis rapide — la voie légère du tirage des grains

> REFERENCE — vivante — dernière révision 2026-11-20

Issue : [#22983](https://github.com/jsboige/CoursIA/issues/22983). Code : `scripts/coordination/tapis_rapide.py`
(fonctions pures et CLI), `scripts/coordination/tapis_marqueurs.py` (lecture des marqueurs de fil, extraite
le 2026-11-14 pour tenir le plafond de lignes), `scripts/coordination/tapis_service.py` (la forme du service :
commande, procédure de conteneur, lecture de secours, sortie texte), `scripts/coordination/tapis_origami.py`
(parcage Origami, #26523), `scripts/coordination/tapis_reverif.py` (re-décision des fils tronqués, #27179),
`scripts/coordination/tapis_seance.py` (les séances de marqueurs : une livraison en ouvre une neuve,
#27338), `scripts/coordination/tapis_citations.py` (les citations des PRs ouvertes : le travail en cours
compte comme une visite, #27338), `scripts/coordination/belt_equite.py` (l'équité du dispatch : un grain
déjà servi ne passe pas devant les premières visites, #27338)
et `scripts/coordination/gh_bulk.py` (seul module qui lance `gh` ou `git`).
Elle **remplace** `scripts/pick_idle_grain.py --belt` pour le tirage : depuis #26926, aucune sortie du tapis rapide ni de `check_lane_claim.py` ne renvoie plus au tapis lourd (240 s, grains non vérifiés), qui reste un outil de diagnostic.

## La commande

```bash
python scripts/coordination/tapis_rapide.py --lane <machine:workspace> [--grains 8] [--json]
       [--jours 45] [--cache-s 300] [--graine S] [--lecture <dossier>]
```

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
(les grains d'abord, les conteneurs ensuite, voir plus bas), puis le compte des écartées par code. `--json` rend les mêmes données (`grains`, `vos_prs`, `ecartees`,
`lecture`).

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
| `LABEL` | label `candidate-delivered` : l'urne de clôture appartient au coordinateur et à l'adjoint |
| `GEL` | parapluie gelé en dur (`frozen_campaigns.py`) ou l'un de ses descendants ; ligne `[FROZEN]` dans le body ; en-tête `[FROZEN]` du fil non suivi d'un `[UNFROZEN]` de `myia-ai-01:CoursIA` ou `myia-po-2025:CoursIA-2` |
| `LIVREE` | dernier commentaire `[INFO] candidate-delivered`, le mot pouvant suivre `lane X —` sur la ligne du tag (forme de #20603), sauf s'il est nié juste avant (`pas`, `non`, `not`) ; ou, hors conteneur et hors consolidation, `[DELIVERED]` sans clause `paths:` que rien ne rouvre ensuite |
| `MERGEE` | hors conteneur et hors consolidation : un commit de `origin/main` la **ferme** depuis moins de `--jours` jours (mot de fermeture devant `#N`, ou `#N` dans la portée du sujet `type(zone,#N):` ; un `See #N` ou `Part of #N` compte comme une visite, pas comme une livraison), et aucun `[NOT-DELIVERED]`, `[RELEASED]`, `[CLAIMED]`, `[CLAIMED-AMEND]` ou `[CLOSURE REVIEW] verdict: KEEP` postérieur ne la rouvre |
| `COUVERTE` | hors conteneur : une PR ouverte (brouillons compris) cite `#N` ; si la PR porte `lane <votre lane>`, le motif dit « votre PR » |
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
| `BONUS_CONSOLIDATION` | 0,4 visite | priorité de consolidation, à tout âge (label ou racine de famille) |
| `BONUS_TOTAL_MAX` | 0,9 visite | borne du bonus total : une issue à 0 visite passe devant une issue à 1 visite |
| `MARATHONS` | #26070, #26510 | racines des marathons de parité C# et Rust, hors équilibrage |
| `TETE` | 24 | la tête de chaque niveau est décalée par lane |
| `PART_CONTENEURS` | 0,25 | part au plus des conteneurs dans la liste (2 sur 8) ; ils la complètent s'il manque des grains |

**Les deux priorités légères du 18/11.** `coordination/tapis_avantages.py` porte deux contributions petites
et distinctes, comptées en dixièmes de visite : le niveau reste ainsi un multiple de 0,1, et les issues se
regroupent par niveau — c'est ce qui fait tourner la tête d'une lane à l'autre. La division par 3 des
consolidations anciennes (`visites // 3`) disparaît : elle était plus forte qu'une priorité légère. Les
marathons (familles #26070 et #26510, titres commençant par « Marathon ») passent après tout le pool équilibré :
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
reste la tranche suivante : elle suppose que la prise en charge qualifie le grain, ce qui est un changement
de protocole autant que de code.

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
| `attente` | `RELACHEE`, `PLAFOND`, `ORIGAMI` | attente bornée, puis le tapis |
| `hors-flotte` | `HORSFLOTTE` | hors flotte |
| `autre` | tout code non mappé | le motif est rapporté |

Une issue **avance** dans la fenêtre du tour (7 jours) par un marqueur `[DELIVERED]` daté, ou par un commit
de `origin/main` qui la cite (`lecture.citations`). Le bilan donne par rôle le nombre d'issues, celles à zéro
visite et celles visitées sans avancer, l'invariant du 16/11 sur le pool servable (hors claim propre et hors
marathon) et les jamais visitées. Mesure du 20/11 sur la lecture de 13:35Z : 443 issues hors marathons, 87 à
zéro visite, dont 59 d'urne et 12 de revue.

```bash
python scripts/coordination/visit_coverage.py [--json] [--dashboard-line]
       [--lecture <dossier>] [--cache-s 3600] [--jours 45] [--lane myia-ai-01:CoursIA]
```

Codes de sortie : `0` tout est couvert ; `1` invariant violé, ou une issue d'urne ou de revue sans visite
dans le tour alors qu'elle a plus de `FENETRE_J` jours ; `2` lecture incomplète sans secours (jamais un faux
`0`). `--dashboard-line` rend une ligne de 200 caractères au plus, à poster sur le dashboard du secrétariat.

**Ce que la mesure ne voit pas** : une fermeture (la lecture ne contient que les issues ouvertes), une PR
fusionnée sans commit cité (le squash cite sa PR, pas forcément l'issue), un `[DELIVERED]` plus ancien que
les 12 derniers commentaires lus (fil tronqué), et `[INFO] candidate-delivered`, reconnu comme livraison par
le tapis mais pas retenu comme preuve d'avancée. Le test de propriété (`scripts/tests/test_visit_coverage.py`)
simule 30 servables et 120 pas de service : la tête de `tapis_equilibre.ordre` garde le niveau minimal du
pool, donc aucune issue n'atteint deux visites tant qu'une autre est à zéro.

# Tapis rapide — la voie légère du tirage des grains

> REFERENCE — vivante — dernière révision 2026-11-18

Issue : [#22983](https://github.com/jsboige/CoursIA/issues/22983). Code : `scripts/coordination/tapis_rapide.py`
(fonctions pures et CLI), `scripts/coordination/tapis_marqueurs.py` (lecture des marqueurs de fil, extraite
le 2026-11-14 pour tenir le plafond de lignes), `scripts/coordination/tapis_service.py` (la forme du service :
commande, procédure de conteneur, lecture de secours, sortie texte), `scripts/coordination/tapis_origami.py`
(parcage Origami, #26523), `scripts/coordination/tapis_reverif.py` (re-décision des fils tronqués, #27179),
`scripts/coordination/tapis_leger.py` (la voie légère du tirage, #27225), `scripts/coordination/tapis_fenetre.py`
(la fenêtre du pool classé et celle du fil, #27225), `scripts/coordination/gh_issues.py`
(la lecture ciblée des issues nommées, #27225) et `scripts/coordination/gh_bulk.py` (seul module qui lance
`gh` ou `git`).
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
| `TETE` | 24 | la tête de chaque niveau est décalée par lane (voie **lourde**) ; en voie légère, c'est la **fenêtre** qui est décalée — voir « La fenêtre qui avance » |
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

**Le mur global** (`--budget-s`, 60 s par défaut) couvre la lecture de sélection ; son dépassement lève
`LectureIncomplete` et l'appelant le dit (code de sortie 3) — jamais une liste à moitié. La qualification
a son propre mur : dépassée, elle rend ce qu'elle a et le dit (`budget_epuise`).

**Les organes du chemin de tirage sont dans la garde de fraîcheur.** `main_freshness.ORGANES` porte
désormais le chemin complet du tirage (sélection, lecture ciblée, snapshot, rotation, fenêtre, avantages,
qualification légère, re-vérif, parcage) : un tirage refuse (sortie `4`) si l'un d'eux diffère
d'`origin/main`. Un nouveau module du tirage entre dans cette liste **avec** sa première livraison.

### Les modules

| Module | Rôle |
| --- | --- |
| `scripts/coordination/tapis_leger.py` | la voie légère : rotation universelle sur les métadonnées, file de grains avec état et action |
| `scripts/coordination/tapis_public.py` | le **lot public** : la proposition comprise (la tranche, les ancres) — la voie que les tests rejouent |
| `scripts/coordination/tapis_tete.py` | la **tête** du lot : le numéro suivant le curseur, ahead de la priorité (famine du 19/11) |
| `scripts/coordination/tapis_fenetre.py` | la **fenêtre** : le bloc servi qui avance sur le pool classé, et la fenêtre du fil (12 derniers commentaires) |
| `scripts/coordination/tapis_prise_en_charge.py` | le CLI de la **prise en charge** : qualifier un grain avant d'agir (le corps, le fil complet, les neuf règles) |
| `scripts/coordination/tapis_qualification.py` | la qualification elle-même : le corps, la fenêtre, la re-décision des neuf règles |
| `scripts/coordination/tapis_qualification_fil.py` | la qualification **côté consommateur** : le fil complet déjà lu, rejoué sans appel réseau (`tapis_rapide.etats`) — extrait de `check_lane_claim.py` (#27242) |
| `scripts/coordination/tapis_fil_complet.py` | le **fil complet** des seuls candidats retenus : lever le doute de la fenêtre (`gh_snapshot`, REST paginé) |
| `scripts/coordination/gh_issues.py` | la lecture **ciblée** des issues nommées, aux champs demandés — une porte pour tous les lecteurs ciblés (`gh_selection.qualifier`) |
| `scripts/coordination/gh_selection.py` | le classement sur métadonnées (pagination complète, budget global) |
| `scripts/coordination/tapis_universel.py` | la rotation universelle sur les métadonnées |
| `scripts/coordination/gh_snapshot.py` | le **fil complet** (REST paginé) — l'organe de la qualification |

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



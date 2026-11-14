# Tapis rapide — la voie légère du tirage des grains

> REFERENCE — vivante — dernière révision 2026-11-14

Issue : [#22983](https://github.com/jsboige/CoursIA/issues/22983). Code : `scripts/coordination/tapis_rapide.py`
(fonctions pures et CLI), `scripts/coordination/tapis_marqueurs.py` (lecture des marqueurs de fil, extraite
le 2026-11-14 pour tenir le plafond de lignes), `scripts/coordination/tapis_origami.py` (parcage Origami,
#26523) et `scripts/coordination/gh_bulk.py` (seul module qui lance `gh` ou `git`).
Elle vit **à côté** de `scripts/pick_idle_grain.py --belt`, qui reste la voie de repli.

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
`origin/main`), **vos PRs ouvertes** (à porter au merge d'abord quand elles ont plus de 24 h), les grains
numérotés avec la commande `python scripts/check_lane_claim.py N --lane <lane>` à jouer **avant d'éditer**,
puis le compte des écartées par code. `--json` rend les mêmes données (`grains`, `vos_prs`, `ecartees`,
`lecture`).

Codes de sortie : `0` grains servis, ou pool réellement vide dit en clair ; `3` lecture incomplète (502/504
répétés à toutes les tailles de page, panne `gh` ou `git`) : rien n'est servi, le message nomme la lecture en
panne et la commande de repli `python scripts/pick_idle_grain.py --belt --lane <lane>`. Il n'y a ni mur de
temps ni budget de sondes : le nombre d'appels est fixé par construction. Mesure du 2026-11-13 : 14 appels
(15 depuis la lecture de la pointe `origin/main`, plus un `git fetch` quand elle dépasse 6 h),
lecture réseau de 25 à 101 s selon GitHub, rejeu d'un instantané en ~1 s (l'ancienne voie : 295 à 382 s).

Le `3` couvre aussi la **mesure Origami** impossible (voir plus bas) : c'est une lecture incomplète au même
titre que la lecture groupée. Un **rejeu** (`--lecture`) ne la refait pas et n'est jamais invalidé par elle.

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
« votre claim ». Quand le fil dépasse les 12 commentaires lus, une note « fil partiel » le dit.

Un **conteneur** (issue nommée comme parent par une autre issue ouverte, label `epic`/`umbrella`, ou titre
`[EPIC` sans parent) se sert : la lane y prend une tranche. C'est pourquoi ni une PR, ni un commit, ni un
`[DELIVERED]` de tranche ne l'écartent.

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
| `measured: false` + `reason` | la mesure est **impossible** ; rien n'est parqué et **la cause est nommée** — jamais une liste vide, qui se lirait « rien à parquer ». En direct, c'est une lecture incomplète : sortie `3`, rien n'est servi |
| `measured: true`, `epics: 0` | le pool ne porte aucun EPIC Origami : la mesure est faite, et vide |

Le parcage est **fail-OPEN**, comme celui du tapis lourd : une mesure absente ne supprime jamais un grain.
Ce qui change, c'est que la mesure est faite — l'absence de mesure se voit au lieu de passer inaperçue.

## L'ordre et les poids

Les issues servables sont groupées par **famille** (la racine, en remontant `Part of #N` ou un titre
`[EPIC … #N]`, `[#N …`, `kind(zone,#N):`, sur cinq niveaux au plus). On sert les familles **à tour de rôle** :
huit grains viennent de huit familles dès qu'il y en a huit.

L'ordre des familles est un tirage pondéré sans remise (clé `u ** (1 / poids)`), semé par
`"<lane>|<date UTC>|<heure // 4>"` : deux lanes ne reçoivent pas la même liste, une lane qui retire dans la
même tranche de quatre heures retrouve la sienne. `--graine` force la graine.

| Constante | Valeur | Quand |
| --- | --- | --- |
| `PRIO_CONSOLIDATION` | 1,5 | une issue servable de la famille, ou sa racine, porte le label `consolidation` |
| `PRIO_VIEIL_EPIC` | 1,5 | la racine est un conteneur ouvert depuis plus de `AGE_VIEIL_EPIC_J` = 60 jours |
| `PART_CONTENEURS` | 0,25 | part au plus des conteneurs dans la liste (2 sur 8) ; ils la complètent s'il manque des grains |

Les deux se cumulent (2,25). C'est une **légère** priorité : aucune famille n'est privée de service. Dans
une famille : votre claim, puis les jamais visitées (la plus ancienne d'abord), puis la visite la plus ancienne
(marqueurs de claim ou de livraison, commits qui la citent) ; à égalité, le grain avant son conteneur.

## Ce qui n'est pas repris de l'ancienne voie (délibéré)

- Le **bandit de fermeture par zone** : la variété vient du tour de rôle par famille et du tirage semé par lane.
- Les **plafonds par EPIC côté tirage pondéré** : le tour de rôle borne déjà la part d'une famille à un grain par tour. Le plafond hebdomadaire #22500 lui **est** repris, sous la forme de l'écart `PLAFOND` ci-dessus, pour ne pas servir ce que le gate de claim refuse ; il ne pèse que les conteneurs, jamais les filles existantes (#26414).
- La **file de réparation** : une réparation due passe par une issue ordinaire, servie comme les autres.

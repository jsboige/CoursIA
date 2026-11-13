# Tapis rapide — la voie légère du tirage des grains

> REFERENCE — vivante — dernière révision 2026-11-13

Issue : [#22983](https://github.com/jsboige/CoursIA/issues/22983). Code : `scripts/coordination/tapis_rapide.py`
(fonctions pures et CLI) et `scripts/coordination/gh_bulk.py` (seul module qui lance `gh` ou `git`).
Elle vit **à côté** de `scripts/pick_idle_grain.py --belt`, qui reste la voie de repli.

## La commande

```bash
python scripts/coordination/tapis_rapide.py --lane <machine:workspace> [--grains 8] [--json]
       [--jours 14] [--cache-s 300] [--graine S] [--lecture <dossier>]
```

Trois lectures groupées, quel que soit le nombre de candidats : les issues ouvertes (GraphQL, pages de 50,
12 derniers commentaires par issue), les PRs ouvertes (REST, pages de 100) et **un** `git log origin/main`
local sur `--jours` jours, d'où l'on tire les numéros cités par les commits de squash. Pas de `git fetch` :
la sortie dit l'âge du dernier commit connu localement. Un cache de `--cache-s` secondes
(`%LOCALAPPDATA%/CoursIA/tapis_rapide/`, `~/.cache/coursia/tapis_rapide/` hors Windows) évite de relire
quand une lane retire ; `--cache-s 0` le désactive. `--lecture <dossier>` rejoue `issues.json` et
`prs_ouvertes.json` d'un instantané, l'heure de référence étant alors celle de la lecture.

La sortie donne, dans l'ordre : l'en-tête (issues, servables, familles, durée, appels, cache, âge de
`origin/main`), **vos PRs ouvertes** (à porter au merge d'abord quand elles ont plus de 24 h), les grains
numérotés avec la commande `python scripts/check_lane_claim.py N --lane <lane>` à jouer **avant d'éditer**,
puis le compte des écartées par code. `--json` rend les mêmes données (`grains`, `vos_prs`, `ecartees`,
`lecture`).

Codes de sortie : `0` grains servis, ou pool réellement vide dit en clair ; `3` lecture incomplète (502/504
répétés à toutes les tailles de page, panne `gh` ou `git`) : rien n'est servi, le message nomme la lecture en
panne et la commande de repli `python scripts/pick_idle_grain.py --belt --lane <lane>`. Il n'y a ni mur de
temps ni budget de sondes : le nombre d'appels est fixé par construction. Mesure du 2026-11-13 : 14 appels,
lecture réseau de 25 à 101 s selon GitHub, rejeu d'un instantané en ~1 s (l'ancienne voie : 295 à 382 s).

## Ce qui écarte un candidat

Chaque issue ouverte reçoit au plus un code ; le premier qui s'applique gagne. Tout se décide sur la lecture
groupée, sans sonde par issue.

| Code | Règle |
| --- | --- |
| `LABEL` | label `candidate-delivered` : l'urne de clôture appartient au coordinateur et à l'adjoint |
| `GEL` | parapluie gelé en dur (`frozen_campaigns.py`) ou l'un de ses descendants ; ligne `[FROZEN]` dans le body ; en-tête `[FROZEN]` du fil non suivi d'un `[UNFROZEN]` de `myia-ai-01:CoursIA` ou `myia-po-2025:CoursIA-2` |
| `LIVREE` | dernier commentaire `[INFO] candidate-delivered` ; ou, hors conteneur et hors consolidation, `[DELIVERED]` sans clause `paths:` que rien ne rouvre ensuite |
| `MERGEE` | hors conteneur et hors consolidation : un commit de `origin/main` la **ferme** depuis moins de `--jours` jours (mot de fermeture devant `#N`, ou `#N` dans la portée du sujet `type(zone,#N):` ; un `See #N` ou `Part of #N` compte comme une visite, pas comme une livraison), et aucun `[NOT-DELIVERED]`, `[RELEASED]`, `[CLAIMED]`, `[CLAIMED-AMEND]` ou `[CLOSURE REVIEW] verdict: KEEP` postérieur ne la rouvre |
| `COUVERTE` | hors conteneur : une PR ouverte (brouillons compris) cite `#N` ; si la PR porte `lane <votre lane>`, le motif dit « votre PR » |
| `RECLAMEE` | claim ouvert d'une autre lane de moins de 48 h ; sur un conteneur, seul un claim sans `paths:` écarte, un claim borné devient une note |

Les marqueurs se lisent en tête de **n'importe quelle ligne** d'un commentaire (souvent après `Grain: …`),
décor de citation ou de gras toléré, blocs de code ignorés. Par lane, `[CLAIMED]`/`[CLAIMED-AMEND]` ouvre ;
`[RELEASED]`, `[DELIVERED]`, `[CANCELLED]`, `[ABANDONED]` et `[DONE]` ferment ; `[OVERRIDE]` remet
l'issue à la lane qui le pose. Un claim de **votre** lane n'écarte pas : l'issue passe en tête avec la note
« votre claim ». Quand le fil dépasse les 12 commentaires lus, une note « fil partiel » le dit.

Un **conteneur** (issue nommée comme parent par une autre issue ouverte, label `epic`/`umbrella`, ou titre
`[EPIC` sans parent) se sert : la lane y prend une tranche. C'est pourquoi ni une PR, ni un commit, ni un
`[DELIVERED]` de tranche ne l'écartent.

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
- Les **plafonds par EPIC** : le tour de rôle borne déjà la part d'une famille à un grain par tour.
- Le **parcage Origami** : une campagne à mettre de côté se gèle par `[FROZEN]`, que la voie lit.
- La **file de réparation** : une réparation due passe par une issue ordinaire, servie comme les autres.

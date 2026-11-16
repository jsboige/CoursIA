# Correction de composition du deck `06-apprentissage` — point 3 de #24171

Ce dossier porte le **relevé de composition après correction** du deck
`06-apprentissage` (124 diapositives), mesuré le 2026-11-11 sur `myia-po-2027`
(Windows 11, canvas 980 × 552).

Il complète le dossier voisin [`docs/captures/24171/`](https://github.com/jsboige/CoursIA/pull/25752), qui
porte l'instrumentation : c'est là que sont la méthode d'export, les deux
contraintes mesurées de `slidev export`, et la première lecture opposable du
deck 06. Ici : **ce que la correction a changé**, mesuré.

## Ce qui a été corrigé

Sept diapositives sortaient du canvas 980 × 552 au scanner de composition
(`scripts/notebook_tools/scan_slidev_composition.py`) :

| Diapositive | Titre | Débordement avant | Marge après |
|---|---|---|---|
| 40 | Réseaux feed-forward multi-couches | 263 px | 37 px |
| 102 | Renforcement passif | 417 px | 80 px |
| 103 | Apprentissage des différences temporelles | 162 px | 61 px |
| 105 | Q-learning = Apprentissage d'utilité action | 176 px | 110 px |
| 106 | Généralisation et approximations | 70 px | 109 px |
| 110 | Deep Q learning — exploration et avancées | 251 px | 46 px |
| 112 | Minimisation de regret hypothétique | 262 px | 52 px |

*« Débordement avant »* : hauteur du conteneur de diapositive moins la hauteur
du canvas (relevé archivé dans [`docs/captures/24171/`](https://github.com/jsboige/CoursIA/pull/25752)).
*« Marge après »* : `canvas_h - content_bottom` dans le relevé ci-dessous, soit
le dégagement du bas du contenu sous le canvas.

**Après correction : `n_hors_canvas = 0` sur les 124 diapositives.**

Les trois causes, et leur traitement :

1. **le budget fixe de 300 px des grilles d'images** — le thème impose
   `.img-grid:not(.absolute) { height: 300px }`, alors que les figures
   n'occupaient qu'une rangée de 118 px (ou deux de 96 px) : le conteneur
   gardait 180 px de vide sous les figures. Traitement : `height: auto` dans
   un bloc `<style scoped>` (précédent #22258, deck 02) ;
2. **les figures empilées en pleine largeur** — traitement : remise en grille,
   hauteur bornée (la figure la plus haute du deck 06, `img_103`, faisait
   336 px de haut) ;
3. **les listes à interligne plein** — traitement : compression typographique
   locale (0.72 em à 0.80 em), comme le font déjà les corrections du lot L3
   sur d'autres diapositives du même deck.

Aucune figure, aucune puce, aucun titre, aucune référence de carnet n'a été
retiré : le contrôle de conservation donne **140 images, 1 136 puces, 123
titres de niveau 1 et 20 références de carnet avant et après**.

## La marge, et pourquoi elle vaut mieux que l'égalité au canvas

Une correction qui vise l'égalité au canvas (contenu qui s'arrête exactement à
552 px) n'est **pas opposable** : sur une autre machine, les métriques de
police diffèrent de quelques pour cent, et la diapositive rebascule dehors.
C'est le cœur de [#24171](https://github.com/jsboige/CoursIA/issues/24171).

La cible retenue est donc un **dégagement** sous le canvas. Après correction,
les sept diapositives ont une marge de 37 px à 110 px.

Il reste **douze diapositives dont la marge est inférieure à 40 px** — donc
susceptibles de basculer sur une autre machine :

| Diapositive | Marge | Déjà compressée ? |
|---|---|---|
| 43 — Apprentissage profond | 8 px | oui (`ul` 0.74 em, grille 130 px) |
| 111 — (diapositive de figures) | 10 px | — |
| 49 — Réseaux récurrents, portes et variantes | 11 px | oui (`ul` 0.8 em, grille 150 px) |
| 44 — Réseaux Convolués LeNet | 25 px | oui (`ul` 0.72 em, grille 100 px) |
| 31 — Du taux d'erreur à la perte | 26 px | — |
| 66 — Apprentissage des SVM | 26 px | — |
| 59 — K-Nearest Neighbor | 28 px | — |
| 53 — Graphs Neural Networks (GNNs) | 29 px | oui (`ul` 0.56 em, grille 200 px) |
| 11 — Arbres de décision | 35 px | — |
| 41 — Apprentissage par rétropropagation | 35 px | — |
| 40 — Réseaux feed-forward multi-couches | 37 px | oui (cette PR) |
| 34 — Méthodes d'ensemble | 39 px | oui (`ul` 0.7 em) |

C'est le **résidu** du point 3, et il n'est pas soluble par compression : six
de ces diapositives ont déjà été comprimées par le lot L3 de l'EPIC #11508 —
jusqu'à 0.56 em sur la diapositive 53 — et il ne reste qu'une poignée de
pixels. La lever davantage dégraderait la lisibilité pour un gain nul. La
solution qui reste est **l'embarquement des polices** (`@font-face`), que
[#24171](https://github.com/jsboige/CoursIA/issues/24171) liste mais que
cette PR ne prend pas : c'est un choix de licence et un poids de fichiers qui
dépassent ce lot.

## Portée du mesuré

- **Ce dossier ne dit pas que le deck est correct** : il dit qu'au moment du
  relevé, sur cette machine, avec ces polices, **aucun élément ne sort du
  canvas**. Un relevé reste un relevé.
- **La liste de l'issue n'est pas la liste mesurée ici.** L'issue nomme huit
  diapositives débordant sur `myia-po-2028` (02/48, 06/34, 06/42, 06/53,
  06/103, 06/112, S8/16) ; le relevé de cette machine en nomme sept, dont
  quatre ne sont pas dans la liste de l'issue (06/102, 06/105, 06/106,
  06/110). L'écart est l'objet même de l'issue : il n'est pas content-expliqué,
  il est lié aux polices système.
- **Les decks 02 et S8 ne sont pas traités ici** : 02/48 et S8/16 appartiennent
  à d'autres decks, dont le lot L2 reste à mesurer.
- Les PNG de rendu ne sont pas archivés : ce sont des rendus reproductibles.
  Le hash de chaque image est dans l'artefact du scanner de rendu
  (`docs/captures/24171/deck-06-overflow.json`).

## L'artefact

[`deck-06-composition-apres-correction.json`](deck-06-composition-apres-correction.json)
— même convention de hash que l'artefact `scan_slidev_overflow --archive` : le
contenu porte son **`content_sha256`**, recalculé sur l'artefact *sans* ce
champ, donc vérifiable par un tiers qui ne l'a pas produit.

```text
content_sha256 : 05e9153cdb19f77ffc075b0b6eb14ca018b6dcb038e3f9778d99cb5201ed391a
font_signature : faea2d8efd2aeb08      (identique au relevé d'avant : même machine, mêmes polices)
n_slides       : 124
n_hors_canvas  : 0
```

## Références

- [#24171](https://github.com/jsboige/CoursIA/issues/24171) — le compteur de
  débordement Slidev n'est pas opposable d'une machine à l'autre.
- [#11508](https://github.com/jsboige/CoursIA/issues/11508) — EPIC parent, lot L2.
- [#22258](https://github.com/jsboige/CoursIA/pull/22258) — précédent : mesure
  et correction du deck 02 par blocs `<style scoped>`.
- [`docs/captures/24171/`](https://github.com/jsboige/CoursIA/pull/25752) — l'instrumentation et la
  première lecture opposable du deck 06.

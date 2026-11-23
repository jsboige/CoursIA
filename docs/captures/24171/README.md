# Preuve de rendu opposable — lot L2 du chantier Slidev (#24171, EPIC #11508)

Ce dossier est le **premier relevé de rendu du lot L2** produit sous une forme
**opposable** : le relevé est archivé comme artefact versionné (hash de chaque
image mesurée, empreinte de la machine), et non comme un compteur que chacun
rejoue sur sa propre machine.

Il porte le deck **`06-apprentissage`** (124 diapositives rendues).

## Pourquoi un artefact, et pas un compte

Le rendu Slidev ne dépend que des **polices système** : `slides/` ne déclare
aucune `@font-face`, donc les métriques de texte — et la hauteur des blocs —
varient d'une machine à l'autre. C'est le constat de [#24171](https://github.com/jsboige/CoursIA/issues/24171) :
le même deck `S8-semantic-web`, au même canvas (980 × 552), donne **2**
diapositives hors canvas sur `myia-ai-01` (#22318) et **1** sur `myia-po-2028`
(#24156), sans qu'aucune modification du dépôt n'explique l'écart.

Deux conséquences, et deux responses apportées ici :

1. **Un relevé nu n'est pas opposable.** L'instrument
   `scripts/notebook_tools/scan_slidev_overflow.py` porte désormais dans sa
   sortie la dépendance aux polices et l'empreinte de la machine ; il sait
   écrire le relevé sous forme d'**artefact versionné** (`--archive`, hash de
   chaque PNG mesuré) et **comparer deux artefacts** (`--compare`) au lieu de
   rejouer un compteur.
2. **Un artefact se vérifie sans l'avoir produit.** Le contenu de l'artefact
   porte son propre `content_sha256` (empreinte recalculée sur le contenu
   sans ce champ) ; le `sha256` du fichier entier est affiché par l'outil.

## Méthode — l'export de rendu, et ses deux contraintes

L'export se fait avec l'outillage du dépôt (`slides/package.json` :
`@slidev/cli` + `playwright-chromium`) :

```bash
cd slides
npx slidev export --format png --range 1-40  --output <dossier> 06-apprentissage/slides.md
npx slidev export --format png --range 41-80 --output <dossier> 06-apprentissage/slides.md
npx slidev export --format png --range 81-124 --output <dossier> 06-apprentissage/slides.md
```

Deux contraintes **mesurées** sur cette machine (Windows 11), qui n'apparaissent
dans aucune documentation du dépôt et qui font échouer une mesure deck par deck :

- **l'export sans `--range` ne produit rien.** Il affiche `✓ exported`, sort
  avec le code **0**, et ne laisse **aucun PNG** dans le répertoire cible
  (reproduit sur les decks 01 et 06). Un lot L2 conduit sans `--range` mesure
  donc **zéro diapositive** en croyant en mesurer toutes.
- **`--output` efface le répertoire cible à chaque invocation.** Les trois
  plages ci-dessus exigent **trois répertoires distincts** ; sinon chaque
  export remplace le précédent et l'export complet est un trou.

Le scan :

```bash
python scripts/notebook_tools/scan_slidev_overflow.py <repertoire_png> \
       --archive docs/captures/24171/deck-06-overflow.json
```

## Résultat

### Lecture 1 — scanner de rendu (encre en bas d'image, export PNG)

| Mesure | Valeur |
|---|---|
| Diapositives rendues (export PNG) | **124** |
| Diapositives OVERFLOW | **0 / 124** |
| Diapositives illisibles | **0** |
| Machine | Windows 11 (AMD64), Python 3.13.15 |
| Canvas | 980 × 552 (valeur par défaut : aucun des decks ne déclare `canvasWidth`/`canvasHeight` dans son headmatter) |
| Lecture archivée | [`deck-06-overflow.json`](deck-06-overflow.json) |

### Lecture 2 — scanner de composition (DOM rendu, canvas 980 × 552)

Le second instrument, `scan_slidev_composition.py`, mesure dans le DOM rendu les
**éléments dont la boîte sort du canvas**. Il exige un serveur `slidev` en
mode dev et le **playwright Python** (avec son chromium) :

```bash
cd slides && npx slidev 06-apprentissage/slides.md --port 8902 --open false
python scripts/notebook_tools/scan_slidev_composition.py \
       --url http://localhost:8902/ --slides-md slides/06-apprentissage/slides.md \
       --out docs/captures/24171/deck-06-composition.json
```

| Mesure | Valeur |
|---|---|
| Diapositives rendues | **124** |
| **Diapositives dont un élément de contenu sort du canvas** (`n_hors_canvas`) | **7** |
| Diapositives dont la boîte sort du canvas, **conteneur de la diapositive inclus** | **21** (dont **14** à conteneur seul) |
| Chevauchements / recouvrements | 0 / 0 |
| `n_occupation_flagged` (advisory) | 7 |
| **Signature des polices** | `faea2d8efd2aeb08` |
| Environnement de rendu | Chrome Headless Shell 158.0.8127.18, canvas 980 × 552 |
| Polices résolues | Segoe UI, Calibri, Arial (toutes résolues, aucune générique) ; hauteur de ligne 21 px (delta 3 px vs police générique) |
| Lecture archivée | [`deck-06-composition.json`](deck-06-composition.json) |

`n_hors_canvas` compte des **diapositives**, pas des éléments : le tableau
ci-dessous donne, pour chacune des 7, le nombre d'**éléments** hors canvas.
Une diapositive dont le seul débordement vient du conteneur (`slidev-layout`
plus haut que le canvas) n'est pas comptée par `n_hors_canvas` — c'est ce qui
rend le chiffre comparable au relevé de #22286, dont la sonde applique la même
règle.

Les **7 diapositives** signalées sur cette machine :

| Diapositive | Titre | Éléments hors canvas |
|---|---|---|
| 40 | Réseaux feed-forward multi-couches | 5 |
| 102 | Renforcement passif | 3 |
| 103 | Apprentissage des différences temporelles | 5 |
| 105 | Q-learning = Apprentissage d'utilité action | 4 |
| 106 | Généralisation et approximations | 2 |
| 110 | Deep Q learning — exploration et avancées | 9 |
| 112 | Minimisation de regret hypothétique | 4 |

### Lecture 3 — la comparaison inter-machines, qui est le cœur de #24171

Le même deck, le même canvas (980 × 552), le même instrument, **deux machines** :

| Relevé | Machine | Date | `n_hors_canvas` | Signature des polices |
|---|---|---|---|---|
| [`docs/captures/22286/manifest.json`](../22286/manifest.json) | `myia-po-2028` | 2026-11-02 | **13** | *absente de l'archive* |
| ce dossier | `myia-po-2027` (Windows 11) | 2026-11-11 | **7** | `faea2d8efd2aeb08` |

**Ce que les deux archives établissent — et ce qu'elles n'établissent pas.**

Les deux relevés comptent **la même chose** : le scanner de composition compte
une diapositive lorsqu'un de ses **éléments de contenu** sort du canvas
(`n_hors_canvas = sum(1 for r in results if content_overflow(r))` — le
conteneur seul ne compte pas). La règle est **inchangée** entre la version de
l'instrument qui a produit le relevé de #22286 (2026-09-15) et celle
d'aujourd'hui : les deux chiffres sont donc comparables. Sur les **124**
diapositives du deck : **13** sur `myia-po-2028`, **7** sur cette machine.

L'archive de #22286 ne capture cependant que **32 des 124 diapositives** du
deck 06 — son README le dit (« parmi les diapositives capturées »). Sur ces
32 diapositives, **6** débordent là-bas : `34`, `40`, `42`, `53`, `103`, `112` —
les six mêmes que #24171 liste pour le deck 06 parmi ses huit diapositives à
corriger. Sur cette machine, **3** de ces six débordent aussi (`40`, `103`,
`112`) et **3** ne débordent qu'y (`34`, `42`, `53`).

L'**énumération complète n'est pas dérivable** des deux archives, et l'écart
exact n'est donc pas connu :

- les **4** diapositives qui débordent ici et dont l'archive ne dit rien de
  l'état là-bas (`102`, `105`, `106`, `110`) ne figurent **pas** parmi les 32
  diapositives capturées ;
- symétriquement, **7 des 13** diapositives signalées là-bas sont hors du
  sous-ensemble capturé et ne sont **pas identifiables**.

Le nombre de diapositives qui diffèrent est donc **borné, non connu** :
**entre 6 et 14** (au moins 3 avérées, plus au moins 3 des 7 non
identifiables ; au plus 3 + 4 + 7).

C'est précisément ce que l'artefact de ce dossier apporte : il porte le verdict
des **124** diapositives, donc l'énumération complète redevient dérivable de
l'archive — ce que celle de #22286, avec ses 32 diapositives capturées sur
124, ne permet pas.

C'est le **second** cas documenté de non-opposabilité du compteur, après
`S8-semantic-web` (2 → 1, voir #24171) — et il porte sur un deck de 124
diapositives, dont 7 contre 13. Aucun écart n'est content-expliqué : le deck
n'a pas bougé entre les deux relevés, et l'instrument est le même.

La lecture **après correction** des 7 diapositives signalées ici est dans
[`docs/captures/24171-point3/`](../24171-point3/README.md) : c'est là que le
point 3 de #24171 — corriger les diapositives qui débordent réellement — est
traité, sur le même deck et avec la même signature de polices.

C'est aussi ce que l'archive de #22286 ne pouvait pas dire : son `manifest.json`
ne porte **ni signature de polices ni empreinte de machine** (il précède la
sonde), donc ses 13 ne sont opposables à rien. C'est le manque que ce dossier
comble, et la raison pour laquelle l'artefact versionné est désormais la forme
 canonique du relevé.

## Portée du mesuré — ce que ce dossier ne dit pas

- **Les PNG ne sont pas committés** : ce sont des rendus, reproductibles à
  partir du deck et de l'outillage ; l'artefact en conserve le hash de chacun
  pour que la mesure reste **pinnée** sur les images exactes qui ont été
  mesurées.
- **Les deux scanners ne mesurent pas la même chose.** Le scanner de rendu
  mesure l'**encre qui touche le bas de l'image** ; le scanner de composition
  mesure, dans le DOM rendu au canvas 980 × 552, les **éléments dont la boîte
  sort du canvas** — y compris par la droite ou par le haut, et y compris le
  conteneur de la diapositive lui-même (que le rapport isole par
  `container_only`). Un « 0/124 » du premier **ne réfute pas** les 7
  diapositives hors canvas du second : ce sont deux questions différentes sur
  le même rendu.
- **Ce dossier ne tranche pas le point 3 de #24171** : les 7 diapositives
  listées ci-dessus débordent **réellement** au canvas du scanner de
  composition sur cette machine ; les corriger (blocs `<style scoped>`, comme
  #22258 l'a fait pour le deck 02) et **re-mesurer** est le travail qui
  reste — et il est fait sur des diapositives que la comparaison inter-machines
  désigne différemment selon la machine (voir ci-dessus) : une correction doit
  donc laisser une **marge**, pas viser l'égalité au canvas.
- **Un « 0/124 » n'est pas un « aucun défaut »** : c'est un relevé, pris sur
  une machine, avec des polices non versionnées. Il vaut ce que vaut l'artefact
  qui le porte — et il se compare à un autre **artefact**, pas à un compteur.

## Références

- [#24171](https://github.com/jsboige/CoursIA/issues/24171) — le compteur de débordement Slidev n'est pas opposable d'une machine à l'autre.
- [#11508](https://github.com/jsboige/CoursIA/issues/11508) — EPIC parent, lot L2 (le débordement au rendu demande l'export, pas un grep).
- [#22258](https://github.com/jsboige/CoursIA/pull/22258) — mesure et correction du deck 02 par blocs `<style scoped>` (le précédent du lot).
- [`docs/captures/22286/README.md`](../22286/README.md) — la preuve de rendu du chantier #22286, et la chaîne d'instruments qui produit un `manifest.json`.

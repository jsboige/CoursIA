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

| Mesure | Valeur |
|---|---|
| Diapositives rendues (export PNG) | **124** |
| Diapositives OVERFLOW (scanner de rendu, encre sur les 6 dernières lignes) | **0 / 124** |
| Diapositives illisibles | **0** |
| Machine | Windows 11 (AMD64), Python 3.13.15 |
| Canvas | 980 × 552 (valeur par défaut : aucun des decks ne déclare `canvasWidth`/`canvasHeight` dans son headmatter) |
| Lecture archivée | [`deck-06-overflow.json`](deck-06-overflow.json) |

## Portée du mesuré — ce que ce dossier ne dit pas

- **Les PNG ne sont pas committés** : ce sont des rendus, reproductibles à
  partir du deck et de l'outillage ; l'artefact en conserve le hash de chacun
  pour que la mesure reste **pinnée** sur les images exactes qui ont été
  mesurées.
- **Ce dossier ne tranche pas le point 3 de #24171** (les huit diapositives
  signalées comme débordant « réellement au canvas du scanner »). Le scanner
  de rendu mesure l'**encre qui touche le bas de l'image** ; le scanner de
  composition (`scan_slidev_composition.py`) mesure, dans le DOM rendu au
  canvas 980 × 552, les **éléments dont la boîte sort du canvas** — y compris
  par le côté, vers la droite, ou par le haut. Les deux instruments ne
  mesurent donc **pas la même chose**, et un « 0/124 » du premier ne réfute
  pas les 13 éléments hors canvas du second relevés sur `myia-po-2028`
  ([`docs/captures/22286/manifest.json`](../22286/manifest.json)).
- **Un « 0/124 » n'est pas un « aucun défaut »** : c'est un relevé, pris sur
  une machine, avec des polices non versionnées. Il vaut ce que vaut l'artefact
  qui le porte — et il se compare à un autre **artefact**, pas à un compteur.

## Références

- [#24171](https://github.com/jsboige/CoursIA/issues/24171) — le compteur de débordement Slidev n'est pas opposable d'une machine à l'autre.
- [#11508](https://github.com/jsboige/CoursIA/issues/11508) — EPIC parent, lot L2 (le débordement au rendu demande l'export, pas un grep).
- [#22258](https://github.com/jsboige/CoursIA/pull/22258) — mesure et correction du deck 02 par blocs `<style scoped>` (le précédent du lot).
- [`docs/captures/22286/README.md`](../22286/README.md) — la preuve de rendu du chantier #22286, et la chaîne d'instruments qui produit un `manifest.json`.

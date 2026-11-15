# Qualification des carnets — difficulté et dimension recherche

Ce répertoire qualifie chaque carnet du corpus sur **deux axes distincts** :

| Axe | Valeurs | Ce qu'il dit | Document |
|---|---|---|---|
| **Difficulté** | `D1` … `D4` | ce que l'étudiant doit fournir pour suivre le carnet | [echelle-difficulte.md](echelle-difficulte.md) |
| **Dimension recherche** | `R0` … `R3` | ce que le carnet produit **au-delà** de l'enseignement de la technique | [dimension-recherche.md](dimension-recherche.md) |

Les deux axes sont **indépendants** : un carnet facile peut toucher un problème
ouvert, un carnet difficile peut n'être qu'une technique établie. Les
confondre en une note unique est ce que l'EPIC [#24993](https://github.com/jsboige/CoursIA/issues/24993)
veut empêcher.

> Ce que le catalogue ne faisait pas : `docs/curriculum/niveaux.json` attribue un
> niveau à **44 carnets sur plus de 1 500**, et le statut « recherche » se
> déduisait du **chemin** du carnet (`_is_research_path` dans
> `generate_catalog.py`), c'est-à-dire du nom de son répertoire — pas de son
> contenu.

## Fichiers

| Fichier | Rôle |
|---|---|
| [echelle-difficulte.md](echelle-difficulte.md) | l'échelle `D1..D4`, ses trois critères, la règle de dérivation |
| [dimension-recherche.md](dimension-recherche.md) | l'axe `R0..R3` et sa justification par carnet |
| [manifest.json](manifest.json) | **la donnée** : une entrée par carnet, avec la justification et les mesures |
| [pilot-nlp.md](pilot-nlp.md) | la série pilote (`NLP`, 11 carnets) qualifiée et lue |

## L'organe

```bash
# la table de qualification
python scripts/notebook_tools/curriculum_qualification.py --report

# la vérification : forme, couverture, dérivation du niveau, dérive des mesures
python scripts/notebook_tools/curriculum_qualification.py --check

# les deux champs par carnet, pour le crochet du générateur (#24994)
python scripts/notebook_tools/curriculum_qualification.py --fields --json
```

`--check` **échoue** (exit 1) sur un carnet absent du manifeste, une valeur hors
énumération, une justification absente, un niveau qui ne se dérive pas de la
règle, ou une **dérive** — des mesures enregistrées qui ne correspondent plus à
l'arbre, parce que le carnet a changé depuis sa qualification.

Il **signale sans échouer** une densité pédagogique sous le plancher de 1200
([#13410](https://github.com/jsboige/CoursIA/issues/13410)) : c'est un défaut
d'enrichissement à corriger, pas une raison de requalifier. Un carnet sous-dense
n'est pas pour autant un carnet difficile.

Il signale de même **la perte d'un signal** — un organe canonique
(`pedagogy_density`, `generate_catalog`) momentanément indisponible : la
dégradation devient un avertissement au lieu d'être avalée en silence. Un
organe qui mesure moins ne doit pas le cacher.

L'organe ne calcule **aucune** valeur : les deux axes sont **déclarés et
justifiés**, une ligne par carnet. Il contrôle la forme, la dérivation et la
fraîcheur — pas le jugement.

## Qualifier un carnet

1. lire le carnet (markdown **et** cellules de code) ;
2. fixer les trois critères de difficulté et la valeur `recherche` ;
3. écrire **une ligne de justification** qui cite la section du carnet qui
   fonde la valeur ;
4. re-mesurer : `python scripts/notebook_tools/curriculum_qualification.py --refresh`
   (seul le bloc `mesures` est réécrit — les valeurs déclarées ne le sont
   jamais) ;
5. relancer `--check`.

## Séquencement dans l'EPIC #24993

| Issue | Objet | Qui la porte |
|---|---|---|
| #24994 | le crochet du générateur (niveau de sous-série) | `myia-po-2024:CoursIA` |
| #24995 | taxonomies des carnets et des concepts | `myia-po-2023:CoursIA-2` |
| **#24996** | **difficulté et dimension recherche** (ce répertoire) | `myia-po-2028:CoursIA-2` |
| #24997 | concepts cartographiés sur AIMA | `myia-po-2028:CoursIA-2` |

Le crochet du générateur — « le catalogue affiche les deux champs, et le statut
recherche cesse de dépendre du seul chemin » — est **la suite de #24994** : le
fichier `generate_catalog.py` est claimé par une autre lane. L'organe expose
déjà l'API dont ce crochet a besoin (`load_manifest()`, `qualification_for()`),
pour qu'il n'y ait pas de seconde source de vérité ; il ne modifie pas le
catalogue.

## Les signaux déjà mesurés sont des **entrées**, pas des verdicts

Trois issues ont produit des signaux que cette qualification consomme sans les
copier :

- [#24282](https://github.com/jsboige/CoursIA/issues/24282) — les **substrats
  dégénérés** : un carnet dont le terrain rend la baseline naïve optimale
  n'enseigne rien du moteur qu'il prétend enseigner. C'est un critère de
  **qualité du substrat**, pas de difficulté : il dit que le carnet doit
  **changer**, pas qu'il est difficile.
- [#24292](https://github.com/jsboige/CoursIA/issues/24292) — le **résultat
  négatif** de l'inventaire D4 : un scan par mots-clés ne mesure pas la
  dégénérescence (39 carnets touchés, aucun vrai cas). C'est pourquoi la
  qualification **ne scanne rien** : chaque valeur est justifiée à la main,
  sur le carnet lu.
- [#13410](https://github.com/jsboige/CoursIA/issues/13410) — la **densité
  pédagogique** : un plancher de 1 200 caractères de prose par cellule de code.
  L'organe la signale ; elle ne décide d'aucun niveau.

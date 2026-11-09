# Taxonomie pédagogique

Cette tranche pilote matérialise le nœud de série et les sept carnets racine de Compression recensés dans `COURSE_CATALOG.generated.md` (le carnet compagnon Lean reste dans sa sous-série distincte). Ces carnets n'ont pas de sous-série dans le catalogue. Elle part des concepts nommés dans les cellules de titre et d'exposé ; chaque rattachement pointe vers le chemin du carnet et son identifiant de cellule. Les UUID des concepts sont opaques et ne changent pas lorsque leurs chemins taxonomiques évoluent.

Le format conserve les trois colonnes de repérage d'Argumentum : `path`, `decimal_path` et `depth`. La hiérarchie pédagogique réserve aussi les niveaux `example` et `exercise` sous le carnet ; ils ne sont pas peuplés dans cette première tranche. Les prérequis reprennent les prérequis déclarés dans les introductions des carnets. Le validateur vérifie les références, les cellules, la couverture des sept carnets, les prérequis inconnus et les cycles.

`compression.json` contient les données éditoriales, et `schema.json` décrit leur structure. Pour régénérer les exports SKOS/Turtle et OWL/RDF/XML dans un répertoire temporaire :

```bash
python scripts/notebook_tools/curriculum_taxonomy.py \
  --skos-output /tmp/compression.ttl \
  --owl-output /tmp/compression.owl
```

Les sources des concepts sont exportées en liens GitHub vers les vrais carnets. Chaque relation `cursus:hasCellCitation` regroupe le lien du carnet et son `cursus:cellId`, contrôlé contre le notebook local.

L'export des concepts reste un graphe à part de l'export catalogue afin que chaque forme garde sa validation dédiée. Un consommateur peut les unir dans un même graphe RDF en chargeant les deux Turtle, par exemple `graph.parse("catalogue.ttl", format="turtle")` puis `graph.parse("compression.ttl", format="turtle")`.

## Série Probas — tranche 1 (sous-série Infer)

`probas.json` étend le même format à la série **Probas**, sur la sous-série **Infer** fondation : six carnets (`Infer-01` à `Infer-05`, dont `Infer-01b`) et 22 concepts. Le même `schema.json` et le même validateur `curriculum_taxonomy.py` s'appliquent ; les **prérequis** relient les carnets entre eux (par ex. les réseaux bayésiens et la d-séparation avant l'inférence causale). Chaque concept cite les cellules de carnet où il est enseigné ; ceux qui s'y rattachent (réseaux bayésiens, d-séparation, inférence causale) nomment en outre le chapitre **AIMA 3e/4e** correspondant dans leur définition, les concepts propres à Infer.NET (moteur, graphes de facteurs, VMP/EP, mélanges gaussiens) n'ayant pas d'équivalent AIMA.

```bash
python scripts/notebook_tools/curriculum_taxonomy.py \
  --data docs/curriculum/taxonomy/probas.json \
  --skos-output /tmp/probas.ttl \
  --owl-output /tmp/probas.owl
```

La tranche 2 ajoutera la sous-série **PyMC** au même fichier, puis les carnets Infer avancés (IRT, TrueSkill, processus de Kalman, etc.).

## Série GameTheory — tranche 1 (cœur : forme normale → Nash → minimax → forme extensive → SPE)

`gametheory.json` étend le même format à la série **GameTheory**, sur le **cœur** de la série : neuf carnets (`GameTheory-01` à `GameTheory-10`, hors `08`) et 28 concepts. Le même `schema.json` et le même validateur `curriculum_taxonomy.py` s'appliquent ; les **prérequis** relient les carnets entre eux (par ex. la forme normale et la meilleure réponse avant l'équilibre de Nash, l'induction arrière avant les raffinements de perfection). Chaque concept cite les cellules de carnet où il est enseigné ; ceux qui s'y rattachent (jeu en forme normale, équilibre de Nash, jeu à somme nulle, forme extensive, induction arrière, dilemme du prisonnier) nomment en outre le chapitre **AIMA 3e/4e** correspondant dans leur définition, les concepts sans équivalent AIMA (topologie des jeux 2x2, théorie évolutionnaire, perfection en sous-jeux, induction avant, perfection en mains tremblantes) n'en citant aucun.

```bash
python scripts/notebook_tools/curriculum_taxonomy.py \
  --data docs/curriculum/taxonomy/gametheory.json \
  --skos-output /tmp/gametheory.ttl \
  --owl-output /tmp/gametheory.owl
```

Les tranches suivantes étendront la série aux sous-séries **SocialChoice**, **Coalitions**, **Dynamics**, aux jeux bayésiens et aux jeux globaux — ajoutées au même `gametheory.json`, une PR par tranche, sur ce même modèle.

## Série Search — tranche 1 (sous-série Part1-Foundations : espaces d'états → non informée → informée → locale → adversariale → MCTS)

`search.json` étend le même format à la série **Search**, sur la sous-série **Part1-Foundations** : six carnets (`Search-01-StateSpace`, `02-Uninformed`, `03-Informed`, `04-LocalSearch`, `06-AdversarialSearch`, `07-MCTS-And-Beyond`) et 24 concepts. Le même `schema.json` et le même validateur `curriculum_taxonomy.py` s'appliquent ; l'arbre de carnets porte ici le niveau **sous-série** (`Search/Part1-Foundations`). Les **prérequis** relient les carnets entre eux (par ex. la formulation du problème avant la recherche non informée, le minimax avant l'élagage alpha-bêta, l'adversarial avant le MCTS). Chaque concept cite les cellules de carnet où il est enseigné ; ceux qui s'y rattachent (espaces d'états, recherche non informée, recherche informée et A*, recherche locale, recherche adversariale, minimax) nomment en outre le chapitre **AIMA 3e/4e** correspondant dans leur définition, les concepts sans équivalent AIMA (MCTS, sélection UCB1, AlphaZero) n'en citant aucun.

```bash
python scripts/notebook_tools/curriculum_taxonomy.py \
  --data docs/curriculum/taxonomy/search.json \
  --skos-output /tmp/search.ttl \
  --owl-output /tmp/search.owl
```

Les tranches suivantes étendront la série aux sous-séries de `Search/` (autres parties du catalogue) et aux carnets de `Part1-Foundations` non couverts ici — ajoutées au même `search.json`, une PR par tranche, sur ce même modèle.

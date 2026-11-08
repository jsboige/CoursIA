# Taxonomie pédagogique

Cette tranche pilote couvre les sept carnets racine de la série Compression recensés dans `COURSE_CATALOG.generated.md` (le carnet compagnon Lean reste dans sa sous-série distincte). Elle part des concepts nommés dans les cellules de titre et d'exposé ; chaque rattachement pointe vers le chemin du carnet et son identifiant de cellule. Les UUID des concepts sont opaques et ne changent pas lorsque leurs chemins taxonomiques évoluent.

Le format conserve les trois colonnes de repérage d'Argumentum : `path`, `decimal_path` et `depth`. La hiérarchie pédagogique réserve aussi les niveaux `example` et `exercise` sous le carnet ; ils ne sont pas peuplés dans cette première tranche. Les prérequis reprennent les prérequis déclarés dans les introductions des carnets. Le validateur vérifie les références, les cellules, la couverture des sept carnets, les prérequis inconnus et les cycles.

`compression.json` contient les données éditoriales, et `schema.json` décrit leur structure. Pour régénérer les exports SKOS/Turtle et OWL/RDF/XML dans un répertoire temporaire :

```bash
python scripts/notebook_tools/curriculum_taxonomy.py \
  --skos-output /tmp/compression.ttl \
  --owl-output /tmp/compression.owl
```

Les sources des concepts sont exportées en liens GitHub vers les vrais carnets ; l'identifiant de cellule reste attaché comme provenance `cursus:taughtInCell` et est contrôlé contre le notebook local.

L'export des concepts reste un graphe à part de l'export catalogue afin que chaque forme garde sa validation dédiée. Un consommateur peut les unir dans un même graphe RDF en chargeant les deux Turtle, par exemple `graph.parse("catalogue.ttl", format="turtle")` puis `graph.parse("compression.ttl", format="turtle")`.

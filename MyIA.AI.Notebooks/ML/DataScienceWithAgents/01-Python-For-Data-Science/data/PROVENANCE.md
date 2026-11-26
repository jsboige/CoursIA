# Jeu de données « Palmer Penguins » — provenance et licence

Vendored dans cette série pour le volet prérequis data science (#19547) : exploration,
nettoyage, visualisation et statistiques descriptives sur des données réelles.

| Fichier | Contenu | Rôle pédagogique |
|---|---|---|
| `penguins_raw.csv` | 344 × 17 — données brutes de terrain (chaînes d'espèces verbeuses, colonnes d'étude, notes de terrain, `NA` épars, dates en texte) | le « jeu réel et sale » du notebook 1.5 (exploration + nettoyage + journal des décisions) |
| `penguins.csv` | 344 × 8 — version remise en forme (espèces abrégées, unités dans les noms de colonnes, 19 valeurs manquantes conservées) | la cible de référence : le nettoyage de 1.5 la rejoint ; jeux des notebooks 1.4 et 1.6 |

## Provenance

- Dépôt : <https://github.com/allisonhorst/palmerpenguins> (fichiers `inst/extdata/penguins.csv` et `inst/extdata/penguins_raw.csv`), copiés tels quels le 2026-10-06.
- Données de terrain : Dr. Kristen Gorman et la station Palmer, Antarctique — Long Term Ecological Research (LTER) Network, palmerpenguins importe les tables « Penguin size clutches 2007-2009 » du [Palmer Station LTER Data Portal](https://pal.lternet.edu/).
- Citation attendue : Gorman K. B., Williams T. D., Fraser W. R. (2014), « Ecological sexual dimorphism and environmental variability within a community of Antarctic penguins (genus Pygoscelis) », *PLoS ONE* 9(3):e90081. doi:10.1371/journal.pone.0090081.

## Licence et redistribution

- Le package R `palmerpenguins` (compilation, documentation, CSV) est distribué sous **CC0 1.0** (« dedicated to the public domain ») : réutilisation et redistribution autorisées, y compris commercialement, sans restriction.
- Les données LTER sous-jacentes relèvent de la politique de diffusion LTER (« distribution unlimited ») avec **attribution attendue** de la source — couverte par la citation ci-dessus, reproduite également dans les notebooks qui consomment le jeu.

Aucune modification des CSV n'a été faite au vendoring (contrôle `wc -l` au moment du dépôt : mêmes dimensions que la référence, en-tête compris).

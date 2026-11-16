# Symmetry — art génératif de symétrie

Série d'art génératif sur la **classification des groupes de symétrie du plan**.
Chaque carnet part d'un **motif de base tiré au hasard** (art génératif : les
illustrations ne se répètent jamais) et l'applique par les **opérations d'un groupe**
pour dessiner ce que la cristallographie compte — les 7 groupes de frieze (1D),
les 17 groupes de wallpaper (2D), les groupes de rosettes.

> **Provenance** : distillation de l'idée de
> [aberke/coloring-book](https://github.com/aberke/coloring-book)
> (« A Coloring Book about Group Theory »), **ré-implémentée indépendamment** en
> Python natif. La classification des groupes de symétrie est un **fait
> mathématique** ; le repo est cité comme *inspiration*, ni son code JS ni ses
> assets ne sont copiés (issue #25324, gate licence, voie a).

## Carnets

| # | Carnet | Sujet |
|---|--------|-------|
| 1 | [Frieze-01-Groups-Python](Frieze-01-Groups-Python.ipynb) | Les 7 groupes de frieze — le motif de base + ses copies par opération, rendu en art génératif |

**Parcours prévu** : frieze (1D) → wallpaper (2D) → rosettes.

## Prérequis

`numpy`, `matplotlib` (aucune dépendance externe).

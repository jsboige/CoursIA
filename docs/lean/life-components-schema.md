# Schéma de motifs et de réactions de Game of Life — tranche 1+2 de #15635

Le moteur cellulaire de #15571 cherche un motif en énumérant des cellules dans
une boîte, puis en encodant son évolution en SAT. Son espace de recherche croît
avec la surface, la période et la cardinalité, et il ignore tout ce que la
communauté Life sait déjà des briques connues (still lifes, catalyseurs,
oscillateurs, collisions de gliders, tronçons de pistes Herschel).

Cette tranche ajoute la couche **symbolique** qui manquait : un format
machine-readable pour décrire des *motifs/composants* et des *réactions*, avec
la propriété qui la rend utile — **aucune métadonnée déclarée n'est acceptée sur
confiance**. Chaque champ numérique est re-dérivé par replay dans le moteur Life
du dépôt (`scripts/lean/life_synthesize.py`) et comparé à ce que le document
prétend. Un écart est un refus, pas un avertissement.

Le module est [`scripts/lean/life_components.py`](../../scripts/lean/life_components.py) ;
le catalogue curé est [`scripts/lean/life_components_fixture.json`](../../scripts/lean/life_components_fixture.json).

## Ce que la tranche couvre — et ce qu'elle ne couvre pas

| Section de #15635 | État |
|---|---|
| §1 schéma minimal versionné (motifs + réactions) | **livré** |
| §2 catalogue reproductible réduit, rejoué indépendamment | **livré** |
| §3 générateur de contraintes compositionnelles | hors tranche |
| §4 démonstrateur multi-composants + ablations de pruning | hors tranche |

Le schéma porte les champs que #15635 nomme pour §1, mais **tous ne sont pas
encore validés mécaniquement** — la distinction est explicite ci-dessous.

## Motif : ce qui est mesuré

Un motif déclare son identifiant, sa provenance, ses cellules canoniques, sa
règle, sa période, sa translation par période, sa population, sa boîte initiale,
son enveloppe sur un cycle et ses symétries autorisées. Sont **recalculés par
replay** puis comparés :

- la **période** — la plus petite `p` telle que `evolve^p T` soit `T` à
  translation près (une période déclarée trop grande est refusée : elle n'est pas
  la période du motif, c'est un de ses multiples) ;
- la **translation** par période, et par conséquent la direction et la vitesse ;
- la **population**, la **boîte initiale**, l'**enveloppe** sur un cycle ;
- la **catégorie** (`still_life` / `oscillator` / `spaceship`), dérivée de la
  période et de la translation plutôt que crue sur parole ;
- la **forme canonique** des cellules (translation ramenée à l'origine, liste
  triée) ;
- les **phases** déclarées, si le document en porte.

Le champ `rule` n'accepte que `B3/S23` : c'est la seule règle que le moteur du
dépôt implémente, et prétendre en valider une autre serait une preuve non
fournie.

## Canonicalisation : normaliser sans fusionner

Deux formes sont « le même objet » si l'une s'obtient à partir de l'autre par
une symétrie **qui préserve son vecteur de translation**. Cette restriction
n'est pas cosmétique : sous le groupe diédral complet, les quatre orientations
d'un glider se confondraient, et la direction de vol — précisément ce qu'une
réaction compositionnelle doit contraindre — disparaîtrait.

| Translation | Symétries admissibles |
|---|---|
| `(0, 0)` (still life, oscillateur) | groupe diédral complet |
| `(1, -1)` (glider du dépôt) | `T`, `D2` |
| `(-1, -1)` (`glider_mirror`) | `T`, `D1` |
| `(-2, 0)` (`lwss`) | `T`, `My` |

Conséquence testée : `glider` et `glider_mirror` ont la même forme à une
réflexion près mais des translations opposées — `same_object` répond **faux**.
Déclarer une symétrie inadmissible est un refus.

## Réaction : ce qui est mesuré

Une réaction déclare ses réactifs et produits (placements de motifs, ou cellules
brutes quand le produit n'est pas un objet catalogué), ses ports, son décalage
temporel, son temps de stabilisation, sa région occupée, ses zones de clearance,
sa nature et sa provenance. Sont **recalculés par replay de l'évolution jointe** :

- le **produit** : l'état à `t = stabilization_time` doit égaler exactement le
  produit déclaré, et être **stable** (`step(état) == état`). Une réaction dont
  le produit est mobile est hors du domaine de ce validateur — c'est une limite
  assumée, pas un silence ;
- les **zones de clearance** : aucune cellule vivante ne doit y passer, à aucun
  pas de la fenêtre. C'est le contrôle négatif de l'absence d'interaction
  parasite ;
- la **région occupée** : boîte englobante de tout ce qui a vécu pendant la
  fenêtre ;
- la **nature** (`consumable` / `reusable` / `catalytic`) : mesurée par survie
  d'un réactif dans l'état final, à translation près.

Les **ports** sont validés structurellement (nom, direction non nulle, position
dans la région occupée). Leur *sémantique de compatibilité* — quel port de quel
composant peut en rencontrer un autre, à quelle phase — appartient à §3 et n'est
pas prétendue ici.

## Le catalogue curé

Six motifs et trois réactions, tous **rejoués** à chaque validation :

| Motif | Catégorie | Période | Translation | Population | Enveloppe |
|---|---|---:|---|---:|---|
| `block` | still_life | 1 | `(0, 0)` | 4 | 2×2 |
| `blinker` | oscillator | 2 | `(0, 0)` | 3 | 3×3 |
| `toad` | oscillator | 2 | `(0, 0)` | 6 | 4×4 |
| `glider` | spaceship | 4 | `(1, -1)` | 5 | 3×3 |
| `glider_mirror` | spaceship | 4 | `(-1, -1)` | 5 | 3×3 |
| `lwss` | spaceship | 4 | `(-2, 0)` | 9 | 5×4 |

| Réaction | Nature | Stabilisation | Produit mesuré |
|---|---|---:|---|
| `glider_pair_annihilation` | consumable | 12 | vide (annihilation complète) |
| `glider_pair_two_blocks` | consumable | 5 | deux `block` |
| `block_catalyses_glider` | catalytic | 43 | 12 cellules, le `block` survit parmi les débris |

La troisième réaction est délibérément **non triviale** : le produit n'est pas la
forme du réactif, donc « le bloc survit » est une mesure qui discrimine. Un cas
où le produit serait exactement la forme du catalyseur serait vrai par
construction et ne prouverait rien.

## Provenance : trois natures d'information, distinguées

Le critère 8 de #15635 demande de ne pas confondre trois choses. Le catalogue
les sépare champ par champ :

1. **Faits importés** — la nomenclature et l'existence des objets (`block`,
   `blinker`, `toad`, `lwss`) viennent de sources Life explicites, nommées dans
   le champ `provenance.source`. Les objets mathématiques eux-mêmes sont du
   domaine public ; ce qui est « importé » est le nom, pas une donnée.
2. **Propriétés revalidées** — période, translation, population, enveloppe,
   produit, stabilisation, clearance, survie. Elles ne sont pas importées : elles
   sont mesurées par le moteur du dépôt, à chaque exécution. Le `glider` n'est
   même pas importé du tout : il est celui que `life_synthesize.py` redécouvre
   par énumération bornée (Loi II, EPIC #12205).
3. **Choix de conception propres à CoursIA** — le format du schéma, la règle
   d'admissibilité des symétries, l'exigence de stabilité du produit, la
   convention de placement des phases (forme normalisée placée à l'offset
   déclaré). Ces choix sont des décisions, pas des faits, et sont énoncés ici
   comme tels.

## Reproduction

```
python scripts/lean/life_components.py --fixture scripts/lean/life_components_fixture.json
python scripts/lean/life_components.py --fixture scripts/lean/life_components_fixture.json --json
python -m pytest scripts/lean/tests/test_life_components.py -q
```

Le validateur sort `0` si toutes les métadonnées déclarées correspondent au
replay, `1` sinon, avec le champ fautif nommé. Les tests falsifient une
métadonnée à la fois (période, translation, population, boîte, enveloppe,
catégorie, symétrie, phases, vitesse, provenance, produit, stabilisation,
clearance, nature, région, ports, version de schéma) et exigent le refus.

See #15635 · See #15571 · See #12205

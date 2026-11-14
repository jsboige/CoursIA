# `scripts/symmetry` — les 17 groupes de symétrie du plan

Paquet **sans dépendance externe** (bibliothèque standard seule) qui décrit les
17 groupes cristallographiques du plan (« wallpaper groups ») par leurs
générateurs, et en **déduit** leurs invariants : réseau de Bravais, groupe
ponctuel, directions de miroir, axes de glissade, centres de rotation.

Tout le calcul est **exact** : les matrices et les translations sont des
`fractions.Fraction`, jamais des flottants. Un invariant approché (un réseau
classé « oblique » au lieu de « rectangulaire centré », une direction de
miroir perdue) est un faux résultat, pas une approximation acceptable.

## Utilisation

```python
from symmetry import GROUPS_BY_SYMBOL, attributes, render_svg

groupe = GROUPS_BY_SYMBOL["p4m"]
attributs = attributes(groupe)
attributs.lattice  # 'square'
attributs.point_group_order  # 8
attributs.mirror_directions  # 4
attributs.centers_by_order  # ((2, 2), (4, 2))
svg = render_svg(groupe, cells=4, size=640)
```

Trois modules :

| Module | Role |
|---|---|
| `symmetry.affine` | algèbre affine exacte (`Affine`, compositions, inverses) |
| `symmetry.wallpaper` | les 17 groupes, leurs générateurs, les attributs dérivés, le rendu SVG |
| `symmetry` (paquet) | ré-export de l'API publique |

## Conventions de comptage

Ces conventions sont explicites parce que les sources publiées
référencent les memes objets avec des unités différentes.

* **Cellule primitive** : les centres de rotation sont comptés par cellule
  primitive du réseau de translation, et chaque position est comptée à son
  **ordre maximal** (une position fixe d'un quart de tour et d'un demi-tour
  est comptée comme d'ordre quatre).
* **Directions** : une droite et son opposée font **une** direction.
* **Lignes** : une ligne de miroir et une ligne portant une glissade sont
  deux lignes distinctes, même si elles sont parallèles. Un décalage de
  ligne est normalisé **modulo le pas du réseau** dans la direction normale
  — deux lignes distinctes ne doivent jamais être confondues (c'est ce qui
  distingue, par exemple, le miroir et l'axe de glissade de `cm`).
* **Axes de glissade** : lignes portant une glissade et ne portant **pas**
  de miroir. Une glissade dont l'axe coïncide avec une ligne de miroir n'est
  pas un axe de glissade distinct.
* **Réseau centré** : le type « rectangulaire centré » se reconnaît à
  l'existence d'une base orthogonale de double pavé dont le centre
  `(u + v) / 2` appartient au réseau ; la base réduite d'un tel réseau n'est
  pas un losange.

## Provenance et licence

Les valeurs attendues proviennent de la page « Wallpaper group » de
Wikipedia, **archivée dans le gisement partagé** (jamais dans le dépôt) :

```text
G:\Mon Drive\MyIA\IA\Bibliographie IA\GroupTheory\
    2026 - Wikipedia - Wallpaper group.html
        sha256 e474cdb659ee888f65c872040caa852dc45db3a81a3071a0dd27acb48cc84a49
    2026 - Wikipedia - Orbifold notation.html
        sha256 f165e66b21f1a6fe242eae8696e65e952f50ebccc4c1ea1197b3c83d1beca368
    2026 - Wikipedia - List of planar symmetry groups.html
        sha256 9a68528933662b0945a41e75f82bd87c04ffa716eede3dc31e1ee333c79f157a
```

**Voie retenue : réimplémentation indépendante (voie a).** Aucun fichier du
gisement n'est copié dans le dépôt : les snapshots sont sous licence
CC BY-SA, et les PDF comme les publications sous droits ne sont jamais
committés dans CoursIA. Le code est écrit de zéro à partir des définitions
algébriques (isométrie affine `x ↦ A x + t`, réseau de translation,
cosets), et la page archivée sert de **référence de valeurs** — les
citations verbatim figurent dans les commentaires de
`scripts/tests/test_wallpaper_groups.py`.

Le dépôt d'origine `aberke/coloring-book` (« A Coloring Book about Group
Theory », art génératif de symétrie) est cité comme **inspiration** seule :
sa licence n'est **pas** déclarée, donc aucun code, aucun asset et aucune
illustration n'en est repris ici. La réimplémentation est **indépendante**
(voie a).

Une recherche de référence historique n'a **pas** abouti : l'ouvrage
« Armstrong 1908 » sur les groupes de symétrie est introuvable (aucune
occurrence dans les archives consultées). Les références probablement
visées sont Coxeter & W. O. J. Moser, *Generators and Relations for
Discrete Groups* (1980), et M. A. Armstrong, *Groups and Symmetry* (1988,
prêt sous contrôle numérique) — aucune n'a été déposée ni utilisée. Rien
n'a été inventé pour combler ce vide.

## Organe natif et non-recouvrement

1. **Quelle série possède déjà cette sémantique ?** Aucune : aucun fichier du
   dépôt ne mentionne les groupes `p4g`, `p3m1`, `p31m` ou `p6m`, et aucun
   module de symétrie du plan n'existe hors de ce paquet.
2. **Peut-on invoquer son module réel ?** Sans objet : il n'y en a pas.
3. **Que faudrait-il exporter ailleurs ?** Rien : ce paquet est l'organe.
4. **Quel témoin négatif fournit l'organe natif ?** Les invariants dérivés
   (type de réseau, groupe ponctuel, directions, centres) sont **recalculés**
   à partir des générateurs, et non recopiés : un générateur erroné change
   le résultat. Les tests le montrent en comparant le réseau **dérivé** au
   réseau **déclaré** par chaque groupe.
5. **Quelle autre série assure la vérification indépendante ?** Les tests
   contrôlent l'exactitude par l'algèbre (fermeture du groupe, invariance du
   réseau par chaque partie linéaire, multiplicité `|det(I - A)|` des
   centres) — un contrôle indépendant du chemin de calcul du moteur.

La PR `claude/terra30-02` (hors flotte) dessine des frises et des rosaces
dans `MyIA.AI.Notebooks/GenAI/Image/05-History/symmetry_art.py` ; elle ne
touche pas ce paquet et ne partage aucun fichier avec lui.

## Limites

* Les groupes sont donnés par **générateurs** : le moteur en déduit tout le
  reste. Ajouter un groupe consiste à ajouter des générateurs et un réseau.
* Le rendu SVG est un témoin de fonctionnement (orbite d'un motif
  asymétrique sous le groupe), pas un rendu de qualité production.
* Les centres secondaires (ordre 2 quand un ordre supérieur existe au même
  point) ne sont pas comptés séparément : la référence publiée les compte
  parfois par cellule illustrée, ce qui n'est pas la même unité.

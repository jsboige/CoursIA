# KNOTS — théorie des nœuds, du récit au lac

Sous-série de la série [Lean](../README.md) (décision de gradation #17545, 24/09) : la théorie des nœuds descend ici avec son lac [`knot_lean`](knot_lean/README.md). L'arc interne va du récit mathématique (Conway, la sliceness du nœud 11n34 et la preuve de Piccirillo) vers le lac réel : chaque carnet finit par interroger les déclarations `Knots.*` qui vivent dans ce dossier.

La série principale garde son tutoriel (numéros 1 à 14) et ses hommages (Lean-16 pour Conway, l'homme et l'œuvre) ; le présent dossier porte l'arc nœuds. Les numéros de la table ci-dessous renvoient à l'ancien identifiant de série (`Lean-17a` → `KNOTS-01`, etc. — table de correspondance dans `docs/reference/rename-ledger.tsv`).

**Escalier depuis la série principale** : [Lean-16 — Conway, l'homme et l'œuvre](../Lean-16-Conway-Homme-et-Oeuvre-Lean-Python.ipynb) présente Conway ; KNOTS-01 en explore la face cachée (le nœud de Conway, la question de sa sliceness ouverte 50 ans, résolue par Lisa Piccirillo en moins d'une semaine).

## Parcours principal

| Carnet | Ce qu'on y apprend | Durée |
|---|---|---|
| [KNOTS-01-Conway-Proofs-Lean-Python](KNOTS-01-Conway-Proofs-Lean-Python.ipynb) | Conway et la théorie des nœuds : le nœud de Conway (11n34), Fox 3-colorabilité, mutants, la preuve de sliceness de Piccirillo (2020) et la question connexe de Lidman (2026) — interrogation de `Conway.lean` et `Lidman.lean` du lac | ~45 min |
| [KNOTS-02-Invariants-Python](KNOTS-02-Invariants-Python.ipynb) | Les invariants de nœuds présentés en KNOTS-01, calculés et vérifiés en Python open source (SnapPy, matplotlib) — le jumeau formel de ces invariants vit dans `knot_lean` | ~30 min |
| [KNOTS-03-Companion-Formel-Lean-Python](KNOTS-03-Companion-Formel-Lean-Python.ipynb) | Le lac `knot_lean` par ses déclarations : les modules que KNOTS-01 ne cite pas (`Basic.lean`, structures fondamentales), les paires i18n FR/EN et l'intégrité des jumeaux | ~30 min |
| [KNOTS-04-Geometrie-Hyperbolique-Python](KNOTS-04-Geometrie-Hyperbolique-Python.ipynb) | La descente géométrique : les tétraèdres idéaux d'un complémentaire hyperbolique, l'équation de raccordement `z·z'·z'' = -1`, le volume de Bloch-Wigner recalculé indépendamment par `mpmath` (cross-check contre SnapPy), la table des remplissages de Dehn avec son cas exceptionnel non hyperbolique, et la rigidité de Mostow vérifiée numériquement (témoin négatif : le nœud torique `3_1`) | ~45 min |
| [KNOTS-05-Dynamique-Tresses-Python](KNOTS-05-Dynamique-Tresses-Python.ipynb) | La couche dynamique : l'action d'Artin de `B_n` sur le groupe libre, vérifiée par ses relations plutôt qu'affirmée, l'itération de `σ1 σ2⁻¹` dont la longueur réduite croît à `φ²`, et le spectre de Perron de la matrice de transition — borne atteinte par les tresses qui étirent dans `B_3`, non serrée en `B_4`, et aveugle au niveau abélianisé | ~30 min |
| [KNOTS-05-Dynamique-Tresses-CSharp](KNOTS-05-Dynamique-Tresses-CSharp.ipynb) | La même dynamique des tresses en C# natif (mots d'Artin, réduction par annulation, croissance sous itération, matrices de transition et abélianisées, rayon spectral par itération de puissance), bibliothèque standard uniquement — parité de sortie avec le jumeau Python | ~30 min |
| [KNOTS-06-Empilements-Cercles-Python](KNOTS-06-Empilements-Cercles-Python.ipynb) | Le théorème Koebe–Andreev–Thurston calculé (relaxation de Stephenson UNM, layout univalent), la conformité de la carte Schwarz–Christoffel mesurée par transport inverse (excentricité ∝ maille, ×16 exact au centre), et l'anneau en contre-témoin — obstruction d'empilement plan certifiée (sommes d'angles au trou > 2π) | ~45 min |
| [KNOTS-07-Feuilletages-Godbillon-Vey-Python](KNOTS-07-Feuilletages-Godbillon-Vey-Python.ipynb) | La classe de Godbillon–Vey calculée de bout en bout par `sympy.diffgeom` — coframe du fibré tangent unitaire d'une surface hyperbolique et crochets de Lie, contact contre feuilletage tranché par le critère de Frobenius (rang 3 contre rang 2), intégrabilité confondue avec l'invariance par le flot géodésique (même zéro), classe `4π²χ` sur `T¹Σ_g` recoupée par l'aire numérique du polygone `{4g, 4g}` (quadrature contre Gauss–Bonnet, écart < 1e-12), composante de Reeb en contre-témoin (η exacte, classe nulle) | ~45 min |

## Comment lire ce README

Le fil est une **descente** : le récit (KNOTS-01) → les invariants calculés (KNOTS-02) → le lac interrogé déclaration par déclaration (KNOTS-03) → les quatre visions — géométrique (04), dynamique (05), conforme (06) et de feuilletage (07), chacune avec son propre contre-témoin.

Trois portes d'entrée, selon ce qu'on vient chercher :

- **le récit** — KNOTS-01 seul suffit, il porte la preuve de Piccirillo et le contexte Conway ;
- **le calcul** — KNOTS-02 (SnapPy) et KNOTS-04 (géométrie hyperbolique, `mpmath`) sont autonomes en Python et se lisent dans n'importe quel ordre ;
- **le lac** — KNOTS-03 est la porte formelle : il montre ce que le lac déclare réellement, et sert de référence quand un carnet cite un théorème.

KNOTS-05 existe en deux exemplaires : la version Python et son jumeau .NET rendent la même chose, et la parité de sortie entre les deux fait partie de ce qu'on y apprend. Le choix se fait sur l'outil, pas sur le contenu.

**Prérequis d'entrée** : le tutoriel de la série principale (numéros 1 à 6, tactiques et Mathlib) ; la lecture de [Lean-16](../Lean-16-Conway-Homme-et-Oeuvre-Lean-Python.ipynb) donne le contexte humain, sans être bloquante.

**Statut du lac** : `knot_lean` est en research-HOLD théorie des nœuds (#2874) — baseline sorry réelle 8, synchronisée avec `lean-knot.yml` et `LEAN_INVENTORY.md` (cf. `knot_lean/README.md`, table des sorries).

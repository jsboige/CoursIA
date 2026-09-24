# Série Geometry — la preuve automatique en géométrie, de la figure à la preuve

La série **Geometry** applique le raisonnement symbolique aux théorèmes de géométrie élémentaire : elle ouvre la question — centrale pour l'IA — de **démontrer automatiquement** un énoncé géométrique, et de savoir *exactement* ce que la démonstration garantit. Là où SMT/Z3 **décide** sous contraintes et Lean **vérifie** des preuves formelles, cette série **traduit la géométrie en algèbre** (hypothèses et conclusion deviennent des polynômes) puis fait parler cette algèbre : test probabiliste, bases de Gröbner, méthode de Wu, et enfin pont vers la preuve formelle.

Le programme est **gradué** : chaque notebook principal ne suppose que ce qui le précède, un même théorème fil rouge (le milieu de l'hypoténuse équidistant des trois sommets) est traversé par les méthodes successives, et les résultats de recherche restent dans les accrétions `b` — le chemin principal se lit sans ouvrir de lettre. Cadre complet : Epic #17544.

## Le programme

| Pos. | Notebook | Public | Contenu | Statut |
|---|---|---|---|---|
| 01 | [Geometry-01-From-Figure-To-Equation.ipynb](Geometry-01-From-Figure-To-Equation.ipynb) | Découverte | De la figure à l'équation : coordonnées, hypothèses et conclusion en polynômes, vérification numérique sur figures aléatoires, pourquoi ce n'est pas une preuve, Schwartz–Zippel et la preuve probabiliste | Livré |
| 02 | Geometry-02 — Prouver par l'algèbre | Licence | Idéal engendré par les hypothèses, appartenance, bases de Gröbner (`sympy.groebner`), conditions de non-dégénérescence | À venir |
| 03 | [Geometry-03-Wu-Method.ipynb](Geometry-03-Wu-Method.ipynb) | Licence | Pseudo-division, ensemble caractéristique (basic-set de Chou), test de Wu, non-dégénérescences auto-générées ; vérification croisée Gröbner (Rabinowitsch) ; fil rouge (milieu de l'hypoténuse) et Ceva ; témoin négatif (papillon, composantes dégénérées) | Livré (#17511) |
| 03b | Geometry-03b — Décomposition de Ritt | Licence | Composantes dégénérées, le papillon, corpus historique de Chou | À venir |
| 04 | Geometry-04 — Raisonner comme un géomètre | Licence | Base de déduction à règles (DD) et raisonnement algébrique (AR), la moitié symbolique d'AlphaGeometry | À venir |
| 04b | Geometry-04b — IMO-AG-30 | Recherche | Wu associé à DD+AR (Sinha et al. 2024), proposeur neuronal | À venir |
| 05 | Geometry-05 — Pont formel | Recherche | Un théorème de 02/03 énoncé et prouvé en Lean/Mathlib : que garantit « prouvé par Gröbner » ? | À venir |

Les notebooks 01, 02 et 03 forment la **première volée** : ils se mergent ensemble, dans l'ordre — le premier état public de la série est déjà une progression complète.

## Le fil rouge

Le **théorème du milieu de l'hypoténuse** traverse 01, 02 et 03 :

- en 01, on le **vérifie numériquement** sur 10 000 figures, et on mesure ce que cette vérification prouve (preuve probabiliste Schwartz–Zippel) et ne prouve pas ;
- en 02, on le **démontre** : la conclusion appartient à l'idéal des hypothèses, décidée exactement par Gröbner ;
- en 03, on le **redémontre** par la méthode de Wu, avec les conditions de non-dégénérescence explicites.

Trois regards sur le même objet — on compare des *méthodes*, pas des exemples.

## Prérequis et coût

- **Environnement** : Python 3.10+, `sympy` + `numpy` + `matplotlib` (déjà présents dans le venv projet), kernel `python3`. Aucune API payante, aucun GPU, aucun réseau.
- **01** : ~5 s de bout en bout (10 000 tirages vectorisés), générateur semé — reproductibilité HIGH.
- **03** : ~3 s de bout en bout (chaînes caractéristiques déterministes, tie-break par expression) — reproductibilité HIGH, sorties committées sur `main`. Détail coût : bloc `metadata.cost` du notebook.
- **Publics** : Découverte (01) suppose la géométrie du lycée ; Licence (02–04) suppose 01 et une première familiarité avec l'algèbre linéaire ; Recherche (04b, 05) suppose la série ou une maturité en vérification formelle.

## Pourquoi une série de plus

Les systèmes de preuve géométriques automatisés connaissent un regain avec les LLM géométriques : l'étude *Wu's Method can Boost Symbolic AI to Rival Silver Medalists...* (Sinha et al., 2024, arXiv:2404.06405 — PDF archivé dans le gisement commun) montre qu'une méthode symbolique **classique** de 1977 résout encore des problèmes IMO que les moteurs neuronaux seuls ne résolvent pas. Comprendre Gröbner et Wu, c'est comprendre où le symbolique reste indispensable face au neuronal — et le notebook 05 posera la question de ce que ces preuves *garantissent* formellement. Ces résultats vivent dans les accrétions `b` (03b, 04b) : le chemin principal reste un cours progressif.

## Références

- Wu Wen-tsün, *On the decision problem and the mechanization of theorem proving in elementary geometry* (1978) — l'algorithme des ensembles caractéristiques.
- Shang-Ching Chou, *Mechanical Geometry Theorem Proving* (1988) — recueil des encodages classiques, repris par la basic-set du notebook 03.
- J. F. Ritt, *Differential Algebra* (1950) — théorie des ensembles caractéristiques, base de la décomposition (accrétion 03b).
- Sinha et al., *Wu's Method can Boost Symbolic AI to Rival Silver Medalists and AlphaGeometry to Outperform Gold Medalists at IMO Geometry* (2024), arXiv:2404.06405 — cité en « Pourquoi une série de plus ».

Série parente : [SymbolicAI](../README.md) — le cycle complet du raisonnement vérifiable.
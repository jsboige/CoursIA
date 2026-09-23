# Série Geometry — démonstration automatique en géométrie

La série **Geometry** applique les outils du raisonnement symbolique aux théorèmes de géométrie élémentaire. Elle ouvre une nouvelle famille du domaine SymbolicAI du dépôt : là où SMT/Z3 **décide** sous contraintes et Lean **vérifie** des preuves formelles, cette série **démontre automatiquement** des énoncés géométriques classiques par algèbre polynomiale — la méthode de Wu.

**Motivation.** Les systèmes de preuve géométriques automatisés connaissent un regain avec l'arrivée des LLM géométriques (AlphaGeometry et consœurs) : l'étude *Wu's Method can Boost Symbolic AI to Rival Silver Medalists on IMO Geometry Problems* (Sinha et al., 2024, arXiv:2404.06405) montre qu'une méthode symbolique *classique* — la méthode de Wen-tsün Wu (1977), fondée sur les ensembles caractéristiques de Ritt — résout 15/30 problèmes de la passerelle IMO-AG-30, dont deux que seuls les moteurs symboliques résolvent. Comprendre Wu, c'est comprendre où le symbolique reste indispensable face au neuronal.

## Notebooks

| # | Notebook | Contenu | Status |
|---|---|---|---|
| 1 | [Geometry-1-Wu-Method.ipynb](Geometry-1-Wu-Method.ipynb) | Méthode de Wu de zéro : pseudo-reste, ensemble caractéristique (basic-set de Chou), test de Wu, non-dégénérescences auto-générées, vérification croisée Groebner (Rabinowitsch). Preuves : milieu de l'hypoténuse, Ceva. Témoin négatif + diagnostic d'échec (papillon, composantes dégénérées) | ✅ livré |

## Prérequis et coût

- **Environnement** : Python 3.10+, `sympy` uniquement (déjà présent dans le venv projet).
- **Exécution** : ~3 s de bout en bout (kernel `python3`, CPU pur). Aucune API payante, aucun GPU, aucun réseau.
- **Reproductibilité** : HIGH — les chaines caractéristiques sont déterministes (tie-break par expression), les sorties committées sur `main`.
- Détail coût : bloc `metadata.cost` du notebook.

## Références

- Sinha et al., *Wu's Method can Boost Symbolic AI to Rival Silver Medalists on IMO Geometry Problems* (2024), arXiv:2404.06405 — PDF archivé dans le gisement commun `G:\Mon Drive\MyIA\IA\Bibliographie IA\Symbolic\`.
- Wu Wen-tsün, *On the decision problem and the mechanization of theorem proving in elementary geometry* (1978).
- Shang-Ching Chou, *Mechanical Geometry Theorem Proving* (1988) — recueil des encodages classiques.
- J. F. Ritt, *Differential Algebra* (1950) — théorie des ensembles caractéristiques.

## Fils à venir

- **Notebook 2** : la décomposition de Ritt (composantes dégénérées, ex. papillon) — la brique manquante du notebook 1.
- **Notebook 3** : le rejet angulaire (Wu&DD+AR) et le benchmark IMO-AG-30.

Série parente : [SymbolicAI](../README.md) — le cycle complet du raisonnement vérifiable.
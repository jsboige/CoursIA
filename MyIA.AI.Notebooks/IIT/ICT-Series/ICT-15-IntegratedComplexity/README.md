# ICT-15 — Integrated Complexity (convergence Φ/F/K et ses obstructions)

Sous-série **strate 4** de la série ICT : le **capstone cross-substrat**. Le carnet de tête teste la convergence des trois scalaires fondateurs — intégration causale ($\Phi$), surprise ($F$), compression ($K$) — sur des substrats non-LLM ; toute l'accrétion lettrée (15b → 15l) examine ensuite les **obstructions** : ce qui, dans un substrat, empêche les proxys de recoller en une mesure unique — et pourquoi ce motif de désaccord est lui-même informatif.

> [↑ Index ICT-Series](../README.md) · [Cadrage ICT-0](../ICT-0-Framing.md) · [Matrice des dissociations](../../../../docs/ict/dissociations-matrix.md) · Epic [#4588](https://github.com/jsboige/CoursIA/issues/4588)

## Ce que chaque carnet démontre

| Carnet | Ce qu'il démontre |
|---|---|
| [ICT-15 — Convergence Φ/F/K (capstone strate 4)](ICT-15-IntegratedComplexity-Python.ipynb) | L'hypothèse fondatrice : les classements produits par $\Phi$, $F$ et $K$ **convergent-ils** sur plusieurs substrats, comme le prédit l'idée d'un système qui modélise son monde ? Étend l'appareil d'ICT-Synthèse (EI/EC, contrôle shuffle) sur les substrats S1/S2/S3. |
| [ICT-15b — Sensibilité & canonicité (Huang 2019)](ICT-15b-SensitivityCanonicity-Python.ipynb) | Le théorème de Huang ($s(f) \geq \sqrt{\deg(f)}$, preuve spectrale) **transposé au zoo ICT** : la sensibilité locale `s_max` borne le degré global `deg_proxy` — un pont théorème ↔ banc mesuré (strate 5 théorie fondatrice, #7288). |
| [ICT-15c — Méta-proxy d'obstruction](ICT-15c-MetaProxyObstruction-Python.ipynb) | Lecture cohomologie-obstruction : quand plusieurs proxys (spectral, sensitivity, free-energy) ne « recollent » pas en une mesure unique, le **motif de leur désaccord** porte de l'information sur le substrat — l'obstruction elle-même est informative (#7395). |
| [ICT-15d — Cochaîne de Čech pondérée](ICT-15d-CechObstruction-Python.ipynb) | L'obstruction **intra-substrat** : une cochaîne de Čech pondérée discriminate les substrats (`NON_TRIVIAL` = les proxys ne se recollent pas en 1D) — au-delà de la dispersion d'échelle que mesurait la Phase Zéro. |
| [ICT-15e — Recouvrabilité et agentivité](ICT-15e-Bridge2-RecoverabilityAgency-Python.ipynb) | Au-delà du gain de réparation brut : la **trajectoire de réparation** post-ablation porte une signature temporelle propre (`s_max`, `slope_ratio`, `monotonicity`, `skewness`) que ne reproduisent ni marche aléatoire calibrée ni diffusion pure — recouvrabilité = agentivité. |
| [ICT-15f — Pont #1-bis : la famille découplée](ICT-15f-Bridge1bis-DecoupledFamily-Python.ipynb) | Le Pont #1 (« la stabilité locale $\sigma$ cause la récupérabilité ») a été **falsifié** sur la fronce (PR #8944) ; la famille découplée — $\sigma$ et largeur de bassin varient indépendamment par construction — tranche le négatif (#9531). |
| [ICT-15g — Test empirique de la borne de Huang](ICT-15g-EmpiricalHuangExploitation-Python.ipynb) | La borne de Huang sur les **graphes de transition** des trajectoires ICT : le banc hérité reste une transposition conjecturale (repères d'instrument, pas des théorèmes) ; le banc appris #17977 livre lui un verdict formel. Deux strates, deux statuts — dit honnêtement. |
| [ICT-15h — Pont #1-bis, régime asymétrique](ICT-15h-Bridge1bis-AsymmetricFamily-Python.ipynb) | Chantier 2/3 : la famille de double-puits **asymétriques** confirme le négatif de $\sigma$ — pas de pouvoir prédictif propre de la courbure locale une fois largeur ET barrière contrôlées. |
| [ICT-15i — Pont #1-bis, paysage 2D anisotrope](ICT-15i-Bridge1bis-2DLandscape-Python.ipynb) | Chantier 3/3 : en 2D, le Hessien donne une courbure **par direction propre** — et clôt l'Epic #9531 : aucun résumé scalaire de la courbure ne prédit la récupérabilité. |
| [ICT-15j — Discriminant Čech par nerf simplicial](ICT-15j-NerveDiscriminant-Python.ipynb) | Le nerf simplicial (GUDHI) distingue un relief topologique que la SVD rate : sur le contre-exemple Axelrod, cocycle et `obstruction_ratio` nuls alors que le verdict SVD reste `NON_TRIVIAL` — le rang spectral n'est pas la cohomologie. |
| [ICT-15k — Recollement des macrocells](ICT-15k-RecollementMacroCells-Python.ipynb) | Le quadtree de Hashlife comme **espace étalé** : le recouvrement des macrocells est imposé par le substrat ; si la clé de mémoïsation ignore une frontière, un cycle concret l'exploite et produit un témoin qui **gagne contre l'agent**. |
| [ICT-15l — Indépendance au générateur](ICT-15l-IndependanceGenerateur-Python.ipynb) | Le relief `b1` mesuré par ICT-15j sur l'Axelrod régénéré survit-il au **contrôle de dimension** ? — la nouveauté stratégique ne doit pas n'être qu'un artefact du mécanisme qui injecte la nouveauté. |

## Place dans l'escalier

Cœur de la strate 4 (ICT-14 → ICT-20) : après la jambe représentationnelle d'[ICT-14](../ICT-14-FreeEnergySurprise/README.md), la série fait converger ses trois scalaires fondateurs sur des substrats non-LLM, puis sonde les obstructions de cette convergence jusqu'au recollement (15k) et au contrôle de générateur (15l). Les ponts #1-bis (15f/h/i) ferment l'Epic #9531 par une **falsification assumée** ; le banc de recollement [ICT-34](../ICT-34-BancRecollementLectures-Python.ipynb) prolonge cette accrétion en strate 5.

## Instruments

Organes : `sensitivity`, `meta_proxy`, `cech_obstruction`, `nerve_discriminant`, `basin_family` — voir la table des organes de l'[index de série](../README.md) et le paquet [`ict/`](../ict/). L'état scientifique de chaque claim (beaucoup restent des **hypothèses** ouvertes dans la matrice) se lit dans la [matrice des dissociations](../../../../docs/ict/dissociations-matrix.md).

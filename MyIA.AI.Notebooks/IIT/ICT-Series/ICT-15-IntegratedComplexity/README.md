# ICT-15-IntegratedComplexity — la convergence Φ/F/K et ses obstructions

Sous-série de la [série ICT](../README.md). Le retour à la théorie fondatrice : les trois scalaires $\Phi / F / K$ convergent sur un banc cross-substrat — puis la sous-série éprouve ce verdict par raffinement, obstructions adversariales, ponts falsifiables et discriminants topologiques.

| Carnet | Ce qu'il démontre et sa place dans l'escalier |
|---|---|
| [ICT-15-IntegratedComplexity-Python](ICT-15-IntegratedComplexity-Python.ipynb) | **Tête de la sous-série** — convergence Φ/F/K sur le banc cross-substrat, gate de convergence sur le squelette de Thom |
| [ICT-15b-SensitivityCanonicity-Python](ICT-15b-SensitivityCanonicity-Python.ipynb) | **Raffinement : canonicité** — la stabilité du verdict de convergence aux perturbations contrôlées du substrat (bruit d'implémentation, recalibrage des coarse-grainings), protocole de re-mesure multi-graines |
| [ICT-15c-MetaProxyObstruction-Python](ICT-15c-MetaProxyObstruction-Python.ipynb) | **Obstruction 1 : méta-proxy** — quand un proxy Φ/F/K cache une divergence de régime (faux-positif de convergence) ; banc adversarial sur substrats où le triplet co-varie par construction |
| [ICT-15d-CechObstruction-Python](ICT-15d-CechObstruction-Python.ipynb) | **Obstruction 2 : cohomologique** — cochaîne de Čech pondérée, une obstruction intra-substrat qui ne se réduit ni à un proxy Φ/F/K ni à la sensibilité de Huang ; module `ict.cech_obstruction` |
| [ICT-15e-Bridge2-RecoverabilityAgency-Python](ICT-15e-Bridge2-RecoverabilityAgency-Python.ipynb) | **Pont no 2** — la recouvrabilité *est* l'agentivité : cinq bridges falsifiables ; la récupération d'un état après `do(·)` discrimine l'agentivité (un dissipateur pur ne recouvre pas) |
| [ICT-15f-Bridge1bis-DecoupledFamily-Python](ICT-15f-Bridge1bis-DecoupledFamily-Python.ipynb) | **Pont no 1-bis, chantier 1/3** — la famille découplée (σ ⟂ largeur de bassin) tranche le négatif de σ : c'est la largeur de bassin qui porte le signe qui falsifiait ICT-15e |
| [ICT-15g-EmpiricalHuangExploitation-Python](ICT-15g-EmpiricalHuangExploitation-Python.ipynb) | **Exploitation empirique de la sensibilité (Huang 2019)** — le théorème appliqué aux substrats réels de la série (tri, Gray-Scott, Axelrod) : la dépendance multilinéaire du degré comme lecteur orthogonal du banc |
| [ICT-15h-Bridge1bis-AsymmetricFamily-Python](ICT-15h-Bridge1bis-AsymmetricFamily-Python.ipynb) | **Pont no 1-bis, chantier 2/3** — double-puits asymétriques : la courbure locale σ n'a aucun pouvoir prédictif propre pour la récupérabilité une fois la largeur *et* la barrière contrôlées |
| [ICT-15i-Bridge1bis-2DLandscape-Python](ICT-15i-Bridge1bis-2DLandscape-Python.ipynb) | **Pont no 1-bis, chantier 3/3 (clôture)** — paysage 2D anisotrope : aucun résumé scalaire de σ ne prédit la récupérabilité ; les trois régimes convergent — c'est la géométrie du bassin qui gouverne |
| [ICT-15j-NerveDiscriminant-Python](ICT-15j-NerveDiscriminant-Python.ipynb) | **Discriminant topologique** — nerf simplicial (gudhi) sur les fenêtres × proxys, comptage des classes $H^1$ persistantes (b1) : le verdict SVD d'`ict.cech_obstruction` consultait le rang spectral, pas la cohomologie du nerf |
| [ICT-15k-RecollementMacroCells-Python](ICT-15k-RecollementMacroCells-Python.ipynb) | **Recollement géométrique** — le quadtree de Hashlife comme espace étalé : recouvrement imposé par le substrat, fibres et transports réels, compatibilité vérifiée empiriquement contre le moteur certifié, recollement cassé converti en témoin qui paie (Dutch book) |
| [ICT-15l-IndependanceGenerateur-Python](ICT-15l-IndependanceGenerateur-Python.ipynb) | **Audit du discriminant** — le relief b1 passe-t-il le contrôle de dimension ? Verdict pré-enregistré `CONFONDU_AVEC_LA_DIMENSION` : le relief accompagne le turnover stochastique de population finie, pas la nouveauté stratégique |

Le retour vers la [série ICT](../README.md) se fait depuis le dernier carnet.

# ICT-19 — Enjeu Battery (la batterie de l'ENJEU)

Sous-série **strate 4** de la série ICT (théorie fondatrice cross-substrat, GPU-free) : le banc qui met les **scalaires fondateurs à l'épreuve d'un enjeu**. La distinction directrice : un **agent** défend un point de consigne (il a un enjeu), un **pur dissipateur** n'en a pas — et la mesure doit séparer les deux sans complaisance.

> [↑ Index ICT-Series](../README.md) · [Cadrage ICT-0](../ICT-0-Framing.md) · [Matrice des dissociations](../../../../docs/ict/dissociations-matrix.md) · Epic [#4588](https://github.com/jsboige/CoursIA/issues/4588)

## Ce que chaque carnet démontre

| Carnet | Ce qu'il démontre |
|---|---|
| [ICT-19 — La batterie de l'ENJEU](ICT-19-EnjeuBattery-Python.ipynb) | **Distinguer** un agent (Gray-Scott S4 : dissipe *et* défend un point de consigne) d'un pur dissipateur. L'enjeu `I_stake` (récupérabilité Levin) est **mesurablement distinct** du moyen `I_thermo` ($\sigma$) : la batterie sépare ce qui se maintient de ce qui se dissipe seulement. |
| [ICT-19b — Raffinement et résolution des stubs](ICT-19b-EnjeuBattery-Raffinement-Python.ipynb) | La mesure raffinée au-delà du `stake_index` brut : `ict.agency.repair_gain` (réaction-diffusion vs diffusion pure) et les modules d'agence — sur S4, le gain de réparation est mesuré avec son incertitude. Le raffinement transforme l'indice en instrument. |

## Place dans l'escalier

Dans la strate 4 (ICT-14 → ICT-20), cette sous-série apporte le scalaire **enjeu** au banc cross-substrat, entre la convergence Φ/F/K d'[ICT-15](../ICT-15-IntegratedComplexity/README.md) et la calibration de méthode d'[ICT-20](../ICT-20-FeatureCatastrophes/README.md). Le `repair_gain` qu'elle introduit relie l'enjeu à la recouvrabilité d'ICT-15e, et la batterie servira de gabarit aux bancs GPU-free de la strate 5.

## Instruments

Organes : [`ict.agency`](../ict/agency.py) (`repair_gain` et les mesures d'agence : ablation, structure, similarité spectrale) — voir la table des organes de l'[index de série](../README.md) et le paquet [`ict/`](../ict/). L'état scientifique de chaque claim se lit dans la [matrice des dissociations](../../../../docs/ict/dissociations-matrix.md).

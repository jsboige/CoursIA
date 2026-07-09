# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks). Les index de cellule sont absolus (toutes cellules : markdown + code), conformément à la convention `extract_readme_figures.py`. Les figures couvrent les strates 1-4 stables ; le capstone [ICT-Synthese-CrossSubstrat](../ICT-Synthese-CrossSubstrat.ipynb) (strate 5) est illustré par sa convergence Φ/F/K sur quatre substrats et sa jambe temporelle de réversibilisation (Epic #4588).

## ict1-phitrajectories.png

- **Source** : notebook `ICT-1-PhiTrajectories.ipynb` (cellule 12, output 0)
- **Alt-text (FR)** : Trajectoires de Phi : paysage de Phi et suivi le long d'un attracteur (pulsations), photographie IIT mise en mouvement avec le vrai PyPhi.
- **Poids** : 52.2 KB (natif)

## ict2-selfsorting.png

- **Source** : notebook `ICT-2-SelfSortingMorphogenesis.ipynb` (cellule 7, output 0)
- **Alt-text (FR)** : Tri auto-organisé comme morphogenèse : trajectoire dans le morphospace, robustesse aux cellules défectueuses et auto-réparation.
- **Poids** : 40.2 KB (natif)

## ict8-attractor.png

- **Source** : notebook `ICT-8-AttractorLandscapesEWS.ipynb` (cellule 3, output 0)
- **Alt-text (FR)** : Paysages d'attracteurs et signaux précurseurs : bistabilité, bifurcation pli et early-warning signals sur le modèle de pâturage de May.
- **Poids** : 55.1 KB (natif)

## ict9-gray-scott.png

- **Source** : notebook `ICT-9-AgencyRegeneration.ipynb` (cellule 3, output 0)
- **Alt-text (FR)** : Agence et régénération : morphogenèse réaction-diffusion de Gray-Scott, ablation puis contraste de deux mondes contrefactuels (régénération vs dissolution).
- **Poids** : 51.8 KB (natif)

## ict13-axelrod.png

- **Source** : notebook `ICT-13-AxelrodStrategicMorphodynamics.ipynb` (cellule 13, output 0)
- **Alt-text (FR)** : Morphodynamique stratégique d'Axelrod : tournoi de stratégies du dilemme du prisonnier itéré, dynamique de réplication et bassins d'invasion.
- **Poids** : 46.7 KB (natif)

## ict14-freeenergy.png

- **Source** : notebook `ICT-14-FreeEnergySurprise.ipynb` (cellule 4, output 0)
- **Alt-text (FR)** : Surprise et énergie libre : free energy et expected free energy comme substrat computationnel de l'anticipation, jambe représentationnelle du triplet fondateur.
- **Poids** : 132.0 KB (natif)

## ict16-mdl-bosse.png

- **Source** : notebook `ICT-16-MDLTwoPartCode.ipynb` (cellule 11, output 0)
- **Alt-text (FR)** : Bosse complexite-entropie (Crutchfield-Feldman 1998) : la complexite statistique (longueur de code du modele, en bits) passe par un maximum a entropie intermediaire, entre le determinisme (H->0, C->0) et le bruit iid (H->H1, C->0). Nuage des trajectoires echantillonnees + mediane lissee par bucket + marqueur du pic.
- **Poids** : 57.0 KB (PIL optimise)

## ict-synthese-gate4-phifk.png

- **Source** : notebook `ICT-Synthese-CrossSubstrat.ipynb` (cellule 23, output 5)
- **Alt-text (FR)** : Capstone ICT-Synthese gate 4 : convergence Phi/F/K sur quatre substrats (tri auto-organise, bistable, replicateur d'Axelrod, activations SAE d'un LLM). Barres groupees par substrat, trois jambes (Phi = ec_gain, F = fe_gain, K = k_gain). Phi et F covarient et ordonnent les substrats a l'identique (tri > replicateur > bistable > LLM, tau de Kendall Phi-F = +1.00) ; K ordonne autrement (replicateur et bistable au-dessus du tri). Le substrat LLM, le plus riche en representations, est le plus faible sur les trois jambes.
- **Poids** : 20.0 KB (PIL optimise)

## ict-synthese-gate5-reversibilisation.png

- **Source** : notebook `ICT-Synthese-CrossSubstrat.ipynb` (cellule 26, output 2)
- **Alt-text (FR)** : Capstone ICT-Synthese gate 5 : jambe temporelle de l'emergence (ICT-18 reversibilisation). Par substrat (tri, bistable, replicateur, LLM), production d'entropie sigma_real et distance a la chaine reversibilisee, sur echelle symlog. Le tri est fortement irreversible (sigma eleve, trajectory directionnelle) ; le bistable est quasi-nul (reversible, equilibre detaille satisfait) ; le replicateur et le LLM restent faibles. L'asymetrie temporelle discrimine les substrats de facon orthogonale aux jambes Phi/F/K.
- **Poids** : 21.2 KB (PIL optimise)

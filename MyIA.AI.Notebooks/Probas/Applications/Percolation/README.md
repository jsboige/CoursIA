# Percolation supercritique

[← Série Probas](../../README.md)

La **percolation de liens** sur un **tore fini** comme **proxy fini** du graphe
transitif infini de la théorie : on mesure ce qui distingue le régime
**supercritique** (p > p_c) du régime sous-critique (p < p_c) et du **point
critique** (p ≈ p_c). Simulation-first : on fait *voir* les trois régimes
(figure), puis on mesure (multi-seed) la queue origine-fixe
`P_p(n ≤ |C_o| < ∞)` avant d'énoncer le théorème de *supercritical sharpness*.

| Composant | Notebook | Stack | Ce qu'il apporte |
|-----------|----------|-------|------------------|
| [Percolation-01-Supercritique-Python](Percolation-01-Supercritique-Python.html) | 1 (Python) | Python 3 + `networkx` | Tore carré (degré 4, `p_c(bond, ℤ²) = 1/2`) et tore hexagonal (degré 3, `p_c ≈ 0.6527`) — trois régimes mesurés, géant du tore, vitesse de disparition `Φ(n) ~ √n` |
| [Percolation-02-Lean](Percolation-02-Lean.html) | 2 (Lean 4) | Lean 4 + Mathlib (`percolation_lean`) | Compagnon exécutable du lake : configurations d'arêtes ouvertes, Harris–Kleitman fini, connexité croissante, composantes, frontière isopérimétrique avec profil calculé sur `C₃`/`C₄` |
| [Percolation-03-Critique-Python](Percolation-03-Critique-Python.html) | 3 (Python) | Python 3 + `networkx` | Physique du point critique : loi d'échelle finie `M(L, 1/2)/L² ~ L^{-β/ν}`, distribution de tailles `P(s) ~ s^{-τ'}`, convergence `p_c(L) → 1/2`. Sweep `L ∈ {8,16,32,64}` × `p ∈ {0.45,…,0.55}` × 32 seeds = 640 simulations `networkx.connected_components` canonique |

## Formalisation Lean (`percolation_lean/`)

Le lake [`percolation_lean/`](percolation_lean/) porte la jambe formelle du
duo : noyau fini de percolation **prouvé sans `sorry`** (configurations,
composantes, connexité, frontière isopérimétrique finie — modules `Basic`,
`Connectivity`, `Components`, `Boundary`, `Examples`, paires FR/EN selon la
convention #4980), `proof-integrity` câblé en CI. Le théorème de l'article
reste un **horizon de recherche** : le lake distingue ce qui est prouvé, ce qui
vient de Mathlib et ce qui est hors portée (voir #14871).

- Diskin, Easo, Radhakrishnan, Sudakov & Tassion, *Supercritical sharpness of
  percolation*, arXiv:2603.03257 (math.PR, v1, CC-BY 4.0) — théorème de la
  section 3.0.

## Plan de croissance

La sous-série garde son emplacement dans `Applications/` (arbitrage #16231,
articulé à la hiérarchie Probas #14873) et grandit par paliers numérotés — le
plan détaillé, avec pour chaque carnet ce qu'il démontre, l'organe qu'il
appelle et son prérequis, vit dans l'issue de suivi **#19494** :

| # | Carnet prévu | Palier |
|---|--------------|--------|
| 03 | `Percolation-03-Critique-Python` | le régime critique comme limite finie : seuil dépendant de la taille, loi de puissance des composantes au point critique |
| 04 | `Percolation-04-Sharpness-Python` | le théorème mesuré : la queue origine-fixe raidit quand `p ↓ p_c` (sharpness supercritique) |
| 04 | `Percolation-04-Sharpness-Lean` (exploratoire) | jumeau formel du palier 4 : énoncé fini paramétrique au-dessus du socle prouvé du lake |

## Pont vers la série ICT

Le notebook conserve un **pont structurel** vers la série **ICT** (modèle
d'adoption collective) : même **forme** — une variable continue (p ou ρ) et un
**changement de nature** du plus grand objet au franchissement d'un seuil —
mais **deux modèles distincts** (seuil d'adoption vs seuil de connectivité
aléatoire). Le pont est une analogie de structure, pas une identité.

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
| [Percolation-01-Supercritique-Python](Percolation-01-Supercritique-Python.ipynb) | 1 (Python) | Python 3 + `networkx` | Tore carré (degré 4, `p_c(bond, ℤ²) = 1/2`) et tore hexagonal (degré 3, `p_c ≈ 0.6527`) — trois régimes mesurés, géant du tore, vitesse de disparition `Φ(n) ~ √n` |
| [Percolation-02-Lean](Percolation-02-Lean.ipynb) | 2 (Lean 4) | Lean 4 + Mathlib (`percolation_lean`) | Compagnon exécutable du lake : configurations d'arêtes ouvertes, Harris–Kleitman fini, connexité croissante, composantes, frontière isopérimétrique avec profil calculé sur `C₃`/`C₄` |
| [Percolation-03-Critique-Python](Percolation-03-Critique-Python.ipynb) | 3 (Python) | Python 3 + `networkx` | Physique du point critique : loi d'échelle finie `M(L, 1/2)/L² ~ L^{-β/ν}`, distribution de tailles `P(s) ~ s^{-τ'}`, convergence `p_c(L) → 1/2`. Sweep `L ∈ {8,16,32,64}` × `p ∈ {0.45,…,0.55}` × 32 seeds = 640 simulations `networkx.connected_components` canonique |
| [Percolation-03b-Critique-L128-L256](Percolation-03b-Critique-L128-L256.ipynb) | 3b (Python) | Python 3 + `networkx` | Extension du carnet 03 aux tailles `L ∈ {128, 256}` pour la convergence asymptotique. Fit log-log sur 6 points (L = 8, 16, 32, 64, 128, 256) : β/ν = 0.1065, τ' = 2.188, p_c(L) → 1/2 monotone. Sweep `L ∈ {128, 256}` × `p ∈ {0.45,…,0.55}` × 32 seeds = 320 simulations ~48 s |
| [Percolation-03c-Critique-L512](Percolation-03c-Critique-L512.ipynb) | 3c (Python) | Python 3 + `networkx` | Extension du carnet 03b à L = 512 pour la convergence asymptotique. Fit log-log sur 7 points (L = 8, 16, 32, 64, 128, 256, 512) : β/ν = 0.1062 (cible 0.1042, R²=0.977, std_err=0.007 — convergence asymptotique bloquée aux corrections d'échelle finie), p_c(L) → 1/2 monotone (écart 0.0013 à L=512). Sweep `L = 512` × `p ∈ {0.45,…,0.55}` × 32 seeds = 160 simulations ~186 s |
| [Percolation-04-Sharpness-Python](Percolation-04-Sharpness-Python.ipynb) | 4 (Python) | Python 3 + `networkx` | Palier 4 du plan #19494 : mesure de la queue supérieure `Ψ(n) = P(\|C_o\| ≥ n)` sur grille `L ∈ {64, 128, 256, 512}` × `p ∈ {0.50, …, 0.70}` × 32 seeds = 1024 simulations ~170 s. Comparaison au théorème de *supercritical sharpness* (Diskin-Easo-Radhakrishnan-Sudakov-Tassion, arXiv:2603.03257 §3.0). **Verdict** : palier non mesurable aux seuils `n ∈ {1, 2, …, 128}` à L ≤ 512 — le fit log-y de `Ψ(n)` est dominé par la transition initiale (Psi(1)=1 → Psi(2)~0.7) et non par la décroissance exponentielle sharpness (qui exigerait `n ~ médiane du géant`). L'alpha mesuré **décroît** avec p, opposé à la cible `(p - 1/2)^{d-1} = p - 1/2` |
| [Percolation-04-Sharpness-Lean](Percolation-04-Sharpness-Lean.ipynb) | 4 (Lean 4) | Lean 4 + Mathlib (`percolation_lean`) | Jumeau formel du palier 4 (#19494, item 3) : module `Sharpness` du lake — inégalité de sharpness finie `#(smallClusterEvent G v k) ≤ Σ_{A ∋ v, \|A\| ≤ k} 2^(N−\|δA\|)` par comptage de candidats confinés (frontière pleine ⇒ arêtes forcées fermées), forme **mixte** de Harris–Kleitman (anti-corrélation croissant × décroissant), témoins exacts calculés sur `C₃` (`2/8`) et `C₄` (`4/16`) |
| [Percolation-05-Dimension-Fractale-Effondrement-Python](Percolation-05-Dimension-Fractale-Effondrement-Python.ipynb) | 5 (Python) | Python 3 + `numpy` (union-find) | Palier 5 du plan #19494 — ce que la série ne mesurait pas : la **dimension fractale** `d_f` de l'amas critique par **comptage de boîtes** (union-find Hoshen-Kopelman from scratch, oracle croisé contre `networkx`), l'exposant `ν` par **deux routes indépendantes** (effondrement d'échelle *data collapse* avec contrôle négatif, pente du pic `dM/dp\|_{p_c} ~ L^{1/ν}`), et le **contrôle croisé** `d_f = d − β/ν` entre la dimension par boîtes et le `β/ν` de la série 03. Sweep `L ∈ {32,48,64,96,128}` × `p ∈ {0.46,…,0.54}` × 15 seeds = 1000 simulations ~42 s |

## Formalisation Lean (`percolation_lean/`)

Le lake [`percolation_lean/`](percolation_lean/) porte la jambe formelle du
duo : noyau fini de percolation **prouvé sans `sorry`** (configurations,
composantes, connexité, frontière isopérimétrique finie et inégalité de
sharpness finie (`card_smallClusterEvent_le`, dont l'inégalité de l'article
arXiv:2603.03257 §3.0 est la limite) — modules `Basic`,
`Connectivity`, `Components`, `Boundary`, `Examples`, `Sharpness`, paires FR/EN
selon la convention #4980), `proof-integrity` câblé en CI. Le théorème de l'article
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
| 05 | `Percolation-05-Dimension-Fractale-Effondrement-Python` | la géométrie fractale et l'effondrement : `d_f` par comptage de boîtes, `ν` par deux routes indépendantes, contrôle croisé `d_f = d − β/ν` |

## Pont vers la série ICT

Le notebook conserve un **pont structurel** vers la série **ICT** (modèle
d'adoption collective) : même **forme** — une variable continue (p ou ρ) et un
**changement de nature** du plus grand objet au franchissement d'un seuil —
mais **deux modèles distincts** (seuil d'adoption vs seuil de connectivité
aléatoire). Le pont est une analogie de structure, pas une identité.

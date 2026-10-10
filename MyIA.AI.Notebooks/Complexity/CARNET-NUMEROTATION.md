# Carnet de numérotation — série Complexity

**Statut** : curriculum arrêté par décision ai-01 du 2026-09-23, EPIC [#17063](https://github.com/jsboige/CoursIA/issues/17063). Ce carnet est la **vue formelle** du chemin principal et des accrétions, à consulter avant d'ajouter un notebook à la série.

## Chemin principal (positions 01-07, numéros nus)

| Pos. | Notebook principal | Public | Notion introduite |
|---|---|---|---|
| 01 | Compter des pas | Découverte | Taille d'entrée, croissances ($n \log n$, $n^2$, $2^n$), machine de Turing pas-à-pas |
| 02 | Vérifier ou trouver : P, NP, certificat, réduction | Découverte | Définitions P/NP, une réduction exécutée (subset-sum, backtracking Sudoku-15) |
| 03 | Plus de temps, plus de problèmes | Licence | Hiérarchie en temps, diagonalisation, limite d'une simulation bornée |
| 04 | Décider sans connaître la suite | Licence | Algorithmes en ligne, analyse compétitive (skis, pagination, secrétaire 1/e) |
| 05 | Compter est plus dur que vérifier | Licence | Classe #P, déterminant vs permanente, frontière quantique |
| 06 | Simuler un circuit quantique classiquement | Licence | Coût de la simulation classique : barrière $O(2^n)$ sur $n$ qubits, simulation **Clifford** en $O(n^2)$ (Gottesman–Knill), échantillonner $\neq$ calculer la distribution exacte, inclusion BQP ⊆ PP ⊆ P#P au niveau **Cité** |
| 07 | Complexité de Kolmogorov bornée : séquences à mémoire limitée | Recherche | $K(x)$ opérationnalisée à **mémoire bornée** (Strannegård, Nizamani, Sjöberg & Engström, AGI 2013) — arrivée de `Search/Applications` (ex-App-34), renumérotée 07 |

> **État mesuré au 2026-10-10.** Les deux positions du chemin principal qui portaient « (à venir) » sont renseignées : la **06** est livrée (PR #19771, `Complexity-06-Simuler-Circuit-Quantique-Classiquement-Python.ipynb`) et la **07** est occupée par *Complexité de Kolmogorov bornée*, déjà livrée et documentée comme « renumérotée 07 » par le README de série.
>
> Le sujet initialement annoncé pour 07, **« La chaîne des inclusions : L ⊆ NL ⊆ P ⊆ NP »**, n'est **pas livré** et n'a plus de position sur le chemin principal — l'historique est conservé ci-dessus plutôt que réécrit. Lui rendre une position (un **08**, ou une accrétion **`07b`**) est un **arbitrage de curriculum** : il appartient à ai-01 au titre de l'EPIC [#17063](https://github.com/jsboige/CoursIA/issues/17063), au même titre que la mention « Licence » de cette même ligne, qui ne décrit plus la position réellement occupée.

## Accrétions (`b` par défaut, `c`/`d` si le palier en compte déjà un)

| Position de base | Accrétion | Hommage fondateur | Matière |
|---|---|---|---|
| 03 | **03b** — Hartmanis–Stearns 1965 | Juris Hartmanis & Richard Stearns (prix Turing 1993) | Théorème de hiérarchie en temps $\mathrm{TIME}(f) \subsetneq \mathrm{TIME}(f \log f)$, diagonalisation |
| 03 | **03c** — Zoo et oracles | Scott Aaronson (fondateur Complexity Zoo 2004), Baker–Gill–Solovay 1975 | Navigation dans le Zoo, barrière de relativisation |
| 04 | **04b** — Conjectures online 2026 | Sahil Singla, Christian Coester, Elias Koutsoupias, Marek Zbysiński | Secrétaire matroïdal, conjecture k-server |
| 04 | **04c** — k-server, work function | Manasse, McGeoch & Sleator ; Coester, Koutsoupias, Zbysiński | Work Function Algorithm (DP exact), duel WFA vs LRU/FIFO |
| 04 | **04d** — Secrétaire matroïdal | Sahil Singla (conjecture 2007) | Banc P[accept \| e ∈ OPT], garantie 1/4 |
| 05 | **05b** — La permanente, frontière quantique | Scott Aaronson & Alex Arkhipov (2011) | BosonSampling, TV vs loi $\lvert\mathrm{perm}\rvert^2$ |
| 06 | **06b** — Aaronson–Gottesman 2004 | Scott Aaronson & Daniel Gottesman (*Improved Simulation of Stabilizer Circuits*) | Formalisme stabilisateur, port CHP, banc discriminant Clifford |

## Règles de fabrication

1. **Chaque notebook principal ne suppose que ce qui le précède.** Étiquette `Public` (Découverte / Licence / Recherche) sur la première cellule.
2. **Aucun résultat de recherche sur le chemin principal.** Preprints, conjectures et chronologies historiques vont en `b` (ou `c`/`d`).
3. **Chaque accrétion s'ouvre** sur un lien vers sa base, et pose les prérequis qu'elle ajoute.
4. **Rien de validé n'est retiré.** Bancs et croisements migrent en `b` avec sorties re-exécutées (C.2).
5. **Trois exercices par notebook principal** (C.1 : stubs non bloquants).
6. **README de série** : la gradation reste visible (colonnes Public + Accrétion + Hommage).

## Renumérotations en cours

| Date | Geste | PR |
|---|---|---|
| 2026-10-07 | `Complexity-06-Aaronson-Dequantification-Stabilizer.ipynb` → **`Complexity-06b-AaronsonGottesman-Dequantification-Python.ipynb`** | [#19691](https://github.com/jsboige/CoursIA/pull/19691) |

Ancien nom à éviter dans les nouveaux liens : `Complexity-06-Aaronson-Dequantification-Stabilizer`. Nouveau nom canonique : `Complexity-06b-AaronsonGottesman-Dequantification-Python`.

## Voir aussi

- EPIC [#17063](https://github.com/jsboige/CoursIA/issues/17063) — décision ai-01 et proposition fondatrice
- `.claude/rules/notebook-accretion-numbering.md` — règle formelle d'accrétion
- README de la série — la table de navigation à jour

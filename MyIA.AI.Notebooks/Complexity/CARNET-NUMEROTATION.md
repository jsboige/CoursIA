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
| 06 | Simuler un circuit quantique classiquement | Licence | (à venir) Pourquoi exponentiel en général, où c'est facile (Clifford) |
| 07 | La chaîne des inclusions : L ⊆ NL ⊆ P ⊆ NP | Licence | (à venir) Carte de la hiérarchie |

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

# Ledger — Issue #15615 (gradation GameTheory, strate "Fondations")

> **Bornage strict** : ce ledger couvre **la strate "Fondations" de la série GameTheory** (carnets 02 et 03, soit 15 notebooks sur `origin/main` au 2026-09-28). Les carnets 04-Nash, 05-ZeroSum et au-delà font l'objet d'un ledger suivant si l'arbitrage du tableau consolidé le demande.

## Origine

Issue #15615 — audit de gradation demandé en réponse au nit user du 2026-09-11 sur la renumérotation mécanique #15586/#15613 : « remettre un peu de cohérence dans la gradation ». Le présent ledger applique le scope 1 de l'acceptance (« tableau de gradation ») sur la **strate des fondations** (carnets 02 + 03), pas sur l'ensemble de la série (100 carnets au 2026-09-28).

## Méthode

Pour chaque carnet :

1. **Prérequis** : carnets dont la section 1 déclare explicitement les acquis utilisés (lecture du front-matter, de la cellule d'introduction, des liens de navigation).
2. **Concepts introduits** : première section markdown qui définit une notion nouvelle (ex. `## 1. Definition formelle`, `## 1. La distance d'un jeu à l'autre`).
3. **Difficulté** : échelle **Basse / Moyenne / Haute / Très haute**, mesurée sur la combinatoire du sujet et la longueur du carnet (cellules total / cellules code) — la longueur est un **proxy** de difficulté technique, pas un verdict.
4. **Jumeau** : `True` si le carnet existe en deux versions (Python + C#/.NET, ou track principal + track Lean).

## Tableau de gradation — strate "Fondations"

| # | Carnet | Prérequis | Concepts introduits | Cells | Diff. | Jumeau |
|---|---|---|---|---:|---|---|
| 02 | [GameTheory-02-NormalForm](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-02-NormalForm.ipynb) | 01-Setup | Jeu sous forme normale $(N,S,u)$, profil, fonction d'utilité $u_i : S \to \mathbb{R}$ | 47 (16 code) | **Basse** | Oui (C#) |
| 02-cs | [GameTheory-02-NormalForm-Csharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-02-NormalForm-Csharp.ipynb) | 01-Setup + 02-NormalForm | Implémentation C#/.NET from-scratch de la classe `NormalFormGame` | 33 (12 code) | Basse | Oui (Py) |
| 02-P2 | [GameTheory-02-NormalForm-Part2-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-02-NormalForm-Part2-Python.ipynb) | 02-NormalForm | Support enumeration, équilibre mixte NxN, vérification `nashpy` | 34 (14 code) | Moyenne | Oui (C#) |
| 02-P2-cs | [GameTheory-02-NormalForm-Csharp-Part2](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-02-NormalForm-Csharp-Part2.ipynb) | 02-NormalForm-Csharp + 02-P2 | Support enumeration en C#/.NET | 36 (14 code) | Moyenne | Oui (Py) |
| 02b | [GameTheory-02b-Lean-Definitions](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-02b-Lean-Definitions.ipynb) | 02-NormalForm | Formalisation Lean 4 (Partie 4 de la série) — kernel Lean 4 WSL | 52 (21 code) | Moyenne | Non (track Lean séparé) |
| 02c | [GameTheory-02c-Travelers-Dilemma](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-02c-Travelers-Dilemma.ipynb) | 02-NormalForm | Fonction de paiement, raisonnement sur un cas non-trivial (Traveler's Dilemma) | 32 (8 code) | Moyenne | Oui (C#) |
| 02c-cs | [GameTheory-02c-Travelers-Dilemma-Csharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-02c-Travelers-Dilemma-Csharp.ipynb) | 02c + 02-NormalForm-Csharp | Twin C# du 02c | 29 (8 code) | Moyenne | Oui (Py) |
| 03 | [GameTheory-03-Topology2x2](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-03-Topology2x2.ipynb) | 02-NormalForm | Représentation ordinale (rangs 1-4), 576 jeux 2x2, archétypes Robinson-Goforth | 82 (26 code) | **Moyenne** | Oui (C#) |
| 03-cs | [GameTheory-03-Topology2x2-Csharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-03-Topology2x2-Csharp.ipynb) | 03 + 02-NormalForm-Csharp | Twin C# classification ordinale from-scratch | 40 (13 code) | Moyenne | Oui (Py) |
| 03a | [GameTheory-03a-Chemins-de-Swaps](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-03a-Chemins-de-Swaps.ipynb) | 03 + 03b | Distance de swap, BFS sur 576 sommets, sphères | 33 (13 code) | Haute | Non |
| 03b | [GameTheory-03b-Chambres-et-Murs](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-03b-Chambres-et-Murs.ipynb) | 03-Topology2x2 | Ordres faibles $\mathbb{R}^4$, murs (joints de codimension), botanique des jeux à égalités | 38 (13 code) | Haute | Non |
| 03c | [GameTheory-03c-Le-Joueur-LLM](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-03c-Le-Joueur-LLM.ipynb) | 03 | LLM-as-agent, six familles (win-win, dilemme, unfair, cyclique, biaisé, ...) | 26 (11 code) | Haute | Non |
| 03d | [GameTheory-03d-Plan-de-deformation](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-03d-Plan-de-deformation.ipynb) | 03-Topology2x2 | Plan de déformation, archétypes (PD, SH, BoS, Chicken), biens publics non-linéaires | 17 (6 code) | Haute | Non |
| 03e | [GameTheory-03e-Meta-Actions-Tarifees](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-03e-Meta-Actions-Tarifees.ipynb) | 03 + 03b + 03c | Meta-actions tarifées, parcours complet d'un agent qui change les règles | 64 (25 code) | **Très haute** | Non |
| 03h | [GameTheory-03h-Deux-Especes-de-Fleches](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-03h-Deux-Especes-de-Fleches.ipynb) | 03 + 03b | Distinction flèche-transformation vs flèche-morphisme (catégoriel) | 30 (10 code) | Très haute | Non |

## Observations

### Trois paliers se dégagent dans la strate "Fondations"

1. **Palier "Introduction" (Basse)** : `02-NormalForm` (+ twin C#) — pose le cadre formel $(N,S,u)$, premiers exemples de bimatrice. Idéal comme **point d'entrée** de la série.
2. **Palier "Application" (Moyenne)** : `02-P2*` (équilibres mixtes), `02b-Lean-Definitions` (formalisation), `02c-Travelers-Dilemma*` (cas non-trivial), `03-Topology2x2*` (576 jeux). Couvre les 4 outils canoniques : équilibre mixte, formalisation, cas empirique, classification.
3. **Palier "Spécialisation" (Haute → Très haute)** : `03a` à `03h` — géométrie ordinale avancée, LLM-as-agent, déformation, méta-actions. **Ces carnets exigent la maîtrise de 03-Topology2x2**.

### Pattern jumeau Python/C#

Le pattern se répète sur `02`, `02-P2`, `02c`, `03`. Le jumelage a un coût pédagogique :

- `02-NormalForm.ipynb` (47c) pose la **substance** théorique (notation, exemple, profil).
- `02-NormalForm-Csharp.ipynb` (33c) **re-derive la même chose en C#/.NET from-scratch** (BCL only).

Pour une audience Python-first, lire les `Part2` Python avant les `Part2` C# — la substance théorique est dans la partie Python. La réciproque est vraie pour une audience .NET-first.

### Lacune constatée

`03-Topology2x2.ipynb` (47c substance) puis le saut à `03a-Chemins-de-Swaps` (33c) **présuppose 03b-Chambres-et-Murs** (qui est numéroté après 03a). Le 03b-Chambres-et-Murs pose les "murs" (joints de codimension) que 03a utilise pour sa "distance de swap". La numérotation actuelle **inverse l'ordre pédagogique** : 03a devrait venir après 03b.

Deux réordonnancements locaux possibles :

| Option | Réord. local | Justification |
|---|---|---|
| A | `03b → 03a → 03c → 03d → 03e → 03h` | Aligne prérequis avant consommateurs (03b avant 03a) |
| B | Statu quo (03a → 03b → 03c → 03d → 03e → 03h) avec note explicite « 03a requiert 03b » | Conserve les numéros acquis (cf PR #18001 OPEN), ajoute un prérequis en introduction |

**Recommandation préliminaire** : option B, tant que la PR #18001 OPEN (rename GameTheory — 93 carnets) n'est pas arbitrée. Une fois l'arbitrage rendu, l'option A devient possible mais impose un re-numérotage lourd.

## Hors périmètre (cycles suivants)

- Strate "Nash et au-delà" (04-Nash, 04b-Lean, 04c, 04d, 04e, 04f, 05-ZeroSum, 05b-Lean, etc.) : 50+ carnets, hors cycle.
- Carnets 06 (Evolution, Bounded agents, Open-Source, Lean Repeated Games) : idem.
- Carnets 07+ : idem.
- Proposition d'ordre cible pour les 100 carnets : livrée par un **deuxième ledger** quand la strate "Fondations" est arbitrée.

## Source des données

- Lecture first-hand des 15 carnets (front-matter + section 1).
- Statistiques cellules : `python -c "import json, glob; ..."` (cf scripts ad hoc dans la branche).
- Issue pivot : #15615 (cf. PR #15987, PR #17797, PR #15586 déjà mergées sur cette strate).

## Voir aussi

- #15615 — issue pivot
- #15586 — renum GameTheory tranche A
- #15613 — renum GameTheory tranche B
- #14944 — Epic renum (mécanique)
- #18001 — PR OPEN `rename GameTheory — 93 carnets (relettrage 03, gradation, departages, suffixes noyau)` — l'arbitrage de cette PR est préalable à toute ré-énumérotation locale
- [15573-cadrage-granulaire.md](15573-cadrage-granulaire.md) — le ledger parent qui a détecté le cadrage par item unitaire sur #15615

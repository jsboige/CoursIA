> **ARCHIVED 2026-08-08** — Verdict **NO-RENUMBER** figé (cf PR [#9898](https://github.com/jsboige/CoursIA/pull/9898)). EPIC #5081 phase-1 close. Document conservé pour référence historique (daté, immutable). Voir triage table c.XXIV [issue #7422](https://github.com/jsboige/CoursIA/issues/7422#issuecomment-5223051530) + archive INDEX [`docs/archive/INDEX.md`](../INDEX.md). *Archivé par : po-2024 (lane CoursIA, c.XXIV) — consistence siblings (infer/search/planners/pymc/texte/video).*

# #5081 — Sudoku : analyse de renumérotation (phase 1, docs-only)

> **EPIC #5081** — Renumérotation narrative des séries. **Fille série Sudoku.**
> **Phase 1 = analyse docs-only, ZÉRO rename** (leçon #4737→#4743 : un rename casse les liens inbound).
> Ce document clot la question renumérotation pour Sudoku, comme `infer.md`, `search.md`,
> `planners.md`, `pymc.md`, `texte.md`, `video.md` l'ont fait pour leurs séries (archivés dans
> [`docs/archive/curriculum-renumbering-phase1/`](../archive/curriculum-renumbering-phase1/)).

## Méthode

Évaluation **firsthand** (lecture directe des 36 notebooks canoniques + check automatique du DAG
des prereqs déclarés), sur `origin/main` (`ae9720c1f5`). Le verdict repose sur deux vérifications
mécaniques, conformes à la méthode phase-1 établie par [#6879](https://github.com/jsboige/CoursIA/pull/6879) :

1. **Tri topologique** — pour chaque notebook, vérifier que tous les prereqs déclarés (champ
   « Prérequis » de la première cellule) pointent vers un numéro **strictement inférieur**.
2. **Carte thématique** — regrouper les notebooks par arc narratif (fondations → recherche →
   métaheuristiques → CSP → solveurs industriels → symbolique → data-driven → méta-comparaison →
   formel) et comparer à l'ordre numérique.

Les navlinks `<<` / `>>` ont déjà été audités par [#6888](https://github.com/jsboige/CoursIA/pull/6888)
(scan L613 stale-RESOLVES : 1 défaut corrigé sur Sudoku-4-Csharp, résidu de réorg).

## Verdict : **AUCUNE renumérotation nécessaire pour Sudoku**

### Preuve 1 — l'ordre numérique 0→19 est un tri topologique VALIDE du DAG des prereqs

Check automatique sur les 36 notebooks canoniques (17 C# + 18 Python + 1 Lean) : **0 arête
broken-order**. Chaque prereq déclaré pointe vers un numéro strictement inférieur.

La série Sudoku est **plate** : à l'inverse d'Infer (chaîne riche 1→2→...→18), la quasi-totalité
des notebooks ne déclarent que **Sudoku-0 (Environment)** comme prereq en commun, plus des
notions externes (C#, Python 3.10+, théorie des graphes, probabilités bayésiennes). **Une seule
arête cross-notebook non triviale** existe dans tout le DAG :

| Notebook | Prereq déclaré (cross-N) | Valide ? |
|----------|--------------------------|----------|
| Sudoku-7 (Norvig, propagation de contraintes) | Sudoku-6 (AIMA-CSP) | ✓ 6 < 7 |

Cette arête est conceptuellement justifiée : Norvig (propagation AC-3) s'appuie sur le cadre CSP
posé par AIMA-CSP (cell[0]). Elle est correctement ordonnée. Aucun autre notebook ne déclare de
dépendance vers un successeur numérique.

**Conséquence pour #5081** : l'anti-pattern dénoncé (« numérotation d'opportunité » où un notebook
est inséré à un numéro disponible sans égard à la pédagogie) **ne s'applique pas** — le DAG est
trivial mais valide, et les ajouts récents (16 NeuralNetwork, 17 LLM, 18b Statistical, 19 Lean)
tombent à la bonne place (fin du corpus, cluster data-driven puis formel).

### Preuve 2 — l'arc thématique suit déjà un flux pédagogique cohérent

Le README documente explicitement « cinq familles d'approches » ; la carte ci-dessous affine en
huit étages, tous contigus et correctement ordonnés :

| Étage | Numéros | Famille | Justification de l'ordre |
|-------|---------|---------|--------------------------|
| **Base** | 0 | Environment | Classes de données partagées — prereq universel |
| **Recherche exhaustive** | 1, 2 | Backtracking → Dancing Links | Du naïf à l'optimisé (Knuth DLX) |
| **Métaheuristiques** | 3, 4, 5 | Genetic → Simulated Annealing → PSO | Évolutionnaire → recuit → essaim (approximation stochastique) |
| **CSP from-scratch** | 6, 7, 8, 9 | AIMA-CSP → Norvig → Human Strategies → Graph Coloring | Modélisation → propagation → heuristiques humaines → réduction (coloration) — **seul cluster avec une arête de prereq (7←6)** |
| **Solveurs industriels** | 10, 11, 12 | OR-Tools → Choco → Z3 | CP (Google) → CP (Choco) → SMT (Z3) — montée en expressivité |
| **Symbolique** | 13, 14 | Symbolic Automata → BDD | Automates → diagrammes de décision booléens |
| **Data-driven** | 15, 16, 17 | Infer.NET (probabiliste) → Neural Network → LLM | Probabiliste → apprentissage profond → zero-shot |
| **Méta-comparaison** | 18, 18b | Comparison → Statistical Comparison | Benchmark puis analyse statistique des résultats |
| **Formel** | 19 | Lean Propagation | Preuve formelle de la propagation de contraintes (capstone) |

L'ordre numérique respecte ces étages : les clusters sont contigus (métaheuristiques 3-5, CSP 6-9,
solveurs 10-12, data-driven 15-17) et la progression va bien du exhaustif (garantie, lent) vers
l'approximatif (rapide, non garanti) puis le formel (preuve).

## Contexte — le défaut de navlink (résolu, hors phase-1)

[#6888](https://github.com/jsboige/CoursIA/pull/6888) a corrigé 1 stale-RESOLVES sur
`Sudoku-4-SimulatedAnnealing-Csharp` (son `<<` pointait vers Sudoku-7, résidu de réorg). Ce défaut
était **structurellement orthogonal** à la renumérotation : le numéro 4 était correct, c'est le
*lien narratif* qui était cassé. Il est désormais résolu et n'affecte pas le présent verdict.

## Point de vigilance (hors-scope de #5081) — une série « plate » par conception

Contrairement à Infer (chaîne prérequis riche, chaque notebook s'appuie sur le précédent), Sudoku
est délibérément **plate** : chaque paradigme (backtracking, génétique, Z3, LLM...) est
**auto-contenu** et ne nécessite que la base (Sudoku-0). C'est un **choix pédagogique assumé** —
la série compare 7 paradigmes sur un même problème, chacun lisible indépendamment — et non un
défaut de numérotation. La seule exception (Sudoku-7 ← Sudoku-6) confirme la règle : Norvig est
une *optimisation* de AIMA-CSP, donc en dépend.

Si l'on voulait forcer une chaîne linéaire (chaque notebook prereq du suivant), on appauvrirait la
modularité sans gain pédagogique. **Statu quo recommandé.**

## Voir aussi

- EPIC [#5081](https://github.com/jsboige/CoursIA/issues/5081) — renumérotation narrative.
- Verdicts sœurs (archivés) : [Infer](../archive/curriculum-renumbering-phase1/infer.md),
  [Search](../archive/curriculum-renumbering-phase1/search.md),
  [Planners](../archive/curriculum-renumbering-phase1/planners.md),
  [PyMC](../archive/curriculum-renumbering-phase1/pymc.md),
  [Texte](../archive/curriculum-renumbering-phase1/texte.md),
  [Video](../archive/curriculum-renumbering-phase1/video.md).
- [#6888](https://github.com/jsboige/CoursIA/pull/6888) — navlink Sudoku-4 (résolu).

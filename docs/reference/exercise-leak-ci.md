# Exercise-leak CI — content-based solution leak gate

**Gate** : `.github/workflows/exercise-leak-ci.yml`
**Detector** : `scripts/notebook_tools/detect_solution_leaks.py` (240 lignes, content-based, `--scan-all --check` exit 1)
**Issue** : [#8053](https://github.com/jsboige/CoursIA/issues/8053) (PR c.762)
**Lane** : po-2023 (CI/tooling)
**Date** : 2026-07-23
**SHA baseline** : `be5998073`

---

## TL;DR

Le détecteur `scripts/notebook_tools/detect_solution_leaks.py` existe depuis longtemps (~240 lignes, content-based, 3 sévérités HIGH/MEDIUM/LOW). Le gate CI **branche ce détecteur** dans GitHub Actions avec un **mode WARN par défaut** (inventaire sur les notebooks changed-by-PR, jamais bloquant) et un **mode STRICT optionnel** (FAIL uniquement si la PR introduit un **nouveau** HIGH). Le backlog actuel (138 findings baseline) est tracké sous #8053 et sera nettoyé par PRs de suivi — le STRICT empêche les **nouvelles** régressions pendant ce nettoyage.

| Tier | Comportement | Activation |
|------|-------------|------------|
| **WARN (default)** | `::warning` step, step-summary avec findings, **jamais bloquant** | Toujours actif sur PR |
| **STRICT** | `::error` step + **exit 1** sur nouveau HIGH (delta vs base > 0) | Label `exercise-leak-strict` OU dispatch input `strict=true` |

---

## Pourquoi deux tiers

**Baseline SHA `be5998073` (2026-07-23)** :
- **111 HIGH** (Exercice + solution complète)
- **27 MEDIUM** (numérotation duplicate)
- **0 LOW**
- **Total = 138 findings**

**Distribution par série** :

| Série | HIGH+MEDIUM | % du total |
|-------|-------------|-----------|
| SymbolicAI | 60 | 43 % |
| Search | 24 | 17 % |
| ML | 18 | 13 % |
| QuantConnect | 16 | 12 % |
| GameTheory | 14 | 10 % |
| Probas | 4 | 3 % |
| CaseStudies | 1 | < 1 % |
| GenAI | 1 | < 1 % |
| **TOTAL** | **138** | **100 %** |

**Contrainte** : ces 138 findings sont **pré-existants** au gate. Si on active FAIL-sur-HIGH directement, **toute PR touchant un notebook legacy est bloquée** — intenable. D'où le deux-tier :
- WARN census : inventaire, pas bloquant, le reviewer décide.
- STRICT : bloque uniquement les **nouvelles** régressions (delta > 0 vs base).
- Bascule WARN → FAIL global : une fois le backlog nettoyé sous un seuil documenté (suivi #8053 follow-ups).

---

## Doctrinal : règle content-based `exercise-example-labeling`

Source : `.claude/rules/exercise-example-labeling.md` (mandat user 2026-05-20, incident #1214/#1336/#1344).

| Combinaison | Verdict | Action |
|-------------|---------|--------|
| **Exemple + code complet** | OK | Ne pas toucher (worked example légitime) |
| **Exemple + stub vide** | INCONSISTENCY | Relabeler le titre en Exercice |
| **Exercice + code complet** | **LEAK (HIGH)** | Stubber le code OU relabeler en Exemple guide |
| **Exercice + stub** | OK | Ne pas toucher |

Le détecteur applique exactement cette règle : il cherche les cellules markdown titrées "Exercice N" puis inspecte la **prochaine cellule code** (dans une fenêtre de 3) et applique `is_stub_code()` (regex STUB_PATTERNS : `pass`, `return None`, `# TODO`, etc. + heuristique 1-ligne). HIGH = ni l'un ni l'autre = leak confirmé.

MEDIUM = numérotation duplicate (deux cellules titrées "Exercice 1" dans le même notebook).
LOW = "Exemple guide" + stub vide (relabeling oublié).

---

## Inventaire baseline SHA `be5998073`

```
Scanning 954 notebooks...
Results: 111 HIGH (leaks), 27 MEDIUM (duplicates), 0 errors
Scanned: 954 notebooks
```

**Échantillon représentatif** (10 premiers HIGH) :

```
[HIGH] MyIA.AI.Notebooks\CaseStudies\Oncology-Planning\solution\Oncology-Planning.ipynb:cell 23
[HIGH] MyIA.AI.Notebooks\GameTheory\GameTheory-15b-Lean-CooperativeGames.ipynb:cell 12
[HIGH] MyIA.AI.Notebooks\ML\ML-3-Regression-Csharp.ipynb:cell 17
[HIGH] MyIA.AI.Notebooks\Probas\InferNet-7-BayesianLinearRegression.ipynb:cell 38
[HIGH] MyIA.AI.Notebooks\Search\Part1-Foundations\Search-7-MCTS-And-Beyond.ipynb:cell 28
[HIGH] MyIA.AI.Notebooks\SymbolicAI\Lean\Lean-3-PropositionalLogic.ipynb:cell 22
[HIGH] MyIA.AI.Notebooks\SymbolicAI\Planners\01-Foundation\Planners-2-PDDL-Basics-Csharp.ipynb:cell 25
[HIGH] MyIA.AI.Notebooks\SymbolicAI\SMT\Z3-Linq2Z3\06_Meal_Planner_Modelisation.ipynb:cell 64
[HIGH] MyIA.AI.Notebooks\QuantConnect\Python\QC-Py-21-OrderFlowImbalance.ipynb:cell 19
[HIGH] MyIA.AI.Notebooks\GenAI\TEXTE\01-Foundation\GenAI-Text-3-PromptEngineering-Csharp.ipynb:cell 14
```

Ces 138 findings seront nettoyés par PRs de suivi scopeées par série (SymbolicAI = 5-6 PRs ; Search = 3 PRs ; etc.).

---

## Utilisation locale

```bash
# Scan complet du repo
py scripts/notebook_tools/detect_solution_leaks.py --scan-all

# Mode CI (exit 1 si HIGH)
py scripts/notebook_tools/detect_solution_leaks.py --scan-all --check

# Scan ciblé
py scripts/notebook_tools/detect_solution_leaks.py --scan MyIA.AI.Notebooks/SymbolicAI/

# Verbosité (LOW aussi)
py scripts/notebook_tools/detect_solution_leaks.py --scan-all --verbose
```

Pour investiguer un HIGH spécifique :
1. `Read` le notebook à `cell N`
2. Vérifier que la cellule code N+1 (ou dans la fenêtre de 3) n'est PAS un stub (`pass`/`return None`/`# TODO`)
3. Si c'est une solution complète, deux choix conformes à `exercise-example-labeling.md` :
   - **Stubber** la cellule (garder le titre "Exercice N", remplacer par `pass` ou `print("Exercice a completer")`)
   - **Relabeler** le titre markdown en "Exemple guide" si c'est intentionnellement un worked example

---

## Suite logique (PRs de suivi)

| Action | Owner | Priorité |
|--------|-------|----------|
| Nettoyage SymbolicAI 60 findings (5-6 PRs scopeées) | po-2023 / po-2025 | P1 |
| Nettoyage Search 24 findings | po-2023 | P1 |
| Nettoyage ML 18 findings | po-2026 | P1 |
| Nettoyage QuantConnect 16 findings | po-2024 (QC) | P1 |
| Nettoyage GameTheory 14 findings | po-2026 (Lean) | P1 |
| Bascule WARN → FAIL global quand baseline < seuil (ex. < 10) | po-2023 / ai-01 | P2 |
| Extension détecteur : ignorer les cellules `# %skip-leak-check` (anti-FP avancé) | future | P3 |

Tracking dans les issues filles de #8053 + EPIC parent #4208.

---

## Anti-FP intégré

- **github-actions[bot]** : bypass automatique (catalog/automation commits).
- **Manual dispatch** : lance un census full-repo (pas de PR → pas de base à diff).
- **Exemple + code complet** : PAS flagué (worked example légitime, règle content-based).
- **Fenêtre de 3 cellules** : cherche le code immédiatement après le markdown "Exercice N", pas trop loin (anti-faux-positif sur des cellules sans rapport).
- **`is_stub_code()` strict** : heuristique `non_empty ≤ 1` ou match STUB_PATTERNS = stub. Pas de faux positif sur un `pass` court.
- **Générés/CKPT exclus** : `*_output.ipynb` et `.ipynb_checkpoints/` ne sont pas scannés (déjà gitignored / générés).

---

## Liens

- **Issue [#8053](https://github.com/jsboige/CoursIA/issues/8053)** — brancher détecteur Exercice/solution en CI (c.762).
- **EPIC [#4208](https://github.com/jsboige/CoursIA/issues/4208)** — open-courseware fiabilisé (parent).
- **PR c.762** — `[open / mergeable]` à venir.
- **`.github/workflows/exercise-leak-ci.yml`** — gate créé par c.762.
- **`scripts/notebook_tools/detect_solution_leaks.py`** — détecteur canonique (240L, pré-existant).
- **`.claude/rules/exercise-example-labeling.md`** — règle content-based (mandat user 2026-05-20, incidents #1214/#1336/#1344).
- **`scripts/notebook_tools/audit_solution_leaks.py`** — détecteur secondaire (3 patterns + C# blind-spot, 422L, utilisé en audit manuel).
- **PR [#7965](https://github.com/jsboige/CoursIA/pull/7965) (c.744)** — origine Tweety parity, point de départ série c.756-c.760.
- **PR [#8070](https://github.com/jsboige/CoursIA/pull/8070) (c.761)** — pivot R6 strict cross-genre précédent (audit-cross-source dénombreurs).
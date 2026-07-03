# Audit renumérotation narrative des séries — 2026-07-03

**Origine** : Issue #5081 (mandat user 2026-07-03T09:50Z verbatim) — « repenser la numérotation dans un arc narratif et pédagogique cohérent. Les sites officiels peuvent aider parfois, comme pour Infer ou PyMC ; en tout cas souvent, les numéros se suivent simplement à l'opportunité des derniers ajouts alors qu'une renumérotation s'impose ».

**Cadre** : audit **propositions**, **pas** PR de renommage. Les renommages concrets seront chacun leur PR atomique (catalog-pr-hygiene R3, scope = 1 famille par PR). Ce document recense les **incohérences factuelles** et propose un **arc narratif cible** à appliquer série par série.

**Sources officielles cross-checkées** (cf mandat user « sites officiels ») :

| Série | Référence officielle | Notes |
|-------|----------------------|-------|
| **Infer.NET** | [infernet.io/docs](https://dotnet.github.io/infer/) | Modèle d'API Tutorial → Examples → API Reference |
| **PyMC** | [pymc.io/projects/docs/en/stable/learn.html](https://www.pymc.io/projects/docs/en/stable/learn.html) | API Quickstart → Fundamentals → Library → Examples |
| **QuantConnect** | [quantconnect.com/docs](https://www.quantconnect.com/docs) | Boot Camp → Tutorials → Research → Advanced |
| **Hugging Face** | [huggingface.co/docs](https://huggingface.co/docs) | Task → Pipeline → Model card |

---

## 1. État des lieux — numérotation actuelle (snapshot 2026-07-03)

Inventaire `find MyIA.AI.Notebooks/ -name "*.ipynb"`. Les fichiers `*_output.ipynb` sont des artefacts d'exécution (papermill), pas de la numérotation éditoriale ; on les exclut du décompte narratif.

### 1.1 Probas / Infer (Python .NET via pythonnet)

`MyIA.AI.Notebooks/Probas/Infer/` — 19 numéros, ordre canonique respecté :

```
Infer-1-Setup → Infer-2-Gaussian-Mixtures → Infer-3-Factor-Graphs → Infer-4-Bayesian-Networks
  → Infer-5-Skills-IRT → Infer-6-TrueSkill → Infer-7-Classification → Infer-8-Model-Selection
  → Infer-9-Topic-Models → Infer-10-Crowdsourcing → Infer-11-Sequences → Infer-12-Recommenders
  → Infer-13-Debugging → Infer-14-Causal-Inference → Infer-15-Sparse-Gaussian-Process
  → Infer-16-Modeles-Hierarchiques → Infer-17-Kalman-Filter → Infer-18-Change-Point
  → Infer-19-Survival-Analysis
```

**Constat** : série **propre**, ordre pédagogique respecté, pas de trou. La densité de contenu baisse sur les 5 derniers (15-19 = ajouts thématiques, pas dans l'arc original).

### 1.2 Probas / PyMC

`MyIA.AI.Notebooks/Probas/PyMC/` — 14 numéros, alignés sur 1-14 :

```
PyMC-1-Setup → ... → PyMC-14-Causal-Inference
```

**Constat** : **alignement strict** avec Infer-1..14 sur les 14 premiers. La parité est maintenue tant que les deux séries existent (cf PR #4956 EPIC). **Truc notable** : PyMC n'a pas de 15+, alors qu'Infer monte jusqu'à 19. Cohérent avec la maturité PyMC = grille plus courte (API plus large, moins de niches).

### 1.3 Probas / Decision Theory / Infer + PyMC

Sous-séries décision (utilité/decision networks/sequential), numérotation **indépendante** :

```
DecisionTheory/Infer/Infer-1-Utility-Foundations → ... → Infer-10-Thompson-Sampling
DecisionTheory/PyMC/PyMC-1-Utility-Foundations → ... → PyMC-7-Sequential
```

**Constat** : **incohérence de prefixes** avec la série principale Infer-/PyMC-. Les deux séries utilisent le même préfixe `Infer-N-` / `PyMC-N-` alors qu'elles sont dans un sous-domaine différent (decision theory). Risque de confusion si un étudiant cherche `Infer-1` (Gaussien mixture vs Utility Foundations). **PROPOSITION** : préfixer `DecInfer-N-` / `DecPyMC-N-` ou `DTInfer-N-` / `DTPyMC-N-`.

### 1.4 IIT (Integrated Information Theory)

`MyIA.AI.Notebooks/IIT/` — **3 notebooks racine** (IIT-1, IIT-2, IIT-3) + **17 notebooks ICT-Series** (ICT-1..15, ICT-20, ICT-Synthese).

```
IIT-1-IntroToPyPhi → IIT-2-AdvancedTopics → IIT-3-CoarseGrainingMacroPhi
ICT-Series : ICT-1 → ... → ICT-15 + ICT-20 (saut) + ICT-Synthese-CrossSubstrat
```

**Constat #1** : **incohérence de préfixe** entre `IIT-N` et `ICT-N` (notation inverse). IIT = Integrated Information Theory (théorie), ICT = Integrated Complexity Trajectories (extension strate 5). Le passage IIT-N → ICT-N est légitime mais gagnerait à être explicité (transition **IIT-3** → **ICT-0/1** = point de rupture pédagogique).

**Constat #2** : **trou ICT-16..19** délibéré (ICT-16 MDL = #5156, ICT-17 Epsilon = #5162, ICT-18 HOLD GPU, ICT-19 bloqué par ICT-18). ICT-20 FeatureCatastrophes = #5168 LIVRÉE C200. Donc **ICT-16 et ICT-17 existent en branche mais pas encore mergés**, **ICT-18 et ICT-19 ne sont pas encore créés**, et la numérotation actuelle saute ces nombres — **verdict honnête G.9** : la numérotation actuelle est **prématurée** et sera ajustée à la livraison ICT-18..21.

**Constat #3** : ICT-Synthese-CrossSubstrat est en queue, sans numéro, ce qui est OK (synthèse transverse ≠ épisode).

### 1.5 Search

`MyIA.AI.Notebooks/Search/` — **structure en 3 parties** :

```
Search/ (racine) :
  - CSPs_Intro.ipynb
  - Exploration_non_informée_et_informée_intro.ipynb
  - GeneticSharp-EdgeDetection.ipynb (legacy)
  - Portfolio_Optimization_GeneticSharp.ipynb (legacy)
  - PyGad-EdgeDetection.ipynb (legacy)

Search/Part1-Foundations/ : Search-1..12 (12 notebooks)
Search/Part2-CSP/ : CSP-1..9 (9 notebooks)
Search/Part3-Advanced/ : vide ou quasi-vide
```

**Constat #1** : la **racine contient 5 notebooks non numérotés**, ce qui crée une **frontière floue** entre "intro racine" et "Part1-Foundations". Soit on les préfixe `Search-0-Intro-...`, soit on les déplace dans Part1-Foundations comme `Search-1-IntroCSPs`, `Search-2-IntroExploration`, etc.

**Constat #2** : **Part3-Advanced vide** = structure anticipée sans contenu. Acceptable si la roadmap affiche clairement les notebooks prévus (Genetic Programming, Neural Architecture Search, etc.).

### 1.6 Sudoku

`MyIA.AI.Notebooks/Sudoku/` — **65 notebooks** numérotés Sudoku-0..18 + suffixe langue/outil :

```
Sudoku-0-Environment-Csharp
Sudoku-1-Backtracking-Csharp / -Python
Sudoku-2-DancingLinks-Csharp / -Python
Sudoku-3-Genetic-Csharp / -Python
Sudoku-4-SimulatedAnnealing-Csharp / -Python
Sudoku-5-PSO-Csharp / -Python
Sudoku-6-AIMA-CSP-Csharp / -Python
Sudoku-7-Norvig-Csharp / -Python   ← note: -7b-Lean-Propagation !!!
Sudoku-8-HumanStrategies-Csharp / -Python
Sudoku-9-GraphColoring-Csharp / -Python
Sudoku-10-ORTools-Csharp / -Python
Sudoku-11-Choco-Csharp / -Python
Sudoku-12-Z3-Csharp / -Python
Sudoku-13-SymbolicAutomata-Csharp
Sudoku-14-BDD-Csharp
Sudoku-15-Infer-Csharp / -Python
Sudoku-16-NeuralNetwork-Python
Sudoku-17-LLM-Python
Sudoku-18-Comparison-Python
```

**Constat #1** : **suffixes langue/outil prolifèrent** (`-Csharp`, `-Python`, parfois les deux pour le même sujet). Verdict honnête : c'est une **contrainte pédagogique** (parité .NET ↔ Python #4956) assumée. Le suffixe est **fonctionnel**, pas redondant. **PROPOSITION** : si la parité est complète, suffixer `-Csharp` ou `-Python` selon disponibilité, sans forcer la duplication.

**Constat #2** : **`Sudoku-7b-Lean-Propagation`** (note: `7b`, pas `7b1`/`7b2`) = numérotation opportuniste ajoutée tardivement. Lean Propagation n'est PAS une variante de Norvig, c'est un solveur **formel** distinct. **PROPOSITION** : soit le promouvoir `Sudoku-19-Lean-Propagation`, soit accepter `7b` comme exception documentée.

**Constat #3** : **arc pédagogique lisible** : 0 = setup, 1-6 = solveurs classiques, 7-12 = solveurs spécialisés (Norvig/OR-Tools/Choco/Z3), 13-15 = solveurs symboliques (Automata/BDD/Infer), 16-18 = solveurs ML. C'est le **seul arc narratif vraiment cohérent** du dépôt (cohérence méthodologique).

### 1.7 QuantConnect

`MyIA.AI.Notebooks/QuantConnect/` — **206 notebooks**, structure éclatée :

```
QC-Py-NN-* : 41 notebooks (01..35 + 40, 41, trous multiples)
QC-Py-Cloud-NN-* : 9 notebooks (01..09)
QC-Py-Dataset-Workflow.ipynb (sans préfixe NN)
QC/Python/research/*.ipynb : notebooks ad-hoc
QC/research/*.ipynb : notebooks ad-hoc (m1..m12, btc_ml, etc.)
QC/projects/<Strategy>/quantbook.ipynb : 1 par stratégie (~30)
QC/projects/<Strategy>/research.ipynb : 1 par stratégie (~30)
QC/ML-Training-Pipeline/*.ipynb : 6 notebooks (m3, m4, m5, m9, m11e, ML-Research-Template)
QC/partner-course-quant-trading/kit-transitoire/01..03-ML-* : 3 notebooks
```

**Constat #1** : `QC-Py-23b-PatchTST-iTransformer` = **numérotation opportuniste** insérée entre 23 et 24 (le `b` = bis/ajout tardif). Mauvais pattern à éviter à l'avenir.

**Constat #2** : `QC-Py-29-` **MANQUANT** (passage 28 → 30). `QC-Py-36-39` **MANQUANTS** (passage 35 → 40). **Trous inexpliqués** dans la série.

**Constat #3** : `QC-Py-40-PaperTrading-Binance` et `QC-Py-41-PaperTrading-IBKR` cassent la continuité thématique (passage de RL-Construction à PaperTrading). Soit ils appartiennent à un nouveau chapitre, soit il faut les préfixer `QC-Py-40-Series-PaperTrading-Binance`.

**Constat #4** : `QC-Py-Cloud-NN-*` est une **série parallèle Cloud** non annoncée comme telle. Confusion garantie : un étudiant qui lit QC-Py-23 (Attention-Transformers) puis cherche QC-Py-Cloud-03 (DualMomentum) ne sait pas qu'il change de registre (local Python vs QC Cloud).

**Constat #5** : la série `m1..m12` dans `research/` et `ML-Training-Pipeline/m3/m4/m5/m9/m11e` utilise un **préfixe totalement différent** des autres séries QC, ce qui rend le parcours étudiant **illisibles** sans table de correspondance.

### 1.8 GenAI / Image, Audio, Video, Texte

**GenAI/Image** : `01-Foundation/` (5 nb), `02-Advanced/` (5 nb), `03-Orchestration/` (3 nb), `04-Applications/` (4 nb), `examples/` (3 nb). **Numérotation canonique 01-N → 04-N respectée**, très propre.

**GenAI/Audio** : `01-Foundation/` (5 nb), `02-Advanced/` (9 nb — note: 02-5 = Multi-Model-TTS-Gateway, **incohérence** dans l'ordre thématique vs foundation 01-5 Kokoro), `03-Orchestration/` (3 nb), `04-Applications/` (13 nb — note: 04-3 = Music-Composition, 04-4 = Audio-Video-Sync, ordre thématique discutable). Verdict honnête : **Audio a 2 anomalies mineures** d'ordre, pas de trou.

**GenAI/Texte** : `1_OpenAI_Intro` à `20_OWUI_Native_API` = **20 notebooks, sans préfixe 0X-YY**. Pas de zéro-padding (`1_` au lieu de `01_`), pas de double-niveau hiérarchique (`1-1-` au lieu de `1_`). **Incohérence stylistique** avec Image/Audio qui utilisent `01-Foundation/01-1-...`.

**GenAI/Video** : pas inventorié en détail (cette branche C201 se concentre sur les séries + problématiques de renumérotation évidentes).

### 1.9 SymbolicAI (non inventorié exhaustivement)

Tweety, Lean, Planning, SmartContract, SemanticWeb = séries multi-modules, structure à vérifier dans un audit ultérieur.

---

## 2. Problèmes transversaux identifiés

| # | Problème | Impact | Série(s) |
|---|----------|--------|----------|
| **P1** | **Numérotation opportuniste** (trous inexpliqués, sauts `23b`, ajouts en queue) | Confusion du parcours, brisure d'arc narratif | QC-Py, ICT, Sudoku, Infer |
| **P2** | **Conflit de préfixes** (`Infer-1` désigne 2 notebooks différents : mixture Gaussienne vs utility foundations) | Confusion à la recherche | Probas/Infer vs Probas/DecisionTheory/Infer |
| **P3** | **Incohérence stylistique des séparateurs** (`Infer-1-Setup` vs `1_OpenAI_Intro` vs `QC-Py-01-Setup`) | Lecture / parsing / grep incohérents | GenAI vs Probas vs QC |
| **P4** | **Suffixes langue/outil proliférants** (`-Csharp`/`-Python`/`-Csharp-Python`) | Ambiguïté sur parité .NET/Python | Sudoku, Lean |
| **P5** | **Séries préfixées `m1..m12`** à côté de séries préfixées `QC-Py-NN` | Parcours étudiant illisible | QC/research, ML-Training-Pipeline |
| **P6** | **Numérotation prématurée** (ICT-16..19 pas encore créés) | Engagement sur un arc futur incertain | ICT-Series |
| **P7** | **Racine vs sous-dossier** (5 notebooks Search/ racine, Part3-Advanced vide) | Frontière floue | Search |
| **P8** | **Lecture pédagogique faible** (les 5 derniers Infer 15-19 sont thématiques, pas dans l'arc) | Parcours linéaire rompu | Infer |
| **P9** | **Absence d'index de correspondance** entre les notations (`Infer-1-Setup` ↔ `PyMC-1-Setup` ↔ `QC-Py-01-Setup`) | Table de parité à construire | Transverse |
| **P10** | **Numérotation Cloud vs Local** pas distinguée | Confusion registre d'exécution | QC |

---

## 3. Propositions — arc narratif cible par série

### 3.1 Probas / Infer — refactor léger

**Statut** : série la plus propre du dépôt, pas de renommage nécessaire. **PROPOSITION** :

1. Documenter l'arc pédagogique actuel (Setup → Mixtures → Factor → Bayes Net → IRT → TrueSkill → Classification → Model Selection → Topic Models → Crowdsourcing → Sequences → Recommenders → Debugging → Causal → Sparse GP → Hierarchical → Kalman → Change Point → Survival).
2. Numéroter les ajouts thématiques 15-19 dans un **chapitre II** explicite (`Infer-II-1-Sparse-GP`, `Infer-II-2-Hierarchical`, ...) ou laisser tel quel (chapitre implicite).
3. Pour les PRs à venir : **interdire le saut opportuniste** (pas de `Infer-19b`).

### 3.2 Probas / DecisionTheory / Infer+PyMC — refactor préfixes

**PROPOSITION** : renommer en `DecInfer-N-...` / `DecPyMC-N-...` pour éviter le conflit avec la série principale. **Acceptable** car la série est jeune (10 + 7 = 17 notebooks) et le coût de redirection est faible (1 PR avec redirects dans README, pas de breaking sur les outputs Papermill).

### 3.3 IIT / ICT-Series — clarifier la transition

**PROPOSITION** :

1. Documenter explicitement que **IIT-3-CoarseGraining** est le **point de rupture** vers ICT-Series (transition pédagogie → séries trajectorielles).
2. Accepter le **trou ICT-16..19** comme un **engagement roadmap** (#4588 strate 5).
3. Numéroter ICT-18, ICT-19, ICT-21, ICT-22 **à la livraison** (pas avant).

### 3.4 Search — clarifier racine vs sous-dossiers

**PROPOSITION** :

1. Déplacer les 5 notebooks racine non numérotés dans `Part1-Foundations/` avec les noms `Search-1-IntroCSPs`, `Search-2-IntroExploration`, `Search-3-GeneticSharp-EdgeDetection` (legacy), etc.
2. Soit remplir `Part3-Advanced/` (Genetic Programming, Neural Architecture Search, etc.), soit **supprimer le dossier vide** + documenter l'absence.
3. Conserver les 5 notebooks legacy (GeneticSharp, PyGad, Portfolio) avec un encadré `> **Legacy**` dans le README de la série.

### 3.5 Sudoku — promouvoir Sudoku-7b à 19

**PROPOSITION** :

1. Renommer `Sudoku-7b-Lean-Propagation` → `Sudoku-19-Lean-Propagation` (place naturelle = solveurs formels en queue).
2. Documenter l'arc : 0 (setup) → 1-6 (classiques) → 7-12 (spécialisés) → 13-15 (symboliques) → 16-18 (ML) → 19 (formels Lean).
3. **Suffixes `-Csharp` / `-Python`** : à conserver (parité #4956), mais à harmoniser en queue : `Sudoku-N-Topic-Csharp.ipynb` / `Sudoku-N-Topic-Python.ipynb` (actuellement déjà le cas, OK).

### 3.6 QuantConnect — refactor majeur

**PROPOSITION** :

1. **Boucher les trous** : QC-Py-29 et QC-Py-36..39 = soit les créer (même stub), soit les supprimer (renommer QC-Py-30..35 → QC-Py-29..34 et QC-Py-40..41 → QC-Py-35..36).
2. **Éliminer le suffixe opportuniste** : `QC-Py-23b-PatchTST-iTransformer` → insérer entre 23 et 24 en tant que notebook à part entière, ou accepter la numérotation 24 = PatchTST-iTransformer (priorité chronologique).
3. **Chapitre explicite** : `QC-Py-36-PaperTrading-Introduction`, `QC-Py-37-PaperTrading-Binance`, `QC-Py-38-PaperTrading-IBKR` (place les paper tradings dans leur propre chapitre, supprime le saut 35→40).
4. **Table de correspondance** : ajouter un README dans `QuantConnect/Python/` qui mappe `m1..m12` → `QC-Py-NN-*` quand applicable (ex: `m11e_ensemble_research.ipynb` ↔ `QC-Py-19-ML-Supervised-Classification`).
5. **Distinction Cloud vs Local** : préfixer `QC-Cloud-NN-*` pour les notebooks QC Cloud (déjà partiellement fait avec `QC-Py-Cloud-NN-*`, à généraliser).

### 3.7 GenAI / Texte — aligner la convention

**PROPOSITION** : aligner `1_OpenAI_Intro` → `01-1-OpenAI-Intro` (format `01-Foundation/01-1-...` des autres familles GenAI). Migration coûteuse (20 fichiers), **à prioriser en PR atomique 1 fichier = 1 PR** ou à laisser tel quel (verdict honnête : la convention actuelle est lisible, juste inconsistante).

### 3.8 Table de parité cross-série

**PROPOSITION** : créer `docs/reference/notebook-parity-table.md` avec colonnes :

| Concept | Infer | PyMC | Lean | .NET | QC-Py | QC-Cloud | Audio | Texte | Image |
|---------|-------|------|------|------|-------|----------|-------|-------|-------|
| Setup | Infer-1 | PyMC-1 | Lean-1 | (varies) | QC-Py-01 | QC-Py-Cloud-01 | 01-1 | 1 | 01-1 |
| Gaussian | Infer-2 | PyMC-2 | Lean-3 | (varies) | (N/A) | (N/A) | (N/A) | (N/A) | (N/A) |
| ... | ... | ... | ... | ... | ... | ... | ... | ... | ... |

Cette table permettrait de naviguer entre frameworks sur un même concept (parité pédagogique). **Effort** : ~50 lignes de Markdown, **bénéfice** : navigation cross-stack immédiate.

---

## 4. Plan d'action proposé (par PR atomique)

| # | PR cible | Scope | Effort | Statut |
|---|----------|-------|--------|--------|
| 1 | Renommer `Sudoku-7b` → `Sudoku-19` | 1 renommage + 1 redirect README | ~30 min | À démarrer (C201+ possible) |
| 2 | Déplacer 5 notebooks Search racine → Part1 | 5 renommages + 1 README update | ~1h | À planifier |
| 3 | Renommer DecisionTheory/Infer → DecInfer | 10 renommages + 1 README | ~1h | À planifier |
| 4 | Renommer DecisionTheory/PyMC → DecPyMC | 7 renommages + 1 README | ~1h | À planifier |
| 5 | Table de parité cross-série | 1 fichier `docs/reference/notebook-parity-table.md` | ~1h | À démarrer |
| 6 | Audit QC-Py trous 29, 36-39 | 1 PR bouchage OU renumérotation 30-35→29-34 | ~2h | À discuter (G.4 composite ?) |
| 7 | GenAI/Texte alignement `01-1` | 20 renommages | ~2h | À discuter (PR atomique) |
| 8 | Documenter arc IIT → ICT | 1 fichier `docs/suivis/iit-ict-transition.md` | ~30 min | À démarrer |

**Total estimé** : 8-10 PRs atomiques sur ~6-10 cycles workers. À dispatcher à po-2023/2024/2025 selon leur partition dominante.

---

## 5. Leçons pour les PRs à venir

1. **JAMAIS de numérotation opportuniste** (`23b`, `7b`, sauts inexpliqués). Si un ajout arrive tardivement, l'insérer **au bon endroit chronologique** (numéro suivant), pas en queue bis.
2. **Chapitres explicites** quand l'arc change (Local → Cloud, Classique → ML, etc.). Préfixe `SeriesII-` ou suffixe `-Cloud`/`-Local` lisible.
3. **Boucher les trous** à la création : si `QC-Py-29` n'existe pas, ne pas passer à 30 — soit créer un stub, soit renuméroter.
4. **Suffixes fonctionnels OK** (`-Csharp`/`-Python`) tant qu'ils sont cohérents et limités à 2 alternatives. Au-delà (`-Csharp-Python`, `-Lean`, `-Symbolic`), c'est une **troisième dimension** qui devrait être un sous-dossier.
5. **Documentation de l'arc** = README de série avec la liste numérotée + arc narratif en intro. Aujourd'hui, seul Sudoku a un arc pédagogique clair ; les autres séries gagneraient à en avoir un.

---

## 6. Liens croisés

- Issue #5081 (Renumérotation narrative des séries)
- Issue #4588 (Epic IIT → ICT)
- Issue #4956 (EPIC Parité .NET ⇄ Python)
- Issue #3973 (EPIC README ascendant — consumer de cet audit)
- `MyIA.AI.Notebooks/Probas/Infer/` — 19 notebooks
- `MyIA.AI.Notebooks/Probas/PyMC/` — 14 notebooks
- `MyIA.AI.Notebooks/Probas/DecisionTheory/` — 10 + 7 notebooks
- `MyIA.AI.Notebooks/IIT/ICT-Series/` — 17 notebooks (ICT-1..15 + ICT-20 + ICT-Synthese)
- `MyIA.AI.Notebooks/Search/` — 120 notebooks (3 parties)
- `MyIA.AI.Notebooks/Sudoku/` — 65 notebooks (Sudoku-0..19)
- `MyIA.AI.Notebooks/QuantConnect/` — 206 notebooks (QC-Py-NN + Cloud + research + projects)

---

*Audit rédigé par po-2023:CoursIA-2 (MiniMax M3 haiku) — C201, 47ᵉ cycle — 2026-07-03T10:15Z.*
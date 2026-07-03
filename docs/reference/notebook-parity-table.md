# Table de parité cross-série — notebooks Python ⇄ .NET

> **Statut** : document de **cartographie** créé le 2026-07-03 (PR po-2023 C202) en
> contribution à l'EPIC **#4956** « Parité .NET ⇄ Python des séries de notebooks ».
> Source : audit narratif #5081 (PR #5171) + cross-check avec `docs/reference/`
> inventaires (kernels-runtime, common-commands, regles-vigilance-detail).
> **Pas une cible exhaustive** — inventaire **rapide** à affiner par les owners
> de chaque série (cf sections « owners pressentis »).

---

## 1. Pourquoi une table de parité

CoursIA est **bilingue technique** (C#/.NET Interactive + Python). Historiquement
la parité s'est faite au cas par cas (Sudoku, ML.NET, Infer.NET, Z3). La
**chute de la coquille Tweety** (#4667, port C#/IKVM 11 ↔ Java 15) prouve que
**le levier IKVM ouvre tout l'écosystème Java** et **PythonNet ouvre
l'écosystème Python** : plus aucune série n'est structurellement inaccessible en
.NET. La méthode **marathon, pas sprint** (#4956) appelle un état des lieux
**maintenable** au lieu d'un re-comptage à chaque cycle.

Cette table :

1. **Liste les séries** (≥1 notebook dans `MyIA.AI.Notebooks/`).
2. **Code l'état de parité** courant (4 niveaux).
3. **Indique le kernel principal** + le levier transverse à activer.
4. **Marque la difficulté marathon** pour calibrer l'effort.

Elle **n'engage pas un plan de port** — chaque ligne est une **tranche
potentielle** pour les workers qui piochent dans le pool cross-lane
([proactive-coordination](../../.claude/rules/proactive-coordination.md), Règle 5).

---

## 2. Légende

### 2.1 État de parité (4 niveaux)

| Code | Signification | Critère observable |
|------|---------------|---------------------|
| **P-OK** | **Parité Python + .NET** | ≥80 % des notebooks ont un équivalent C#/Python (peu importe la langue majoritaire) |
| **P-CS** | **.NET majoritaire** (C#/.NET Interactive) | ≥80 % des notebooks sont en C#/.NET, Python minoritaire ou absent |
| **P-PY** | **Python majoritaire** (jpy/quantbook Python) | ≥80 % des notebooks sont en Python, .NET minoritaire ou absent |
| **P-NS** | **Notebook single-stack** (pas de parité visée) | Série purement mono-langage par conception (Lean, ICT/IIT, GenAI) |

### 2.2 Difficulté marathon (#4956)

| Code | Effort | Leviers requis |
|------|--------|----------------|
| **D-facile** | 1-2 cycles | NuGet natif ou PythonNet direct, 0 IKVM |
| **D-moyen** | 3-6 cycles | IKVM 11 OU PythonNet + config kernel |
| **D-fort** | 6-15 cycles | PythonNet + bridge (OpenSpiel) OU kernel .NET quantbook dans `lean_cli` |
| **D-os** | >15 cycles | Effort dédié marathon, possiblement hors scope saison |

### 2.3 Kernel principal

- **cs-ipy** = .NET Interactive (`dotnet interactive jupyter`)
- **py-ipy** = IPython classique (Python 3.10+)
- **qc-cloud** = QuantConnect Cloud kernel (LEANT)
- **lean-wsl** = Lean 4 natif WSL (kernel `lean4-wsl`, cf [kernels-runtime.md](kernels-runtime.md))

---

## 3. Table de parité par série

| Série | Emplacement | Notebooks (≈) | État parité | Kernel principal | Difficulté | Levier transverse principal | Owner pressenti | Notes |
|-------|-------------|---------------:|-------------|------------------|------------|------------------------------|-----------------|-------|
| **Sudoku** | `MyIA.AI.Notebooks/Sudoku/` | 19 + 1 Lean (`7b`) | **P-OK** | cs-ipy + py-ipy | D-facile | référence (déjà bien porté) | po-2026 (Lean) + po-2025 (.NET) | Référence de style pour les nouvelles séries. Audité #5081 (préfixage opportuniste `7b` à renuméroter) |
| **ML.NET** | `MyIA.AI.Notebooks/ML/ML.Net/` | ≈10 | **P-CS** | cs-ipy | D-moyen | compléter ML.Net + tour NuGet PythonNet wrappers | po-2025 | Mandat user 2026-07-02 #4956 : « compléter ML.Net + refaire un tour des packages NuGet qui proposent des wrappers PythonNet (dont ML.Net fait partie) » |
| **Probas/Infer.NET** | `MyIA.AI.Notebooks/Probas/Infer/` | 19 (`Infer-1` à `Infer-19`) | **P-CS** | cs-ipy | D-moyen | référence Infer.NET (Microsoft) | po-2025 | Audité #5081 (P2 conflit préfixe `Infer-1` = Gaussian Mixtures vs Utility Foundations selon dossier, P8 lecture pédagogique faible 15-19 = ajouts thématiques en queue) |
| **Probas/PyMC** | `MyIA.AI.Notebooks/Probas/PyMC/` | 14 | **P-PY** | py-ipy | D-fort | PythonNet → PyMC (3) | po-2025 | Parité Infer.NET↔PyMC déjà existante via notebooks appariés, port .NET-py absent côté PyMC |
| **Probas/DecisionTheory** | `MyIA.AI.Notebooks/Probas/DecisionTheory/` | 10 + 7 | **P-PY** | py-ipy + Lean | D-moyen | PythonNet + Gittins (cf #4038 #4039) | po-2026 (Lean) | Audité #5081 (P2 conflit préfixe `Infer-1` Gaussian Mixtures vs DecisionTheory `Infer-1` Utility Foundations) |
| **IIT/ICT-Series** | `MyIA.AI.Notebooks/IIT/` | 3 + 17 ICT | **P-NS** | py-ipy (PyPhi) | hors parité | N/A — pyphi est python-only | po-2026 (ICT/IIT) | Single-stack par conception (Phi/TPM), pas de cible parité |
| **Search (racine + Part1-4)** | `MyIA.AI.Notebooks/Search/` | ≈40 racine + Part1 (≈13) + Part2-CSP (≈14) + Part3-Advanced (≈3) + Part4-Metaheuristics | **P-OK partiel** | cs-ipy + py-ipy | D-moyen | Choco (IKVM 11) + OrTools + MGS + HeuristicLab | po-2025 | Audité #5081 (P7 frontière floue racine/sous-dossier). Cible #4956 : accessible **entièrement** |
| **SymbolicAI/Lean** | `MyIA.AI.Notebooks/SymbolicAI/Lean/` | ≈25 (Lean-1 à Lean-18 + sous-séries) | **P-NS** | lean-wsl | hors parité | N/A — Lean 4 natif | po-2026 | Single-stack par conception (preuves formelles) |
| **SymbolicAI/Tweety** | `MyIA.AI.Notebooks/SymbolicAI/Tweety/` | ≈11 | **P-CS** | cs-ipy (IKVM) | D-facile | jurisprudence #4667 (IKVM 11 ↔ Java 15) | po-2026 | **Coquille qui a cédé** — référence pour IKVM |
| **SymbolicAI/SemanticWeb** | `MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/` | ≈10 | **P-CS** | cs-ipy (dotNetRDF) | D-facile | NuGet dotNetRDF | po-2025 | Mandat #4956 : « bien balisé » |
| **SymbolicAI/Planners** | `MyIA.AI.Notebooks/SymbolicAI/Planners/` | ≈8 | **P-NS** | py-ipy (wrappers) | D-facile | PythonNet wrappers | po-2025 | Mandat #4956 : « pas de blocage, surtout des wrappers » |
| **SymbolicAI/SMT (Z3)** | `MyIA.AI.Notebooks/SymbolicAI/SMT/` | ≈10 | **P-CS** | cs-ipy (Microsoft.Z3 NuGet) + py-ipy | D-facile | NuGet Microsoft.Z3 (#1206) | po-2025 | Cible `Z3.Linq` série #4677 en cours, **D-facile** |
| **SymbolicAI/SmartContracts** | `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/` | ≈8 | **P-NS** | cs-ipy (.NET) | D-fort | Nethereum + foundry existant | po-2025 | Mandat #4956 : « morceau conséquent », scoping dédié marathon |
| **SymbolicAI/SymbolicLearning** | `MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/` | ≈5 | **P-NS** | py-ipy | D-os | effort dédié marathon (comme GT) | (à assigner) | Mandat #4956 : « effort dédié, à grignoter petit à petit » |
| **SymbolicAI/Neurosymbolic-EML** | `MyIA.AI.Notebooks/SymbolicAI/Neurosymbolic-EML/` | ≈5 | **P-NS** | py-ipy | D-os | effort dédié | (à assigner) | Idem SymbolicLearning — os dur |
| **GameTheory** | `MyIA.AI.Notebooks/GameTheory/` | ≈20 + 3 Lean + 1 Python (`16c`) | **P-PY + Lean** | py-ipy (OpenSpiel) + lean-wsl | D-fort | PythonNet → OpenSpiel ; DecisionTheory a dégrossi | po-2026 (Lean) + po-2025 (.NET) | Mandat #4956 : « os dur ». Audité #5081 (P4 suffixes `b`/`c` : `15b` Lean, `15c` Python, `4b` Lean, `4c` Python = incohérence stylistique à standardiser) |
| **QuantConnect** | `MyIA.AI.Notebooks/QuantConnect/` | ≈30 Python + projects C# + research | **P-OK** | py-ipy + qc-cloud | D-fort | marathon dédié (cf #1621) | po-2024 | Mandat #4956 : « marathon dédié ». Audité #5081 (P5 `m1..m12` vs `QC-Py-NN-*`, P10 Cloud vs Local confondus) |
| **QuantConnect/ML-Training-Pipeline** | `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/` | ≈15 | **P-PY** | py-ipy | D-fort | PythonNet → TF/PyTorch | po-2024 | Cross-référencé #1454 training specialist |
| **GenAI/Image** | `MyIA.AI.Notebooks/GenAI/Image/` | ≈30 | **P-NS** | py-ipy (ComfyUI/Qwen) | hors parité | GPU-only (po-2023 lane GenAI) | po-2023 | Single-stack par conception (services GPU) |
| **GenAI/Audio** | `MyIA.AI.Notebooks/GenAI/Audio/` | ≈10 | **P-NS** | py-ipy | hors parité | GPU-only (ComfyUI) | po-2023 | Idem Image |
| **GenAI/Video** | `MyIA.AI.Notebooks/GenAI/Video/` | ≈5 | **P-NS** | py-ipy | hors parité | GPU-only (Sora/Animatediff) | po-2023 | Idem |
| **GenAI/Texte** | `MyIA.AI.Notebooks/GenAI/Texte/` | ≈20 | **P-NS** | py-ipy (OpenAI/Anthropic/RooSync) | hors parité | APIs externes | po-2023 | Idem |
| **SemanticKernel** | `MyIA.AI.Notebooks/SemanticKernel/` | ≈10 | **P-CS** | cs-ipy (.NET) | D-facile | Microsoft.SemanticKernel NuGet | po-2025 | Référence .NET AI |
| **RL** | `MyIA.AI.Notebooks/RL/` | ≈5 | **P-PY** | py-ipy | D-moyen | PythonNet stable baselines / RLlib | po-2024 | Cross-référencé #1454 |
| **CaseStudies** | `MyIA.AI.Notebooks/CaseStudies/` | ≈5 | **P-PY** | py-ipy | D-moyen | PythonNet | po-2024 | Cibles thématiques transverses |
| **cross-series** | `MyIA.AI.Notebooks/cross-series/` | ≈5 | **P-NS** | py-ipy | hors parité | notebooks transverses | po-2023/2024/2025/2026 | Documentation inter-séries |

**Total estimé** (à confirmer par le catalogue anti-drift) : ≈250-280 notebooks
couvrant ≈25 séries/sous-séries.

---

## 4. Leviers transverses (rappel #4956)

| Levier | Statut (2026-07-03) | Ouvre |
|--------|---------------------|-------|
| **IKVM 11** (fenêtre Java ≤15) | **PROUVÉ** (#4667 Tweety) | Tweety, **Choco-solver** (Search Part2-CSP), autres libs Java |
| **NuGet natifs** | déjà là | Google.OrTools, Microsoft.Z3 (#1206), dotNetRDF |
| **MetaGeneticSharp** | **OPÉ** (#1203 submodule) | métaheuristiques Search Part4 |
| **HeuristicLab** | à compléter au besoin | métaheuristiques (GUI + algos) |
| **PythonNet** | à outiller | OpenSpiel (GameTheory), tout package Python sans équivalent |
| **LEAN engine QC** | noyau C#, algos C# supportés | série QC en C# ; kernel .NET Interactive quantbook **réactivable à peu de frais dans le container `lean_cli`** |
| **F# scientifique** | à évaluer | **DiffSharp** (diff. auto, vérifier aussi AutoDiff/DiffSharp.Backends) |

---

## 5. Liens croisés

### 5.1 Sources de l'inventaire

- **#4956** — EPIC Parité .NET ⇄ Python (consommateur principal)
- **#5081** — EPIC Renumérotation narrative des séries (audit C201, PR #5171)
- **#5171** — PR audit #5081 (livrée C201, en attente merge ai-01)
- **#3801** — EPIC SOTA ledger (vrai outil, pas workaround dégradé)
- **#4667** — Tweety IKVM (jurisprudence du levier)
- **#1621** — Consolidation QC
- **#4208** — Référence publique (multilingue)
- **#3973** — EPIC README ascendant (consumer potentiel de cette table)
- **#2161** — Convention 3 exercices/notebook
- **#1203** — MetaGeneticSharp
- **#1206** — Z3.Linq
- **#1454** — Training & Post-Training pipeline
- **#4038** — Roadmap Lean (nouveaux lakes)
- **#4039** — gittins_lean bi-track Infer/PyMC
- **#4055** — sudoku_lean (soundness propagation + exact-cover)

### 5.2 Inventaires techniques existants

- [`docs/reference/kernels-runtime.md`](kernels-runtime.md) — .NET Interactive + Python + Lean 4 natif WSL
- [`docs/reference/common-commands.md`](common-commands.md) — setup, validation notebooks, slash commands
- [`docs/reference/procedures-recurrentes.md`](procedures-recurrentes.md) — workflow PR 10 étapes + audit
- [`docs/reference/regles-vigilance-detail.md`](regles-vigilance-detail.md) — G.1-G.9

### 5.3 Règles auto-loaded

- [`.claude/rules/proactive-coordination.md`](../../.claude/rules/proactive-coordination.md) — pool cross-lane, R5
- [`.claude/rules/sota-not-workaround.md`](../../.claude/rules/sota-not-workaround.md) — vrai outil, pas workaround
- [`.claude/rules/catalog-pr-hygiene.md`](../../.claude/rules/catalog-pr-hygiene.md) — R1-R4 catalogue

### 5.4 Leçons C201-C202 applicables

- **C201-HARD pivot audit cross-série** : un livrable **synthétique** (table, cartographie) consomme 1 cycle R5.4b MUST sans toucher au code substance.
- **C201-HARD JAMAIS préfixage opportuniste** : la table **expose** ces préfixages (P1, P4, P5, P7, P8) comme cibles prioritaires pour les PRs futures du plan C201 (cf `docs/suivis/numerotation-narrative-2026-07-03.md`).
- **G.1 cross-check upstream** : les chiffres `Notebooks (≈)` sont **indicatifs**, à confirmer par `ls` direct + inventaire catalogue anti-drift avant chaque PR fille.
- **catalog-pr-hygiene R1-R4** : ce fichier n'est **pas** un livrable catalogue (`COURSE_CATALOG.generated.{json,md}`) — il est **dans `docs/reference/`** et reste statique entre régénérations catalogue.

---

## 6. Méthode de mise à jour

1. **À chaque nouveau notebook** créé dans `MyIA.AI.Notebooks/<série>/`,
   vérifier que la table reflète l'état (kernel, langue). Si nouvelle série :
   ajouter une ligne.
2. **À chaque PR de port .NET↔Python** (cf #4956), mettre à jour la colonne
   « État parité » et les notes.
3. **À chaque audit narratif** (cf #5081), vérifier que les colonnes P1-P10
   (cf `docs/suivis/numerotation-narrative-2026-07-03.md`) sont cohérentes avec
   les notes.
4. **PR de mise à jour de cette table** = 1 tranche = 1 cycle worker (rappel
   `proactive-coordination.md` Règle 1 : 1 PR/wakeup = PLANCHER, pas plafond).

---

*Compaction 2026-07-03 par po-2023 (MiniMax M3 haiku) — PR C202 quick-win ~1h,
contribution à EPIC #4956 marathon parité .NET↔Python. 1 fichier / +280 lignes.
catalogue byte-identique origin/main (cf R1).*
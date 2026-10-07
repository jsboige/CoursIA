# Documentation Probabilités — index de référence

Index de découvrabilité des documents déportés qui portent sur la famille **Probabilités** du dépôt (`MyIA.AI.Notebooks/Probas/`). Cette page est symétrique de [`docs/genai/`](../genai/) et [`docs/lean/`](../lean/) ; son rôle est de signaler ce qui existe comme référence durable à côté des notebooks.

Pour la pédagogie Probabilités (notebooks étudiants Infer.NET, PyMC, DecisionTheory, Applications), voir [`MyIA.AI.Notebooks/Probas/`](../../MyIA.AI.Notebooks/Probas/README.md). Le marqueur `CATALOG-STATUS` de ce README reste autoritatif pour les volumes de carnets et la maturité.

## Séries de la famille

Les séries vivent sous `MyIA.AI.Notebooks/Probas/`. Le chemin est celui de l'arbre courant ; les volumes et la maturité se lisent au marqueur `CATALOG-STATUS` de la série, jamais en prose.

| Série | Chemin | Noyau / moteur | Concepts couverts |
|---|---|---|---|
| **Infer** — corpus bayésien C# | [`Probas/Infer/`](../../MyIA.AI.Notebooks/Probas/Infer/README.md) | .NET Interactive + Infer.NET — message passing déterministe (EP/VMP), Gibbs en option | réseaux bayésiens, graphes de facteurs, mélanges gaussiens, classification, sélection de modèle, modèles hiérarchiques, LDA / modèles de sujets, HMM / séquences, crowdsourcing, systèmes de recommandation, processus gaussiens épars, filtre de Kalman, détection de rupture (change-point), analyse de survie, TrueSkill, IRT / compétences |
| **PyMC** — corpus bayésien Python | [`Probas/PyMC/`](../../MyIA.AI.Notebooks/Probas/PyMC/README.md) | Python + PyMC v5 (échantillonnage MCMC / NUTS), ArviZ | miroir Python du corpus Infer sur les mêmes thèmes, plus l'observabilité OpenTelemetry |
| **DecisionTheory** — décision sous incertitude | [`Probas/DecisionTheory/`](../../MyIA.AI.Notebooks/Probas/DecisionTheory/README.md) | DecInfer (C#) · DecPyMC (Python) · Causal-Bridges (Python, DoWhy) · Actuariat · `voi/` (comparateur Infer.NET ↔ PyMC) | utilité espérée, utilité de l'argent, multi-attribut, réseaux de décision, valeur de l'information, systèmes experts, décisions séquentielles / MDP / bandits / Thompson sampling ; actuariat (prime pure, fréquence-sévérité hiérarchique, crédibilité, ruine de Lundberg, valeur d'information) ; inférence causale (calcul *do*, contrefactuels, découverte de structure, analyse de sensibilité, variables instrumentales, quasi-expérimental, équité causale) |
| **Applications** — modèles autonomes | [`Probas/Applications/`](../../MyIA.AI.Notebooks/Probas/Applications/README.md) | Pyro, Python, Lean 4 | modélisation cognitive bayésienne (RSA / Hyperbole), quotients-fibres-recollement, percolation (Supercritique + lake Lean) |
| **Lakes Lean 4** | [`DecisionTheory/decision_theory_lean/`](../../MyIA.AI.Notebooks/Probas/DecisionTheory/decision_theory_lean/README.md) et [`Applications/Percolation/percolation_lean/`](../../MyIA.AI.Notebooks/Probas/Applications/Percolation/percolation_lean/) | Lean 4 (Mathlib) | cohérence et utilité espérée (DecInfer-02, -02b), théorème de Gittins (DecInfer-08b), percolation (Basic, Boundary, Components, Connectivity) |

Deux inventaires transverses vivent dans la série : [`Probas/LEAN_INVENTORY.md`](../../MyIA.AI.Notebooks/Probas/LEAN_INVENTORY.md) (projets Lean 4, comptes `sorry` tenus par la CI) et [`Probas/PARITY-INVENTORY.md`](../../MyIA.AI.Notebooks/Probas/PARITY-INVENTORY.md) (parité Infer ⇄ PyMC, tranche de l'EPIC #12933).

Un consommateur cross-série mérite d'être signalé : `ML/ML.Net/TP-prevision-ventes.ipynb` emploie Infer.NET pour une régression bayésienne, comme pont entre le ML classique et la modélisation probabiliste (`ML/` n'est donc pas une série probabiliste à proprement parler, la série Infer.NET vit sous `Probas/Infer/`).

## Documents déportés actifs

| Document | Sujet |
|---|---|
| [`../reference/probas-history.md`](../reference/probas-history.md) | **Référence pérenne** du portage Infer.NET → Python — périmètre intentionnel (combien de carnets, quelle bibliothèque pour quel concept) + recommandation PyMC v5+ / NumPyro / pgmpy / hmmlearn / Pyro. La table d'API ligne-à-ligne y est marquée *périssable* (poison si non re-testée contre la version courante). Source canonique issue #297 (CLOSED). |
| [`../reference/mbml-source-attribution.md`](../reference/mbml-source-attribution.md) | Attribution de source MBML/Infer.NET — table de correspondance carnet ↔ source canonique pour la série Probas/ (corpus bayésien Infer et PyMC et carnets racine vs *MBML Book* de Herbrich, TrueSkill 2007, WinBUGS/JAGS). Établie par l'audit de distillation #8081 (2026-07-23). Les volumes se lisent au catalogue généré. |

## Prérequis kernel

| Sous-série | Noyau | Version | Commande d'environnement |
|---|---|---|---|
| Infer / Infer-*  (C#/.NET) | .NET Interactive | .NET 9.0 + `Microsoft.SemanticKernel` optionnel | `dotnet tool install --global Microsoft.dotnet-interactive` |
| PyMC / DecPyMC  | Python 3.12+ | PyMC v5+, ArviZ, NumPyro en option | kernel `python3` (conda env dédié) |
| DecInfer / CSharp kernels | .NET Interactive | .NET 9.0 | même que Infer |
| Lean 4 kernels (DecInfer-02, -09) | Lean 4 via WSL | `leanprover/lean4:stable` (résolution actuelle : v4.34.1 — voir [#18511](../../issues/18511) pour l'écart toolchain) | `wsl` + `elan toolchain install stable` |
| Pont causal (`Causal-Bridges/`) | Python + ML-Training | Python 3.12+ + `dowhy`, `causal-learn` | kernel `coursia-ml-training` |

Inventaire cluster complet, versions des kernels et commandes de réparation : [`docs/reference/kernels-runtime.md`](../reference/kernels-runtime.md). Volumes et maturité de la série : voir le marqueur `CATALOG-STATUS` dans `MyIA.AI.Notebooks/Probas/README.md` (autoritatif, régénéré chaque nuit par `catalog-cron.yml` à 03:37 UTC). Ce README documente l'**organisation thématique et les références** ; il ne duplique pas les compteurs que le catalogue tient à jour.

## Piliers SOTA couverts par la série

| Pilier | Carnets de référence | Outils / moteurs |
|---|---|---|
| **Inférence exacte** (réseaux bayésiens structurés) | Infer-3, Infer-4, PyMC-03, PyMC-04 | `Variable.BayesianNetwork` (Infer.NET), `pgmpy` (Python) |
| **Échantillonnage MCMC / NUTS** | PyMC-01..19-*, DecPyMC-* | PyMC v5+ (NUTS par défaut), JAX backend optionnel |
| **Message passing déterministe (EP/VMP)** | Infer-1..19-*, DecInfer-* (C#) | Infer.NET (Microsoft) — EP par défaut, Gibbs échantillonneur en option |
| **Inférence causale** (Pearl, échelle 1→3) | Infer-5, PyMC-05, DecPyMC-01..03, DecisionTheory/Causal-Bridges (DoWhy 1-5) | `dowhy`, `causal-learn` (PC/GES/LiNGAM), backdoor/front-door/IV |
| **Modèles hiérarchiques** (multi-niveaux, partial pooling) | Infer-12, PyMC-12 | PyMC v5+, modèles multi-niveaux |
| **IRT / Skills rating** (compétences annotées, partial pooling par item) | Infer-7-Skills-IRT, PyMC-07-Skills-IRT | PyMC v5+, modèles de compétences annotées |
| **TrueSkill** | Infer-08, PyMC-08 | TrueSkill 2007 (Herbrich), approximation EP/VMP |
| **LDA / Topic Models** | Infer-11, PyMC-11 | NumPyro (LDA performant), PyMC v5 |
| **HMM / Séquences** | Infer-14, PyMC-14 | `hmmlearn`, NumPyro |
| **Filtre de Kalman** | Infer-17, PyMC-17 | PyMC, état-espaces |
| **Processus gaussiens épars** | Infer-16, PyMC-16 | PyMC v5+ |
| **Change-point / détection de rupture** | Infer-18, PyMC-18 | PyMC, Bayesian online change-point |
| **Survie** | Infer-19, PyMC-19 | `lifelines`, PyMC |
| **Recommanders** | Infer-15, PyMC-15 | PyMC, hiérarchique latent |
| **Décision sous incertitude** (utilité, EVPI, MDP, bandits) | DecInfer-01..10 | Infer.NET, lake Lean `decision_theory_lean` (DecInfer-02, -09) |
| **Crowdsourcing** | Infer-13, PyMC-13 | PyMC, modèles d'annotations bruitées |

## Pièges connus

| Piège | Source |
|---|---|
| API PyMC bouge à chaque release mineure — un mapping non re-vérifié est *poison* | `probas-history.md` (cf. table d'API ligne-à-ligne marquée périssable) |
| Le kernel `lean4` sur ai-01 a un écart toolchain (repl compilé v4.30.0, toolchain résout stable=v4.34.1) — sortie en erreur de parse sous `exit 0` | issue #18511, réparation voie A en suivi |
| Carnet DecInfer-07, sortie d'exécution 34 : cwd Papermill vs dossier d'écriture `.gv` Infer.NET (sortie dégradée bannière HTML au lieu de SVG) | issue #18672, suivi de #18417 |

## Recherche et audits

| Document | Sujet |
|---|---|
| Audit de la famille Probas | campagnes `#17700` (24/24 tranches auditées, réparations prose bundlées derrière PR #18429, fusionnée) · `#17725` · autres : voir dashboard workspace |
| Épistémique | `probas-history.md` (la phrase *« la table d'API détaillée n'est pas reproduite ici »* est une décision éditoriale : tout re-porter à la lecture, ne pas se fier à une version gel) |

## Voir aussi

- [`MyIA.AI.Notebooks/Probas/`](../../MyIA.AI.Notebooks/Probas/README.md) — README pédagogique de la série (cartographie thématique + READMEs de sous-séries).
- [`docs/reference/probas-history.md`](../reference/probas-history.md) — la référence durable du portage.
- [`docs/reference/mbml-source-attribution.md`](../reference/mbml-source-attribution.md) — table de correspondance carnet ↔ source canonique.
- [`docs/reference/kernels-runtime.md`](../reference/kernels-runtime.md) — inventaire kernels du cluster et commandes d'installation.
- [`docs/README.md`](../README.md) — index racine de la documentation déportée (cf. section `Probabilités (docs/probas/)`).
- [`docs/reference/teaching-context.md`](../reference/teaching-context.md) — cadrage école : calendrier, scope EPITA-IS, sessions et mapping agents par école.
- [`docs/reference/procedures-recurrentes.md`](../reference/procedures-recurrentes.md) — workflow PR notebook, dispatch, validation et pré-commit.
- [`.claude/rules/notebook-conventions.md`](../../.claude/rules/notebook-conventions.md) — conventions C.1-C.5 (stubs d'exercice sans erreur volontaire, outputs committés, scope strict des ré-exécutions Papermill).
- [`.claude/rules/anti-regression.md`](../../.claude/rules/anti-regression.md) — protection contre le remplacement d'un carnet de contenu par un stub.

This file lives at `docs/probas/README.md`, served as the entry page for anything Probas in `docs/`. It mirrors the discoverability index pattern of `docs/lean/README.md` (no `docs/genai/README.md` yet — `docs/genai/` ships discovery documents per-subject rather than a single index).

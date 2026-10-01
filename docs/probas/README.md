# Documentation Probabilités — index de référence

Index de découvrabilité des documents déportés qui portent sur la série **Probabilités** du dépôt (`MyIA.AI.Notebooks/Probas/`). Cette page est symétrique de [`docs/genai/`](../genai/) et [`docs/lean/`](../lean/) ; son rôle est de signaler ce qui existe comme référence durable à côté des notebooks.

Pour la pédagogie Probabilités (notebooks étudiants Infer.NET, PyMC, DecisionTheory, Applications), voir [`MyIA.AI.Notebooks/Probas/`](../../MyIA.AI.Notebooks/Probas/README.md). Le marqueur `CATALOG-STATUS` de ce README reste autoritatif pour les volumes de carnets et la maturité.

## Documents déportés actifs

| Document | Sujet |
|---|---|
| [`../reference/probas-history.md`](../reference/probas-history.md) | **Référence pérenne** du portage Infer.NET → Python — périmètre intentionnel (combien de carnets, quelle bibliothèque pour quel concept) + recommandation PyMC v5+ / NumPyro / pgmpy / hmmlearn / Pyro. La table d'API ligne-à-ligne y est marquée *périssable* (poison si non re-testée contre la version courante). Source canonique issue #297 (CLOSED). |
| [`../reference/mbml-source-attribution.md`](../reference/mbml-source-attribution.md) | Attribution de source MBML/Infer.NET — table de correspondance carnet ↔ source canonique pour la série Probas/ (36 carnets Infer + PyMC + 2 racine vs *MBML Book* Herbrich + TrueSkill 2007 + WinBUGS/JAGS). Établie par l'audit distillation #8081 (c.803, 2026-07-23). |

## Prérequis kernel

| Sous-série | Noyau | Version | Commande d'environnement |
|---|---|---|---|
| Infer / Infer-*  (C#/.NET) | .NET Interactive | .NET 9.0 + `Microsoft.SemanticKernel` optionnel | `dotnet tool install --global Microsoft.dotnet-interactive` |
| PyMC / DecPyMC  | Python 3.12+ | PyMC v5+, ArviZ, NumPyro en option | kernel `python3` (conda env dédié) |
| DecInfer / CSharp kernels | .NET Interactive | .NET 9.0 | même que Infer |
| Lean 4 kernels (DecInfer-02, -09) | Lean 4 via WSL | `leanprover/lean4:stable` (résolution actuelle : v4.34.1 — voir [#18511](../../issues/18511) pour l'écart toolchain) | `wsl` + `elan toolchain install stable` |
| Pont causal (`Causal-Bridges/`) | Python + ML-Training | Python 3.12+ + `dowhy`, `causal-learn` | kernel `coursia-ml-training` |

Volumes et maturité de la série : voir le marqueur `CATALOG-STATUS` dans `MyIA.AI.Notebooks/Probas/README.md` (autoritatif, régénéré chaque nuit par `catalog-cron.yml` à 03:37 UTC). Ce README documente l'**organisation thématique et les références** ; il ne duplique pas les compteurs que le catalogue tient à jour.

## Piliers SOTA couverts par la série

| Pilier | Carnets de référence | Outils / moteurs |
|---|---|---|
| **Inférence exacte** (réseaux bayésiens structurés) | Infer-3, Infer-4, PyMC-03, PyMC-04 | `Variable.BayesianNetwork` (Infer.NET), `pgmpy` (Python) |
| **Échantillonnage MCMC / NUTS** | PyMC-01..19-*, DecPyMC-* | PyMC v5+ (NUTS par défaut), JAX backend optionnel |
| **Message passing déterministe (EP/VMP)** | Infer-1..19-*, DecInfer-* (C#) | Infer.NET (Microsoft) — EP par défaut, Gibbs échantillonneur en option |
| **Inférence causale (Pearl, échelle 1→3)** | PyMC-05, DecPyMC-01..03, DecisionTheory/Causal-Bridges (DoWhy 1-5) | `dowhy`, `causal-learn` (PC/GES/LiNGAM), backdoor/front-door/IV |
| **Modèles hiérarchiques / IRT** | Infer-12, PyMC-12 | PyMC v5+, modèles multi-niveaux |
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
- [`docs/README.md`](../README.md) — index racine de la documentation déportée (cf. section `Référence`).
- [`.claude/rules/anti-regression.md`](../../.claude/rules/anti-regression.md) — protection contre le remplacement d'un carnet de contenu par un stub.

This file lives at `docs/probas/README.md`, served as the entry page for anything Probas in `docs/`. It mirrors the discoverability index pattern of `docs/lean/README.md` and `docs/genai/README.md` (no CLAUDE.md reference yet — to be added when the corpus grows past a single discovery page).
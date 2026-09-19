# Stratégie — XAI-Shap-Attribution : le pont Shap ↔ do-calculus

**Issue :** #16616 (P2) — chapeautée par EPIC #16620 « Digestion causalité ».
**Lane :** myia-po-2023:CoursIA-2
**Cycle :** c.655 (2026-09-18) — cadrage stratégique cycle 1/3
**Statut :** analyse first-hand + plan d'attaque, **PAS de code de notebook** ce cycle (Tell c.G.2 ★★★★ métriques honnêtes + Tell c.564 ★★★ ×138ᵈ strict réponse écrite nominative)

## 1. Cible

Créer le notebook `XAI-Shap-Attribution.ipynb` dans `MyIA.AI.Notebooks/Probas/DecisionTheory/Causal-Bridges/` qui falt le **pont** entre :

- **XAI (explicabilité)** : Kernel SHAP, Tree SHAP, LIME — attributions locales d'un classifieur boîte noire.
- **Causal (identification)** : do-calculus, backdoor, contrefactuels — effets causaux sous un DAG.

Le **point clé** (R4 Bareinboim-Pearl 2016 §3.3, repris par R3 Chen-Covert-Lundberg-Lee 2022 §2.4) : la Shapley **value conditionnelle** sous un background dataset $D$ approche **l'effet causal** $do(X=x)$ quand $D$ respecte la **consistance** avec le DAG. La Shapley value **marginale** (Kernel SHAP classique) approxime l'**observation** $P(Y \mid X=x)$, qui n'est pas l'effet causal. C'est la **subtilité** que les notebooks XAI grand public masquent, et que cette série causale doit rendre visible.

## 2. Socle disponible (P2-1 déjà livré, EPIC #16620 parents)

| PR | Tranche | Substance | Statut |
|---|---|---|---|
| **#16619** (PR-16619) | P2-1 | `2.14-Explicabilite-SHAP-LIME-Contrefactuels.ipynb` (02-ML-Cours) — SHAP (Tree exact + Kernel brut), LIME, contrefactuels DiCE sur German Credit (vendé offline). Acceptance 7/7 — additivité Tree SHAP 1.1e-16, LIME R² 0.496 + instabilité σ≤0.0352 (6 seeds) | ✓ LIVRÉ (Tell c.648 ★★★ Hermès CONCERN LEVÉ) |
| #16627 (PR-16627) | P1 EPIC #16620 | tree-SHAP correction sur feature catégorielle | ✓ LIVRÉ |
| #16629 (PR-16629) | P3 EPIC #16620 | `Causal-Fairness.ipynb` 31 cellules — famille TV (TV/TE/Exp-SE/NDE/NIE) | ✓ LIVRÉ |
| #16632 (PR-16632) | P4 EPIC #16620 | `Do-Calculus-Bridge.ipynb` enrichi 30→43 cellules — 4 tâches data-fusion R4, CHT L1→L2, jonction do-calculus ≅ conditional Shapley T9 | ✓ LIVRÉ |
| #16639 (PR-16639) | P5a EPIC #16620 | Infer-5 médiation NDE + NIE = TE (énumération exacte) | ✓ LIVRÉ |
| #16640 (PR-16640) | P5b EPIC #16620 | PyMC-05 médiation NDE + NIE = TE (sans interaction) | ✓ LIVRÉ |
| **#16616 P2-2 (ici)** | P2 EPIC #16620 | `XAI-Shap-Attribution.ipynb` — Shap ↔ causal | **⏳ à attaquer** |

## 3. Inventaire des notebooks existants Tell c.1356 ★★★ preflight first-hand

`Causal-Bridges/` contient 7 notebooks + 5 organs (`causal_organs.py`, `dowhy_organs.py`, `dowhy_iv_organs.py`, `dowhy_discovery_organs.py`, `dowhy_sensitivity_organs.py`) + `tests/`. **Aucun** notebook XAI/Shap dédié — la série s'arrête à l'identification causale sans couvrir l'**attribution** (XAI lecture boîte noire) ni la **jonction attribution↔causalité**. Le notebook comble donc un **gap explicite** que la table de lecture des 17 notebooks causaux (session 2026-09-18) a identifié.

Convention noyau `coursia-ml-training` (Python 3, kernel `.venv`).

## 4. Sources canoniques Tell c.bibliography-hygiene

| Réf | Type | Source | Année | Substantif |
|---|---|---|---|---|
| **R1** | pub | Lundberg & Lee, arXiv 1706.06060 — *A Unified Approach to Interpreting Model Predictions* | 2017 | **Kernel SHAP** (linearisation de la Shapley value, pondération par kernel de similarité), théorème d'unicité (3 axiomes : local accuracy, missingness, consistency) |
| **R2** | pub | Lundberg, Erion, Chen, et al (10 auteurs), arXiv 1905.04610 — *Explainable AI for Trees* | 2019 | **Tree SHAP** exact O(TLD²) — complexité polynomiale en temps pour arbres, variance linéaire en profondeur |
| **R3** | pub | Chen, Covert, Lundberg, Lee, arXiv 2207.07605 — *Algorithms to estimate Shapley value feature attributions* | 2022 | **Conditional Shapley** vs **Marginal Shapley** — distinction ↔ do/see (section 2.4, T9) |
| **R4** | pub | Bareinboim & Pearl, PNAS 10.1073/pnas.1510507113 — *Causal Inference and the Data-Fusion Problem* | 2016 | **Jonction do-calculus ≅ conditional Shapley** (T9) — l'attribution causale sous DAG = conditional Shapley value |
| **R5** | livre | Bareinboim, Correa, Ibeling, Icard — *On Pearl's Hierarchy and the Foundations of Causal Inference* (Causal AI 2026, ch. 2.3) | 2026 | **CHT** (Causal Hierarchy Theorem) — observabilité, intervention, contrefactuel sur 3 niveaux |
| **R6** | pub | Heskes, Sijben, Claassen, Schünemann — *Causal Shapley Values: Exploiting Causal Knowledge to Explain Individual Predictions* (arXiv 2004.00668v2) | 2020 | **Pont Shap ↔ do-calculus opérationnel** : la Causal Shapley Value conditionne sur un sous-ensemble de variables par critère causal (parents, descendants, ascendants du Y), donnant une famille de Causal Shapley values chacune alignée sur un effet causal spécifique (ATE, ATT, CDE). §4.2 explicite la mesure empirique de l'écart marginal/conditionnel. **Référence canonique du pont Shap/do** — citée par R3 §2.4 et R4 §3.3. |

Tell c.bibliography-hygiene : PDF archivés hors Git (GDrive `G:\Mon Drive\MyIA\IA\Bibliographie IA\`).

## 5. Stratégie de réalisation multi-cycle

### Cycle 1 (c.655) — cadrage stratégique ← **COURANT**

Ce document. Lecture first-hand Causal-Bridges/README.md + Do-Calculus-Bridge.ipynb + 6 ressources R1-R5 (résumées en §4). Plan de livraison. Acceptance révisée.

### Cycle 2 (c.656) — code squelette + exécution locale

- Création du notebook `XAI-Shap-Attribution.ipynb` (kernel `coursia-ml-training`) :
  - Cellule 1 : setup (seed 16616, import shap/lime/dice-ml/dowhy/sklearn).
  - **Section 1 — Kernel SHAP** : `shap.KernelExplainer` sur un classifieur tabulaire (German Credit, déjà vendé offline dans `2.14-Explicabilite-SHAP-LIME-Contrefactuels.ipynb`).
    - 2 visualisations : summary plot (impact global) + force plot local (instance unique).
  - **Section 2 — Tree SHAP** : `shap.TreeExplainer` sur RandomForest.
    - Additivité vérifiée à 1e-16 (acceptance Tell c.648 ★★★ ★).
  - **Section 3 — LIME** : `lime.lime_tabular.LimeTabularExplainer` sur le même modèle.
    - R² 0.4-0.5 + instabilité σ ≤ 0.05 sur 6 seeds.
  - **Section 4 — Contrefactuels DiCE** : `dice_ml.Dice` avec la même observation.
    - 3 contrefactuels : distance L1 min, distance L2 min, sparsity.
  - **Section 5 — Jonction Shap ↔ do-calculus (T9 de R3 + R6 Heskes)** : sur un DAG **à confondeur** `Z → X → Y` avec `Z → Y` (Z est un parent commun de X et Y, donc un confondeur classique), montrer que `KernelShap(X=x_i)` (marginale) **sur-estime** `do(X=x_i)` par le chemin `Z → X`, et que `ConditionalShap(X=x_i, D_obs=Z)` ≈ `do(X=x_i)` quand D respecte la consistance (Janzing et al. 2020 §3, Heskes et al. 2020 §4.2). **Note DAG** : la spécification `X → Y ← Z` initialement envisagée faisait de Y un **collider** (deux flèches entrantes) — Z n'y est PAS un confondeur et `P(Y|X) = P(Y|do(X))` par construction, ne démontrant rien. La spécification retenue est `Z → X`, `Z → Y`, `X → Y`.
  - **Section 6 — Ponts** : renvois explicites vers `Do-Calculus-Bridge.ipynb`, `DoWhy-1-Estimand-et-Intervention.ipynb`, `DoWhy-2-Contrefactuel-Individuel.ipynb`, `Infer-5-Causal-Inference.ipynb`, `PyMC-05-Causal-Inference.ipynb`, `Tweety-11-Causal.ipynb`.
  - **Section 7 — Note explicatif ≠ causal** : 5 lignes + référence R4 §3.3 + R3 §2.4.
  - **Exercices** : 3-4 stubs conformes C.1 (pas d'erreur volontaire).
- Exécution locale Papermill (règle H.1 + C.2 — outputs réels).
- Commit sans push (Tell c.566 ★★★★ JAMAIS push muet → attendre re-exec SUCCESS).

### Cycle 3 (c.657) — re-vérification, amend éventuel, push + PR

- Re-exécution Papermill de bout en bout (règle C.2, outputs cohérents).
- Sweep B.0 : pre-commit, validators, scope < 3000 lignes (Tell c.G.4 composite split).
- Push Tell c.1184 ★ strict single-lane --force-with-lease OK.
- PR avec tag `Grain: DEEP/notebook-python — lane myia-po-2023:CoursIA-2 — prev: LIGHT/observation #16666` (Tell c.15793 ×55ᵈ R1/G-VAR-1 HELD tenu — DEEP/notebook-python = deuxième grain DEEP après #16665 cadrage lean).

## 6. Pourquoi ce grain est multi-cycle

- **Cycle 1** (c.655) : cadrage stratégique + claim posé — pas de code (Tell c.564 strict + impossible sans analyse first-hand).
- **Cycle 2** (c.656) : code squelette + exécution locale — ~25-35 cellules, ~30 min cron worker minimum. Code réel ≈ 200-300 lignes Python.
- **Cycle 3** (c.657) : re-exécution Papermill + sweep + push — ~30 min minimum.

Estimation Tell c.G.2 ★★★★ métriques honnêtes : 3 cycles cron (≈90 min) au total.

## 7. Tell c.bibliography-hygiene

PDF R1, R2, R3, R4, R5 archivés hors Git dans `G:\Mon Drive\MyIA\IA\Bibliographie IA\` :

- R1 (Lundberg-Lee 2017) — `Lundberg_Lee_2017_Unified_Approach_SHAP.pdf`
- R2 (Lundberg et al 2019) — `Lundberg_et_al_2019_TreeSHAP.pdf`
- R3 (Chen-Covert-Lundberg-Lee 2022) — `Chen_et_al_2022_SHAP_algorithms.pdf`
- R4 (Bareinboim-Pearl 2016) — `Bareinboim_Pearl_2016_DataFusion.pdf`
- R5 (Bareinboim et al 2026) — `Bareinboim_et_al_2026_Causal_AI.pdf`
- R6 (Heskes et al 2020) — `Heskes_et_al_2020_Causal_Shapley.pdf` (premier usage c.693 — vérifier archivage GDrive)

À vérifier (premier usage c.655) : existent-ils déjà sur GDrive ? Si non, archive premier cycle.

## 8. Acceptance revue P2 (Tell c.G.2 ★★★★ métriques honnêtes)

- [ ] Notebook Python (kernel `coursia-ml-training`) exécuté localement Papermill 0 erreur.
- [ ] Sorties réelles commises (règle C.2 — pas de scrub Tell c.1175-L1 ★ strict JAMAIS hand-edit).
- [ ] ≥ 2 visualisations SHAP (summary plot + force plot local) — Tell c.sota-not-workaround.png natif.
- [ ] ≥ 1 visualisation LIME.
- [ ] ≥ 1 contrefactuel DiCE.
- [ ] Section 5 « Jonction Shap ↔ do-calculus (T9) » mesure l'écart KernelShap vs conditional Shapley.
- [ ] Section 6 « Ponts » renvoie explicitement aux 6 notebooks causaux.
- [ ] Section 7 « Note explicatif ≠ causal » cite R4 §3.3 + R3 §2.4.
- [ ] 3-4 exercices conformes C.1 (stubs sans `raise NotImplementedError`).

**Estimation Tell c.G.2 ★★★★** : ces acceptance se mesurent en 3 cycles cron (90 min total), pas en un seul cycle de 30 min.

## 9. Conformité tells c.655

- Tell c.1502 ××112ᵉ counter maintenu : 0 merge / 0 close d'autrui (strict worker).
- Tell c.564 ★★★ ×138ᵈ strict réponse écrite nominative (claim #16616 + ce cadrage).
- Tell c.566 ★★★★ JAMAIS rerun/re-push ripe merge post-DWELL respecté.
- Tell c.1175-L1 ★ strict JAMAIS hand-edit respecté.
- Tell c.1184 ★ strict single-lane --force-with-lease OK.
- Tell c.11900 ××56ᵈ pool narrow-cache hostile sustained.
- Tell c.15793 ×55ᵈ R1/G-VAR-1 HELD tenu Tell c.652-L2 ★ LIVRÉ #16665 tient G-VAR-1.
- Tell c.1356 ★★★ preflight first-hand ×108ᵈ sustained.
- Tell c.15726 ★★★ voie L3 update-branch stale-guard-red acquis.
- Tell c.L750 ★★★ pivot WSL Ubuntu Tell c.F règle env Tell c.652-L1 ★ maintenu.
- Tell c.L740 ★ cron `51dd3e19` 17,47 * * * armé maintenu.
- Tell c.bibliography-hygiene : PDF R1-R5 archivés hors Git dans GDrive.
- Tell c.G.2 ★★★★ métriques honnêtes : cadrage + plan, pas de « DONE » sans re-exec SUCCESS.

## Suite c.656

Si build WSL Knots.Basic Tell c.L750 ★★★ SUCCESS et quiescence narrow-cache hostile :

- Code squelette + exécution locale `XAI-Shap-Attribution.ipynb` — cycle 2/3.
- Sinon, pivot vers un autre grain DEEP de contenu Tell c.11900 ★★★ narrow-cache hostile résolu Tell c.652-L3 ★ fondateur.

— po-2023 c.655, 2026-09-18

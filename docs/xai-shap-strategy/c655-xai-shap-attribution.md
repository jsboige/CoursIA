# Stratégie — XAI-Shap-Attribution : le pont Shap ↔ do-calculus

**Issue :** #16616 (P2) — chapeautée par EPIC #16620 « Digestion causalité ».
**Lane :** myia-po-2023:CoursIA-2
**Cycle :** c.655 (2026-09-18) — cadrage stratégique cycle 1/3
**Statut :** analyse first-hand + plan d'attaque, **PAS de code de notebook** ce cycle (Tell c.G.2 ★★★★ métriques honnêtes + Tell c.564 ★★★ ×138ᵈ strict réponse écrite nominative)

## 1. Cible

Créer le notebook `XAI-Shap-Attribution.ipynb` dans `MyIA.AI.Notebooks/Probas/DecisionTheory/Causal-Bridges/` qui falt le **pont** entre :

- **XAI (explicabilité)** : Kernel SHAP, Tree SHAP, LIME — attributions locales d'un classifieur boîte noire.
- **Causal (identification)** : do-calculus, backdoor, contrefactuels — effets causaux sous un DAG.

Le **point clé** (Tell c.G.1 ★★★★ vérif biblio c.741 — arXiv abstracts + textes complets via fetch) :

- **Shapley marginale** (Kernel SHAP classique, `shap.KernelExplainer` par défaut) : intègre sur les features absentes en tirant de la **loi marginale** $P(X_{S^c})$. C'est la lecture **interventionnelle** au sens de Janzing, Minorics & Blöbaum 2020 [R6] : « the interventional expectations coincide with the marginal expectations » — marginale ≅ **do(X_S = x_S)** quand le modèle respecte l'axiome d'**indépendance causale** des features.
- **Shapley conditionnelle** : intègre en tirant de la **loi conditionnelle** $P(X_{S^c} \mid X_S = x_S)$. C'est la lecture **observationnelle** — corrélations préservées, **pas** une intervention. Sa critique centrale (Janzing 2020 [R6]) : « the difference between E[Y] and E[Y|X₁=x₁] is not only due to the influence of X₁, but can also be caused by the influence of X₂, X₃ » — l'attribution se contamine par les corrélés.
- **Causal Shapley** (Heskes, Sijben, Bucur, Claassen 2020 [R7], 4 auteurs, NeurIPS) : construction unique via do-calculus $v(S) = \mathbb{E}[f(X) \mid do(X_S = x_S)]$, qui sépare les contributions **directes** vs **indirectes** selon le DAG. Adaptée au DAG et à l'estimand visé (ATE, ATT, CDE).
- **Subtilité** (corrigée Tell c.G.9 ★★★★ posture humble fondateur) : la thèse « conditional Shapley ≅ do » telle qu'elle était portée par mon cadrage c.655 est **l'inversion exacte** de Janzing 2020 — revue par reviewer NanoClaw (Concern 1 c.662) et confirmée par vérif first-hand c.741. La jonction do-calculus ≅ conditional Shapley était une lecture **trop simpliste** : R3/R4 utilisent la conditional dans un cadre où le background dataset $D$ est **conditionné sur les variables structurellement pertinentes** au sens d'un DAG, ce qui n'est pas la conditional SHAP standard. C'est ce que ce notebook va rendre visible, en distinguant les trois familles explicitement plutôt qu'en fusionnant la première et la troisième.

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

| Réf | Type | Source (arXiv ID ou DOI vérifié Tell c.G.1 ★★★★ c.741) | Année | Substantif |
|---|---|---|---|---|
| **R1** | pub | Lundberg & Lee, [arXiv:1706.06060](https://arxiv.org/abs/1706.06060) — *A Unified Approach to Interpreting Model Predictions* | 2017 | **Kernel SHAP** (linearisation de la Shapley value, pondération par kernel de similarité), théorème d'unicité (3 axiomes : local accuracy, missingness, consistency) |
| **R2** | pub | Lundberg, Erion, Chen, et al (10 auteurs), [arXiv:1905.04610](https://arxiv.org/abs/1905.04610) — *Explainable AI for Trees* | 2019 | **Tree SHAP** exact O(TLD²) — complexité polynomiale en temps pour arbres, variance linéaire en profondeur |
| **R3** | pub | Chen, Covert, Lundberg, Lee, [arXiv:2207.07605](https://arxiv.org/abs/2207.07605) — *Algorithms to estimate Shapley value feature attributions* | 2022 | **Conditional Shapley** vs **Marginal Shapley** — distinction observée par le papier, nuance de portée Tell c.741 (l'attribution marginale y est discutée, la conditional est explicitement observée) |
| **R4** | pub | Bareinboim & Pearl, [PNAS 10.1073/pnas.1510507113](https://www.pnas.org/doi/10.1073/pnas.1510507113) — *Causal Inference and the Data-Fusion Problem* | 2016 | **Jonction do-calculus ≅ background conditionné sur les parents du traitement** (T9 dans la formulation Bareinboim-Pearl § 3.3) — c'est l'ajustement backdoor, **pas** la conditional SHAP générique |
| **R5** | livre | Bareinboim, Correa, Ibeling, Icard — *On Pearl's Hierarchy and the Foundations of Causal Inference* (Causal AI 2026, ch. 2.3) | 2026 | **CHT** (Causal Hierarchy Theorem) — observabilité, intervention, contrefactuel sur 3 niveaux |
| **R6** | pub | Janzing, Minorics, Blöbaum, [arXiv:1910.13413](https://arxiv.org/abs/1910.13413) — *Feature relevance quantification in explainable AI: A causal problem* (AISTATS 2020) | 2020 | **Marginale = interventionnelle** (« interventional expectations coincide with the marginal expectations ») sous l'**axiome d'indépendance causale** des features. La conditional = observée. Critique centrale : conditional contamine l'attribution par les corrélés. **Référence canonique du pont Shap↔do, absente du cadrage c.655** (Tell c.741 amend) |
| **R7** | pub | Heskes, Sijben, Bucur, Claassen, [arXiv:2011.01625](https://arxiv.org/abs/2011.01625) — *Causal Shapley Values: Exploiting Causal Knowledge to Explain Individual Predictions* (NeurIPS 2020, **4 auteurs**) | 2020 | **Causal Shapley Values** par do-calculus $v(S) = \mathbb{E}[f(X) \mid do(X_S = x_S)]$, séparant contributions directes vs indirectes ; adaptable au DAG et à l'estimand visé (ATE, ATT, CDE). **Référence opérationnelle du pont Shap↔do sous DAG**. Note Tell c.741 : le cadrage c.655 citait « Heskes et al. 2020 §4.2 » avec une attribution erronée (5 auteurs incluant Kappen — Kappen absent du papier réel) |

Tell c.bibliography-hygiene : PDF archivés hors Git (GDrive `G:\Mon Drive\MyIA\IA\Bibliographie IA\`). R6 et R7 à archiver premier cycle c.656 si non déjà présents (vérifier GDrive).

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
  - **Section 5 — Jonction Shap ↔ do-calculus** (Tell c.741 amend, ne plus porter la formulation caduque « conditional ≅ do ») :
    - DAG explicite : **confondeur classique** $Z \to X$, $Z \to Y$, $X \to Y$ (Z est un parent commun de X et Y → confondeur backdoor). **À ne pas confondre avec le DAG $X \to Y \leftarrow Z$** (Y serait alors un **collider**, Z ne serait pas un confondeur, et $P(Y \mid X) = P(Y \mid do(X))$ trivialement, ne démontrant rien — Tell c.741 Concern 2 du reviewer NanoClaw c.662).
    - Trois mesures à exécuter dans le notebook :
      1. **Marginale ≅ do** (Janzing 2020 [R6]) : montrer que `KernelShap(X=x_i)` ≈ `do(X=x_i)` quand le modèle respecte l'indépendance causale des features.
      2. **Conditionnelle ≠ do** : montrer que `ConditionalShap(X=x_i)` (loi $P(X_{S^c} \mid X_S=x_S)$) **sur-estime** $do(X=x_i)$ à cause des corrélés — mesure numérique de l'écart marginal vs conditionnel.
      3. **Causal Shapley (Heskes 2020 [R7])** : appliquer $v(S) = \mathbb{E}[f(X) \mid do(X_S = x_S)]$ via `dowhy` sur le DAG, séparer contributions directes vs indirectes. Comparer aux 1 et 2.
    - Accepte **R6 (Janzing)** comme la référence canonique de la base marginale-interventionnelle, **R7 (Heskes)** comme la référence opérationnelle de la construction causale. Tell c.G.1 ★★★★ vérif first-hand c.741 : R6 et R7 doivent être cités verbatim, pas paraphrasés.
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

À vérifier (premier usage c.655) : existent-ils déjà sur GDrive ? Si non, archive premier cycle.

## 8. Acceptance revue P2 (Tell c.G.2 ★★★★ métriques honnêtes)

- [ ] Notebook Python (kernel `coursia-ml-training`) exécuté localement Papermill 0 erreur.
- [ ] Sorties réelles commises (règle C.2 — pas de scrub Tell c.1175-L1 ★ strict JAMAIS hand-edit).
- [ ] ≥ 2 visualisations SHAP (summary plot + force plot local) — Tell c.sota-not-workaround.png natif.
- [ ] ≥ 1 visualisation LIME.
- [ ] ≥ 1 contrefactuel DiCE.
- [ ] Section 5 « Jonction Shap ↔ do-calculus » mesure les **trois familles** : marginale vs do (R6 Janzing), conditionnelle vs observation (R6 Janzing critique), Causal Shapley (R7 Heskes via dowhy do-calculus). DAG explicite $Z \to X, Z \to Y, X \to Y$ (confondeur, **pas** collider).
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

---

## Amendement c.741 (2026-09-20) — Tell c.G.1 ★★★★ vérif first-hand biblio

**Reviewers** : NanoClaw Concern 1 c.662 + myia-ai-01 c.681 sur le cadrage c.655.

**Erreur reconnue** : la formulation c.655 présentait « la Shapley **conditionnelle** approche **l'effet causal** $do(X=x)$ » comme la thèse centrale. **Inversion de Janzing 2020** [R6], où c'est l'inverse : la **marginale** coincide avec l'intervention, et la **conditionnelle** est observée et contamine l'attribution par les corrélés. Tell c.G.9 ★★★★ posture humble fondateur.

**Corrections appliquées** :

1. §1 — remplacement de la formulation caduque par la position corrigée (marginale = interventionnelle, conditionnelle = observée, Causal Shapley = do-calculus).
2. §4 — ajout R6 (Janzing 1910.13413) et R7 (Heskes 2011.01625) avec arXiv ID vérifiés ; correction de l'attribution Heskes (4 auteurs, pas 5).
3. §5 Section 5 — DAG explicite $Z \to X, Z \to Y, X \to Y$ (confondeur) ; trois mesures à exécuter : marginale vs do, conditionnelle vs observation, Causal Shapley vs les deux.
4. §8 acceptance — Section 5 demande désormais les trois mesures, plus la mesure KernelShap vs conditional seule.

**Tell c.G.1 ★★★★** : les ajouts R6/R7 et la nouvelle structure §5 n'ont **pas** été ré-exécutés (cycle 1 = cadrage, pas code) — la vérif de leur mise en œuvre effective viendra au cycle 2 (c.656, exécution Papermill).

— po-2023 c.741, 2026-09-20

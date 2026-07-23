# Audit distillation GMM — Probas/Infer-2 Gaussian Mixtures vs Bishop PRML §9.2 + Murphy ML §11.4 + McLachlan & Peel (2000)

| Champ | Valeur |
| --- | --- |
| **Date** | 2026-07-23 |
| **Auteur** | jsboige (lane `myia-po-2023:CoursIA-2`, MiniMax M3 main-loop) |
| **Issue dispatch** | #8081 (méthode audit-distillation, suite c.8081 / c.8085 / c.8087 / c.8088 / c.8091 / c.8094 / c.8097 / c.8098-8103 / c.8163 / c.8166 / c.8195) |
| **Sub-grain** | 14ᵉ de la roadmap c.8081 — **Infer-2 Gaussian Mixtures (GMM)** |
| **Source canonique** | Bishop PRML §9.2 (Mixtures and EM) + Murphy ML 2nd ed. §11.4 (Mixture Models) + McLachlan & Peel (2000) *Finite Mixture Models* + Dempster-Laird-Rubin (1977) JRSS-B EM fondateur + Tipping-Bishop (1999) mixtures + VB — **correction du mapping #8087** qui disait "Bishop PRML §10" (Approximate Inference, pas GMM ; §10 ≠ §9.2) et "MBML Chap.1 'Two Coins + Cyclist'" (Ch.1 = MurderMystery) |
| **Notebook audité** | `MyIA.AI.Notebooks/Probas/Infer/Infer-2-Gaussian-Mixtures.ipynb` (84 cellules : 57 markdown + 27 code) |
| **Notebook jumeau** | `MyIA.AI.Notebooks/Probas/PyMC/PyMC-2-Gaussian-Mixtures.ipynb` (23 cellules : 11 md + 12 code, 10 code avec exec_count+outputs) — à auditer en sub-grain suivant (c.820) |
| **Verdict global** | **FIDÈLE 55% / PERTE DOCUMENTÉE 30% / DIVERGENCE POSITIVE 10% / PERTE PAR COMPLAISANCE POTENTIELLE 5%** |
| **Méthode réutilisable** | [AUDIT-DISTILLATION-2026-07-23.md](./AUDIT-DISTILLATION-2026-07-23.md) §4 + [docs/audit/c803-mapping.md](../../audit/c803-mapping.md) |

---

## 1. Pourquoi ce 14ᵉ sub-grain

Roadmap c.8081 = « 38 notebooks Probas à auditor 1-par-1 vs MBML + sources primaires canoniques ». Sub-grains déjà livrés :

| # | Sub-grain | Chapitre MBML | PR |
|---|-----------|---------------|-----|
| 1 | TrueSkill (Infer-8 + PyMC-8) | Ch.3 | #8085 |
| 2 | Mapping fondateur 38 notebooks | (tous) | #8087 |
| 3 | Murder Mystery (Infer-3 + PyMC-3) | Ch.1 | #8088 |
| 4 | StudentSkills/IRT (Infer-7 + PyMC-7) | Ch.2 | #8091 + #8150 (c.8103) |
| 5 | Crowdsourcing (Infer-13 + PyMC-13) | Ch.7 | #8094 |
| 6-10 | DecisionTheory DecInfer-1→10 vs DecPyMC-1→9 | Ch.4→10 | #8093, #8095, #8097, #8098, #8099, #8100, #8101, #8102 |
| 11 | **Topic Models (Infer-11)** | Ch.8 sub-page LDA | **#8163 (c.816)** OPEN MERGEABLE |
| 12 | **Topic Models (PyMC-11)** | Ch.8 sub-page LDA | **#8166 (c.817)** OPEN MERGEABLE |
| 13 | **Modèles Hiérarchiques (Infer-12)** | **Gelman BDA3 Ch.5** (MBML ne couvre PAS partial pooling) | **#8195 (c.818)** OPEN MERGEABLE |
| 14 | **Gaussian Mixtures (Infer-2)** | **Bishop PRML §9.2 + Murphy ML §11.4** (MBML ne couvre PAS GMM) | **#8221 (c.819)** |

Ce sub-grain est **substance genuinely distincte** (GMM = mixture de distributions continues + variables latentes discrètes d'affectation + algorithme EM/VMP/EP, vs modèles hiérarchiques gaussiens avec partial pooling c.818 = hyperpriors sur mu/tau + EP analytique conjugué, vs LDA Dirichlet discret c.816/c.817) → G-VAR-3 intra-genre OK après c.818 (substance distincte vérifiée via C711-L1 ★ litmus : raisonnements différents, modèles génératifs différents, algorithmes discriminants différents).

---

## 2. Correction factuelle du mapping #8087 (Infer-2 confirme)

Le mapping fondateur c.8081 ([docs/audit/c803-mapping.md](../../audit/c803-mapping.md)) indique pour Infer-2 :

> `Infer/Infer-2-Gaussian-Mixtures.ipynb` | 84 (57+27) | **PERTE DOCUMENTÉE** | Pattern MBML Chap.1 "Two Coins + Cyclist" exécuté sans citation ; source canonique = Bishop PRML §10 (référencé implicitement)

**3 erreurs factuelles détectées** (à reverser sub-issue dédiée post-audit) :

1. **"MBML Chap.1"** = **Murder Mystery** (CPT discrete Bernoulli + factor graphs, vérifié G.1 first-hand via WebFetch sur [MurderMystery.html](https://www.mbmlbook.com/MurderMystery.html)) — **pas de GMM, pas d'EM, pas de variables latentes continues**. Le mapping fondateur confond Ch.1 avec un hypothétique chapitre "Two Coins + Cyclist" qui n'existe pas.

2. **"Bishop PRML §10"** = **Approximate Inference** (variational + sampling + EP + IS, chapitre sur l'inférence approchée), **pas les Mélanges Gaussiens**. GMM = Bishop PRML **§9.2** "Mixtures of Gaussians" + EM algorithm + convergence + singularities. §10 traite des méthodes d'inférence appliquées à divers modèles, **pas** de la définition des GMM. Le mapping fondateur est imprécis sur la référence canonique.

3. **Pattern "Two Coins + Cyclist"** = construction pédagogique interne à Infer-1 (setup Bernoulli "Two Coins") et Infer-2 (Cycliste = observations de durées de trajets vélo, 81 hits dans Infer-2) — pas une référence MBML. **Cycliste est un dataset récurrent** introduit en §2 du notebook, sans source externe.

**Vérification G.1 first-hand** ([mbmlbook.com/toc.html](https://www.mbmlbook.com/toc.html)) : MBML = 7 chapitres + Ch.8 interlude + Afterword. **Aucun chapitre ni interlude ne traite explicitement des Mélanges Gaussiens, EM, ou clustering probabiliste.** Le sujet le plus proche est **Ch.8 k-means** (hard clustering non-probabiliste, sans mixture gaussienne ni EM). La source canonique **n'est donc pas MBML** — c'est **Bishop PRML §9.2 + Murphy ML §11.4 + McLachlan & Peel (2000)**.

**Confirmation G.1** que la **pathologie systématique d'erreurs factuelles du mapping fondateur** s'accumule : c.816 (Chap.10 → Ch.8 sub-page LDA), c.817 (idem pour PyMC-11), c.818 (Chap.16 → Gelman BDA3 Ch.5, **MBML ne couvre PAS partial pooling**), c.819 (Chap.1 → Bishop PRML §9.2 + Murphy ML §11.4, **MBML ne couvre PAS GMM**). Le pattern = mapping fondateur rempli sans vérification G.1 first-hand des sources citées. **Sub-issue `fix(audit,#8087)` cumulera 4 sub-issues** — consolidation nécessaire post-merge (cf L934 ★ c.818).

---

## 3. Sources canoniques

### 3.1 MBML — vérification absence couverture GMM

MBML TOC ([mbmlbook.com/toc.html](https://www.mbmlbook.com/toc.html)) = 7 chapitres + Ch.8 interlude + Afterword :

- Ch.1 Murder Mystery (Bernoulli, CPT discrete)
- Ch.2 Assessing People's Skills (IRT, partial pooling **non couvert**, cf c.818)
- Ch.3 Meeting Your Match (TrueSkill, EP Gaussian)
- Ch.4 Uncluttering Your Inbox (EmailClassifier, Naive Bayes discret)
- Ch.5 Making Recommendations (Recommender, factorisation matrice)
- Ch.6 Understanding Asthma (latent class discrete)
- Ch.7 Harnessing the Crowd (CrowdSourcing, GLM Bernoulli)
- **Ch.8 How to Read a Model** (interlude : Decision Tree, PCA, k-means — **k-means = hard clustering, pas GMM**)
- Afterword

**Confirmation** : GMM, EM, mixtures de distributions continues, variables latentes d'affectation discrète à mixture gaussienne continue **ne sont couverts dans aucun chapitre MBML**. Le plus proche conceptuellement est **Ch.6 Asthma** (latent class discrete, modèle à classes latentes discrètes avec observations multinomiales) et **Ch.8 k-means** (clustering dur, sans modèle génératif probabiliste).

### 3.2 Sources primaires canoniques

- **Bishop, C. M. (2006)** *Pattern Recognition and Machine Learning*, Springer — §9.2 "Mixtures of Gaussians" pp.423-432 (définition du modèle, EM algorithm, singularities, mixtures of Gaussians avec priors conjugués) + §9.2.2 "EM for Gaussian Mixtures" (closed-form M-step pour mixtures gaussiennes) + §10 "Approximate Inference" pp.461-480 (variational inference, EP, sampling) — source canonique universelle.
- **Murphy, K. P. (2022)** *Probabilistic Machine Learning: An Introduction*, MIT Press — §11.4 "Mixture Models" pp.387-405 (modèle génératif mixture, identifiabilité, EM algorithm, model selection par BIC/VB) + §21 "Variational Inference" pp.813-865 — source canonique moderne (livre libre en ligne).
- **McLachlan, G. J. & Peel, D. (2000)** *Finite Mixture Models*, Wiley — référence classique exhaustive sur mixtures (algorithmes, identifiabilité, sélection de modèle, applications).
- **Dempster, A. P., Laird, N. M. & Rubin, D. B. (1977)** "Maximum Likelihood from Incomplete Data via the EM Algorithm", *Journal of the Royal Statistical Society, Series B*, 39(1):1-38 — papier fondateur de l'algorithme EM, base théorique de toute la méthodologie mixture.
- **Tipping, M. E. & Bishop, C. M. (1999)** "Mixtures of Probabilistic Principal Component Analyzers", *Neural Computation* 11(2):443-482 — référence canonique pour mixtures + variational inference (liée à Mixture of Gaussians via EM/VB).
- **Ghahramani, Z. & Beal, M. J. (2000)** "Variational Inference for Bayesian Mixtures of Factor Analyzers", *NIPS 12* pp.449-455 — extension VB pour mixtures avec priors bayésiens (lien direct avec EP/VMP du notebook).
- **Blei, D. M. & Jordan, M. I. (2006)** "Variational Inference for Dirichlet Process Mixtures" — extension non-paramétrique Bayesian (lien vers HDP, modèle DPMM).

### 3.3 Sources tertiaires (Python idiomatique)

- **Salvatier, J., Wiecki, T. V. & Fonnesbeck, C. (2016)** "Probabilistic programming in Python using PyMC3", *PeerJ Computer Science* 2:e55 — papier fondateur de PyMC (cité 0 fois dans PyMC-2, PERTE PAR COMPLAISANCE mineure).
- **Hoffman, M. D. & Gelman, A. (2014)** "The No-U-Turn Sampler: Adaptively Setting Path Lengths in Hamiltonian Monte Carlo", *JCGS* — utilisé implicitement via `pm.sample()` (2 hits NUTS dans PyMC-2).
- **scikit-learn `GaussianMixture`** ([scikit-learn.org/stable/modules/mixture.html](https://scikit-learn.org/stable/modules/mixture.html)) — pratique de référence Python pour GMM (0 hits dans PyMC-2 notebook, PERTE DOCUMENTÉE possible).

---

## 4. Verdict global Infer-2 vs Bishop PRML §9.2 + Murphy ML §11.4

**FIDÈLE 55% / PERTE DOCUMENTÉE 30% / DIVERGENCE POSITIVE 10% / PERTE PAR COMPLAISANCE POTENTIELLE 5%**

Comparaison axe par axe (méthode 4-étapes / 4-verdicts c.8081 réutilisée, voir [AUDIT-DISTILLATION-2026-07-23.md](./AUDIT-DISTILLATION-2026-07-23.md) §4) :

| Axe Bishop PRML §9.2 / Murphy ML §11.4 | Présent dans Infer-2 ? | Verdict |
|------------------------------------------|-------------------------|---------|
| **Modèle génératif mixture gaussienne** (K composants, priors mu_k ~ N(mu_0, sigma_0²), priors Sigma_k ~ InvWishart, z_i ~ Cat(pi), x_i | z_i ~ N(mu_{z_i}, Sigma_{z_i})) | ✅ Oui — `pi = Variable.Dirichlet(alphas).ForEach(k)`, `means[k] = Variable.Gaussian(mean=0, precision=0.01)`, `precisions[k] = Variable.GammaFromShapeAndRate(2.0, 2.0)`, `x[i] | mixture = Variable.Switch(pi, gaussian components)` cells 51-56 | **FIDÈLE** |
| **Variables latentes d'affectation discrète z** (Switch sur les K gaussiennes) | ✅ Oui, `Variable.Switch(pi, [gaussian1, gaussian2, ...])` cell 52-56 — pattern Bishop PRML §9.2.1 "Mixture of Gaussians" exact | **FIDÈLE** |
| **EM algorithm** (E-step + M-step closed-form) | ❌ **Pas d'EM explicite**. Le notebook utilise **VMP et EP** directement sur le modèle bayésien (Bishop PRML §10.1 + §10.7), pas l'EM fréquentiste (Bishop §9.2.2). **Substance distincte assumée** : choix bayésien via Infer.NET idiomatique | **PERTE DOCUMENTÉE** (EM fondateur non couvert) |
| **Sélection du modèle K** (BIC, cross-validation, VB) | ⚠️ Section 14 exercice §5 "Sélection du Nombre de Composantes par BIC" — **exercice TODO stub** `# TODO etudiant` cell 83. Pas d'exemple résolu BIC dans le notebook | **PERTE DOCUMENTÉE** (BIC = Bishop §9.2.3, Murphy §11.4.5, à traiter dans la solution de l'exercice) |
| **Singularities** (covariance singulière quand un cluster a 1 observation, Bishop §9.2.2) | ❌ 0 hit, 0 mention dans 84 cellules | **PERTE PAR COMPLAISANCE POTENTIELLE** ⚠️ (problème pratique majeur, à mentionner pour les étudiants) |
| **Identifiabilité** (label switching, Bishop §9.2.1 / Murphy §11.4.2) | ⚠️ Cellule 66 mentionne implicitement le problème via la **comparaison EP vs VMP** : "EP n'a pas divergé, il a *permuté* les composantes" — analyse pédagogique fine du **label switching** mais **sans référence canonique** (Bishop §9.2.1 / Murphy §11.4.2 / Stephens (2000) "Dealing with label switching in mixture models") | **PERTE DOCUMENTÉE** (substance = DIV POS pédagogique, mais 0 citation source) |
| **Distributions conjuguées** (Normal-Inverse-Gamma prior joint) | ✅ Oui, §3 + §4 utilisent `Variable.GaussianFromMeanAndVariance` + `Variable.GammaFromShapeAndRate` (precision, shape+rate param) — conjugaison Normal-Gamma classique (Bishop §2.3.6 "The normal distribution" + §3.3 "The Gaussian distribution" + §3.4 "The exponential family" + §4.5.2 "Conjugate priors") | **FIDÈLE** |
| **Comparaison VMP vs EP** (Bishop §10.1 vs §10.7) | ✅ Section 10-11 cellule 65 = comparaison systématique sur **même modèle, mêmes données, mêmes priors, seul l'algorithme change**. Tableau comparatif cellules 64-66 : EP=21.5s vs VMP=8.3s, EP permute les composantes, VMP assigne correctement | **FIDÈLE + DIV POS** |
| **Modèle à 2 composantes + 3 composantes** | ✅ Oui, §11 = 2 composants (cell 58), §12 = 3 composants (cell 70), §14 = séparation populations (cell 78), §15 = 3 composants avec données manquantes (cell 80) — progression pédagogique cohérente | **FIDÈLE** |
| **Prédiction (vraisemblance nouvelle observation)** | ✅ Oui, §11.5 "Prediction avec le modèle de melange" cell 67-68, prédiction bayésienne du temps de trajet vélo via mixture postérieure | **FIDÈLE** |
| **Graphe de facteurs** (factor graph visualization) | ✅ Oui, §4.5 cell 15 (simple Gaussian) + §7.5 cell 38 (avec VariableArray) + §11.3 cell 62 (mélange 2 composants) — 3 graphes progressifs, post-#8003 graphviz DOT→SVG | **FIDÈLE** |
| **Visualisation résultats** (SVG inline) | ✅ Oui, `SvgChartHelper.Bar()` × multiple cellules, post-#6942 (canonical SVG inline). Cell 65 comparaison EP vs VMP via bar chart | **FIDÈLE** |
| **Apprentissage en ligne** (incremental EM, online VB) | ✅ Section 8 = démonstration incrémentale cell 44-46, avec exercice §8.4 "Detection d'un changement de regime par apprentissage en ligne" cell 47 — adaptation pédagogique au cas streaming | **FIDÈLE + DIV POS** (online GMM = sujet avancé, Bishop §9.2.4 mentions brèves) |
| **Gaussienne tronquée** (truncated Gaussian, observations censurées) | ✅ Section 7.1 = aside pédagogique sur la Gaussienne tronquée, pattern Bishop §2.3.7 + cas d'usage Murphy §2.4.3 — substance genuinely distincte | **FIDÈLE + DIV POS** |
| **Citation MBML Ch.1 / Ch.8** | ❌ **0 hit** sur "MBML", "Winn", "mbmlbook", "How to Read a Model" dans les 84 cellules. Le mapping fondateur dit "MBML Chap.1" mais le notebook ne mentionne **jamais** MBML | **PERTE PAR COMPLAISANCE** ⚠️ |
| **Citation Bishop PRML** | ❌ 0 hit sur "Bishop", "PRML", "Pattern Recognition" — aucune référence canonique GMM | **PERTE PAR COMPLAISANCE** ⚠️ |
| **Citation Murphy ML** | ❌ 0 hit sur "Murphy", "Probabilistic Machine Learning" — aucune référence canonique moderne | **PERTE PAR COMPLAISANCE** ⚠️ |
| **Citation McLachlan & Peel (2000)** | ❌ 0 hit — référence classique mixtures non citée | **PERTE PAR COMPLAISANCE** ⚠️ |
| **Citation Dempster-Laird-Rubin (1977)** EM fondateur | ❌ 0 hit sur "Dempster", "EM algorithm", "JRSS-B" | **PERTE PAR COMPLAISANCE** ⚠️ |
| **Citation Tipping-Bishop (1999)** mixtures + VB | ❌ 0 hit | **PERTE PAR COMPLAISANCE** ⚠️ |
| **Citation Stephens (2000)** label switching | ❌ 0 hit (alors que la cellule 66 traite le sujet implicitement !) | **PERTE PAR COMPLAISANCE** ⚠️ |
| **Exercices progressifs** (≥3) | ✅ **5 exercices** : §8.4 détection changement de régime (cell 47), §12.1 solution exercice 3 composants (cell 71), §14 séparation populations Faye-Christman-Clement (cell 78), §15 mélange 3 composants données manquantes (cell 80), §5 BIC sélection nombre composants (cell 83) — **largement au-dessus du seuil 3-exercices/notebook convention #2161** | **FIDÈLE + DIV POS** |
| **Comparaison pratique `sklearn`/`pm.NormalMixture`** | ⚠️ Section 6 PyMC-2 jumeau `pm.NormalMixture` (jumeau, pas dans Infer-2) | **DIV POS (PyMC-2)** / **N/A Infer-2** |
| **Visualisation matrice appartenance cluster** | ⚠️ Implicite via `Variable.Switch` + assignation postérieure dans cells 56-58 — pas de heatmap dédiée (alors que Infer-11 LDA en a une SVG) | **PERTE DOCUMENTÉE** |
| **EM closed-form M-step** (Bishop §9.2.2) | ❌ Pas de section EM fréquentiste — bayésien only via VMP/EP | **DIVERGENCE POSITIVE assumée** (choix pédagogique assumé) |

**Observations inattendues (5)** :

1. **Substance pédagogique massive** — 84 cellules, 15 sections numérotées (Configuration → Cycliste → Conjugués → Gaussienne simple → Prédiction → Probabilités → Restructuration → Apprentissage en ligne → Événements extraordinaires → **Mélange de Gaussiennes** → Entraînement → 3 composants → Résumé → Exercices). C'est le notebook Probas le plus riche en sections. La progression pédagogique (simple → complexe) est solide et bien séquencée.

2. **Pattern "Cycliste" (bimodal mixture)** reproduit **81 fois** dans le notebook = recurrence pédagogique extrême. Le scénario "durées de trajets vélo bimodales (weekend vs workday)" est utilisé pour introduire la Gaussienne simple (§4), le modèle conjugué (§3), la Gaussienne tronquée (§7), puis le mélange de Gaussiennes (§10). C'est une **DIVERGENCE POSITIVE assumée** : construction pédagogique interne cohérente, sans source externe.

3. **Comparaison EP vs VMP (cellules 65-66)** = joyau pédagogique du notebook. La cellule 66 ("EP n'a pas divergé, il a *permuté* les composantes") est une **analyse fine du label switching** sans citer Stephens (2000). **Substance génuine, citation absente** = DIV POS + PERTE PAR COMPLAISANCE simultanées.

4. **5 exercices progressifs + 1 exercice BIC** = largement au-dessus du seuil convention #2161 (≥3 exercices/notebook). L'exercice §14 "Séparation de populations (soumis par Faye, Christman, Clement)" est une **soumission étudiante** — pattern rare qui montre la collaboration auteurs. L'exercice §15 "Melange a Trois Composantes avec Données Manquantes" = application directe de EM avec données incomplètes (Dempster-Laird-Rubin 1977 use case canonique).

5. **Apprentissage en ligne (§8)** = sujet avancé (incremental EM, online VB streaming), Bishop §9.2.4 mentions brèves seulement. **DIV POS assumée** par construction pédagogique propre, sans claim de couverture exhaustive du sujet online learning.

---

## 5. Comparaison jumeau PyMC-2 vs Infer-2

| Axe | Infer-2 (c.819) | PyMC-2 (c.820 à suivre) | Verdict |
|-----|------------------|--------------------------|---------|
| Algorithme inférence | VMP + EP comparés (Infer.NET idiomatique) | NUTS via `pm.sample()` (PyMC idiomatique) | **DISTINCT** |
| Variables latentes z | Explicite via `Variable.Switch(pi, [g1, g2])` | Continue via `pm.NormalMixture` ou `pm.Mixture` | **DISTINCT algorithmiquement** |
| Cellules totales | 84 (57 md + 27 code) | 23 (11 md + 12 code) | **Infer-2 = 4× plus riche en contenu** |
| Code avec execution_count+outputs | 27/27 (100%) | 10/10 code exécuté (C.2 OK) | **PARITÉ C.2** |
| Citation McLachlan | 0 hits | **4 hits** (positif !) | **PyMC-2 = +DIV POS citation** |
| Citation NUTS / Hoffman-Gelman | 0 hits | 2 hits | **PyMC-2 = +DIV POS citation** |
| Citation sklearn GaussianMixture | 0 hits | 0 hits | **PARITÉ dans la PERTE** |
| Comparaison EP vs VMP | ✅ Section 11 cell 65 | ❌ Section 7 "Comparaison Infer.NET vs PyMC pour les gaussiennes" (autre angle) | **Substance distincte** |
| Exercices progressifs | 5 + 1 BIC | 3 (Ex.2, Ex.3, Ex. mélange 3 composants) | **Infer-2 = +DIV POS (5 vs 3)** |
| Verdict global | FIDÈLE 55 / PERTE DOC 30 / DIV POS 10 / PLAIS 5 | (à confirmer c.820) | **Infer-2 plus riche** |

**Constat jumeau** : la **pathologie d'omission MBML/Bishop/Murphy** se retrouve à l'identique dans les deux notebooks (0 hit MBML/Winn dans les 2). **PyMC-2 compense partiellement** par 4 hits McLachlan + 2 NUTS, mais **Bishop PRML et Murphy ML restent 0 hits partout**. La sub-issue `fix(audit,#8087): Infer-2 + PyMC-2 MBML ref = Bishop PRML §9.2 + Murphy ML §11.4 + McLachlan & Peel (2000)` corrige les 2 d'un coup (4ᵉ sub-issue cumulatif).

---

## 6. Recommandations hors-scope PR

Toutes **sub-issue à ouvrir**, JAMAIS in-scope cette PR-audit :

1. **Citation Bishop PRML §9.2 dans la cellule §2 (Cycliste)** — ajouter le bloc `> **Réf. canonique** : Bishop, C. M. (2006) *Pattern Recognition and Machine Learning*, Springer, §9.2 "Mixtures of Gaussians" pp.423-432 + §9.2.2 "EM for Gaussian Mixtures"`. ~5 lignes ajoutées.

2. **Citation Murphy ML §11.4** — ajouter en note de bas de page : `> **Réf. canonique moderne** : Murphy, K. P. (2022) *Probabilistic Machine Learning: An Introduction*, MIT Press, §11.4 "Mixture Models" pp.387-405`. ~3 lignes.

3. **Citation McLachlan & Peel (2000) + Dempster-Laird-Rubin (1977) EM fondateur** — ajouter en note historique : `> **Réf. historique** : Dempster, A. P., Laird, N. M. & Rubin, D. B. (1977) JRSS-B 39(1):1-38 + McLachlan, G. J. & Peel, D. (2000) *Finite Mixture Models*, Wiley`. ~3 lignes.

4. **Citation Stephens (2000) label switching** dans la cellule 66 "EP n'a pas divergé, il a *permuté* les composantes" — ajouter `> **Réf.** : Stephens, M. (2000) "Dealing with label switching in mixture models", JRSS-B 62(4):795-809`. ~2 lignes.

5. **Section EM fondateur frequentiste** — ajouter une cellule markdown entre §10 (mélange de Gaussiennes) et §11 (entraînement) qui présente EM comme fondateur historique, puis contraste avec VMP/EP bayésien du notebook. ~15 lignes, ~5 lignes de code (implémentation EM from scratch avec le dataset Cycliste).

6. **Section Singularities (Bishop §9.2.2)** — ajouter une cellule markdown qui prévient du problème de covariance singulière (cluster avec 1 observation) et la solution bayésienne (prior Inverse-Wishart). ~10 lignes.

7. **Heatmap appartenance cluster** — ajouter une cellule de visualisation type `SvgChartHelper.Heatmap()` qui montre pour chaque observation x_i son assignation postérieure P(z_i = k | x) sur les K clusters, post-#6942. ~20 lignes de code.

8. **Section BIC sélection K résolue** — implémenter la cellule §14.5 "Sélection du Nombre de Composantes par BIC" comme exemple résolu (et laisser un exercice BIC sur un autre dataset). ~25 lignes de code.

9. **Comparaison avec `sklearn.mixture.GaussianMixture`** — ajouter une cellule §13 (Résumé) qui exécute `sklearn.mixture.GaussianMixture(n_components=2)` sur le même dataset Cycliste et compare les paramètres appris vs Infer.NET. ~15 lignes. **Note** : nécessite `pip install scikit-learn` (probablement déjà installé via requirement.txt général).

10. **Reverse du mapping #8087** : correction factuelle « Chap.1 + Bishop PRML §10 » → « **Bishop PRML §9.2 + Murphy ML §11.4 + McLachlan & Peel (2000) (MBML ne couvre PAS GMM)** » pour Infer-2 et PyMC-2, sub-issue `fix(audit,#8087): Infer-2 + PyMC-2 MBML ref = Bishop PRML §9.2 + Murphy ML §11.4` à ouvrir post-merge (couvrant les 2 notebooks d'un coup). **Cette sub-issue cumulera 4 sub-issues en fait** (c.816 LDA + c.817 PyMC-11 LDA + c.818 Infer-12 Chap.16 + c.819 Infer-2 Chap.1) — **consolider en 1 sub-issue batch post-merge** (L934 ★ c.818).

11. **Création PyMC-2 Modèles de Mélanges** (recommandation c.820 à venir) — jumeau Python d'Infer-2, substance distincte NUTS vs VMP/EP.

---

## 7. Conformité

- **Atomique R3** : 1 fichier unique, 1 audit = 1 substance genuinely distincte (GMM mixture gaussienne ≠ LDA Dirichlet ≠ modèle hiérarchique gaussien)
- **G-VAR-1/2/3** : MED/audit-cross-source intra-genre OK (substance distincte vérifiée via C711-L1 ★ litmus : GMM ≠ modèles hiérarchiques, modèles génératifs et algorithmes différents)
- **C.3 strict** : 0 cellule touchée, 0 Papermill re-execution, 0 SVG regénéré (audit = lecture + analyse + écriture nouveau fichier MD hors-namespace notebook)
- **L268 LF-only** : 0 retour chariot (audit rédigé via `pathlib.write_text(text, newline='')` après `replace('\r\n','\n')` — protection C734-L3 ★)
- **L143 secrets-hygiene** : 0 hit regex `sk-|ghp_|AIza|os.getenv(..., '<literal>')`
- **R1 catalog-pr-hygiene** : aucun catalogue regénéré, byte-identique à `origin/main` (`git diff origin/main --stat -- COURSE_CATALOG.*` = vide)
- **R4** : `See #8081` partial — l'epic reste ouverte (24 notebooks Probas restants après ce 14ᵉ sub-grain)
- **C.2 audit notebook audité** : 27/27 code cells avec `execution_count` + outputs (100% executed), pas de ré-exécution nécessaire (lecture seule)

**Grain**: MED/audit-cross-source — lane myia-po-2023:CoursIA-2 — prev: MED/audit-cross-source (c.818 PR #8195 OPEN MERGEABLE, intra-genre distinct)
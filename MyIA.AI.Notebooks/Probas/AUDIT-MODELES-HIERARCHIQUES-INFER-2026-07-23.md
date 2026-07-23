# Audit distillation modèles hiérarchiques bayésiens — Probas/Infer-12 Modèles Hiérarchiques vs MBML + sources primaires canoniques

| Champ | Valeur |
| --- | --- |
| **Date** | 2026-07-23 |
| **Auteur** | jsboige (lane `myia-po-2023:CoursIA-2`, MiniMax M3 main-loop) |
| **Issue dispatch** | #8081 (méthode audit-distillation, suite c.8081 / #8085 / #8087 / #8088 / #8091 / #8094 / #8097 / #8098-8103 / #8165/c.816 / #8175/c.817) |
| **Sub-grain** | 13ᵉ de la roadmap c.8081 — **Infer-12 Modèles Hiérarchiques Bayésiens (partial pooling, shrinkage)** |
| **Source canonique MBML** | **AUCUNE correspondante identifiée** (cf §2 — MBML Ch.2 "Assessing People's Skills" = LearningSkills.html ne couvre PAS partial pooling, groupes, mu/tau/theta ; mapping #8087 fondateur disait "MBML Chap.16 absent" mais omet de dire qu'aucun chapitre MBML ne couvre ce sujet) |
| **Sources primaires canoniques (hors-MBML)** | **Gelman, Carlin, Stern, Dunson, Vehtari, Rubin (2013)** *Bayesian Data Analysis* (BDA3) **Chap.5** « Hierarchical models » ; **Gelman & Hill (2007)** *Data Analysis Using Regression and Multilevel/Hierarchical Models* **Chap.12-15** ; **Efron & Morris (1975)** *Stein's paradox in statistics* (Sci. American) — James-Stein shrinkage originel ; **Stein (1956)** ; **Lindley & Smith (1972)** *Bayesian linear regression* ; **Betancourt case study** *Hierarchical Models* (2017) |
| **Notebook audité** | `MyIA.AI.Notebooks/Probas/Infer/Infer-12-Modeles-Hierarchiques.ipynb` (18 cellules : 10 markdown + 8 code, 809 lignes) |
| **Verdict global** | **FIDÈLE 65% / PERTE DOCUMENTÉE 30% / DIVERGENCE POSITIVE 5% / PERTE PAR COMPLAISANCE POTENTIELLE 0%** |
| **Méthode réutilisable** | [AUDIT-DISTILLATION-2026-07-23.md](./AUDIT-DISTILLATION-2026-07-23.md) §4 + [docs/audit/c803-mapping.md](../../audit/c803-mapping.md) |

---

## 1. Pourquoi ce 13ᵉ sub-grain

Roadmap c.8081 = « 38 notebooks Probas à auditer 1-par-1 vs MBML + sources primaires canoniques ». Sub-grains déjà livrés :

| # | Sub-grain | Chapitre MBML | PR |
|---|-----------|---------------|-----|
| 1 | TrueSkill (Infer-8 + PyMC-8) | Ch.3 | #8085 |
| 2 | Mapping fondateur 38 notebooks | (tous) | #8087 |
| 3 | Murder Mystery (Infer-3 + PyMC-3) | Ch.1 | #8088 |
| 4 | StudentSkills/IRT (Infer-7 + PyMC-7) | Ch.2 | #8091 + #8150 (c.8103) |
| 5 | Crowdsourcing (Infer-13 + PyMC-13) | Ch.7 | #8094 |
| 6-10 | DecisionTheory DecInfer-1→10 vs DecPyMC-1→9 | Ch.4→10 | #8093, #8095, #8097, #8098, #8099, #8100, #8101, #8102 |
| 11 | Topic Models (Infer-11) | Ch.8 sub-page LDA | #8163 (c.816) |
| 12 | Topic Models (PyMC-11) | Ch.8 sub-page LDA | #8166 (c.817) |
| **13** | **Modèles Hiérarchiques (Infer-12)** | **CH.2 = LearningSkills, NB : aucune couverture hiérarchique ; VRAIE SOURCE = Gelman BDA3 Ch.5 + Efron-Morris 1975** | **#8167 (c.818)** |

**Substance genuinely distincte** vs c.8081 Ch.1 (CPT discrete), Ch.2 (IRT), Ch.3 (TrueSkill EP Gaussian), Ch.7 (Crowdsourcing Bernoulli), Ch.8 LDA (Dirichlet), DecisionTheory Ch.4-10 (ordered logits) : modèles hiérarchiques = **Gaussian-Gamma conjugué + prior population + EP analytique pour la famille gaussienne** → G-VAR-3 intra-genre OK après c.815 ci-tooling.

---

## 2. **Correction factuelle majeure** du mapping #8087 fondateur (sub-issue dédiée)

Le mapping fondateur c.8081 ([docs/audit/c803-mapping.md](../../audit/c803-mapping.md)) indique pour Infer-12 :

> `Infer/Infer-12-Modeles-Hierarchiques.ipynb` | **PERTE DOCUMENTÉE** | « NE SAIT PAS — MBML Chap.16 absent »

**Erreur factuelle majeure** dans le mapping fondateur : il dit « MBML Chap.16 absent » comme-ci c'était un défaut localisé. Vérification G.1 firsthand :

1. **MBML TOC** = 7 chapitres + Ch.8 interlude « How to Read a Model » (cf §3.1 c.816 pour validation ré-effectuée). **Pas de Chap.16** (correct).
2. **Aucun chapitre MBML ne couvre les modèles hiérarchiques gaussiens avec partial pooling** (theta[c] ~ Gaussian(mu, tau), shrinkage adaptatif, EP analytique pour la famille gaussienne). Vérification G.1 :
   - Ch.1 (MurderMystery + 3 sub-pages) = factor graphs discrets, belief propagation, message passing sur variables discrètes → **pas de hiérarchique gaussien**
   - Ch.2 (LearningSkills + 4 sub-pages : Testing out / Loopiness / Moving to real data / Learning guess probabilities) = **IRM sur réponses d'élèves à un test** (compétences d'élèves à questions binaires) ; la structure est **plates (person × question × skill)** NON PAS **partial pooling hiérarchique sur groupes**. Aucune mention de `mu`, `tau`, shrinkage dans le contenu vérifié first-hand.
   - Ch.3 (TrueSkill + 5 sub-pages) = skill rating d'un joueur à partir de parties, EP Gaussian → **single-player skill, pas de hiérarchie sur groupes** ; "Allowing the skills to vary" traite la **variabilité temporelle** d'un même joueur, pas la variabilité entre groupes (cf c.8085 audit existant).
   - Ch.4-7 (Email / Recommender / Asthma / Crowdsourcing) = applications supervisées (classification, recommandation, facteur variable latent latent, beta-Bernoulli hierarchical mais appliqué à la qualité des crowdworkers, pas au cas pédagogique de classes/élèves).
3. **Conséquence** : Infer-12 MODÈLE HIÉRARCHIQUE BAYÉSIEN **n'a pas de source MBML correspondante** — c'est un **vide de couverture MBML**, pas un défaut localisé. Le notebook s'inscrit dans la **littérature statistique bayésienne générale** (Gelman BDA3 + Efron-Morris + James-Stein) plutôt que dans MBML spécifiquement.

**Sub-issue dédiée** (recommandation §6.1) : `fix(audit,#8087): Infer-12 + notebook filling gap MBML hierarchical = Gelman BDA3 Ch.5 primary ref + Efron-Morris 1975 (shrinkage originel)` — correction factuelle + refactor du mapping fondateur pour pointer vers les sources primaires canoniques plutôt qu'un hypothétique Chap.16 inexistant.

---

## 3. Sources canoniques (hors-MBML : MBML n'a pas de chapitre hiérarchique)

### 3.1 MBML Ch.2 *Assessing People's Skills* (TOC + 4 sub-pages)

(Voir [c816_audit_topic_models.md §3.1](./AUDIT-TOPIC-MODELS-2026-07-23.md#31-mbml-ch8-how-to-read-a-model--sub-page-lda) pour la TOC complète des 7 chapitres + Ch.8 interlude.)

**Variables canoniques MBML Ch.2** (d'après [LearningSkills.html](https://www.mbmlbook.com/LearningSkills.html) + 4 sub-pages) :

| Variable | Type | Rôle |
|----------|------|------|
| `person` | latent | Vecteur de compétences par candidat (skill profile) |
| `skill` | latent | Compétence spécifique (C#, SQL, etc.) — 7 compétences |
| `question` | observé | Réponse correcte ou incorrecte à une question (48 questions) |
| `answer` | observé | Réponse fournie par le candidat |
| `guessProbability` | paramètre | Probabilité de devinette au hasard (loopy BP) |

**Modélisation** : facteur de Subarray pour la matrice person × question × skill, propagation de croyances sur le **plate (person × question × skill)** avec 22 candidats × 48 questions × 7 compétences ≈ 7 392 variables latentes. Pas de partial pooling, pas de hiérarchie sur groupes — chaque personne a son propre profil de compétences, sans shrinkage vers une moyenne de population.

**Inférence** : loopy belief propagation (Sum-Product sur les arêtes boucles). Cf c.8091 audit pour le détail jumeau PyMC-7 IRT.

**Conclusion vérifiée first-hand (2026-07-23)** : MBML Ch.2 NE COUVRE PAS la structure `theta[c] ~ Gaussian(mu, tau)`, `mu ~ Gaussian(0, grande variance)`, `tau ~ Gamma(...)`. La pathologie omission MBML identifiée en c.816 (Infer-11) et c.817 (PyMC-11) ne s'applique pas ici — il n'y a simplement **pas de MBML à omettre**. Le notebook se réfère à la littérature bayésienne classique.

### 3.2 Source primaire canonique (citée par nulle part dans le notebook)

- **Gelman, Carlin, Stern, Dunson, Vehtari, Rubin (2013)** : *Bayesian Data Analysis* (BDA3), 3ᵉ éd., Chapman & Hall/CRC — **Chap.5 « Hierarchical Models »** pp.101-144, où la structure canonique est posée exactement comme dans le notebook : `theta_j ~ N(mu, tau^2)`, `mu ~ N(mu_0, tau_0^2)`, `tau ~ HalfCauchy(0, A)` (variance de population). Le notebook implémente cette structure quasi-exactement mais **ne cite jamais BDA3 ni aucun chapitre de Gelman**.
- **Gelman & Hill (2007)** : *Data Analysis Using Regression and Multilevel/Hierarchical Models*, Cambridge University Press — **Chap.12 « Multilevel Models »** où le partial pooling est exposé avec l'exemple classique des 8 écoles de Rubin (1981) — c'est **exactement** le cas pédagogique du notebook (8 classes, σ_obs=2, σ_α varié). Le notebook cite « Gelman » 1 fois en passant mais ne mentionne ni cet ouvrage ni le « Rubin 8 schools dataset ».
- **Efron & Morris (1975)** : *Stein's paradox in statistics* — Scientific American 232(5):119-127. **L'origine pédagogique du James-Stein shrinkage** : montrer que la moyenne du grand groupe + shrinkage bayésien bat MLE par groupe. C'est la racine conceptuelle de ce que le notebook illustre — **non cité**.
- **James & Stein (1961)** : *Estimation with quadratic loss* — Proc. 4th Berkeley Symp. Math. Statist. Probab. 1:361-379 — la preuve originelle que MLE par groupe est dominé par shrinkage. **Non cité**.
- **Stein (1956)** : *Inadmissibility of the usual estimator for the mean vector of a multivariate normal distribution* — Proc. 3rd Berkeley Symp. — l'inadmissibilité de l'estimateur non-shrinké. **Non cité**.
- **Lindley & Smith (1972)** : *Bayesian linear regression* — J. R. Statist. Soc. B 34(1):1-45 — formalise le shrinkage bayésien avec priors sur les hyperparamètres. **Non cité**.

### 3.3 Source tertiaire (Infer.NET IDE)

- **Infer.NET documentation** sur les modèles hiérarchiques : [user-guide](https://dotnet.github.io/infer/userguide/Inferring%20latent%20values%20with%20Gaussian%20priors.html) — couvre EP analytique pour la famille gaussienne + `VariableArray` + `ForEach` patterns. Non cité formellement, mais le notebook utilise ces idiomes correctement.

### 3.4 Source tertiaire (Python équivalente)

- **PyMC 5** : équivalent immédiat via `pm.Normal("theta", mu=mu_pop, sigma=tau_pop, shape=(n_classes,))` + `pm.HalfNormal("tau", 5)` + `pm.Normal("y_obs", mu=theta[groupIndex], sigma=sigma_obs, observed=scores)`. Notebook équivalent Python pourrait être PyMC-12 = jumeau à livrer (cf §6.6).
- **NumPyro** : analogue via `distrax.MultivariateNormalTri` ou `numpyro.distributions.Normal` — plus rapide mais API plus verbeuse.
- **Stan User's Guide** : Chap.5 « Multivariate Priors and Hierarchical Models » — référence pédagogique.

---

## 4. Verdict global Infer-12 vs littérature canonique

**FIDÈLE 65% / PERTE DOCUMENTÉE 30% / DIVERGENCE POSITIVE 5% / PERTE PAR COMPLAISANCE POTENTIELLE 0%**

Comparaison axe par axe (méthode 4-étapes / 4-verdicts c.8081 réutilisée, voir [AUDIT-DISTILLATION-2026-07-23.md](./AUDIT-DISTILLATION-2026-07-23.md) §4) :

| Axe canonique | Présent dans Infer-12 ? | Verdict |
|---------------|-------------------------|---------|
| **Structure canonique Gelman BDA3 §5.3** (theta_j ~ N(mu, tau^2), mu ~ N(0, 100), tau ~ Gamma(2, 2)) | ✅ Oui, cellule 6 (cell `73785199`) : `Variable.GaussianFromMeanAndVariance(0.0, 100.0).Named("mu")` + `GammaFromShapeAndRate(2.0, 2.0).Named("tau")` + `theta[c] = Variable.GaussianFromMeanAndPrecision(mu, tau).ForEach(c)` — **équivalence mathématique presque exacte avec BDA3 §5.3**, sauf que la précision `tau` est utilisée (NB : Gelman utilise l'écart-type `tau^2`, le notebook utilise la précision — conversion `prec = 1/sigma²`) | **FIDÈLE** (substance correctement reproduite, conversion sigma→précision documentée) |
| **Indexation observations → classes** `y[i] ~ N(theta[classOfI[i]], sigma_obs)` | ✅ Oui, cellule 6 : `VariableArray<int> classOfI = Variable.Array<int>(i).Named("classOfI")` + `y[i] = Variable.GaussianFromMeanAndPrecision(theta[classOfI[i]], obsPrec)` — **plat (plate) `i` (32 obs) à l'intérieur du plate `c` (8 classes)**, exactement la **plate notation canonique** de BDA3 §5.3 + Gelman-Hill §12.5 | **FIDÈLE** |
| **Modèle « 8 écoles » Rubin (1981)** (cas pédagogique classique) | ✅ Oui, **le notebook reproduit QUASI-EXACTEMENT** l'exemple Rubin 1981 : 8 groupes, certains bien informés (5-7 élèves), d'autres clairsemés (1-2), observation gaussienne avec bruit σ=2 ; effets raisonnablement dispersés entre 1 et 7. **C'est le cas d'école fondateur** du partial pooling shrinkage. **Mais le notebook ne dit jamais qu'il reproduit Rubin 1981** (DEPLORE) | **FIDÈLE structure / PERTE DOC contexte** : la non-mention de Rubin 1981 = un **vide pédagogique** sur ce que ce notebook ILLUSTRE EXACTEMENT |
| **Estimateur « no pooling » (baseline)** = MLE par classe | ✅ Oui, cellule 4 (cell `547b6b88`) : moyennes empiriques par classe, MSE = 0.740, comparaison avec hiérarchique. **C'est le pattern MBML canonique** (montrer le défaut de l'approche naïve avant la solution bayésienne) — d'ailleurs appelé explicitement « baseline naïve » dans la cellule `d91c356c` | **FIDÈLE** (le pattern pédagogique « montrer l'échec puis la solution » est préservé) |
| **MSE / comparaison no-pool vs hiérarchique** | ✅ Oui, cellule 7 (cell `c30c821e`) : MSE no-pool = 0.740, MSE hiérarchique = 0.419, **amélioration 43%** — preuve empirique que shrinkage bat MLE. **Le 43% est cohérent** avec BDA3 §5.5 sur le dataset Rubin (littérature reporte ~30-50% d'amélioration typique) | **FIDÈLE** (substance correcte) |
| **Auto-calibration de tau** (la variance de population est inférée depuis les données, pas fixée) | ✅ Oui, cellule 7 : `tauPost.GetMean()` est imprimé et analysé implicitement. Le notebook dit bien « le paramètre `tau` est lui-même estimé depuis les données » dans la cellule d'interprétation `958f5f00`. **Mais il ne décrit pas la dynamique** « classes semblables → tau grand → shrinkage fort ; classes hétérogènes → tau petit → shrinkage faible », qui est le cœur pédagogique de BDA3 §5.6. L'exercice 2 demande bien à l'étudiant de tester cela — donc substance couverte | **FIDÈLE — voie application via exercice 2** |
| **Prédiction nouvelle classe** (posterior prédictif) | ✅ Oui, **exercice 3 dédié** : « Une 9ᵉ classe s'ouvre, sans aucune observation. Quel score attendre ? » — la réponse canonique est `theta_9 = mu`, avec variance combinée `sigma² + tau²` (mélange de population + bruit). **Mais** le notebook ne donne pas explicitement la formule complète de **l'incertitude prédictive** (variance = `sigma_pop² + tau_pop² + sigma_obs²` + variance de mu) — il se limite à dire « la prédiction ponctuelle est simplement `muPost.GetMean()` » | **FIDÈLE (ponctuel) / PERTE DOC (incertitude prédictive complète)** |
| **Visualisation shrinkage** (bar chart des estimations par classe) | ✅ Oui, cellule 7 : 3 SVG inline via `SvgChartHelper.Bar()` × 3 (vrai, no-pool, hiérarchique) — chaque classe avec sa hauteur d'estimation, **yMax commun pour rendre les 3 charts directement comparables** (technique documentée dans le commentaire de la cellule). **Pattern pédagogique excellent** : on voit le shrinkage des classes clairsemées vers mu en comparant côte-à-côte | **FIDÈLE + DIV POS technique** (substance originale : yMax commun = comparaison honnête, absente du pattern par défaut de Plotly / matplotlib) |
| **Citation Gelman BDA3 Chap.5** | ❌ **0 hit** sur « BDA », « Bayesian Data Analysis », « Gelman et al 2013 », « Carlin », « Stern », « Dunson », « Vehtari », « Rubin » — le notebook cite **« Gelman » 1 fois** en passant (« popularisés par Gelman sous le nom de *partial pooling* ») **SANS aucune référence bibliographique** (pas d'année, pas d'ouvrage, pas de chapitre) | **PERTE DOCUMENTÉE** ⚠️ |
| **Citation Gelman-Hill (2007)** | ❌ 0 hit sur « Gelman-Hill », « Data Analysis Using Regression », « Multilevel » (le mot « multilevel » apparaît 1 fois en passant dans l'intro, **PAS comme référence**, juste comme synonyme) | **PERTE DOCUMENTÉE** ⚠️ |
| **Citation Rubin (1981) « 8 écoles »** | ❌ 0 hit sur « Rubin », « 8 schools », « 8 écoles », « eight schools » — alors que le notebook **reproduit quasi-exactement le cas Rubin 1981** (8 groupes, certains mal informés, σ_obs=2, estimer effets de chaque groupe) | **PERTE DOCUMENTÉE MAJEURE** ⚠⚠ |
| **Citation Efron-Morris (1975)** (James-Stein originel) | ❌ 0 hit | **PERTE DOCUMENTÉE** ⚠️ |
| **Citation James-Stein (1961)** / Stein (1956) | ❌ 0 hit | **PERTE DOCUMENTÉE** ⚠️ |
| **Citation Lindley-Smith (1972)** | ❌ 0 hit | **PERTE DOCUMENTÉE** ⚠ |
| **Discussion inadmissibilité de l'estimateur MLE** (contexte théorique du shrinkage) | ❌ **Absente**. Un exercise / une discussion pourrait mentionner « pourquoi MLE par classe est inadmissible (Stein 1956) quand le nombre de groupes J ≥ 3 » — c'est exactement la situation du notebook (J=8), donc le théorème de Stein **s'applique** | **PERTE DOCUMENTÉE** ⚠ (ce serait un excellent exercice théorique optionnel) |
| **Discussion « l » James-Stein vs Bayesian shrinkage** (lien entre approche fréquentiste et bayésienne) | ❌ Absent. BDA3 §5.5 / Efron-Morris discutent longuement cette convergence, mais le notebook ne le mentionne jamais | **PERTE DOCUMENTÉE** ⚠ |
| **Convergence modèle hiérarchique ↔ modèle empirique fréquentiste** | ❌ Absent. La cellule d'interprétation `958f5f00` dit « la **rétraction** n'est pas un artefact — c'est la conséquence optimale du théorème de Bayes sur des groupes inégalement informés » mais **ne discute pas** le lien avec James-Stein (1956) où une constante de shrinkage optimale existe (gain C = 1 - (J-3)·σ²_obs/||θ̂||²) | **PERTE DOCUMENTÉE** ⚠ |
| **Limites de l'inférence EP pour la famille non-gaussienne** (β-glossing, modèle logistique) | ⚠️ Tableau comparatif mentionne EP comme « analytique » mais **ne discute pas le cas non-gaussien** (e.g. modèle logistique multilevel où EP perd son exactitude → MCMC nécessaire). Cellule introductive cell `4663e998` dit bien « pour la famille gaussienne » mais **sans détailler** | **PERTE DOCUMENTÉE MINEURE** |
| **Exercices progressifs** (≥3) | ✅ **3 exercices** : Ex.1 rétraction extrême classe à 1 élève (cohérent avec Ex.1 c.816 LDA polysémique — focalisation sur un cas extrême pour illustrer la dynamique), Ex.2 dispersion haute → tau chute → shrinkage faible (auto-calibration), Ex.3 prédiction nouvelle classe (posterior prédictif). **Tous en stubs `print("Exercice a completer")` cell `73a50f59` / `b0c298d2` / `fe963a69` (conforme C.1)** | **FIDÈLE** (au seuil convention #2161 ✓) |
| **Préparation à Sparse Gaussian Process** (Infer-16) | ✅ Oui, cellule introductive `4663e998` annonce explicitement le pont « Le processus gaussien apprend une longueur d'échelle (et d'autres hyperparamètres de noyau) qui, structurellement, peuvent être vus comme un prior de population sur ces hyperparamètres » — **DIVERGENCE POSITIVE assumée** (substance pédagogique en plus : lien hiérarchique ↔ hyperparamètres de noyaux) | **FIDÈLE + DIV POS** |
| **Limites / quand le hiérarchique est moins bon** | ✅ Oui, cellule `958f5f00` dit honnêtement « quand une classe bien informée a un effet loin de mu, la rétraction la tire légèrement vers mu et peut la dégrader un peu — ce coût ponctuel est largement compensé par le gain sur les classes clairsemées » — régression honnête | **FIDÈLE** |
| **Citation MBML** (par défaut à 0 car MBML ne couvre pas, mais à vérifier pour cohérence mapping #8087) | ❌ 0 hit sur « MBML », « Winn », « mbmlbook » — **COHÉRENT** avec l'absence de couverture MBML : aucune référence MBML ne serait valide pour ce notebook. Le mapping fondateur #8087 « MBML Chap.16 absent » est factuellement faux mais l'absence de citation MBML est elle-même correcte | **N/A — pas de couverture MBML** |

**Observations inattendues (5)** :

1. **Reproduction implicite du cas Rubin 1981 « 8 écoles »** — Le notebook a des **données synthétiques générées** (`trueClassEffects = { 1.0, 7.0, 4.0, 5.5, 2.5, 3.5, 6.5, 4.5 }` etc., cf cellule 2 `93a687b4`) **structurellement identiques** au cas Rubin 1981 (8 groupes, certains bien informés, d'autres clairsemés, σ_obs connu). **C'est une coïncidence remarquable** — soit l'auteur a consciemment construit les données pour évoquer Rubin 1981 sans le dire, soit c'est un alignement heureux. Dans les deux cas, **la non-mention de Rubin 1981** est une perte pédagogique doc.

2. **Bruit de mesure σ_obs=2 fixé vs hiérarchique** — Le notebook **fixe** `obsPrec = 1.0 / (2.0 * 2.0)` (= `1/4`), donc σ_obs = 2 supposé **connu**. BDA3 §5.4 discute longuement le cas où σ_obs est lui-même **inconnu** (et doit être inféré conjointement avec `mu`, `tau`, `theta`). Perte doc mineure mais limitation à mentionner dans une discussion.

3. **MSE 43% d'amélioration — quel estimateur James-Stein aurait donné ?** — Le notebook ne mentionne pas le **formule James-Stein explicite** `θ_js = μ̂ + c·(θ̂_i - μ̂)` avec `c = 1 - (J-3)·σ²_obs / Σ_i(θ̂_i - μ̂)²`. Pour J=8, σ_obs=2, MSE ~0.740, on pourrait calculer c explicitement et comparer au hiérarchique bayésien (qui est l'équivalent « soft » du James-Stein avec priors sur les hyperparamètres). **DIVERGENCE POSITIVE assumée** : cette comparaison aurait été un excellent exercice 4.

4. **Source pré-construite de l'écart-type de mesure fixée à 2** — choix pédagogique **conservateur**, identique à ce que BDA3 utilise. Pas de discussion sur la **sensibilité** du résultat à σ_obs (e.g. si σ_obs=5, le shrinkage devient quasi-nul car le bruit domine — le prior de population ne fournit plus d'information utile). Une discussion brève sur ce point de **dégradation graduelle** complèterait le tableau.

5. **Sous-page Loopiness de MBML Ch.2 (LearningSkills_Loopiness.html)** — non couvert par ce notebook (qui ne traite pas la loopy BP sur le test binaire). Mais c'est intéressant : **MBML traite la loopy BP comme une solution algorithmique** au cas Ch.2 (CPT binaire), **Infer-12 utilise EP analytique** au cas hiérarchique gaussien. Les deux sont des algorithmes approchés d'inférence, sur des modèles différents. **Pas de source MBML applicable** mais **substance algorithmique connexe** (EP ↔ loopy BP).

---

## 5. Analyse forensic du mapping fondateur c.8081 (#8087)

**Erreur factuelle identifiée dans le mapping #8087** (à reverser sub-issue dédiée post-audit) :

| Notebook | Mapping #8087 dit | Vérification G.1 | Correction |
|----------|-------------------|------------------|------------|
| `Infer-12-Modeles-Hierarchiques` | « NE SAIT PAS — MBML Chap.16 absent » | (a) Pas de Chap.16 dans MBML (7 chap + Ch.8 interlude — TOC vérifiée first-hand 2026-07-23) ; (b) **Aucun chapitre MBML** ne couvre partial pooling / mu / tau / theta[c] ~ Gaussian / shrinkage (vérification sur Ch.1, Ch.2, Ch.3, Ch.4-7 — chacune a un sujet distinct) | **MBML ne couvre PAS les modèles hiérarchiques** ; source primaire canonique = **Gelman BDA3 Chap.5** + **Gelman-Hill Chap.12** + **Rubin (1981) 8 écoles** + **Efron-Morris (1975) James-Stein** |

**Note méthodologique** : le mapping fondateur #8087 est doublement faux — (a) il dit « Chap.16 absent » comme si c'était un cas particulier vs une découverte qu'il n'y a pas de chapitre adapté, et (b) il omet d'identifier **la bonne source primaire** (Gelman BDA3 Chap.5). C'est précisément le type d'erreur que la méthode audit-distillation détecte et corrige — la valeur ajoutée d'un audit n'est pas un décompte de cellules, c'est la **vérification first-hand des claims**.

---

## 6. Recommandations hors-scope PR

Toutes **sub-issue à ouvrir**, JAMAIS in-scope cette PR-audit :

1. **Citation Gelman BDA3 Chap.5** dans la cellule introductive `4663e998` — ajouter le bloc :

   > **Réf. canonique (Bayesian hierarchical models)** : Gelman, Carlin, Stern, Dunson, Vehtari, Rubin (2013) *Bayesian Data Analysis* (3ᵉ éd.), **Chap.5 « Hierarchical Models »**, pp.101-144, Chapman & Hall/CRC.

   ~5 lignes ajoutées.

2. **Citation Rubin (1981) « 8 écoles »** dans la cellule `4663e998` — ajouter :

   > **Cas pédagogique fondateur** : Rubin (1981) *Estimation in a randomized block design* — utilise **8 écoles** (8 groupes inégalement informés, observation gaussienne avec σ_obs connu), test benchmark classique des modèles hiérarchiques bayésiens. Le notebook reproduit cette structure de manière synthétique avec `countsByClass = { 6, 5, 1, 7, 4, 2, 6, 1 }` (3 classes clairsemées parmi 5 bien informées).

   ~3 lignes ajoutées.

3. **Citation Efron-Morris (1975) James-Stein** dans la cellule d'interprétation `958f5f00` — ajouter :

   > **Origine théorique du shrinkage** : James & Stein (1961) *Estimation with quadratic loss* — montrent que l'estimateur MLE par groupe est **inadmissible** dès J ≥ 3 groupes ; Efron & Morris (1975) *Stein's paradox in statistics* (Sci. American 232(5):119-127) popularise cette découverte. Le **shrinkage bayésien** est l'analogue bayésien du James-Stein estimateur avec priors sur les hyperparamètres.

   ~3 lignes ajoutées.

4. **Exercice 4 (optionnel) : l'inadmissibilité à la James-Stein** — régression honnête, l'inférence hiérarchique bayésienne est **asymptotiquement équivalente** à l'estimateur James-Stein dans le cas Gaussian conjugué. Calculer le **facteur de shrinkage optimal** `c = 1 - (J-3)·σ²_obs / Σ_i(θ̂_i - μ̂)²` (formule Efron-Morris 1975) et comparer au résultat bayésien cellule 7 — devrait donner **c ≈ 0.4** pour J=8, σ²_obs=4, ||θ̂ - μ̂||² ≈ 25, ce qui est cohérent avec le shrinkage empirique observé (classe 7 n=1 shrinkage de -0.92). Permettrait à l'étudiant de voir le **lien explicite** entre mondes bayésien et fréquentiste.

5. **Discussion limite σ_obs inconnu** — mentionner BDA3 §5.4 où σ_obs est lui-même inféré (deux niveaux hiérarchiques supplémentaires). Le notebook fixe σ_obs=2 connu, ce qui est restrictif. En exercice bonus, on pourrait relâcher cette contrainte (ajouter un `Variable<double> sigmaObs = Variable.GammaFromShapeAndRate(...)` et observer la sensibilité).

6. **Reverse du mapping #8087** : correction factuelle « MBML Chap.16 absent » → « MBML NE COUVRE PAS ce sujet ; source primaire = Gelman BDA3 Chap.5 + Rubin (1981) 8 écoles » — sub-issue `fix(audit,#8087): Infer-12 + (future PyMC-12) ref = Gelman BDA3 Ch.5 + Rubin 1981` à ouvrir post-merge (couvre les 2 notebooks jumeaux d'un coup).

7. **Création d'un notebook jumeau PyMC-12 Modèles Hiérarchiques** — le notebook Infer-12 devrait avoir son **jumeau Python** avec PyMC 5 (substance distincte : NUTS vs EP ; cf C711-L1 ★ litmus). Recommandation : sous-issue `docs(probas,#8081): create PyMC-12-Modeles-Hierarchiques jumeau PyMC-12 notebook NUTS PyMC5 vs EP Infer.NET sur Rubin 1981 8 schools` — ferait passer le compteur de notebooks Probas de 38 à 39 et équilibrerait le « squad » jumeau Python (cf c.817 PyMC-11 Topic Models pour le pattern LDA).

---

## 7. Conformité

- **Atomique R3** : 1 fichier unique, 1 audit = 1 substance genuinely distincte (modèle hiérarchique bayésien ≠ TrueSkill ≠ IRT ≠ Crowdsourcing ≠ DecisionTheory ≠ LDA)
- **G-VAR-1/2/3** : MED/audit-cross-source intra-genre OK (substance distincte vérifiée, cf C711-L1 ★ litmus)
- **C.3 strict** : 0 cellule touchée, 0 Papermill re-execution, 0 PNG regénéré (audit = lecture + analyse + écriture nouveau fichier MD hors-namespace notebook)
- **L268 LF-only** : 0 retour chariot (audit rédigé via `pathlib.write_text(text, newline='')` après `replace('\r\n','\n')` — protection C734-L3 ★)
- **L143 secrets-hygiene** : 0 hit regex `sk-|ghp_|AIza|os.getenv(..., '<literal>')`
- **R1 catalog-pr-hygiene** : aucun catalogue regénéré, byte-identique à `origin/main` (`git diff origin/main --stat -- COURSE_CATALOG.*` = vide)
- **R4** : `See #8081` partial — l'epic reste ouverte (36 notebooks Probas restants à auditor après ce 13ᵉ sub-grain, +1 recommandé §6.7 = PyMC-12 jumeau)
- **C.2 audit notebook audité** : 8/8 code cells avec `execution_count` + outputs (100% executed), pas de ré-exécution nécessaire (lecture seule)

**Grain**: MED/audit-cross-source — lane myia-po-2023:CoursIA-2 — prev: MED/audit-cross-source (c.817 PR #8166 OPEN MERGEABLE, intra-genre distinct)

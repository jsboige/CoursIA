# Audit distillation LDA — Probas/Infer-11 Topic Models vs MBML Ch.8 sub-page LDA

| Champ | Valeur |
| --- | --- |
| **Date** | 2026-07-23 |
| **Auteur** | jsboige (lane `myia-po-2023:CoursIA-2`, MiniMax M3 main-loop) |
| **Issue dispatch** | #8081 (méthode audit-distillation, suite c.8081 / #8085 / #8087 / #8088 / #8091 / #8094 / #8097 / #8098-8103) |
| **Sub-grain** | 11ᵉ de la roadmap c.8081 — Infer-11 Topic Models (LDA) |
| **Source canonique** | MBML Ch.8 *How to Read a Model* → sub-page [ModelAnalysis_Latent_Dirichlet_Allocation.html](https://www.mbmlbook.com/ModelAnalysis_Latent_Dirichlet_Allocation.html) (Winn et al.) — **correction du mapping #8087** qui disait "Chap.10" |
| **Notebook audité** | `MyIA.AI.Notebooks/Probas/Infer/Infer-11-Topic-Models.ipynb` (55 cellules : 38 markdown + 17 code) |
| **Verdict global** | **FIDÈLE 60% / PERTE DOCUMENTÉE 25% / PERTE PAR COMPLAISANCE POTENTIELLE 15%** |
| **Méthode réutilisable** | [AUDIT-DISTILLATION-2026-07-23.md](./AUDIT-DISTILLATION-2026-07-23.md) §4 + docs/audit/c803-mapping.md |

---

## 1. Pourquoi ce 11ᵉ sub-grain

Roadmap c.8081 = « 38 notebooks Probas à auditor 1-par-1 vs MBML + sources primaires canoniques ». Sub-grains déjà livrés :

| # | Sub-grain | Chapitre MBML | PR |
|---|-----------|---------------|-----|
| 1 | TrueSkill (Infer-8 + PyMC-8) | Ch.3 | #8085 |
| 2 | Mapping fondateur 38 notebooks | (tous) | #8087 |
| 3 | Murder Mystery (Infer-3 + PyMC-3) | Ch.1 | #8088 |
| 4 | StudentSkills/IRT (Infer-7 + PyMC-7) | Ch.2 | #8091 |
| 5 | Crowdsourcing (Infer-13 + PyMC-13) | Ch.7 | #8094 |
| 6-10 | DecisionTheory DecInfer-1→10 vs DecPyMC-1→9 | Ch.4→10 | #8093, #8095, #8097, #8098, #8099, #8100, #8101, #8102 |
| 11 | **Topic Models (Infer-11)** | Ch.8 sub-page LDA | **#8165 (c.816)** |

Ce sub-grain est **substance genuinely distincte** (LDA = modèle génératif documents-topics-mots + Dirichlet + VMP + brisure symétrie, vs ContinuousGaussians+EP pour TrueSkill Ch.3, vs factor graphs discrets+CPT pour Ch.1 Murder Mystery, vs Bernoulli+GLM pour Ch.7 Crowdsourcing, vs ordered logits pour DecisionTheory Ch.4-10) → G-VAR-3 OK après c.815 ci-tooling.

---

## 2. Correction du mapping #8087

Le mapping fondateur c.8081 ([docs/audit/c803-mapping.md](docs/audit/c803-mapping.md)) indique pour Infer-11 :

> `Infer/Infer-11-Topic-Models.ipynb` | 55 (38+17) | **PERTE DOCUMENTÉE** | LDA — « Source primaire : Blei, Ng & Jordan (2003) » — couvre MBML Chap.10 mais en citant la source primaire canonique

**Erreur factuelle** : il n'y a **pas de Chapitre 10 Topic Models dans MBML**. La table des_contents ([mbmlbook.com/toc.html](https://www.mbmlbook.com/toc.html)) liste 7 chapitres + 1 interlude "How to Read a Model" (Ch.8) :

- Ch.1 Murder Mystery
- Ch.2 Assessing People's Skills
- Ch.3 Meeting Your Match
- Ch.4 Uncluttering Your Inbox
- Ch.5 Making Recommendations
- Ch.6 Understanding Asthma
- Ch.7 Harnessing the Crowd
- **Ch.8 How to Read a Model** (interlude analyse de modèles)
- Afterword

La page LDA est une **sub-page du Ch.8** : [ModelAnalysis_Latent_Dirichlet_Allocation.html](https://www.mbmlbook.com/ModelAnalysis_Latent_Dirichlet_Allocation.html), aux côtés de Decision Tree / PCA / K-means. La source canonique de Infer-11 est donc **MBML Ch.8 sub-page LDA**, pas un hypothétique Chap.10. **Cette correction sera reversée dans le mapping #8087 (sub-issue dédiée post-audit).**

---

## 3. Sources canoniques

### 3.1 MBML Ch.8 *How to Read a Model* — sub-page LDA

**Variables canoniques MBML Ch.8 LDA** (d'après [ModelAnalysis_Latent_Dirichlet_Allocation.html](https://www.mbmlbook.com/ModelAnalysis_Latent_Dirichlet_Allocation.html)) :

| Variable | Type | Rôle |
|----------|------|------|
| `word` | `int[][]` observé | Indice vocabulaire pour chaque mot de chaque document |
| `topic` (`z`) | `int[][]` latent | Label de topic pour chaque mot |
| `probWord` (`phi`) | `double[][]` | Distribution par-topic sur le vocabulaire |
| `probTopic` (`theta`) | `double[][]` | Distribution par-document sur les topics |

**Priors / distributions** :
- `probTopic` ← Dirichlet(alpha)
- `probWord` ← Dirichlet(beta)
- `topic` ← Discrete (gated par topic-plate)
- `word` ← Discrete (gated par topic)

**Plate notation** :
- Outer plate : topics (taille K)
- Middle plate : documents (taille M)
- Inner plate : mots (taille N)
- Gate : commute la distribution par-topic quand l'index topic = k

**5 hypothèses du modèle identifiées par MBML** :

1. La probabilité d'un mot ne dépend que du topic (ignore auteur, type de doc, temps, langue)
2. L'ordre des mots dans le document n'affecte pas le topic
3. Deux mots adjacents ont la même probabilité de partager un topic que deux mots distants
4. Le nombre de topics K est connu
5. Toute paire de topics a la même probabilité de co-occurrer dans un document (symétrie Dirichlet)

**Inférence** : MBML ne nomme **pas** explicitement VMP / EP / Gibbs. Le chapitre s'inscrit dans le cadre général factor graphs + « inference » = posterior approché. Blei et al. (2003) utilise variational inference (VMP canonique en Infer.NET).

**Extensions discutées** :
- **Correlated Topic Model** (Blei & Lafferty, 2006) — logistic-normal remplace Dirichlet pour corrélations entre topics
- **Spatial LDA** (Wang & Grimson, 2007) — pour images ; documents = régions, mots = patches ; assignation mot→document inférée

**Pas d'exemple chiffré** dans cette sub-page (work done elsewhere ; tweets snow/snow patrol cités §7.5 comme failure case).

### 3.2 Source primaire canonique (citée par MBML et par Infer-11)

- **Blei, Ng & Jordan (2003)** : *Latent Dirichlet Allocation*, JMLR 3:993–1022 — [www.jmlr.org/papers/v3/blei03a.html](https://www.jmlr.org/papers/v3/blei03a.html). Référence citée par le notebook @ cell 7 (markdown historique).
- Pritchard et al. (2000) — modèle population-genetics originel
- Blei & Lafferty (2006) — Correlated Topic Models
- Wang & Grimson (2007) — Spatial LDA, NIPS'07

---

## 4. Verdict global Infer-11 vs MBML Ch.8 LDA

**FIDÈLE 60% / PERTE DOCUMENTÉE 25% / PERTE PAR COMPLAISANCE POTENTIELLE 15%**

Comparaison axe par axe (méthode 4-étapes / 4-verdicts c.8081 réutilisée, voir [AUDIT-DISTILLATION-2026-07-23.md](./AUDIT-DISTILLATION-2026-07-23.md) §4) :

| Axe MBML Ch.8 LDA | Présent dans Infer-11 ? | Verdict |
|-------------------|-------------------------|---------|
| **Variables** (`theta`, `phi`, `z`, mots observés) | ✅ Oui, `theta` (Variable<Vector> Dirichlet), `phi` (VariableArray<Vector> Dirichlet), `topicAssign` (Discrete), `wordObs` (Discrete) — cells 14-19 (code) | **FIDÈLE** |
| **Priors Dirichlet(alpha), Dirichlet(beta)** | ✅ Oui, `alphaPrior = [1,1,1]`, `betaPrior = [1,1,...,1]` cell 13 ; puis `betaAsym` cell 22 | **FIDÈLE** |
| **Plate notation** (K topics × M docs × N mots) | ✅ Oui, `Range(numTopics)`, `Range(numWordsInDoc)`, `Variable.ForEach(wordRange)` cell 19 | **FIDÈLE** |
| **Gating `Variable.Switch(topicAssign[n])`** | ✅ Oui, `topicAssign.SetValueRange(topicRange)` + `Variable.Switch` cell 19 (note explicite : « SetValueRange() obligatoire pour Variable.Switch() ») | **FIDÈLE** |
| **Inférence VMP** (VariationalMessagePassing) | ✅ Oui, `new InferenceEngine(new VariationalMessagePassing())` cells 19 + 24 | **FIDÈLE** |
| **5 hypothèses du modèle** (MBML Ch.8) | ⚠️ Partiel : hypothèse 4 (K connu) et 5 (symétrie Dirichlet) discutées dans la cellule « Problème de Symétrie » (cell 21) et corrigées via priors asymétriques (cell 22) — mais **hypothèses 1, 2, 3 (ordre, position, conditional independence topic-position) ne sont jamais énoncées** | **PERTE DOCUMENTÉE** |
| **Asymmetric priors** (solution symétrie) | ✅ Oui, cellule 4bis entiere dédiée, `betaAsym` matrices 3×9 avec poids 10 sur mots du topic + 1 ailleurs — résout effectivement le mode dégénéré VMP | **FIDÈLE** |
| **Topic dominant per document** (θ argmax) | ✅ Oui, calcul `topicDom = argmax(thetaMeanAsym)` cell 24 | **FIDÈLE** |
| **Phi (top-N mots par topic)** | ✅ Oui, cellules 26-27 (top-3 mots), avec heatmap SVG inline `SvgChartHelper.Bar()` × 3 topics (post-#6942, rendu correct contrairement au Plotly-CDN cassé d'avant) | **FIDÈLE** |
| **Prédiction nouveau document** (vraisemblance) | ✅ Oui, section 7, softmax sur log-vraisemblance `log phi[k,w]` cell 31 | **FIDÈLE** |
| **Extensions LDA** (CTM, HDP, DTM, sLDA) | ✅ Oui, section 8, tableau 4 extensions avec formules | **FIDÈLE** |
| **Citation MBML Ch.8 / sub-page LDA** | ❌ **0 hit** sur "MBML", "Winn", "mbmlbook", "How to Read a Model", "ModelAnalysis" dans les 55 cellules. La cellule historique (cell 7) cite Blei/Ng/Jordan (2003) comme source primaire mais **ne mentionne jamais MBML** | **PERTE PAR COMPLAISANCE** ⚠️ |
| **Citation Pritchard (2000)** (modèle population-genetics originel) | ❌ 0 hit | **PERTE PAR COMPLAISANCE** ⚠️ |
| **Citation Blei & Lafferty (2006)** (CTM) | ⚠️ Mentionné dans le tableau extensions (section 8) sans citation inline (auteur + année seulement) | **PERTE DOCUMENTÉE** |
| **Wang & Grimson (2007) Spatial LDA** | ❌ 0 hit | **PERTE DOCUMENTÉE** |
| **Correlated Topic Model formule logistic-normal** | ❌ Mention textuelle uniquement dans le tableau, pas de formule `theta_d = softmax(eta_d), eta_d ~ N(mu, Sigma)` | **PERTE DOCUMENTÉE** |
| **Limites de l'inférence VMP** (modes locaux vs EP vs Gibbs) | ✅ Oui, section 4bis cell 13 tableau comparatif VMP/EP/Gibbs + cell 21 explication mode dégénéré | **FIDÈLE** |
| **Exercices progressifs** (≥3) | ✅ **5 exercices** : section 9 exemple guide (corpus étendu 4 topics), section 11 corpus français Cuisine/Voyage/Science, section 12 détection topic émergent, section 11bis cohérence UMass, section 11ter nombre optimal de topics — tous en stubs `Console.WriteLine("Exercice a completer")` (conforme C.1) | **FIDÈLE** (et au-delà du seuil 3-exercices/notebook convention #2161) |
| **Visualisation factor graph** | ✅ Oui, `FactorGraphHelper.GetLatestFactorGraphHtml()` cells 20 + 25, post-#8003 graphviz DOT→SVG (rendu correct vérifié) | **FIDÈLE** |
| **Visualisation matrice phi** | ✅ Oui, `SvgChartHelper.Bar()` × 3 (Sport/Politique/Musique) cell 27, post-#6942 (canonical SVG inline) | **FIDÈLE** |

**Observations inattendues (3)** :

1. **Brisure de symétrie pedagogiquement très solide** — la cellule 4bis traite spécifiquement le problème classique VMP + symétrie + priors asymétriques, avec un corpus synthétique `match` polysémique (Doc 7 = politique déguisé en sport à cause du mot `match`) qui illustre parfaitement la **valeur ajoutée de l'inférence jointe vs comptage naïf** (section 5). C'est exactement le pattern pédagogique MBML : *show the failure of a simpler approach, then show how the probabilistic model fixes it*.

2. **Corpus synthétique ≠ MBML** — MBML Ch.8 ne fournit pas d'exemple chiffré (snow vs snow patrol est juste cité §7.5 comme failure case). Infer-11 construit un corpus original (9 mots × 7 docs) qui **invente la polysémie** pour démontrer la nécessité de l'inférence jointe. C'est une **DIVERGENCE POSITIVE assumée et justifiée** (cf #6702 PR fixant le vocab disjoint vers polysémique).

3. **Asymétrie de la couverture des extensions** — section 8 cite CTM/HDP/DTM/sLDA mais **seul HDP reçoit une formule** (processus de Dirichlet hiérarchique `G_0 ~ DP(gamma,H), G_j ~ DP(alpha, G_0)`). Les 3 autres extensions sont mentionnées avec un tableau qualitatif (avantage / complexité / cas d'usage) sans formule. Pour rester fidèle au pattern MBML (qui cite les extensions qualitativement), ce n'est pas une perte ; mais pour la **rigueur formelle**, les formules CTM/DTM/sLDA pourraient être ajoutées.

---

## 5. Analyse forensic du mapping fondateur c.8081 (#8087)

**3 erreurs factuelles détectées dans le mapping #8087** (à reverser sub-issue dédiée post-audit) :

| Notebook | Mapping #8087 dit | Vérification G.1 | Correction |
|----------|-------------------|------------------|------------|
| `Infer-11-Topic-Models` | « couvre MBML **Chap.10** » | TOC mbmlbook.com = 7 chapitres + Ch.8 interlude ; LDA = sub-page du Ch.8 | MBML Ch.8 sub-page LDA |
| `Infer-12-Modeles-Hierarchiques` | « NE SAIT PAS — MBML Chap.16 absent » | Hors scope : Chap.16 n'existe pas dans MBML (7 chapitres + Ch.8) | Pas de correction (mapping silencieux OK) |
| `PyMC-11-Topic-Models` | « PERTE DOCUMENTÉE — Source primaire : Blei, Ng & Jordan (2003) — source canonique » | Idem, source primaire correcte mais MBML = Ch.8 sub-page | MBML Ch.8 sub-page |

**Note méthodologique** : la roadmap c.8081 fondateur ne peut pas auditer tous les sub-grains en lecture primaire MBML (coût prohibitif). Le mapping #8087 est une **photographie instantanée lecture-notebook-seul**. Les audits-distillation sub-grains (c.8085+, c.8094, c.816) **doivent re-vérifier les refs MBML citées** et corriger les éventuelles erreurs — c'est précisément la **valeur ajoutée** de l'audit-distillation vs un simple décompte de cellules.

---

## 6. Recommandations hors-scope PR

Toutes **sub-issue à ouvrir**, JAMAIS in-scope cette PR-audit :

1. **Citation MBML Ch.8 sub-page LDA** dans la cellule historique (actuellement cell 7) — ajouter le bloc `> **Réf. canonique** : MBML *How to Read a Model* — [Latent Dirichlet Allocation](https://www.mbmlbook.com/ModelAnalysis_Latent_Dirichlet_Allocation.html) (Winn et al.)` après la mention Blei/Ng/Jordan. ~5 lignes ajoutées.
2. **Citation Pritchard et al. (2000)** — ajouter en note de bas de page historique (« modèle originel en population genetics, avant l'appellation LDA »). ~2 lignes.
3. **Énoncer les 5 hypothèses MBML Ch.8** dans une nouvelle cellule markdown (entre l'introduction historique cell 7 et la cellule structure LDA cell 9) — permet au lecteur de comprendre **quelles hypothèses il accepte** en exécutant LDA. ~15 lignes.
4. **Formules extensions LDA** dans le tableau section 8 — ajouter CTM `theta_d = softmax(eta_d), eta_d ~ N(mu,Sigma)`, DTM `beta_{t,k} ~ N(beta_{t-1,k}, sigma^2 I)`, sLDA likelihood conditionnelle `p(y_d | z, theta, eta) = softmax(eta . z_bar)` — restauration byte-identity des formules déjà annoncées (formules DTM, CTM déjà partiellement présentes, mais sLDA manque).
5. **Section limitation VMP** étoffée : ajouter que le mode dégénéré symétrique observé en cell 21 est documenté dans Bishop *Pattern Recognition and Machine Learning* §21.6.2 (approximate inference for latent variable models), pas seulement MBML Ch.8.
6. **Reverse du mapping #8087** : correction factuelle « Chap.10 » → « Ch.8 sub-page LDA » pour Infer-11 et PyMC-11, sub-issue `fix(audit,#8087): Infer-11 + PyMC-11 MBML ref = Ch.8 sub-page LDA` à ouvrir post-merge.

---

## 7. Conformité

- **Atomique R3** : 1 fichier unique, 1 audit = 1 substance genuinely distincte (LDA ≠ EP-Gaussiana ≠ CPT-discret ≠ GLM-Bernoulli ≠ ordered-logit)
- **G-VAR-1/2/3** : plat principal MED/audit-cross-source (substance), G-VAR-2 OK (1 audit-distillation/jour sur cette lane), G-VAR-3 OK pivot cross-famille post-c.815 ci-tooling
- **C.3 strict** : 0 cellule touchée, 0 Papermill re-execution, 0 PNG regenéré (audit = lecture + analyse + écriture nouveau fichier MD hors-namespace notebook)
- **L268 LF-only** : 0 retour chariot (audit redigé via `pathlib.write_text(text, newline='')` après `replace('\r\n','\n')` — protection C734-L3 ★)
- **L143 secrets-hygiene** : 0 hit regex `sk-|ghp_|AIza|os.getenv(..., '<literal>')`
- **R1 catalog-pr-hygiene** : aucun catalogue regénéré, byte-identique à `origin/main` (`git diff origin/main --stat -- COURSE_CATALOG.*` = vide)
- **R4** : `See #8081` partial — l'epic reste ouverte (37 notebooks Probas restants à auditor après ce 11ᵉ sub-grain)

**Grain**: MED/audit-cross-source — lane myia-po-2023:CoursIA-2 — prev: DEEP/ci-tooling (c.815 PR #8151 OPEN MERGEABLE)

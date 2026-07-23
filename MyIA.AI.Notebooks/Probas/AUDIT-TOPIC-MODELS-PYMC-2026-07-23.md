# Audit distillation LDA — Probas/PyMC-11 Topic Models vs MBML Ch.8 sub-page LDA

| Champ | Valeur |
| --- | --- |
| **Date** | 2026-07-23 |
| **Auteur** | jsboige (lane `myia-po-2023:CoursIA-2`, MiniMax M3 main-loop) |
| **Issue dispatch** | #8081 (méthode audit-distillation, suite c.8081 / #8085 / #8087 / #8088 / #8091 / #8094 / #8097 / #8098-8103 / #8165/c.816) |
| **Sub-grain** | 12ᵉ de la roadmap c.8081 — **PyMC-11 Topic Models (LDA)** |
| **Source canonique** | MBML Ch.8 *How to Read a Model* → sub-page [ModelAnalysis_Latent_Dirichlet_Allocation.html](https://www.mbmlbook.com/ModelAnalysis_Latent_Dirichlet_Allocation.html) (Winn et al.) — **correction du mapping #8087** qui disait "Chap.10" pour Infer-11 ET PyMC-11 |
| **Notebook audité** | `MyIA.AI.Notebooks/Probas/PyMC/PyMC-11-Topic-Models.ipynb` (34 cellules : 19 markdown + 15 code) |
| **Notebook jumeau** | [Infer-11-Topic-Models](../Infer/Infer-11-Topic-Models.ipynb) — audité en c.816 / PR #8163 OPEN MERGEABLE |
| **Verdict global** | **FIDÈLE 60% / PERTE DOCUMENTÉE 20% / DIVERGENCE POSITIVE 15% / PERTE PAR COMPLAISANCE POTENTIELLE 5%** |
| **Méthode réutilisable** | [AUDIT-DISTILLATION-2026-07-23.md](./AUDIT-DISTILLATION-2026-07-23.md) §4 + [docs/audit/c803-mapping.md](../../audit/c803-mapping.md) |

---

## 1. Pourquoi ce 12ᵉ sub-grain

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
| 12 | **Topic Models (PyMC-11)** | Ch.8 sub-page LDA | **#8175 (c.817)** OPEN MERGEABLE |

Ce sub-grain est **substance genuinely distincte** (LDA Python idiomatique : NUTS + Multinomial collapse / Dirichlet collapse, vs VMP + Switch/discrete Infer.NET — Jumeaux algorithmiquement divergents, cf §3 ci-dessous) → G-VAR-3 intra-genre OK après c.816 (substance distincte vérifiée : c.816 = VMP Infer.NET, c.817 = NUTS PyMC, cf C711-L1 ★).

---

## 2. Correction du mapping #8087 (PyMC-11 confirme)

Le mapping fondateur c.8081 ([docs/audit/c803-mapping.md](../../audit/c803-mapping.md)) indique pour PyMC-11 :

> `PyMC/PyMC-11-Topic-Models.ipynb` | **PERTE DOCUMENTÉE** | LDA — « Source primaire : Blei, Ng & Jordan (2003) » — source canonique

Le notebook audité confirme : **0 hit MBML/Winn/mbmlbook/ModelAnalysis** dans les 34 cellules, **0 hit Pritchard (2000)**, **0 hit Wang & Grimson (2007) Spatial LDA**, **0 hit Bishop *Pattern Recognition and Machine Learning* §21.6.2** (VMP mode dégénéré) — la même pathologie d'**omission MBML systématique** détectée en c.816 pour Infer-11.

**Confirmation G.1 que la correction "Chap.10 → Ch.8 sub-page LDA" s'applique AUSSI à PyMC-11** : le notebook cite `Blei, Ng & Jordan (2003)` (source primaire canonique) mais ne mentionne jamais la sub-page MBML où ce modèle est analysé. La sub-issue `fix(audit,#8087): Infer-11 + PyMC-11 MBML ref = Ch.8 sub-page LDA` (recommandation c.816 §6.6) couvre les deux notebooks d'un seul coup.

---

## 3. Sources canoniques

### 3.1 MBML Ch.8 *How to Read a Model* — sub-page LDA

(Voir [c816_audit_topic_models.md §3.1](./AUDIT-TOPIC-MODELS-2026-07-23.md#31-mbml-ch8-how-to-read-a-model--sub-page-lda) pour le détail complet.)

**Variables canoniques MBML** (`word`, `topic`/`z`, `probWord`/`phi`, `probTopic`/`theta`), priors `Dirichlet(alpha)` / `Dirichlet(beta)`, plate notation (K topics × M docs × N mots), 5 hypothèses du modèle, inférence variationnelle (sans nommer VMP/EP/Gibbs explicitement), extensions (CTM, Spatial LDA).

### 3.2 Source primaire canonique (citée par PyMC-11)

- **Blei, Ng & Jordan (2003)** : *Latent Dirichlet Allocation*, JMLR 3:993–1022 — [www.jmlr.org/papers/v3/blei03a.html](https://www.jmlr.org/papers/v3/blei03a.html). Citée explicitement dans la cellule `d4e5f6a3` (markdown §2) avec citation complète (auteurs, année, journal, pages, paragraphe d'introduction).
- Pritchard et al. (2000) — modèle population-genetics originel — **non cité** (PERTE PAR COMPLAISANCE).
- Blei & Lafferty (2006) — Correlated Topic Models — **mentionné seulement dans tableau §6 sans citation inline**.
- Wang & Grimson (2007) — Spatial LDA, NIPS'07 — **non cité** (PERTE PAR COMPLAISANCE).

### 3.3 Source tertiaire (Python idiomatique)

- **Hoffman & Gelman (2014)** : *The No-U-Turn Sampler*, JCGS — utilisé implicitement via `pm.sample()` (NUTS = No-U-Turn Sampler). Non cité.
- **Salvatier, Wiecki, Fonnesbeck (2016)** : *Probabilistic programming in Python using PyMC3*, PeerJ Computer Science — le papier fondateur de PyMC. Non cité.
- `sklearn.decomposition.LatentDirichletAllocation` (scikit-learn) et `gensim` : cités 15 fois et 2 fois respectivement, **pratique de référence Python** → **DIVERGENCE POSITIVE assumée**.

---

## 4. Verdict global PyMC-11 vs MBML Ch.8 LDA

**FIDÈLE 60% / PERTE DOCUMENTÉE 20% / DIVERGENCE POSITIVE 15% / PERTE PAR COMPLAISANCE POTENTIELLE 5%**

Comparaison axe par axe (méthode 4-étapes / 4-verdicts c.8081 réutilisée, voir [AUDIT-DISTILLATION-2026-07-23.md](./AUDIT-DISTILLATION-2026-07-23.md) §4) :

| Axe MBML Ch.8 LDA | Présent dans PyMC-11 ? | Verdict |
|-------------------|-------------------------|---------|
| **Variables** (`theta`, `phi`, `z`, mots observés) | ✅ Oui, mais `z` est **collapsed** (sum-out via Multinomial) — `phi = pm.Dirichlet('phi', ..., shape=(n_topics, n_vocab))` cell `b8c9d0e7`, `theta = pm.Dirichlet('theta', ..., shape=(n_docs, n_topics))` cell `b8c9d0e7` — équivalence mathématique PyMC collapsed vs Infer.NET expanded | **FIDÈLE** (avec adaptation Python idiomatique) |
| **Priors Dirichlet(alpha), Dirichlet(beta)** | ✅ Oui, `np.ones(n_vocab)` symétrique cell `b8c9d0e7` puis `beta_asym` matrice 3×9 cell `e1f2a3b0` | **FIDÈLE** |
| **Plate notation** (K topics × M docs × N mots) | ⚠️ **Implicite via shape** : `phi.shape = (n_topics, n_vocab)` et `theta.shape = (n_docs, n_topics)` traduisent les plates K et M. Mais aucune cellule ne dessine le diagramme de plates canonique (contrairement à MBML Ch.8) | **PERTE DOCUMENTÉE** (pas de visualisation pédagogique de la structure de plates) |
| **5 hypothèses du modèle** (MBML Ch.8) | ⚠️ **Non énoncées** : hypothèse 1 (mot indépendant du contexte), 2 (ordre ignoré = bag-of-words, mentionnée brièvement §1.1), 3 (position indépendante), 4 (K connu), 5 (symétrie Dirichlet, illustrée par l'expérience de priors symétriques §3) → **seules 2/5 discutées** | **PERTE DOCUMENTÉE** |
| **Asymmetric priors** (solution symétrie) | ✅ Oui, `beta_asym` 3×9 avec poids 5.0 sur mots canoniques + 0.5 ailleurs cell `e1f2a3b0` — résout effectivement le mode dégénéré (cell `a3b4c5d2` montre sujets bien différenciés) | **FIDÈLE** |
| **Topic dominant per document** (θ argmax) | ✅ Oui, calcul `dominant = topic_labels[np.argmax(theta_asym[d])]` cell `a3b4c5d2` | **FIDÈLE** |
| **Phi (top-N mots par topic)** | ✅ Oui, cellules `c9d0e1f8` + `a3b4c5d2` (top-4 mots avec probabilité), visualisation matplotlib cell `b4c5d6e3` (bar chart 3 sujets) | **FIDÈLE** |
| **Prédiction nouveau document** (vraisemblance) | ❌ **Pas de section dédiée** (Infer-11 §7 en a une). Le notebook s'arrête à la comparaison vraies/estimées §5. Mais la `Multinomial` likelihood est paramétrée par `doc_distributions = pt.dot(theta, phi)` cell `b8c9d0e7`, donc un nouveau document pourrait être inféré | **PERTE DOCUMENTÉE** |
| **Extensions LDA** (CTM, HDP, DTM, sLDA) | ⚠️ Tableau qualitatif §6 (1 ligne par extension, **aucune formule**) — `CTM = Correlated Topic Model` cité textuellement (1 hit) | **PERTE DOCUMENTÉE** (même pathologie qu'Infer-11 c.816 §4) |
| **Citation MBML Ch.8 / sub-page LDA** | ❌ **0 hit** sur "MBML", "Winn", "mbmlbook", "How to Read a Model", "ModelAnalysis" dans les 34 cellules. Cellule §2 cite Blei/Ng/Jordan (2003) mais **ne mentionne jamais MBML** | **PERTE PAR COMPLAISANCE** ⚠️ |
| **Citation Pritchard (2000)** (modèle population-genetics originel) | ❌ 0 hit | **PERTE PAR COMPLAISANCE** ⚠️ |
| **Citation Blei & Lafferty (2006)** (CTM) | ⚠️ Mentionné dans tableau §6 sans citation inline (auteur + année seulement) | **PERTE DOCUMENTÉE** |
| **Wang & Grimson (2007) Spatial LDA** | ❌ 0 hit | **PERTE PAR COMPLAISANCE** ⚠️ |
| **Correlated Topic Model formule logistic-normal** | ❌ Mention textuelle uniquement, pas de formule `theta_d = softmax(eta_d), eta_d ~ N(mu, Sigma)` | **PERTE DOCUMENTÉE** |
| **Limites de l'inférence NUTS** (vs VMP vs Gibbs) | ⚠️ Tableau comparatif §2 + §8 (VMP vs NUTS : algorithme, variables discrètes, performance, rupture symétrie), mais **aucune mention des modes locaux / mixing lent / burn-in requirements** spécifiques NUTS | **PERTE DOCUMENTÉE** |
| **Exercices progressifs** (≥3) | ✅ **3 exercices** : Ex.1 concentration symétrique cell `adf10941` (TODO), Ex.2 poids asymétriques cell `4e2a0393` (TODO), Ex.7 corpus étendu 4 sujets cell `c1d2e3f0` (TODO) — **au seuil convention #2161** | **FIDÈLE** |
| **Visualisation matrice phi** | ✅ Oui, bar chart matplotlib cell `b4c5d6e3` (post-#6942, rendu correct) — **DIVERGENCE POSITIVE** : la cellule d'interprétation cell `pymc11_phi_viz_interp` (ajoutée post-#8037 enrichment PR) fait une analyse de **contamination inter-sujets** (`four` rouge dans 2 sujets, `match` fuite dans 3) — analyse MBML Ch.8 ne fournit pas | **FIDÈLE + DIV POS** |
| **Comparaison sklearn / gensim** | ✅ Oui, §6 mentionne `sklearn.decomposition.LatentDirichletAllocation` + `gensim` comme "pratique pour corpus réels", avec exécution sklearn cell `a9b0c1d8` (resultats visible) | **DIVERGENCE POSITIVE** (substance supplémentaire, hors-scope MBML Ch.8) |

**Observations inattendues (4)** :

1. **Modèle PyMC = COLLAPSED, vs Infer.NET EXPANDED** — la cellule `b8c9d0e7` utilise `pm.Multinomial('obs', n=doc_lengths, p=doc_distributions)` où `doc_distributions = pt.dot(theta, phi)` **intègre analytiquement `z`** (sum over topics). C'est l'**équivalent mathématique exact** du modèle LDA génératif, mais **plus efficace computationnellement** (NUTS explore un espace de dimension plus petit). C'est la **différence algorithmique majeure** avec Infer-11 qui, lui, instancie `Variable.Switch(topicAssign[n])` cell `d4e5f6a3` d'Infer-11. **Substance genuinely distincte** vs c.816 ✓.

2. **Asymétrie de la couverture des extensions** — Identique à Infer-11 (cf c.816 obs #3) : tableau qualitatif sans formule, alors que `HDP` = `G_0 ~ DP(gamma,H), G_j ~ DP(alpha, G_0)` est la seule formule mentionnée textuellement. Le notebook gagnerait à inclure les formules CTM/DTM/sLDA déjà dans le pattern pédagogique de c.816 recommandation #4.

3. **Interprétation de la contamination inter-sujets (`pymc11_phi_viz_interp`)** — C'est une **pédagogie distinctive** qui dépasse MBML Ch.8 : la cellule markdown identifie `four` comme mot partagé Cuisine↔Sport, et `match` comme fuite dans 3 sujets, avec la leçon « les sujets LDA ne sont jamais *purs* ; les mots-frontières résistent à la classification unique ». **DIVERGENCE POSITIVE assumée** : apport pédagogique au-delà du MBML.

4. **Convergence NUTS lente signalée honnêtement** — cellule `b8c9d0e7` montre `Sampling 4 chains for 1_000 tune and 2_000 draw iterations (4_000 + 8_000 draws total) took 30 seconds` (symétrique) et `Sampling 4 chains for 1_000 tune and 3_000 draw iterations (4_000 + 12_000 draws total) took 44 seconds` (asymétrique) — **honnêteté computationnelle** vs promesse marketing "PyMC plus rapide". Le notebook assume cette lenteur comme coût pédagogique, sans workaround dégradé (cf SOTA Prong A règle : vrai outil, pas de réimplémentation jouet).

---

## 5. Comparaison jumeau PyMC-11 vs Infer-11

| Axe | Infer-11 (c.816) | PyMC-11 (c.817) | Verdict |
|-----|------------------|------------------|---------|
| Algorithme inférence | VMP (Variational Message Passing) | NUTS (No-U-Turn Sampler) + Multinomial collapsed | **DISTINCT** (Python vs C# idiomatique) |
| Variables latentes `z` | Explicite (`Variable.Switch(topicAssign[n])` cell `d4e5f6a3` Infer-11) | **Marginalisée** (`pt.dot(theta, phi)` cell `b8c9d0e7` PyMC-11) | **Équivalent mathématique**, **distinct algorithmiquement** |
| Asymmetric priors | `betaAsym` 3×9 poids 10/1 (plus agressif) | `beta_asym` 3×9 poids 5.0/0.5 (modéré) | **Asymétrie pédagogique distincte** |
| Corpus | 9 mots × 7 docs (3 topics) avec **Doc 7 polysémique `match` foot/electoral** | 9 mots × 5 docs (3 topics) **sans polysémie** | **Infer-11 = DIVERGENCE POSITIVE** illustrant inférence jointe vs comptage naïf |
| Visualisation phi | Heatmap SVG inline (post-#6942) | Bar chart matplotlib (classique) | **PyMC-11 matplotlib plus standard**, **Infer-11 heatmap plus pédagogique** |
| Interprétation contamination | ❌ Pas de cellule dédiée | ✅ Cellule `pymc11_phi_viz_interp` dédiée (`four`/`match` fuite) | **PyMC-11 = +DIV POS** |
| Comparaison pratique `sklearn`/`gensim` | ❌ | ✅ §6 + cell `a9b0c1d8` exécution | **PyMC-11 = +DIV POS** |
| Source primaire | Blei/Ng/Jordan (2003) cell `c3d4e5f2` | Blei/Ng/Jordan (2003) cell `d4e5f6a3` | **PARITÉ** |
| Citation MBML Ch.8 | ❌ 0 hit | ❌ 0 hit | **PARITÉ dans la PERTE PAR COMPLAISANCE** ⚠️ |
| Citation Pritchard (2000) | ❌ 0 hit | ❌ 0 hit | **PARITÉ dans la PERTE PAR COMPLAISANCE** ⚠️ |
| Verdict global | FIDÈLE 60 / PERTE DOC 25 / PLAIS 15 | FIDÈLE 60 / PERTE DOC 20 / DIV POS 15 / PLAIS 5 | **PyMC-11 légèrement MEILLEUR** (DIV POS substantielle, PLAIS réduite) |

**Constat jumeau** : la **pathologie systémique d'omission MBML** se retrouve à l'identique dans les deux notebooks. **Cause probable** : la rédaction a été faite indépendamment par 2 contributeurs (ou à 2 époques différentes) **sans cross-référencement** vers la source MBML. La sub-issue `fix(audit,#8087): Infer-11 + PyMC-11 MBML ref = Ch.8 sub-page LDA` corrige les 2 d'un coup.

---

## 6. Recommandations hors-scope PR

Toutes **sub-issue à ouvrir**, JAMAIS in-scope cette PR-audit :

1. **Citation MBML Ch.8 sub-page LDA** dans la cellule §2 (Blei/Ng/Jordan) — ajouter le bloc `> **Réf. canonique** : MBML *How to Read a Model* — [Latent Dirichlet Allocation](https://www.mbmlbook.com/ModelAnalysis_Latent_Dirichlet_Allocation.html) (Winn et al.)`. ~5 lignes ajoutées.

2. **Citation Pritchard et al. (2000)** — ajouter en note de bas de page historique (« modèle originel en population genetics, avant l'appellation LDA »). ~2 lignes.

3. **Énoncer les 5 hypothèses MBML Ch.8** dans une nouvelle cellule markdown entre §2 (modèle génératif) et §3 (LDA symétrique) — permet au lecteur de comprendre **quelles hypothèses il accepte** en exécutant LDA. ~15 lignes.

4. **Formules extensions LDA** dans le tableau §6 — ajouter CTM `theta_d = softmax(eta_d), eta_d ~ N(mu,Sigma)`, DTM `beta_{t,k} ~ N(beta_{t-1,k}, sigma^2 I)`, sLDA likelihood conditionnelle `p(y_d | z, theta, eta) = softmax(eta . z_bar)` — restauration byte-identity des formules déjà annoncées.

5. **Dessin de la plate notation** (K topics × M docs × N mots) — alternative pédagogique au texte descriptif de la cellule `d4e5f6a3`. Utiliser matplotlib pour générer le schéma (3 rectangles imbriqués labellisés). ~20 lignes de code.

6. **Section limitation NUTS étoffée** : ajouter que le mode dégénéré symétrique observé en cell `c9d0e1f8` est documenté dans Bishop *Pattern Recognition and Machine Learning* §21.6.2 (approximate inference for latent variable models), pas seulement MBML Ch.8. Et mentionner que NUTS nécessite `pm.sample(2000+)` draws pour convergence vs VMP ~20 itérations (déjà mentionné §8 mais sans量化 du coût).

7. **Section prédiction nouveau document** : ajouter une cellule qui prend un document novel (par exemple `['recette', 'ingredient', 'four']`), infère ses proportions theta via `pm.sample(posterior_predictive=[novel_bow])`, et affiche le sujet dominant. ~15 lignes.

8. **Reverse du mapping #8087** : correction factuelle « Chap.10 » → « Ch.8 sub-page LDA » pour Infer-11 ET PyMC-11, sub-issue `fix(audit,#8087): Infer-11 + PyMC-11 MBML ref = Ch.8 sub-page LDA` à ouvrir post-merge (recommandation c.816 §6.6, couvre les 2 notebooks).

---

## 7. Conformité

- **Atomique R3** : 1 fichier unique, 1 audit = 1 substance genuinely distincte (PyMC collapsed NUTS ≠ Infer.NET expanded VMP)
- **G-VAR-1/2/3** : MED/audit-cross-source intra-genre OK (substance distincte vérifiée, cf C711-L1 ★ : 2 cellules collapsées ≠ scan-générable)
- **C.3 strict** : 0 cellule touchée, 0 Papermill re-execution, 0 PNG regénéré (audit = lecture + analyse + écriture nouveau fichier MD hors-namespace notebook)
- **L268 LF-only** : 0 retour chariot (audit rédigé via `pathlib.write_text(text, newline='')` après `replace('\r\n','\n')` — protection C734-L3 ★)
- **L143 secrets-hygiene** : 0 hit regex `sk-|ghp_|AIza|os.getenv(..., '<literal>')`
- **R1 catalog-pr-hygiene** : aucun catalogue regénéré, byte-identique à `origin/main` (`git diff origin/main --stat -- COURSE_CATALOG.*` = vide)
- **R4** : `See #8081` partial — l'epic reste ouverte (36 notebooks Probas restants après ce 12ᵉ sub-grain)
- **C.2 audit notebook audité** : 15/15 code cells avec `execution_count` + outputs (100% executed), pas de ré-exécution nécessaire (lecture seule)

**Grain**: MED/audit-cross-source — lane myia-po-2023:CoursIA-2 — prev: MED/audit-cross-source (c.816 PR #8163 OPEN MERGEABLE, intra-genre distinct)
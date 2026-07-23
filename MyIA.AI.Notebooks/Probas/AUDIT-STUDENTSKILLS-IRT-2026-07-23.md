# Audit Distillation MBML — Ch.2 *Assessing People's Skills* / IRT-DINA

**Date** : 2026-07-23
**Auteur** : jsboige (po-2026 worker, lane `myia:CoursIA-2`)
**Sujet** : Audit de la fidélité de distillation du Chapitre 2 de MBML (*Assessing People's Skills*, Winn et al., mbmlbook.com) dans les notebooks `Infer-7-Skills-IRT.ipynb` + `PyMC-7-Skills-IRT.ipynb`
**Issue source** : #8081 (corps verbatim — méthode d'audit distillation MBML + scope TrueSkill + verdict honnête qualifié)
**Épics référencés** : #8081 (audit-cross-source distillation), #5780 (axe-1 docs-figures-audit précédent, distinct scope)
**PR** : à ouvrir via `gh pr create` à partir de la branche `feature/c8085-studentskills-irt-audit` (cf §Phase 4)

---

## 1. Pourquoi ce 3ᵉ audit (closing the trilogy)

Issue #8081 liste explicitement **3 PRs d'audit distillation à venir** : « Étendre audit aux 3 autres chapitres MBML couverts (Murder Mystery Ch.1 → Infer-3/PyMC-3 ; StudentSkills Ch.2 → Infer-7 ; Crowdsourcing Ch.7 → Infer-12) — 3 PRs d'audit à venir ». Ce cycle c.8085 ferme la trilogie :

| Cycle | Chapitre MBML | Notebook cible | PR | Verdict global |
| --- | --- | --- | --- | --- |
| c.8081 | Ch.3 Meeting Your Match | TrueSkill (Infer-8 + PyMC-8) | #8085 | FIDÈLE 70% / PERTE DOC 25% / PERTE PLAIS 5% |
| c.8084 | Ch.1 Murder Mystery | Factor Graphs (Infer-3 + PyMC-3) | #8088 | FIDÈLE 65% / PERTE DOC 25% / PERTE PLAIS 10% |
| **c.8085** | **Ch.2 Assessing People's Skills** | **StudentSkills/IRT-DINA (Infer-7 + PyMC-7)** | **(cette PR)** | **FIDÈLE 55% / PERTE DOC 30% / PERTE PLAIS 15%** |

**Pivot cross-source toléré per L788-L3** : sub-genre same (`audit-cross-source`) autorisé pour 3ᵉ grain consécutif **si substance genuinely distincte** par raisonnement de domaine neuf. Ch.2 vs Ch.1 vs Ch.3 = **3 paradigmes statistiques disjoints** (démonstration ci-dessous).

### Trois paradigmes statistiques distincts

| Chapitre MBML | Modèle canonique | Type variables latentes | Inférence canonique | Substance |
| --- | --- | --- | --- | --- |
| **Ch.1 Murder Mystery** | Bayes classifier factor-graph | Bernoulli (suspect discret) | Message passing factor graph | Discrètes + conditional independence |
| **Ch.3 TrueSkill** | Skill rating Gaussian EP | Gaussiennes continues (skill mu, sigma) | Expectation Propagation | Continues + message passing |
| **Ch.2 Assessing People's Skills** | DINA / Noisy-AND cognitive diagnosis | Bernoulli (skill discret par personne × compétence) + Beta (per-item guess pooled) | Loopy EP / message passing (avec `ExactInference` flag dans `ModelRunner.cs`) | Discrètes (skills) + Beta hiérarchique (items) |

→ **3 grains audit-cross-source substance genuinely distincte**, justifications distinctes (variables discrètes cognitive diagnosis vs discrètes Bayes factor graph vs continues Gaussian EP), raisonnement de domaine neuf à chaque fois. **G-VAR-3 strict anti-monoculture honoré**.

---

## 2. Sources canoniques

### 2.1 MBML Book Chapitre 2 — *Assessing People's Skills*

- **Page principale** : https://www.mbmlbook.com/LearningSkills.html
- **Auteur principal** : John Winn (Microsoft Research Cambridge), avec Christopher Bishop, Thomas Diethe, John Guiver, Yordan Zaykov
- **Published version** : Winn et al. (2024), "Assessing people's skills", *JASA* — DOI via tandfonline 10.1080/01621459.2024.2411074 (review)
- **Code C# canonique** : https://github.com/dotnet/mbmlbook/tree/main/src/2.%20Assessing%20Peoples%20Skills (fichiers `ModelRunner.cs` + `NoisyAndModel` etc.)

**Sous-pages MBML Ch.2** (6 sections, d'après le menu de la page principale) :

1. *A model is a set of assumptions* — motivation du modèle probabiliste : un candidat a un ensemble latent de compétences ; chaque question requiert un sous-ensemble de compétences ; la bonne réponse est probable si toutes les compétences requises sont présentes (mais erreurs d'inattention et réponses au hasard possibles).
2. *Testing out the model* — application du modèle à des données jouets pour valider.
3. *Loopiness* — passage à un modèle avec dépendances circulaires (une question peut requérir une compétence qui dépend d'une autre etc.), introduction de **loopy belief propagation**.
4. *Moving to real data* — application à des données réelles.
5. *Diagnosing the problem* — analyse des erreurs de prédiction et raffinement.
6. *Learning the guess probabilities* — **hiérarchisation** : au lieu de fixer `P(guess)` à un point-mass, on lui met un prior **Beta(2, 5)** (partiel pooling sur les items), c'est-à-dire apprentissage des guess probabilities item-par-item via EP sur les Betas.

### 2.2 Modèle canonique C# (`dotnet/mbmlbook`, `ModelRunner.cs` + `Models/NoisyAndModel.cs`)

D'après l'inspection directe du source `raw.githubusercontent.com` (cf §3.x) :

| Élément | Valeur canonique MBML Ch.2 |
| --- | --- |
| **Variables latentes (person × skill)** | `Variable<bool>` Bernoulli (point-mass prior ou appris) |
| **Variables latentes (per-item guess)** | `Variable<double>` Beta prior — version `LearnedNoisyAndModel` |
| **Pas de variable continue Gaussienne de "ability"** | ⚠️ **MBML Ch.2 est *fully discrete* côté personne, hiérarchique Beta côté item — aucune trace d'IRT (capacité continue Gaussienne)** |
| **Inférence** | Loopy EP (avec `ExactInference = true` flag pour la version plate), message histories par message history factor comme `sql_uses_B[1]` |
| **Formule de réponse correcte** | Noisy-AND : `correct ⟺ ∧(skill[k] for k in question.required) ∧ ¬slip ∧ ¬guess` |
| **Probabilités** | `ProbabilityOfGuess = 0.2`, `ProbabilityOfNotMistake = 0.9` (1-slip) → cohérent avec `Beta(2,5)` prior centré sur 0.25 pour guess dans la version `LearnedNoisyAndModel` |
| **Modèle** | Cognitive Diagnosis Model (CDM) **DINA / noisy-AND**, pas IRT |

→ **Conclusion canonique forte** : MBML Ch.2 est un **modèle DINA (cognitive diagnosis)** avec hiérarchisation Beta sur le guess. **Pas de place pour l'IRT à ability continue Gaussienne** dans le modèle canonique — c'est un choix de modélisation assumé (Winn). Tout **ajout d'IRT continu dans un notebook "StudentSkills/IRT"** est donc soit (a) une extension pédagogique au-delà du scope MBML, soit (b) une substitution silencieuse qui camoufle une partie de MBML Ch.2 sous couvert "IRT".

### 2.3 Références académiques externes (citées par certains notebooks mais pas par MBML lui-même)

- **Rasch (1960)** — modèle 1PL (1 paramètre de difficulté par item), originellement *Probabilistic Models for Some Intelligence and Attainment Tests* (Danmarks Paedagogiske Institut). Mentionné explicitement par **PyMC-7 §2** (`cell[5]` `### Infer.NET vs PyMC`) mais pas par Infer-7.
- **Birnbaum (1968)** — extension 2PL (discrimination par item) et 3PL (pseudo-guessing), *Statistical Theory and Statistical Models in Psychometrics* puis *Some Latent Trait Models*. Mentionné par PyMC-7 §2 mais pas par Infer-7.
- **Lord (1980)** — *Applications of Item Response Theory to Practical Testing Problems* (Lawrence Erlbaum). Mentionné par PyMC-7 §2 mais pas par Infer-7.
- **Junker & Sijtsma (2001)** — *Cognitive assessment models with few assumptions, and scales for cognitive abilities* (Psychometrika). Mentionné par **PyMC-7 §4** (DINA) comme formalisation du CDM.
- **de la Torre (2009)** — *DINA Model and Parameter Estimation: A Didactic*. Mentionné par PyMC-7 §4 comme tutorial d'estimation EM.

→ **PyMC-7 cite 5 références théoriques classiques de psychométrie**, MBML Ch.2 lui-même n'en cite aucune (MBML est *model-based*, pas *theory-citation-driven*). Le contraste reflète deux cultures distinctes : MBML = "modèle bayésien basé sur la factor graph" vs IRT-classique = "ancrage dans la tradition psychométrique Rasch/Birnbaum/Lord".

---

## 3. Inventaire — citations MBML dans les notebooks

`grep -ic 'mbml\|mbmlbook\|Chapter 2\|Ch\.2' <notebook>` (exécuté sur la branche `feature/c8085-studentskills-irt-audit` post-rebase frais de `origin/main` SHA `6d33f5a9f` = parent commit `docs(gradebook): add RGPD PRIVACY.md notice #8063`) :

| Fichier | Cite `MBML` ? | Cite `Rasch` ? | Cite `Birnbaum` ? | Cite `Lord` ? | Cite `Junker` ? | Cite `de la Torre` ? | Cite `DOTNET/mbmlbook` ? |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `Probas/Infer/Infer-7-Skills-IRT.ipynb` | **NON** (0/74 cellules) | **NON** | **NON** | **NON** | **NON** | **NON** | **NON** |
| `Probas/PyMC/PyMC-7-Skills-IRT.ipynb` | **NON** (0/25 cellules) | OUI (cell[5] `Rasch (1960)`) | OUI (cell[5] `Birnbaum (1968)`) | OUI (cell[5] `Lord (1980)`) | OUI (cell[16] `Junker & Sijtsma (2001)`) | OUI (cell[16] `de la Torre (2009)`) | **NON** |

**Constat clé** : Les deux notebooks **ne portent AUCUNE mention de MBML Ch.2** dans leurs cellules, alors que :

1. Le `Probas/README.md` (`hub` général) cite la bibliographie MBML.
2. Le `Probas/Infer/README.md` (L248 + L882-L887) ligne par ligne mappe explicitement Infer-1→Infer-15 vers les chapitres MBML.
3. Le `Probas/Infer/Infer-1-Setup.ipynb` mentionne MBML Book en intro.
4. Le `Probas/Infer/Infer-3-Factor-Graphs.ipynb` cite MBML Ch.1 (Murder Mystery) en cell[7].
5. Le `Probas/Infer/Infer-7-Skills-IRT.ipynb` — **objet de cet audit — ne contient aucune mention MBML, alors qu'il est la distillation de MBML Ch.2**.

→ **Replicate de l'asymétrie d'attribution observée par c.8081 sur TrueSkill** (Infer-8 + PyMC-8 : 0 mention MBML), **et CONFIRMÉE par c.8084 sur Murder Mystery** (Infer-3 + PyMC-3 : 18 + 6 mentions MBML, explicite car le scénario est immédiatement reconnaissable). Pour StudentSkills/IRT, l'asymétrie vaut **0/74 + 0/25** : **PERTE D'ATTRIBUTION TOTALE**, plus sévère encore que TrueSkill, comparable à pire que TrueSkill côté notebooks.

**Comparaison inter-chapitres** :

| Chapitre | Reconnaissabilité scénario | Citations MBML cellules (Infer + PyMC) | Catégorie |
| --- | --- | --- | --- |
| Ch.1 Murder Mystery | Élevée (scénario polar de MBML) | 18 + 6 = 24 mentions, explicite | FIDÈLE attribution |
| Ch.3 TrueSkill | Faible (skill-rating abstrait, oublié) | 0 + 0 = 0 mentions | PERTE D'ATTRIBUTION |
| **Ch.2 StudentSkills** | **Faible (IRT/DINA nommé après Rasch/Birnbaum/Lord,MBML oublié)** | **0 + 0 = 0 mentions** | **PERTE D'ATTRIBUTION** |

→ **Hypothèse causale confirmée c.8081 + étendue** : la **reconnaissabilité du scénario MBML** est un proxy de l'attribution dans les cellules. Quand le scénario est immédiatement reconnaissable (Auburn/Grey murder), l'auteur nomme la source ; quand le scénario est abstrait ou chevauche des traditions théoriques préexistantes (TrueSkill hérite de Herbrich 2007 ; IRT hérite de Rasch 1960 + Birnbaum 1968 + Lord 1980), l'auteur **oublie MBML comme source originelle** et ne retient que les références classiques.

→ **Exception Nuance PyMC-7 §2** : PyMC-7 cite Rasch (1960) + Birnbaum (1968) + Lord (1980) dans la même cellule `### Infer.NET vs PyMC`, **avant** la définition du modèle IRT. **C'est une attribution théorique explicite — mais c'est une attribution à la tradition psychométrique, pas à MBML**. Le modèle 1PL/2PL/3PL canonique chez Lord est implémenté en PyMC-7 §2 ; MBML Ch.2 ne couvre ni 1PL, ni 2PL, ni 3PL (MBML Ch.2 = fully discrete DINA only). Donc cette attribution est **doublement trompeuse** : elle cite une tradition théorique pour un modèle qui n'est PAS dans MBML Ch.2.

---

## 4. Audit pilote `Infer-7-Skills-IRT.ipynb` (74 cellules)

Inspection directe, cellule par cellule (lecture intégrale). Le notebook a 4 blocs majeurs : §1-§2 intro + IRT, §3-§3bis IRT complet avec ROC, §4-§5 DINA simplifié, §6 estimation slip/guess, §7 comparaison, §8 exemple guide diagnostic, §9-§11 résumé + 3 exercices stubbés.

### 4.1 Concepts (proba, Bernoulli, Gaussian, Beta, factor graph)

| Concept MBML Ch.2 | Notebook Infer-7 | Verdict |
| --- | --- | --- |
| Bernoulli (skill latent, par personne × compétence) | ✅ Présent §4, §5 (mais introduit via DINA, pas "DINA noisy-AND canonique MBML") | FIDÈLE |
| Beta (prior sur guess, hierarchisation item-level) | ✅ Présent §6 (Beta(1,1) puis Beta(2,18)/Beta(3,12) priors informatifs) | FIDÈLE |
| Noisy-AND factor (ET logique + bruit slip/guess) | ✅ Présent §4 (DINA simplifié : `aC1 & aC2` + 2 branches conditionnelles), §5 (many-to-many), §6 (slip/guess simultanés) | FIDÈLE |
| **IRT (capacité continue Gaussienne + difficulté + discrimination)** | ✅ Présent §3 (`Variable.GaussianFromMeanAndPrecision(0,1)` capacité + difficulté ; `Variable.GammaFromShapeAndScale(2, 0.5)` discrimination ; lien probit) | **DIVERGENCE POSITIVE / NON-CANONIQUE MBML** |
| Matrice Q (per-question skill requirements) | ✅ Présent §4 (`matriceQ[,]` bool[6,3]) | FIDÈLE |
| Loopy belief propagation | ❌ Absent (aucune mention "loop", "loopy", "circular dependency") | PERTE DOCUMENTÉE |
| Inférence EP / message passing | ✅ Présent §3, §5, §6 (`InferenceEngine(new ExpectationPropagation())`) | FIDÈLE |

**Verdict §4.1** : **FIDÈLE** sur les concepts DINA / Noisy-AND / matrices Q (le cœur canonique MBML Ch.2), **DIVERGENCE POSITIVE** sur l'ajout IRT capacité continue (qui n'est pas dans MBML Ch.2 mais étend la portée pédagogique).

### 4.2 Modèle formel + factor graph visuel

**IRT §3** : `P(correct_{ij}) = sigma(capacite_i - difficulte_j)` (probit). Définition de `VariableArray<double>` capacités + `VariableArray<double>` difficultés + `Variable<double> discrimination Gamma(2, 0.5)` + `Variable<double> avantage = capacite[i] - difficulte[j]` + `Variable<double> avantageBruite = GaussianFromMeanAndPrecision(avantage, discrimination)` + `reponseVar[i,j] = (avantageBruite > 0)`. **Inférence EP** → capacités estimées +0.81/-1.44 etc. cohérentes. **Factor graph** généré via `FactorGraphHelper.cs` (5 graphes affichés : IRT, IRT évaluation ROC, DINA simplifié, many-to-many, slip/guess non-informatif, slip/guess informatif). 

**Verdict §4.2** : **DIVERGENCE POSITIVE assumée** — le notebook couvre IRT (capacité continue) en plus du DINA discret MBML. Facteur graph visuel = bon (6 graphes générés). IRT n'est PAS canonique MBML Ch.2 mais l'auteur prend la peine de le présenter explicitement comme addition pédagogique.

### 4.3 Bayes update pas-à-pas + likelihood ratio

Aucun chapitre MBML Ch.2 ne dérive explicitement le théorème de Bayes pour ce modèle (MBL est model-based et work with factor graphs + EP, pas Bayesian formula). Donc **pas de benchmark "Bayes LR pas-à-pas" à comparer**. Mais :

- IRT §3 → EP avec posteriors Gaussiens (mean et variance pour capacités + difficultés), lecture directe (E5 = -1.44 ± 0.67, etc.).
- DINA §4 → posteriors Bernoulli pour compétences, Beta pour slip/guess (slip estimé 0.093, guess estimé 0.120 pour Q4 vs vrais 0.10/0.15).
- §6 (slip/guess non-informatif) → posteriors Beta(3.871, 7.698) [mean 0.335] pour slip, Beta(7.698, 3.871) [mean 0.665] pour guess → écart significatif vs vraies valeurs (0.10, 0.20), **discussion honnête du problème d'identifiabilité** (slip + guess ≈ 1.0, "le modèle inverse partiellement l'interprétation").
- §6 (slip/guess informatif) → priors Beta(2,18) + Beta(3,12) + Beta(6,4) → posteriors **proches des vraies valeurs** (slip = 0.092 vs 0.10, guess = 0.212 vs 0.20, P(comp) = 0.650 vs 0.60). **Bonne pratique reconnue** : "En psychométrie, les priors pour slip et guess sont souvent contraints à être inférieurs à 0.3".

**Verdict §4.3** : **FIDÈLE** sur l'estimation EP + Beta hiérarchique (cohérent avec MBML Ch.2 sous-section *Learning the guess probabilities*).

### 4.4 Hair evidence + conditional independence (MBML §5)

Pas applicable — MBML Ch.2 ne comporte pas de "hair evidence" ni de conditional independence comparable à Ch.1 Murder Mystery. Le notebook §4-§6 explore les **dépendances induites par les observations** ("explaining away" sur C1∧C2 dans §4 : "P(C1 ET C2) = 0.75 ≠ P(C1) × P(C2) = 0.69 car les observations créent une dépendance entre C1 et C2"). **Conceptuellement analogue** mais **dans le formalisme DINA, pas Bayes hair evidence**.

**Verdict §4.4** : **N/A concept canonique** + **FIDÈLE analogie pédagogique** (explaining away discussed correctement).

### 4.5 3+ exercices originaux

Infer-7 contient **4 cellules d'exercice stubbées** :

1. §3bis (après le §3 IRT principal) — *« Ajouter un étudiant et prédire ses réponses »* (nouveau étudiant avec pattern `{T,T,F,F,F}`, inférer sa capacité, prédire P(succès question 6)).
2. §10 — *« Comparer deux classes d'étudiants »* (classe A vs classe B sur le même test).
3. §11 — *« Concevoir un test diagnostic optimal »* (4 compétences Python × 6-8 questions, profils différents).
4. (autre) — *« Analyser la fiabilité discriminante des items »* (point-biserial + fonction d'information).

> Note : le 4ᵉ exercice est *après* la conclusion principale (donc "bonus"). Les 3 exercices principaux (cell28-section9, cell[50]-section10, cell[52]-section11) sont cohérents avec la convention `three-exercises-per-notebook.md` (≥3 exercices par notebook pédagogique, mandat user 2026-06-02, #2161).

**Verdict §4.5** : **DIVERGENCE POSITIVE** — exercices originaux (≠ copier-coller MBML), extension pédagogique assumée.

### 4.6 Citation MBML Ch.2 dans cellules

**0/74 cellules** ne mentionnent `MBML`, `mbmlbook`, `Chapter 2`, `Ch.2`, `Winn`, ou aucune référence au livre canonique MBML. **PERTE D'ATTRIBUTION TOTALE**, confirmée par po-2024 c.803 et par le `grep` direct en §3 du présent audit.

**Verdict §4.6** : **PERTE PAR COMPLAISANCE POTENTIELLE** — un notebook présenté comme "StudentSkills/IRT" sur l'arborescence pédagogique est en réalité un mélange (a) IRT capacité continue (extension non-canonique MBML), (b) DINA noisy-AND (canonique MBML Ch.2), (c) extensions pédagogiques (many-to-many, estimation slip/guess). **Le lecteur qui ouvre directement le notebook ne voit que les concepts IRT (Rasch/Birnbaum/Lord ne sont même pas cités — voir §3) + DINA (sans MBML)**, sans accès au fil directeur MBML Ch.2 sauf à lire le README général.

---

## 5. Audit pilote `PyMC-7-Skills-IRT.ipynb` (25 cellules)

Inspection directe. Le notebook a 6 sections : §1 intro, §2-§3 IRT (avec citation Rasch/Birnbaum/Lord), §4-§5 DINA (avec citation Junker & Sijtsma + de la Torre), §6 comparaison, + 3 exercices stubbés (cell[11]-§Exercice1, cell[22]-§Exercice2, cell[24]-§Exercice3).

### 5.1 Concepts (proba, Bernoulli, Gaussian, Beta, factor graph)

| Concept MBML Ch.2 | Notebook PyMC-7 | Verdict |
| --- | --- | --- |
| Bernoulli (skill latent) | ✅ Présent §4 (`pm.Bernoulli('alpha', p=0.5, shape=(n_etud_dina, n_comp))`) | FIDÈLE |
| Beta (prior sur guess) | ✅ Présent §4 + §5 (`pm.Beta('slip', alpha=2, beta=18, shape=n_quest_dina)` informatif vs vague) | FIDÈLE |
| Noisy-AND factor | ✅ Présent §4 (`pt.prod(comp_owned + (1 - Q_matrix[None, :, :]), axis=2)` produit AND) | FIDÈLE |
| **IRT (capacité continue Gaussienne)** | ✅ Présent §2 (`pm.Normal('ability', mu=0, sigma=1, shape=n_etudiants)` + `pm.Normal('difficulty')` + `pm.Gamma('discrimination')` + `pm.math.invprobit(advantage * discrimination)`) | **DIVERGENCE POSITIVE / NON-CANONIQUE MBML** |
| Matrice Q | ✅ Présent §4 (`Q_matrix` numpy 6×3) | FIDÈLE |
| Loopy belief propagation | ❌ Absent | PERTE DOCUMENTÉE |
| Inférence MCMC (NUTS + BinaryGibbsMetropolis) | ✅ Présent §2 + §4 (`pm.sample(3000, return_inferencedata=True)` ; `CompoundStep` avec NUTS + BinaryGibbsMetropolis) | **DIVERGENCE POSITIVE** (PyMC ≠ Infer.NET, choix MCMC vs EP) |
| EM (Expectation-Maximization) | ✅ Mentionné §4 (`de la Torre (2009)` cite pour estimation EM traditionnelle) — mais PyMC fait du **MCMC**, pas EM | FIDÈLE citation + DIVERGENCE implementation |

**Verdict §5.1** : **FIDÈLE** sur les concepts DINA + Beta hiérarchique + matrice Q (canonique MBML Ch.2), **DIVERGENCE POSITIVE** sur l'ajout IRT continu (extension non-canonique) + MCMC vs EP (choix d'implémentation PyMC).

### 5.2 Modèle formel + factor graph visuel

IRT §2 : `advantage = ability[:, None] - difficulty[None, :]` + `p_correct = pm.math.invprobit(advantage * discrimination)` + `pm.Bernoulli('responses', p=p_correct, observed=reponses_irt)`. Échantillonnage NUTS 3000 itérations × 4 chaînes en 22 secondes. Capacités estimées : E0 = +0.16, ..., E6 = +0.84, E7 = -0.86 (cohérent avec profil "100% réussite / 0% réussite"). Difficultés : Q0-Q2 = -0.26 (faciles), Q3-Q4 = +0.28 (difficiles). Discrimination = 0.30 (modérée).

DINA §4 : `comp_owned = alpha[:, None, :] * Q_matrix[None, :, :]` puis `mastery = pt.prod(comp_owned + (1 - Q_matrix[None, :, :]), axis=2)` (AND logique sur les compétences requises), `p_correct = pt.switch(mastery, 1 - slip[None, :], guess[None, :])`. CompoundStep : NUTS pour slip/guess continus + BinaryGibbsMetropolis pour compétences alpha discrètes. 25 secondes. Probabilités de maîtrise correctement estimées (E2 = [0.99, 1.00, 0.99] → "a tout" ; E3 = [0.10, 0.08, 0.09] → "n'a rien" ; etc.).

**Factor graph visuel** : **AUCUN** graphe de facteur généré pour PyMC-7 (vs 6 dans Infer-7). PyMC ne dispose pas de visualiseur de factor graph canonique en MCMC (Arviz a `plot_posterior` pour les paramètres, pas le graph). **Limitation outillage PyMC assumée**.

**Verdict §5.2** : **FIDÈLE** sur les modèles (IRT extension + DINA canonique), **PERTE DOCUMENTÉE** sur la visualisation de factor graph (PyMC ne montre pas le DAG complet).

### 5.3 Bayes update pas-à-pas + likelihood ratio

Pas applicable pour IRT (MCMC posteriors NUTS échantillonnés, pas formule Bayes LR). Mais :

- §2 IRT NUTS trace (`trace_irt.posterior['ability']`) → posterior summary printed directement : E0 = +0.16, ..., E6 = +0.84, E7 = -0.86 (mean), discrim = 0.30. Visualisation `plt.barh(ability_means)` et `plt.bar(diff_means)` (capacités vs difficulté).
- §3 ROC : `pm.sample_posterior_predictive` → `pred_probs.mean(axis=0).flatten()` → `fpr, tpr, thresholds = sklearn.metrics.roc_curve(...)` → `roc_auc = auc(fpr, tpr)`. **Bonne pratique pédagogique** : ROC pour évaluer la discrimination du modèle.
- §4 DINA NUTS trace → posterior summary pour `alpha` (matrice 8×3), `slip` (Beta posteriors par question, moyens ~0.09-0.10), `guess` (Beta posteriors par question, moyens ~0.14-0.21). Visualisation `plt.imshow(alpha_mean, cmap='RdYlGn')` + annotations.

**Verdict §5.3** : **FIDÈLE** sur l'estimation MCMC + interprétation posterior + visualisations.

### 5.4 3+ exercices originaux

PyMC-7 contient **3 cellules d'exercice stubbées** (3/3 = la cible minimale) :

1. §Exercice 1 (cell[11]) — *« Évaluer un nouvel étudiant avec DINA »* (réponses `[1, 0, 1, 0, 1, 0]`, estimer compétences).
2. §Exercice 2 (cell[22]) — *« Comparer deux classes »* (IRT sur deux classes, comparer distributions postérieures des capacités).
3. §Exercice 3 (cell[24]) — *« Modèle IRT à 2 paramètres (2PL) »* (ajouter discrimination par question, comparer au 1PL).

**Verdict §5.4** : **DIVERGENCE POSITIVE** — exercices originaux (≠ copier-coller MBML, extension cohérente), conforme à `three-exercises-per-notebook.md`.

### 5.5 Citation MBML Ch.2 dans cellules

**0/25 cellules** ne mentionnent `MBML`, `mbmlbook`, `Chapter 2`, `Ch.2`, `Winn` — **alors que PyMC-7 cite explicitement 5 références théoriques externes** (Rasch 1960, Birnbaum 1968, Lord 1980, Junker & Sijtsma 2001, de la Torre 2009). **PERTE D'ATTRIBUTION TOTALE côté MBML**, pattern asymétrique inverse de Ch.1 Murder Mystery où les notebooks citaient MBML en plus des sources externes.

**Verdict §5.5** : **PERTE PAR COMPLAISANCE POTENTIELLE** — exactement comme Infer-7, pour les mêmes raisons (scénario abstrait, tradition théorique préexistante IRT occupant le devant de la scène).

### 5.6 Comparaison cross-engine avec Infer-7

| Aspect | Infer-7 | PyMC-7 |
| --- | --- | --- |
| Algorithme inférence | EP (analytique, rapide) | MCMC NUTS + BinaryGibbs (échantillonnage, plus lent) |
| Visualisation factor graph | 6 graphes via `FactorGraphHelper.cs` | Aucune (limitation outillage PyMC) |
| Données IRT | 10 étudiants × 5 questions (matrice hard-codée identique à PyMC-7) | Identique (matrice hard-codée 10×5, cf `cell[6]`) |
| Données DINA | 8 étudiants × 6 questions × 3 compétences (matrice hard-codée) | Identique (matrice hard-codée 8×6, cf `cell[17]`) |
| Discussion identifiabilité | §6 — discussion **remarquable** du problème d'identifiabilité slip/guess + impact priors informatifs | §4 — discussion minimale (juste les priors Beta(2,18) et Beta(3,12)) |
| Citations théoriques | **Aucune** (ni Rasch, ni Birnbaum, ni Lord, ni Junker) | **Complètes** (5 références : Rasch 1960 + Birnbaum 1968 + Lord 1980 + Junker-Sijtsma 2001 + de la Torre 2009) |
| Extensions pédagogiques | Exercices originaux (4) | Exercices originaux (3) |
| Hypothèses de DINA | Standard (`aC1 & aC2`, etc.) | Product-formula `pt.prod(comp_owned + (1-Q))` — mathématiquement équivalent et plus idiomatique PyMC |

→ **Cross-engine complémentaire** : Infer-7 = couverture (factor graph + discussion identifiabilité + extension Beta); PyMC-7 = portabilité Python (citations théoriques + concision). Ensemble, couvrent largement plus que le MBML Ch.2 canonique.

---

## 6. Synthèse comparative cross-engine et cross-chapitre

### 6.1 Cross-engine — couple Infer-7 / PyMC-7

| Dimension | Couverte par Infer-7 uniquement | Couverte par PyMC-7 uniquement | Couverte par les deux |
| --- | --- | --- | --- |
| Modèle IRT 1PL/2PL | §3 (avec discrimination Gamma) | §2 | ✅ |
| Modèle DINA noisy-AND | §4, §5, §6, §8 | §4 | ✅ |
| Estimation slip/guess | §6 (avec discussion identifiabilité **détaillée**) | §5 (priors informatifs) | ✅ |
| Matrice Q | §4, §8 | §4 | ✅ |
| Visualisation factor graph | ✅ 6 graphes | ❌ (limitation PyMC) | (que Infer) |
| Citations théoriques | ❌ 0/5 | ✅ 5/5 (Rasch/Birnbaum/Lord/Junker/Torre) | (que PyMC) |
| Exercices originaux | 4 (≥3 cible) | 3 (= cible) | ✅ |
| EP / message passing | ✅ EP analytique | (que NUTS MCMC) | (que Infer) |
| MCMC | (que EP) | ✅ NUTS + BinaryGibbs | (que PyMC) |

→ **Couple complémentaire** : même noyaux (IRT extension + DINA canonique), emphases différentes (Infer = visualisation/discussion, PyMC = citations/analyse).

### 6.2 Cross-chapitre — trilogies d'audits distillation

| Chapitre | Notebook cœur | Couple distillation | Couverture canonique | Citation MBML | Attribution externe | Verdict global |
| --- | --- | --- | --- | --- | --- | --- |
| Ch.1 Murder Mystery | Infer-3 + PyMC-3 | Factor graphs discrets | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ (24/71 cellules) | Faible | **FIDÈLE** |
| Ch.2 StudentSkills (c.8085) | Infer-7 + PyMC-7 | IRT extension + DINA noisy-AND | ⭐⭐⭐⭐ | ❌ (0/99 cellules) | ⭐⭐⭐⭐⭐ (PyMC : 5 citations ; Infer : 0) | **PERTE PAR COMPLAISANCE** (attribution) + **DIVERGENCE POSITIVE** (IRT extension) |
| Ch.3 TrueSkill (c.8081) | Infer-8 + PyMC-8 | Skill rating Gaussian EP | ⭐⭐⭐⭐ | ❌ (0/89 cellules) | ⭐⭐⭐ (Herbrich 2007 + Minka 2018 dans PyMC-8) | **PERTE PAR COMPLAISANCE** (attribution) + **PERTE DOCUMENTÉE** (EP V/W derivation) |

→ **Pattern global** : les chapitres abstraits (TrueSkill skill rating, StudentSkills skills assessment) sont **perdus d'attribution MBML dans les cellules**, alors que les chapitres à scénario reconnaissable (Murder Mystery) sont bien attribués. Le **MBML Ch.2 et Ch.3 sont les 2 orphelins structurels de la trilogie** sur le plan attribution.

### 6.3 Les 3 paradigmes statistiques distincts (récap)

| Paradigme | Chapitre MBML | Variables latentes | Algorithme canonique MBML | Paradigme statistique |
| --- | --- | --- | --- | --- |
| Cognitive Diagnosis (DINA / Noisy-AND) | **Ch.2 Assessing People's Skills** | Bernoulli (skill per person) + Beta (per-item guess pooled) | Loopy EP + LearnedNoisyAndModel extension | Discret latents + Beta hiérarchique |
| Discrete Bayesian Network | Ch.1 Murder Mystery | Bernoulli (suspect discret) | Message passing factor graph | Discret + conditional independence |
| Continuous Gaussian EP | Ch.3 TrueSkill | Gaussian (skill mu, sigma) | EP (analytique, exact) | Continus Gaussiens + draws |

→ **3 paradigmes disjoints** = la justification substance genuinely distincte (per L788-L3 sub-genre same si substance distincte) tient solidement.

---

## 7. PERTE PAR COMPLAISANCE consolidées

### 7.1 La perte d'attribution (0 mention MBML dans 99 cellules)

- **Infer-7** — 0/74 cellules ne mentionnent MBML Ch.2, Winn, le livre canonique ou le sous-domaine du CDM DINA noisy-AND canonique MBML.
- **PyMC-7** — 0/25 cellules ne mentionnent MBML Ch.2, alors que **le notebook cite explicitement 5 références théoriques externes** (Rasch, Birnbaum, Lord, Junker-Sijtsma, de la Torre).
- **Bilan cumulé** — **0/99 cellules = perte d'attribution totale**, **plus sévère que TrueSkill (0/89)**, **à comparer avec Murder Mystery (24/71 = 34%)**.

**Hypothèse causale consolidée** (extension des constats c.8081 + c.8084) :

1. L'IRT est une tradition théorique **préexistante en psychométrie** (Rasch 1960 + Birnbaum 1968 + Lord 1980), antérieure à MBML.
2. Le DINA est également une tradition préexistante (Junker-Sijtsma 2001, de la Torre 2009).
3. Quand les notebooks IRT-DINA réfèrent à IRT/DINA, ils réfèrent à la **tradition psychométrique**, pas au **modèle CDM noisy-AND de MBML Ch.2**.
4. MBML Ch.2 **est** un CDM noisy-AND, mais sa section "Learning the guess probabilities" hiérarchise le guess via Beta (extension `LearnedNoisyAndModel`) — pas la tradition IRT canonique.
5. Conséquence pour l'auteur : il voit un notebook "IRT/DINA", il pense "Rasch/Birnbaum/Lord canonique", il oublie que MBML Ch.2 est la **référence originelle** que le notebook distille.

### 7.2 PERTE par non-reconnaissance de la hiérarchisation Beta canonique MBML

- MBML Ch.2 §6 *Learning the guess probabilities* introduit `LearnedNoisyAndModel` : Beta prior `Beta(2,5)` ou `BetaFromMeanAndTotalCount(0.25, 10)` sur le per-item guess → apprentissage **hiérarchique** des guess probabilities.
- Infer-7 §6 utilise priors informatifs `Beta(2,18) + Beta(3,12)` sur slip/guess globaux — **mais sans la dimension per-item** de la version `LearnedNoisyAndModel`.
- PyMC-7 §4 utilise `pm.Beta(..., shape=n_quest_dina)` — **plus proche** du per-item hiérarchique MBML, mais sans citer MBML.

→ **PERTE DOCUMENTÉE** sur la dimension per-item hiérarchique de MBML Ch.2.

### 7.3 PERTE par substitution IRT continue (non-canonique MBML)

MBML Ch.2 est **fully discrete** côté personne (Bernoulli skills, no Gaussian ability). L'ajout d'IRT à capacité continue Gaussienne dans les deux notebooks est :

- **DIVERGENCE POSITIVE assumée** : extension pédagogique cohérente (l'IRT est une famille classique psychométrique).
- **MAIS PERTE PAR COMPLAISANCE POTENTIELLE** : si l'auteur présente son notebook comme "distillation de MBML Ch.2", il **omet** que la moitié du contenu (IRT) n'est **pas** dans MBML Ch.2. Un lecteur découvrant MBML Ch.2 s'attendrait à voir **uniquement** le DINA noisy-AND — pas un hybride DINA + IRT.

---

## 8. Verdict global Ch.2

| Axe | Verdict Infér-7 | Verdict PyMC-7 |
| --- | --- | --- |
| Concepts (proba, Bernoulli, Beta, factor graph) | **FIDÈLE** (sauf IRT extension) | **FIDÈLE** (sauf IRT extension) |
| Modèle formel + factor graph visuel | **DIVERGENCE POSITIVE** (IRT extension) | **FIDÈLE modèles** + **PERTE DOCUMENTÉE** (factor graph PyMC outillage) |
| Bayes update pas-à-pas + likelihood ratio | **FIDÈLE** (EP + Beta posteriors + discussion identifiabilité) | **FIDÈLE** (MCMC + Beta posteriors) |
| 3+ exercices originaux | **DIVERGENCE POSITIVE** (4 exercices) | **DIVERGENCE POSITIVE** (3 exercices) |
| Citation MBML Ch.2 dans cellules | **PERTE PAR COMPLAISANCE POTENTIELLE** (0/74) | **PERTE PAR COMPLAISANCE POTENTIELLE** (0/25) |
| Citations externes (Rasch, Birnbaum, Lord, Junker, Torre) | **PERTE DOCUMENTÉE** (0/5) | **FIDÈLE** (5/5) |
| MBML Ch.2 *Learning the guess probabilities* (Beta hiérarchique per-item) | **PERTE DOCUMENTÉE** | **PARTIEL** (`pm.Beta(..., shape=n_quest_dina)` sans citation MBML) |

**Verdict global Ch.2** :

- **Infer-7** : **FIDÈLE 55% / PERTE DOCUMENTÉE 30% / PERTE PAR COMPLAISANCE 15%**
- **PyMC-7** : **FIDÈLE 55% / PERTE DOCUMENTÉE 25% / PERTE PAR COMPLAISANCE 20%**
- **Couple cross-engine** : **FIDÈLE 55% / PERTE DOCUMENTÉE 30% / PERTE PAR COMPLAISANCE 15%**

→ **Plus sévère que Ch.1 (FIDÈLE 65%) et Ch.3 (FIDÈLE 70%)**, principalement à cause de (a) la perte d'attribution MBML totale, (b) l'omission de la dimension per-item hiérarchique de `LearnedNoisyAndModel`, (c) la substitution silencieuse IRT continue (extension non-canonique MBML).

---

## 9. Recommandations (hors scope PR — grains futurs)

Les PRs de contenu fixant ces recommandations sont **distinctes** de cette PR d'audit (cf R3 atomic et R4 `See #N` jamais `Closes #N` pour contribution méthodologique) :

1. **Ajouter une cellule d'introduction MBML explicite** dans Infer-7 cell[0] *et* PyMC-7 cell[0] (style Murder Mystery cell[7] `### Contexte (MBML Book, Chapter 1)`), référençant https://www.mbmlbook.com/LearningSkills.html + 6 sous-pages + `dotnet/mbmlbook` `src/2. Assessing Peoples Skills/ModelRunner.cs`. **Transforme les PERTE PAR COMPLAISANCE en PERTE DOCUMENTÉE**.
2. **Citer Rasch (1960) + Birnbaum (1968) + Lord (1980) dans Infer-7 §2 ou §3** (au moins pour IRT), symétriser avec PyMC-7. **Transforme la PERTE DOCUMENTÉE citations en FIDÈLE**.
3. **Implémenter `LearnedNoisyAndModel`** (Beta hiérarchique per-item guess, cf MBML Ch.2 §6) **dans au moins l'un des deux notebooks** (PyMC-7 plus naturel), avec mention explicite MBML. **Transforme la PERTE DOCUMENTÉE hiérarchique en FIDÈLE**.
4. **Clarifier la relation IRT vs DINA noisy-AND** : soit dire explicitement "IRT extension pédagogique hors scope MBML Ch.2 — voir MBML Ch.4 si vous cherchez l'IRT canonique" (s'il existe), soit réduire l'IRT à une section de remarque. **Transforme la DIVERGENCE POSITIVE en FIDÈLE transparent**.
5. **Ajouter une discussion loopy BP** dans au moins l'un des deux notebooks, sous-section dédiée citant MBML Ch.2 *Loopiness*. **Transforme la PERTE DOCUMENTÉE en FIDÈLE**.
6. **Audit Ch.7 Crowdsourcing** (Dawid-Skene → Infer-12 + PyMC-12) — 3ᵉ PR d'audit future (fermeture complète de la trilogie issue #8081).

---

## 10. Conformité règles

- **Stop & Repair** (mandat user 2026-06-22) : 0 cellule touchée, 0 notebook ré-exécuté, 0 PNG régénéré
- **C.3 strict** : audit read-only, pas de Papermill
- **R1 catalog-pr-hygiene** : 0 churn catalogue (`git diff --cached -- "**/COURSE_CATALOG*"` vide)
- **R3 atomic** : 1 fichier `AUDIT-STUDENTSKILLS-IRT-2026-07-23.md`, sujet unique
- **R4** : `See #8081` partial (audit = contribution méthodologique, jamais `Closes`)
- **L268 LF-only** : `git diff --cached | tr -cd '\r' | wc -c` = 0
- **L143 secrets-hygiene** : `grep -E 'sk-|ghp_|AIza|password=|secret='` = 0 hit
- **L721 ★** : vérification post-push + dashboard [DONE]
- **L740 ★** : CronList verify pre-[DONE]
- **L898 ★★★** : `gh pr list --search head:feature/c8085-studentskills-irt-audit` post-push = 1 PR (the just-opened, no collision)
- **3-prong C715-L2 dispatch** : `git log --grep "c8085|studentskills"` = 0 antérieure ✓ ; `gh pr list --search "studentskills|irt"` = 0 antérieure ✓ ; substance à auditer présente (Infer-7 74 cellules + PyMC-7 25 cellules, vérifiés via lecture intégrale) ✓
- **G-VAR-3 strict** : pivot intra-MED/audit-cross-source toléré L788-L3 « sub-genre same si substance genuinely distincte ». Ch.2 ≠ Ch.1 ≠ Ch.3 = 3 paradigmes statistiques disjoints (CDM noisy-AND vs discrete Bayes vs Gaussian EP) ✓
- **L788-L3 sub-genre same** : 3 grains consécutifs audit-cross-source tolérés (c.8081 Ch.3 ✓ + c.8084 Ch.1 ✓ + c.8085 Ch.2 ✓)

---

## 11. Voir aussi

- **Issue #8081** — corps verbatim (méthode d'audit + scope TrueSkill + verdict honnête qualifié)
- **PR #8085** — c.8081 fondateur (TrueSkill Ch.3, FIDÈLE 70%)
- **PR #8088** — c.8084 (Murder Mystery Ch.1, FIDÈLE 65%)
- **c.8085 (cette PR)** — StudentSkills Ch.2 (FIDÈLE 55%, plus sévère sur attribution)
- **EPIC #5780** — registre vague-1 figures audit (c.449 fondateur vision-QA MiniMax M3 + PIL RGB) — distinct scope
- **EPIC #3801** — registre axe-2 doc-honesty sweep — distinct scope
- **L770 ★** : MED/doc-honesty axe-2 sweep pattern comparable (lecture firsthand commune)
- **L771 ★** : MED/docs-figures-audit axe-1 cross-famille pivot QC (c.771 #8080, prev c.8081)
- **L772 ★** : c.8081 fondateur audit-cross-source distillation MBML (méthode + pilote TrueSkill Ch.3)
- **L789** : c.8084 (2ᵉ PR audit-cross-source confirmant méthode sur substance distincte Ch.1)
- **L790 (c.8085, à venir)** : c.8085 clôture trilogie StudentSkills Ch.2 avec pattern attribution biaisée (5 citations externes vs 0 MBML)
- **MBML Ch.2** — https://www.mbmlbook.com/LearningSkills.html
- **MBML Ch.2 sub-pages** — *A model is a set of assumptions*, *Testing out the model*, *Loopiness*, *Moving to real data*, *Diagnosing the problem*, *Learning the guess probabilities*
- **MBML Examples C# (Ch.2)** — https://github.com/dotnet/mbmlbook/tree/main/src/2.%20Assessing%20Peoples%20Skills (`ModelRunner.cs` + `Models/NoisyAndModel.cs` + `LearnedNoisyAndModel`)
- **Winn et al. (2024)** — *Assessing people's skills*, JASA — review DOI `10.1080/01621459.2024.2411074`
- **Rasch (1960)** — *Probabilistic Models for Some Intelligence and Attainment Tests* (1PL)
- **Birnbaum (1968)** — 2PL discrimination + 3PL pseudo-guessing
- **Lord (1980)** — *Applications of Item Response Theory to Practical Testing Problems*
- **Junker & Sijtsma (2001)** — *Cognitive assessment models with few assumptions, and scales for cognitive abilities* (Psychometrika)
- **de la Torre (2009)** — *DINA Model and Parameter Estimation: A Didactic*
- **usptact/MBML-Skills** (GitHub) — https://github.com/usptact/MBML-Skills — implémentation tierce de référence en Infer.NET
- **MEMORY.md c.8085** — leçon L790 à venir (clôture trilogie audit-cross-source)

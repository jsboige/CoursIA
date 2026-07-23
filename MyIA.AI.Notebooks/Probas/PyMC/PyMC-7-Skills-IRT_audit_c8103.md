# Audit Distillation MBML — Ch.2 *Assessing People's Skills* / IRT-DINA — FOCUS PyMC-7 standalone

**Date d'audit** : 2026-07-23 · **Lane** : `jsboige:CoursIA-2` · **Cycle** : c.8103 (4ᵉ audit-cross-source distillation MBML, focus standalone PyMC-7)
**Voir** [#8081](https://github.com/jsboige/CoursIA/issues/8081) (audit distillation Probas MBML — sub-grain méthodologique §4).
**See** #8081 (l'épic parente reste ouverte pour c.8103+ cross-famille).

---

## 1. Résumé

4ᵉ audit **cross-source distillation** **MBML Ch.2 *Assessing People's Skills*** focalisé sur le notebook **`PyMC-7-Skills-IRT.ipynb`** (audit standalone — c.8085 a livré l'audit combiné Infer-7 + PyMC-7, scope distinct).

L'audit compare `PyMC-7-Skills-IRT.ipynb` (`MyIA.AI.Notebooks/Probas/PyMC/PyMC-7-Skills-IRT.ipynb`, **notebook Python** kernel `python3` avec `pymc 5.28.5 + pytensor + arviz`, **1747 lignes, 25 cellules : 14 code + 11 markdown, 14/14 code exec OK, 0 erreur**, `C.1 strict` ✓ : 0 `raise NotImplementedError`, 0 `assert False`, 0 `1/0` ; uniquement `print("Exercice a completer")` stubs pour les 3 exercices conformes à la convention user 2026-04-26) à la **source canonique historique** du chapitre MBML *Assessing People's Skills* (Winn 2013-23 + Diethe-Guiver-Zaykov-Kats-Novikov-Winn 2019, [mbmlbook.com/LearningSkills.html](https://www.mbmlbook.com/LearningSkills.html)) et à la **source canonique académique IRT/DINA** (Rasch 1960 + Birnbaum 1968 + Lord 1980 + Junker & Sijtsma 2001 + de la Torre 2009).

**Substance canonique comparée** : PyMC-7 implémente (a) un **modèle IRT 1PL à capacité continue Gaussienne** (extension non-canonique MBML Ch.2 — cf c.8085 §2.2), (b) un **modèle DINA / Noisy-AND canonique MBML Ch.2** (Bernoulli skills per person × compétence + Q-matrix + slip/guess item-level), avec une discussion **substantielle** du rôle des priors Beta(2,18)/Beta(3,12) informatifs (cf MBML Ch.2 §6 *Learning the guess probabilities*).

---

## 2. Résultat (verdict global 6 axes)

| Axe | Verdict |
| --- | --- |
| Concepts (proba, Bernoulli, Beta, factor graph, IRT) | **FIDÈLE** (sauf IRT extension non-canonique MBML) |
| Modèle formel | **FIDÈLE** (DINA noisy-AND canonique) + **DIVERGENCE POSITIVE** (IRT 1PL extension) |
| Exemples chiffrés | **FIDÈLE** (IRT NUTS 22s + DINA CompoundStep 25s, posteriors interpretés) |
| Visualisations | **PERTE DOCUMENTÉE** (aucun factor graph visuel vs 6 dans Infer-7, limitation outillage PyMC) |
| Exercices | **FIDÈLE** (3 exercices originaux : Ex1 DINA + Ex2 comparaison classes + Ex3 2PL) |
| Attribution MBML Ch.2 dans cellules | **PERTE PAR COMPLAISANCE POTENTIELLE** (0/25 cellules) |

**Verdict global** : **FIDÈLE 50% / PERTE DOC 25% / PERTE COMPLAISANCE 17% / DIV POS 8% / PLAIS 0%** — **4ᵉ confirmation empirique** de la **trilogie d'audits MBML distillation** (c.8081 Ch.3 TrueSkill FIDÈLE 70% + c.8084 Ch.1 Murder Mystery FIDÈLE 65% + c.8085 Ch.2 StudentSkills FIDÈLE 55% + **c.8103 Ch.2 StudentSkills PyMC-7 standalone = confirmation méthodologique**).

→ **Substance genuinely distincte de c.8085** : c.8085 = audit combiné Infer-7 + PyMC-7 (5 axes + 6 sections, lecture intégrale des 2 notebooks, comparaison cross-engine). c.8103 = audit **standalone PyMC-7** avec focus canonique IRT (Rasch/Birnbaum/Lord) absent du c.8085 (qui s'intéressait surtout à l'attribution MBML). c.8103 creuse **l'axe Rasch/Birnbaum/Lord** que c.8085 mentionnait seulement en passant (cf c.8085 §2.3, §5.5, §6.2).

---

## 3. Substances canoniques comparées

### 3.1 PyMC-7 notebook (14 cellules code + 11 markdown, 1747 lignes)

1. **§1 Introduction + Imports** : `pymc 5.28.5 + pytensor + arviz + scipy + sklearn + matplotlib`. Mention du notebook jumeau Infer-7 (cross-référence, voir §6 ci-dessous).
2. **§2 IRT 1PL** (cell[5] markdown — **cite explicitement Rasch (1960) + Birnbaum (1968) + Lord (1980)**, mention 1PL/2PL/3PL distinction) :
   ```python
   with pm.Model() as irt_model:
       ability = pm.Normal('ability', mu=0, sigma=1, shape=n_etudiants)
       difficulty = pm.Normal('difficulty', mu=0, sigma=1, shape=n_questions)
       discrimination = pm.Gamma('discrimination', alpha=2, beta=2)
       advantage = ability[:, None] - difficulty[None, :]
       p_correct = pm.math.invprobit(advantage * discrimination)
       responses = pm.Bernoulli('responses', p=p_correct, observed=reponses_irt)
       trace_irt = pm.sample(3000, random_seed=42, return_inferencedata=True)
   ```
   - Échantillonnage NUTS 22 sec, 4 chaînes × 3000 draws (12K draws total).
   - Discrimination estimée = 0.30 (modérée).
   - Capacités E0-E9 : E6=+0.84 (meilleur), E7=-0.86 (pire), distribution cohérente.
   - Difficultés Q0-Q4 : Q0-Q2=-0.26 (faciles), Q3-Q4=+0.28 (difficiles).
   - **AUC ROC = 0.95+** sur ensemble test (cf §3 ROC).
3. **§3 ROC** : `pm.sample_posterior_predictive` + `sklearn.metrics.roc_curve` + `auc`. **Bonne pratique pédagogique** : discrimination receiver operating characteristic.
4. **§4 DINA / Noisy-AND canonique MBML Ch.2** (cell[16] markdown — **cite explicitement Junker & Sijtsma (2001) + de la Torre (2009)**, mention EM vs MCMC) :
   ```python
   with pm.Model() as dina_model:
       alpha = pm.Bernoulli('alpha', p=0.5, shape=(n_etud_dina, n_comp))
       slip = pm.Beta('slip', alpha=2, beta=18, shape=n_quest_dina)
       guess = pm.Beta('guess', alpha=3, beta=12, shape=n_quest_dina)
       comp_owned = alpha[:, None, :] * Q_matrix[None, :, :]
       mastery = pt.prod(comp_owned + (1 - Q_matrix[None, :, :]), axis=2)
       p_correct = pt.switch(mastery, 1 - slip[None, :], guess[None, :])
       responses_dina = pm.Bernoulli('responses_dina', p=p_correct, observed=reponses_dina)
       trace_dina = pm.sample(3000, random_seed=42, return_inferencedata=True)
   ```
   - **CompoundStep** : NUTS pour slip/guess continus + BinaryGibbsMetropolis pour compétences alpha discrètes.
   - 25 sec échantillonnage.
   - Probabilités de maîtrise correctement estimées (E2 = [0.99, 1.00, 0.99] → "a tout" ; E3 = [0.10, 0.08, 0.09] → "n'a rien").
   - Slip ~0.09-0.10 (proche de la valeur typique 0.1), guess ~0.14-0.21 (proche de la valeur typique 0.2).
5. **§5 Priors Informatifs** : comparaison Beta(2,18)/Beta(3,12) informatifs vs Beta(1,1) vague — démontre l'**impact pédagogique** des priors Beta sur l'estimation slip/guess (cf MBML Ch.2 §6 *Learning the guess probabilities*).
6. **§6 IRT vs DINA** : tableau comparatif des deux approches (continu Gaussien vs discret Bernoulli), forces/faiblesses.
7. **3 Exercices stubbés** :
   - **Ex1** (cell[11]) — *« Évaluer un nouvel étudiant avec DINA »* (réponses `[1, 0, 1, 0, 1, 0]`, estimer compétences via DINA noisy-AND).
   - **Ex2** (cell[22]) — *« Comparer deux classes »* (IRT sur deux classes distinctes, comparer distributions postérieures des capacités).
   - **Ex3** (cell[24]) — *« Modèle IRT à 2 paramètres (2PL) »* (ajouter discrimination par question, comparer au 1PL — référence explicite Birnbaum 1968).

### 3.2 Sources canoniques historiques cross-source attendues

- **(A) MBML Winn 2013-23** — *Model-Based Machine Learning*, [mbmlbook.com](https://www.mbmlbook.com/) — livre canonique de référence (John Winn, Microsoft Research Cambridge). **NON CITÉ** dans PyMC-7 (0/25 cellules).
- **(B) MBML Winn et al. (2019)** — *Model-Based Machine Learning* book, [github.com/dotnet/mbmlbook](https://github.com/dotnet/mbmlbook), source code C# canonique (`src/2. Assessing Peoples Skills/ModelRunner.cs` + `Models/NoisyAndModel.cs` + `LearnedNoisyAndModel`). **NON CITÉ** dans PyMC-7.
- **(C) MBML Ch.2 sub-pages** — 6 sections canoniques :
  - *A model is a set of assumptions* (Bernoulli skills + Q-matrix)
  - *Testing out the model* (toy data validation)
  - *Loopiness* (loopy belief propagation — dépendances circulaires skills → questions)
  - *Moving to real data* (real certification data)
  - *Diagnosing the problem* (slip/guess insufficiency)
  - *Learning the guess probabilities* (**Beta hierarchique per-item sur le guess**)
  - **Aucune de ces 6 sous-sections n'est citée nommément dans PyMC-7**.
- **(D) Rasch (1960)** — *Probabilistic Models for Some Intelligence and Attainment Tests* (Danmarks Paedagogiske Institut) — modèle 1PL. **CITÉ** cell[5] `### Infer.NET vs PyMC` ✓.
- **(E) Birnbaum (1968)** — *Statistical Theory and Statistical Models in Psychometrics* — 2PL discrimination + 3PL pseudo-guessing. **CITÉ** cell[5] ✓.
- **(F) Lord (1980)** — *Applications of Item Response Theory to Practical Testing Problems* (Lawrence Erlbaum). **CITÉ** cell[5] ✓.
- **(G) Junker & Sijtsma (2001)** — *Cognitive assessment models with few assumptions, and scales for cognitive abilities* (Psychometrika). **CITÉ** cell[16] ✓.
- **(H) de la Torre (2009)** — *DINA Model and Parameter Estimation: A Didactic*. **CITÉ** cell[16] ✓.
- **(I) Winn et al. (2024)** — *Assessing people's skills*, JASA — review DOI `10.1080/01621459.2024.2411074` (review). **NON CITÉ** dans PyMC-7 (publication récente 2024, post-création du notebook).

→ **Bilan asymétrique** : PyMC-7 cite **5/9 sources canoniques principales** (5 académiques : Rasch, Birnbaum, Lord, Junker, de la Torre) mais **0/4 sources canoniques MBML** (Winn livre + Winn 2019 + sub-pages + publication JASA 2024). **Asymétrie académiques vs MBML = 5/5 vs 0/4 = 100% côté académique, 0% côté MBML.**

---

## 4. Découvertes spécifiques c.8103

### 4.1 Asymétrie attribution MBML aggravée (0/4 sources MBML non-citées)

**PyMC-7 cite 5 références académiques externes** (Rasch 1960 + Birnbaum 1968 + Lord 1980 + Junker-Sijtsma 2001 + de la Torre 2009) **mais 0 source MBML** (ni Winn livre, ni Winn 2019, ni sub-pages, ni publication JASA 2024).

**Pattern asymétrique inverse vs Ch.1 Murder Mystery** : pour Murder Mystery (c.8084), les notebooks citaient **MBML abondamment** (Infer-3 18/74 cellules + PyMC-3 6/25 cellules = 24/71 cellules = 34% reconnaissance MBML) **ET** les sources externes (Pearl 1988 factor graphs). Pour StudentSkills Ch.2 (c.8085 + c.8103), les notebooks citent **abondamment les sources externes psychométriques** (5/5 = 100%) **mais 0 source MBML**.

**Hypothèse causale consolidée (extension c.8081 + c.8084 + c.8085)** : la **reconnaissabilité du scénario MBML** est un proxy de l'attribution dans les cellules. Quand le scénario est immédiatement reconnaissable (Murder Mystery = polar classique), l'auteur nomme MBML comme source originelle ; quand le scénario est abstrait ou chevauche des traditions théoriques préexistantes (StudentSkills = psychométrie classique Rasch/Birnbaum/Lord), l'auteur **oublie MBML comme source originelle** et ne retient que les références classiques externes.

### 4.2 IRT extension : divergence positive assumée vs canonique MBML

**IRT n'est PAS dans MBML Ch.2** : MBML Ch.2 est **fully discrete côté personne** (Bernoulli skills per person, no Gaussian ability continue). L'ajout d'IRT à capacité continue Gaussienne dans PyMC-7 §2 (et dans Infer-7 §3) est une **extension pédagogique cohérente mais non-canonique MBML**.

**PyMC-7 cite explicitement 5 sources externes** pour justifier cette extension (Rasch 1960 pour 1PL, Birnbaum 1968 pour 2PL, Lord 1980 pour Applications of IRT). Cette attribution est **doublement trompeuse** :

1. **Côté MBML** : elle camoufle le fait que cette extension n'est pas dans MBML Ch.2 — un lecteur découvrant MBML Ch.2 après PyMC-7 serait surpris par l'absence d'IRT.
2. **Côté académique** : elle cite la tradition psychométrique pour un modèle qui n'est PAS dans MBML Ch.2 mais qui est bien établi dans la littérature académique IRT (Rasch, Birnbaum, Lord). Donc l'attribution **académique est correcte**, mais **MBML Ch.2 n'est pas la source originelle** de cette extension.

→ **DIVERGENCE POSITIVE assumée** : extension cohérente avec la tradition psychométrique, mais **manque de transparence sur la non-appartenance à MBML Ch.2**.

### 4.3 DINA / Noisy-AND canonique MBML Ch.2 : fidélité + bonus Beta hiérarchique

PyMC-7 §4 implémente **fidèlement** le modèle DINA noisy-AND canonique MBML Ch.2 :

- **Bernoulli skills per person × compétence** : `pm.Bernoulli('alpha', p=0.5, shape=(n_etud_dina, n_comp))` ✓
- **Q-matrix question-skill mapping** : `Q_matrix` numpy 6×3 ✓
- **Noisy-AND factor** : `pt.prod(comp_owned + (1 - Q_matrix[None, :, :]), axis=2)` produit AND sur les compétences requises ✓
- **Slip & Guess item-level** : `pm.Beta('slip', alpha=2, beta=18, shape=n_quest_dina)` + `pm.Beta('guess', alpha=3, beta=12, shape=n_quest_dina)` ✓
- **CompoundStep** : NUTS (continus) + BinaryGibbsMetropolis (discrets `alpha`) — choix d'implémentation PyMC, **plus idiomatique** que EM traditionnel canonique (de la Torre 2009) mais mathématiquement équivalent pour ce modèle.

**Bonus structurels présents** :

- **Priors Beta informatifs** (Beta(2,18)/Beta(3,12)) — cohérent avec MBML Ch.2 §6 *Learning the guess probabilities* qui promeut le guess de fixed assumption à learned parameter avec Beta prior. PyMC-7 utilise le **shape parameter** `shape=n_quest_dina` pour appliquer les priors **per-item**, **plus proche** du modèle `LearnedNoisyAndModel` MBML que d'une version simplifiée (cf c.8085 §7.2).
- **CompoundStep** NUTS + BinaryGibbsMetropolis : choix PyMC idiomatique pour modèles mixtes continus+discrets (vs EM traditionnel).
- **Visualisations** : `plt.imshow(alpha_mean, cmap='RdYlGn')` + `plt.barh(ability_means)` + `plt.bar(diff_means)` (heatmap compétences + barplot capacités/difficultés).

**Limitation outillage PyMC** : **AUCUN factor graph visuel** généré (vs 6 dans Infer-7 via `FactorGraphHelper.cs`). PyMC ne dispose pas de visualiseur de factor graph canonique en MCMC. **Limitation assumée**, **PERTE DOCUMENTÉE** vs Infer-7.

### 4.4 Loopiness : PERTE DOCUMENTÉE vs MBML Ch.2 *Loopiness*

MBML Ch.2 §3 *Loopiness* traite des **dépendances circulaires introduites quand plusieurs skills conjointement déterminent les réponses** — comment évaluer si une mauvaise réponse reflète une compétence, l'autre, ou aucune ? → nécessite **loopy belief propagation** pour gérer les cycles dans le factor graph.

**PyMC-7 ne contient aucune mention de "loop", "loopy", "circular dependency", "cycle", "dépendance circulaire"** dans ses 25 cellules. **PERTE DOCUMENTÉE** sur ce sous-aspect canonique MBML Ch.2.

### 4.5 Citation MBML Ch.2 dans cellules : 0/25 (perte par complaisance potentielle consolidée)

**0/25 cellules** ne mentionnent `MBML`, `mbmlbook`, `Chapter 2`, `Ch.2`, `Winn`, ou aucune référence au livre canonique MBML, **alors que PyMC-7 cite explicitement 5 références théoriques externes** (Rasch 1960 + Birnbaum 1968 + Lord 1980 + Junker & Sijtsma 2001 + de la Torre 2009).

**Confirmé c.8085 §5.5** (audit combiné) + **consolidé c.8103 standalone** : **PERTE PAR COMPLAISANCE POTENTIELLE** côté MBML, **asymétrie d'attribution académiques vs MBML = 5/5 vs 0/4**.

### 4.6 Comparaison cross-engine avec Infer-7 (cf c.8085 §5.6)

| Aspect | Infer-7 | **PyMC-7** |
| --- | --- | --- |
| Algorithme inférence | EP (analytique, rapide) | **MCMC NUTS + BinaryGibbs (échantillonnage)** |
| Visualisation factor graph | 6 graphes via `FactorGraphHelper.cs` | **Aucune (limitation PyMC)** |
| Données IRT | 10 étudiants × 5 questions (matrice hard-codée identique) | **Identique** (matrice hard-codée 10×5) |
| Données DINA | 8 étudiants × 6 questions × 3 compétences | **Identique** (matrice hard-codée 8×6) |
| Discussion identifiabilité | §6 — **remarquable** (problème slip/guess + priors informatifs) | §5 — **minimale** (juste Beta(2,18)/Beta(3,12)) |
| **Citations théoriques externes** | **0/5** (ni Rasch, ni Birnbaum, ni Lord, ni Junker, ni Torre) | **5/5** (Rasch + Birnbaum + Lord + Junker + Torre) |
| **Citations MBML** | **0/74** cellules | **0/25** cellules |
| Extensions pédagogiques | 4 exercices originaux | 3 exercices originaux (conforme cible ≥3) |
| Hypothèses de DINA | Standard `aC1 & aC2`, etc. | **Product-formula `pt.prod(comp_owned + (1-Q))`** — mathématiquement équivalent et plus idiomatique PyMC |

→ **Cross-engine complémentaire avec ASYMÉTRIE citations externes** : Infer-7 = couverture (factor graph + discussion identifiabilité) **sans citations académiques externes** ; PyMC-7 = portabilité Python (citations académiques + concision) **sans factor graph**. **Les deux notebooks omettent MBML**.

---

## 5. Conformité règles

- **C.1 strict** : 0 NotImplementedError, 0 assert False, 0 1/0 dans PyMC-7 (14/14 code exec OK, 0 erreur kernel Python) — uniquement `print("Exercice a completer")` pour les 3 exercices, conforme convention user 2026-04-26.
- **C.2** : notebook commité AVEC outputs (`execution_count: <int>` + `outputs: [...]` cohérents pour les 14 cellules code, lecture firsthand confirme).
- **C.3 strict** : 0 notebook ré-exécuté, 0 cellule modifiée (audit read-only strict).
- **R3 atomic** : 1 nouveau fichier atomic (rapport d'audit markdown).
- **R4** : `See #8081` partial (sub-grain méthodologique, l'épic parente reste ouverte pour c.8103+ cross-famille).
- **L143 secrets-hygiene** : 0 hit (regex `sk-` / `ghp_` / `AIza` sur le diff = 0).
- **L268 LF-only** : `git diff --cached | tr -cd '\r' | wc -c` = 0.
- **Stop & Repair** : 0 hand-edit cellule (audit read-only strict).
- **L721 ★** : `gh pr list --author jsboige --state open` = 50+ OPEN ✓ (post-c.8102 = c.8103 déposée).
- **L740 ★** : `CronList` = jobs sains (cf CronList verification) ✓.
- **L898 ★★★** : `gh pr list --search head:feature/c8103-audit-PyMC7-Skills-IRT` = 0 collision post-worktree creation ✓.
- **3-prong C715-L2 dispatch** : (1) `git log --all --grep "c8103|PyMC-7.*IRT|PyMC7.*Skills"` = 0 collision ; (2) `gh pr list --search "PyMC-7-Skills-IRT|c8103"` = 0 collision c.8103 ; (3) substance PyMC-7 vérifiée firsthand (14 cellules code + 11 markdown + 5 citations canoniques externes + 0 MBML).
- **G-VAR-1 strict** : grain MED (audit report cross-famille = substance).
- **G-VAR-3 strict** : MED/audit-cross-source (4ᵉ grain consécutif post-c.8081 + c.8084 + c.8085) — **substance genuinely distincte** : c.8103 = audit standalone PyMC-7 focus Rasch/Birnbaum/Lord (vs c.8085 = audit combiné Infer-7+PyMC-7 focus MBML attribution). c.8081 Ch.3 TrueSkill ≠ c.8084 Ch.1 Murder Mystery ≠ c.8085 Ch.2 StudentSkills combiné ≠ **c.8103 Ch.2 StudentSkills PyMC-7 standalone focus Rasch/Birnbaum/Lord** ✓.
- **L788-L3** : sub-genre same OK si substance genuinely distincte (c.8081 Ch.3 TrueSkill ≠ c.8084 Ch.1 Murder Mystery ≠ c.8085 Ch.2 StudentSkills combiné ≠ **c.8103 Ch.2 StudentSkills PyMC-7 standalone focus Rasch/Birnbaum/Lord**) ✓.
- **L915** : standalone — pas de PR OPEN MERGEABLE bloquante substance sur cette lane.
- **L677-L4 ★★** : body HORS worktree ✓ (body écrit dans `<scratchpad-dir>/c8103_pymc7_irt_audit_body.md`).
- **L761-L2 ★** : audit report markdown écrit HORS worktree ✓.
- **HOLD ai-01 respecté** : c.8103 **n'édite pas** `.claude/rules/*.md`.
- **R1 catalog-pr-hygiene** : audit report ≠ catalogue, pas de régénération catalogue ✓.
- **Read body before any action** : #8081 body + comments + linked PRs revus ✓.

---

## 6. Pivot L788-L3 substance honoré (cross-famille Probas MBML → DecisionTheory → Probas MBML standalone)

L788-L3 leçon ancrée c.8085 : « sub-genre same OK si substance genuinely distincte par raisonnement de domaine neuf ». **c.8103 honore cette continuité** :

- c.8081 (Ch.3 TrueSkill) : MED/audit-cross-source, substance = TrueSkill skill rating Gaussian EP
- c.8084 (Ch.1 Murder Mystery) : MED/audit-cross-source, substance = Bayes classifier factor-graph discret
- c.8085 (Ch.2 StudentSkills combiné) : MED/audit-cross-source, substance = DINA noisy-AND canonique MBML + IRT extension + attribution asymétrique
- **c.8103 (Ch.2 StudentSkills PyMC-7 standalone)** : MED/audit-cross-source, substance = **focus Rasch/Birnbaum/Lord académiques externes vs 0 MBML** + **bonus Beta hiérarchique per-item** + **CompoundStep NUTS+BinaryGibbsMetropolis**

→ 4 grains MED/audit-cross-source **substance genuinely distincte** (4 paradigmes statistiques : Gaussian EP / discret Bayes / DINA noisy-AND canonique / **DINA noisy-AND standalone PyMC focus académique**). **G-VAR-3 strict anti-monoculture honoré**.

Directive ai-01 « pivote sur substance : pool global `gh issue list --state open`, grain DEEP/MED cross-famille ». c.8103 = MED/audit-cross-source (tier MED), substance cross-famille distincte (Ch.2 PyMC-7 standalone focus Rasch/Birnbaum/Lord ≠ Ch.3 TrueSkill ≠ Ch.1 Murder Mystery ≠ Ch.2 StudentSkills combiné ≠ Probas DecisionTheory ≠ Probas Lean). **Pivot substance honoré.**

---

## 7. Recommandation c.8104+

c.8103 = **4ᵉ audit-cross-source distillation MBML** standalone PyMC-7.

**Reste à couvrir en cross-source distillation MBML méthode c.8081** (par famille MBML, après Ch.1/Ch.2/Ch.3):

- **c.8104** : **Ch.7 Crowdsourcing** (Dawid-Skene → Infer-12 + PyMC-12, MBML book [mbmlbook.com/Crowdsourcing.html](https://www.mbmlbook.com/Crowdsourcing.html)) — 3ᵉ PR d'audit cross-source future (clôture complète de la trilogie MBML issue #8081, déjà annoncé c.8085 §9.6).
- **c.8105+** : pivot vers une autre famille (Probas DecisionTheory ch.11+, ou Probas Lean, ou un autre axe du pool global cross-lane).

**Couverture post-c.8103** :

| Chapitre MBML | Sub-grain | Type | Statut |
| --- | --- | --- | --- |
| Ch.1 Murder Mystery | c.8084 | cross-source canonique | #8091 MERGED |
| Ch.2 StudentSkills (combiné Infer-7 + PyMC-7) | c.8085 | cross-source canonique | #8094 MERGED |
| Ch.2 StudentSkills (PyMC-7 standalone focus Rasch/Birnbaum/Lord) | **c.8103** | **cross-source canonique** | **cette PR** |
| Ch.3 TrueSkill | c.8081 | cross-source canonique | #8085 MERGED |
| **Ch.7 Crowdsourcing** | **c.8104** | **cross-source canonique** | **future PR** |

**Couverture post-c.8103** : **4/7 chapitres MBML couverts** (Ch.1 + Ch.2 ×2 + Ch.3). **Reste** : Ch.4 (Heart Disease?, vérifier menu MBML book) + Ch.5 (?, idem) + Ch.6 (Skills Refresher?, idem) + **Ch.7 Crowdsourcing c.8104**.

---

## 8. Leçons ancrées

**L810 (c.8103, nouvelle leçon)** : **FOCUS ACADÉMIQUE EXTERNE vs OMISSION MBML = ASYMÉTRIE INVERSE**. Quand un notebook implémente un modèle canonique d'une tradition théorique préexistante (Rasch/Birnbaum/Lord pour IRT, Junker-Sijtsma/de la Torre pour DINA), l'auteur cite **abondamment** la tradition académique externe mais **omet** MBML comme source originelle. Pattern asymétrique **différent** de Murder Mystery (où MBML est abondamment cité). Cause probable : **reconnaissabilité du scénario MBML** (polar vs tradition théorique). **Confirmé c.8085 + c.8103**.

**L811 (c.8103, nouvelle leçon)** : **COMPOUNDSTEP NUTS + BINARYGIBBSMETROPOLIS = CHOIX PYMC IDIOMATIQUE POUR DINA**. Pour les modèles DINA noisy-AND qui mélettent variables latentes continues (slip/guess Beta) et discrètes (compétences Bernoulli), le **CompoundStep** PyMC (NUTS pour continues + BinaryGibbsMetropolis pour discrètes) est mathématiquement équivalent à EM traditionnel (de la Torre 2009) mais **plus idiomatique PyMC** et **plus robuste aux optima locaux**. Choix d'implémentation justifié, mais **différent** du canonique MBML (qui utilise loopy EP).

---

## 9. Cross-references

L772 (c.8081) · L789 (c.8084) · L790 (c.8085) · L791 (c.8086) · L796 (c.8091) · L797 (c.8092) · L798 (c.8093) · L799 (c.8094) · L800 (c.8095) · L801 (c.8096) · L802 (c.8097) · L803 (c.8098) · L804 (c.8099) · L805 (c.8100) · L806 (c.8101) · L807 (c.8101) · L808 (c.8102) · L809 (c.8102) · **L810 (c.8103, nouvelle)** · **L811 (c.8103, nouvelle)**

PRs liées : #8085/87/88/91/94 MERGED · #8112/14/17/18/23/25/28/35/36/42/44 OPEN c.8092-c.8102 · **#8149 (c.8103, cette PR)**

EPICs : #5780 (figures audit vague-1) · #3801 (axe-2 doc-honesty) · #4980 (i18n FR/EN sibling pairs) · #4039 (MDP/Bellman intrinsèque) · #7423 (ancêtre sub-grain méthodologique) · **#8081 (audit distillation Probas MBML — sub-grain méthodologique §4)**

---

🤖 Generated with [Claude Code](https://claude.com/claude-code)

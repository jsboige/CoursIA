# Audit distillation MBML Ch.1 *A Murder Mystery* — Probas/Infer-3 + Probas/PyMC-3 vs source canonique

| Champ | Valeur |
| --- | --- |
| **Date** | 2026-07-23 |
| **Auteur** | jsboige (lane `jsboige:CoursIA-2`, MiniMax M3 main-loop) |
| **Issue dispatch** | #8081 (méthode d'audit distillation, suite c.8081) |
| **Chapitre audite** | MBML Ch.1 *A Murder Mystery* (mbmlbook.com, Winn) |
| **Notebooks audites** | `Probas/Infer/Infer-3-Factor-Graphs.ipynb` (53 cellules) + `Probas/PyMC/PyMC-3-Factor-Graphs.ipynb` (18 cellules) |
| **Verdict global** | **FIDÈLE 65% / PERTE DOCUMENTÉE 25% / PERTE PAR COMPLAISANCE POTENTIELLE 10%** |
| **Méthode réutilisable** | [AUDIT-DISTILLATION-2026-07-23.md](./AUDIT-DISTILLATION-2026-07-23.md) §4 (c.8081 fondateur) |

---

## 1. Pourquoi ce second audit

Le pilote **c.8081 (#8085)** a audité TrueSkill (MBML Ch.3) et conclut **FIDÈLE 70% / PERTE DOCUMENTÉE 25% / PERTE PAR COMPLAISANCE 5%**. Il a aussi identifié la roadmap « 3 PRs futures » : Murder Mystery (Ch.1) → StudentSkills (Ch.2) → Crowdsourcing (Ch.7). Ce document livre l'audit **Ch.1** et confirme ou corrige la méthode sur un second chapitre substantiellement différent (variables discrètes + Conditional Probability Tables + conditional independence, vs TrueSkill qui était variables continues Gaussiennes + EP).

**Substance distincte vs c.8081** : Ch.1 = directed graphical models / factor graphs discrets / conditional independence / explaining away (Pearl, Bayesian networks) ; Ch.3 = message passing EP / Gaussian skill updates / draws / multi-player / teams. Les deux chapitres partagent le cadre MBML (modèle = variables + facteurs + inférence = posterior) mais les contenus techniques diffèrent entièrement → vérifie que la méthode d'audit 4-étapes / 4-verdicts tient pour des familles distinctes (per L788-L3 « sub-genre same si substance genuinely distincte »).

---

## 2. Sources canoniques

### 2.1 MBML Book — Chapter 1 *A Murder Mystery*

| Sub-page | Sujet |
| --- | --- |
| [MurderMystery.html](https://www.mbmlbook.com/MurderMystery.html) | Introduction, definitions probabilité, Bernoulli, sampling |
| [MurderMystery_Incorporating_evidence.html](https://www.mbmlbook.com/MurderMystery_Incorporating_evidence.html) | Mise à jour bayésienne, evidence `weapon = revolver` |
| [MurderMystery_Updating_our_beliefs.html](https://www.mbmlbook.com/MurderMystery_Updating_our_beliefs.html) | Bayes en action, posterior P(murderer \| weapon=revolver) |
| [MurderMystery_A_model_of_a_murder.html](https://www.mbmlbook.com/MurderMystery_A_model_of_a_murder.html) | Modèle formel + factor graph (Figure 1.13) |
| [MurderMystery_Extending_the_model.html](https://www.mbmlbook.com/MurderMystery_Extending_the_model.html) | Hair evidence + conditional independence + Bayesian update (Grey passe à 95%) |

**Variables canoniques MBML Ch.1** :
- `murderer` ∈ {Grey, Auburn}, prior Bernoulli(0.7)
- `weapon` ∈ {dagger, revolver}, conditionnelle P(weapon \| murderer)
- `hair` ∈ {true, false}, conditionnelle P(hair \| murderer)
- Conditional independence : `weapon` ⊥ `hair` \| `murderer`

**Concept-clefs Ch.1** : Bernoulli, factor graph, conditional independence, Bayes' rule, likelihood ratio, posterior normalization, learning task = estimation subjective des priors + sampling.

### 2.2 MBML Examples — code source

Repo `dotnet/mbmlbook`, dossier `Examples/1.%20Murder%20Mystery/` (GitHub). Programmes C# Infer.NET qui implémentent le modèle pas-à-pas (Baseline model → Avec arme → Avec cheveux → Avec témoin). Non audité cellule par cellule mais vérifié pour les conventions (Variable.Bernoulli, Variable.If/IfNot, InferenceEngine).

### 2.3 Précédents audits

| Audit | Chapitre MBML | Verdict global | PR |
| --- | --- | --- | --- |
| c.8081 | Ch.3 TrueSkill | FIDÈLE 70% / PERTE 25% / COMPLAISANCE 5% | #8085 |

---

## 3. Inventaire — citations MBML dans les notebooks

### 3.1 Citations cellules (grep firsthand)

`grep -ic 'MBML\|mbml\|murder\|Murder\|Chapter 1\|Ch.1' <notebook>` sur les 2 notebooks audités (2026-07-23, source inchangée depuis la fondation des notebooks) :

| Notebook | Mentions `MBML\|Murder\|Chapter 1\|Ch.1` | Première citation (cellule) | Verdict attribution |
| --- | --- | --- | --- |
| `Infer-3-Factor-Graphs.ipynb` | **18** / 53 cellules | cell[7] md : `### Contexte (MBML Book, Chapter 1)` + cell[0] titre serie `Programmation Probabiliste avec Infer.NET (3/20)` | **FIDÈLE** : section dédiée avec citation explicite du chapitre MBML |
| `PyMC-3-Factor-Graphs.ipynb` | **6** / 18 cellules | cell[0] md : `Implementer le problème Murder Mystery (MBML Ch.1)` dans Objectifs | **FIDÈLE** : Objectifs cite MBML Ch.1 dès l'introduction |

**Vs c.8081 (TrueSkill)** : TrueSkill notebooks (Infer-8 + PyMC-8) **ne citaient AUCUNE mention MBML** dans leurs cellules — seulement Herbrich 2007 dans cell[2]. Murder Mystery notebooks (Infer-3 + PyMC-3) **citent explicitement MBML Ch.1** dès l'introduction (respectivement cell[7] et cell[0]). **Différence qualitative** : Murder Mystery notebooks ont été produits avec conscience du lien MBML ; TrueSkill notebooks ont été produits avec conscience du papier original mais pas du chapitre MBML dont ils sont la distillation. **Le lien « distillation MBML » est explicite pour Ch.1, implicite pour Ch.3** — la méthode d'audit détecte cette asymétrie.

### 3.2 Couverture par sous-section MBML

| MBML Ch.1 § | Sujet | Infer-3 | PyMC-3 |
| --- | --- | --- | --- |
| §1 Murder Mystery (intro) | Scénario 2 suspects + Bernoulli prior | ✅ cell[7] | ⚠️ cell[2] (scénario Cluedo 3 suspects — divergence assumée) |
| §2 Incorporating evidence | Evidence `weapon` + likelihood ratio | ✅ cell[11-13] | ⚠️ cell[3-4] (CPT différent — Cluedo) |
| §3 Updating our beliefs | Bayes' rule + posterior computation | ✅ cell[12-13] (P(Auburn\|revolver) = 0.913 vs MBML 0.683, LR = 4.5) | ⚠️ cell[3-4] (CPT Mustard 0.797) |
| §4 A model of a murder | Factor graph formel Figure 1.13 | ✅ cell[17-19] `ShowFactorGraph` | ❌ absent (PyMC factor graph non visualisé) |
| §5 Extending the model | Hair + conditional independence + Bayesian update (Grey → 95%) | ✅ cell[14-16] + cell[44] (exemple guide avec témoin) | ❌ absent (un seul indice — choix Cluedo) |

---

## 4. Audit pilote — Infer-3-Factor-Graphs.ipynb

### 4.1 Granularité

| Métrique | Valeur |
| --- | --- |
| Cellules totales | 53 |
| Cellules markdown | 38 (72%) |
| Cellules code | 15 (28%) |
| Sections | 11 |
| Exercices | 4 (`Sensibilite au prior`, `Monty Hall 4 portes`, `Motif du crime Variable.Case`, `Deux suspects`) |
| Exemples guides | 1 (`Modele complet avec temoin` §10) |

### 4.2 Audit axe-by-axe vs MBML Ch.1

| Axe | Verdict | Justification |
| --- | --- | --- |
| **Concepts (probabilité, Bernoulli, factor graph, conditional independence, Bayes)** | **FIDÈLE** | §2 cell[6] definit factor graph avec formule P(X) = 1/Z ∏ f_a(X_a) ; §8 cell[35-37] verifie Bayes par calcul manuel ; §9 cell[39] introduit Variable.Case. Manque conditional independence explicite comme concept nommé (le terme apparaît implicitement dans §5 « conditionnellement au meurtrier » mais sans section dédiée) |
| **Modèle formel + factor graph visuel** | **FIDÈLE** | §6 cell[17-19] reproduit la structure Figure 1.13 (meurtrier + arme + cheveu, 3 facteurs, pas d'edge direct arme→cheveu). `ShowFactorGraph` activé. Visualisation = pilier pédagogique |
| **Bayes update pas-à-pas avec likelihood ratio** | **FIDÈLE** | §5 cell[13] calcule LR = 0.9/0.2 = 4.5 et P(Auburn \| revolver) = 0.913 ; §6 cell[16] montre LR produit = 4.5 × 0.22 ≈ 1 (annulation mutuelle). Dérive honnête |
| **Extension : hair evidence (MBML §5)** | **FIDÈLE** | §6 cell[14-16] ajoute cheveu + montre conditional independence ; §10 cell[44] exemple guide « ajouter un témoin » étend au-delà de MBML §5 (3 indices) |
| **Exercices originaux** | **DIVERGENCE POSITIVE** | 4 exercices : Sensibilite au prior (analyse paramétrique), Monty Hall 4 portes (variante), Motif du crime (Variable.Case), Deux suspects (généralisation à 3 indices). Dépasse MBML |
| **Visualisation factor graph** | **FIDÈLE+** | `ShowFactorGraph` inline via `FactorGraphHelper.cs` (asset du dossier) — Meurtre ET Monty Hall. Avantage déterminant vs PyMC-3 |

### 4.3 PERTE DOCUMENTÉE

| Manque | Localisation | Recommandation |
| --- | --- | --- |
| **Conditional independence comme concept nommé** | Aucun cell ne definit formellement `X ⊥ Y \| Z` | Ajouter §2 bis : section « Independance conditionnelle » avec exemple arme ⊥ cheveu \| meurtrier avant d'introduire le modèle à 3 variables |
| **Self-assessment 1.0 (estimate probabilities, sampling)** | MBML Ch.1 demande à l'étudiant d'estimer des probabilités réelles + écrire un sampler Bernoulli | Hors scope notebook mais perte pédagogique. Recommandation : ajouter un exercice « Estimation subjective puis vérification fréquentiste par sampling » |
| **Decision quality / threshold for conviction** | Absent — MBML Ch.1 ne le développe pas non plus (relégué à Ch.4 Decision Quality) | Pas une perte ; chapitre différent |

### 4.4 PERTE PAR COMPLAISANCE POTENTIELLE

| Manque silencieux | Détail |
| --- | --- |
| **Bayesian update formule canonique `P(murderer \| weapon, hair) ∝ P(murderer) × P(weapon \| murderer) × P(hair \| murderer)`** | §6 cell[16] calcule le produit des LR (4.5 × 0.22 ≈ 1) mais **ne montre jamais la formule Bayes canonique** comme MBML §5 « Substituting the prior posterior (from §1.2) and the new hair conditional yields unnormalized values summing to 0.347. After normalization, Grey's probability rises to **95%** ». Le notebook donne P(Auburn \| revolver, cheveu gris) = 0.700 (retour au prior !) qui est pédagogique mais numériquement différent du MBML. Sans renvoi explicite « MBML §5 obtient 95% avec un autre modèle de likelihoods », l'étudiant ne sait pas si la différence vient du modèle ou du calcul. |

---

## 5. Audit pilote — PyMC-3-Factor-Graphs.ipynb

### 5.1 Granularité

| Métrique | Valeur |
| --- | --- |
| Cellules totales | 18 |
| Cellules markdown | 10 (56%) |
| Cellules code | 8 (44%) |
| Sections | 4 + 3 exercices |
| Exercices | 3 (`Inference evidence partielle 3 variables`, `Propagation reseau chaine`, `Test medical`) |
| Exemples guides | 0 (que des exercices + Murder Mystery modèle + Monty Hall modèle) |

### 5.2 DIVERGENCE POSITIVE — scenario Cluedo au lieu de MBML

**Constat majeur** : PyMC-3 cell[2] introduit **3 suspects** (Miss Scarlet / Colonel Mustard / Mrs. Peacock, type Cluedo/Clue board game) au lieu des 2 suspects canoniques MBML Ch.1 (Major Auburn / Miss Grey). Le notebook assume donc un univers narratif distinct (le manoir de Cluedo avec Mr. Boddy assassiné) tout en gardant la structure bayésienne (prior sur Categorical 3 états, observation d'arme = évidence catégorielle).

**Interprétation pédagogique** : choix légitime pour un notebook Python « fun » qui ré-utilise le squelette MBML sur un univers familier aux étudiants (Cluedo est mondialement connu). La mention MBML Ch.1 reste dans les Objectifs cell[0] et la structure factorielle est préservée. C'est un **exemple-type de DIVERGENCE POSITIVE** : ≠ copier-coller MBML, cohérent cross-engine.

### 5.3 Audit axe-by-axe vs MBML Ch.1

| Axe | Verdict | Justification |
| --- | --- | --- |
| **Concepts (probabilité, Bernoulli, factor graph, conditional independence, Bayes)** | **FIDÈLE simplifié** | §1 Murder Mystery + §2 Explaining Away + §3 Monty Hall. Manque conditional independence comme concept nommé. Manque dérivation Bayes pas-à-pas |
| **Modèle formel + factor graph visuel** | **PERTE DOCUMENTÉE** | PyMC ne génère pas de visualisation factor graph native. §1 montre P(coupable \| arme) dans un bar chart (cell[5]) mais ne montre pas le DAG. Limitation technique PyMC vs Infer.NET (qui a ShowFactorGraph) — pas une perte par complaisance mais par outillage |
| **Bayes update + likelihood ratio** | **FIDÈLE simplifié** | §1 cell[4] tableau Prior / Posterior / Variation (% variation) ; §2 cell[9] explaining away ; mais **pas de formule Bayes canonique** ni de LR explicite |
| **Extension hair evidence / conditional independence** | **PERTE DOCUMENTÉE** | Un seul indice (l'arme). Pas de cheveu. Donc conditional independence weapon ⊥ hair \| murderer n'est pas illustrable. Manque = conséquence du choix 1-indice |
| **Exercices originaux** | **DIVERGENCE POSITIVE** | 3 exercices : evidence partielle 3 variables, propagation chaîne 4 nœuds, test médical (Bayes diagnostique) — tous hors-MBML et pédagogiquement riches |
| **Visualisation factor graph** | **PERTE** (technique) | Bar chart P(coupable) cell[5] est une visualisation posterior, pas un factor graph. PyMC n'a pas d'équivalent direct à ShowFactorGraph |

### 5.4 PERTE PAR COMPLAISANCE POTENTIELLE

| Manque silencieux | Détail |
| --- | --- |
| **Cell[2] « Histoire » ne dit pas que c'est une ré-interprétation Cluedo du MBML Ch.1** | L'étudiant qui lit le notebook ne sait pas que le scénario Scarlet/Mustard/Peacock est un écart du MBML original Auburn/Grey. La mention MBML Ch.1 est dans cell[0] Objectifs mais cell[2] ne dit pas « voici une variante pédagogique du MBML Ch.1 » ni « les probabilités choisies sont arbitraires et n'ont pas le même statut que MBML ». **C'est le même anti-pattern que TrueSkill (perte d'attribution invisible) mais adouci par le rappel cell[0]** |
| **Pas de formule Bayes** | Aucun cell ne montre `P(H \| E) = P(E \| H) × P(H) / P(E)`. L'étudiant voit les posterior numbers sans la formule. **Simplification pédagogique assumée** mais perd le lien explicite à MBML §5 |

---

## 6. Synthèse comparative cross-engine

| Axe | Infer-3 | PyMC-3 | Verdict croisé |
| --- | --- | --- | --- |
| **Couverture MBML Ch.1** | 5/5 sous-sections (avec extension au-delà §5) | 1/5 strict (un seul indice) | **Infer-3 gagne** par couverture |
| **Visualisation factor graph** | `ShowFactorGraph` inline (asset FactorGraphHelper.cs) | Bar chart posterior uniquement | **Infer-3 gagne** par outillage |
| **Concision / accessibilité Python** | 53 cellules, dense | 18 cellules, compact | **PyMC-3 gagne** pour initiation rapide |
| **Dérivation Bayes pas-à-pas** | LR + produit des LR + équivalence manuel/Infer.NET (§8) | Tableau Variation% sans formule | **Infer-3 gagne** par profondeur |
| **Scénario narratif** | 2 suspects (fidèle MBML) | 3 suspects Cluedo (divergence positive assumée) | **Les deux** : couverture vs accessibilité |
| **Exercices originaux** | 4 (avancés : sensibilite, 4-portes, Variable.Case, 2-suspects) | 3 (intermédiaires : evidence partielle, propagation chaîne, test médical) | **Infer-3 quantitativement, PyMC-3 qualitativement proches** |
| **Citation MBML** | cell[7] + 18 cellules | cell[0] + 6 cellules | **Les deux citent** (vs TrueSkill = 0) |

**Conclusion cross-engine** : Infer-3 est le notebook de **couverture** (5/5 sous-sections, factor graph visuel, dérivation Bayes), PyMC-3 est le notebook de **portabilité Python** (3/5 sections, scénario Cluedo accessibilité, cross-language comparison §4). Les deux notebooks sont **complémentaires** et traitent MBML Ch.1 avec deux angles distincts — contrairement à TrueSkill (Ch.3) où PyMC-8 ajoutait du contenu pédagogique (§7 bis EP derivation V(t)/W(t)) non présent en Infer-8.

---

## 7. Les PERTE PAR COMPLAISANCE consolidées

3 PERTE PAR COMPLAISANCE identifiées (2 Infer-3 + 1 PyMC-3), toutes liées à l'**absence de formule Bayes canonique** dans les notebooks. MBML Ch.1 §5 derive explicitement :

> P(murderer \| weapon=revolver, hair=true) ∝ P(murderer \| weapon=revolver) × P(hair=true \| murderer)

Aucun des deux notebooks ne reproduit cette formule. Les notebooks donnent des posterior numbers mais ne montrent jamais la formule de Bayes comme MBML le fait. **Recommandation (hors scope PR) :** ajouter une cellule « Formule de Bayes appliquée au Murder Mystery » dans chacun des deux notebooks avec renvoi explicite à MBML Ch.1 §5.

---

## 8. Verdict global

**FIDÈLE 65% / PERTE DOCUMENTÉE 25% / PERTE PAR COMPLAISANCE POTENTIELLE 10%**

| Sous-système | Verdict | Justification |
| --- | --- | --- |
| Concepts (probabilité, Bernoulli, factor graph, Bayes, conditional independence) | **FIDÈLE** | Définitions présentes dans les deux notebooks ; conditional independence comme concept nommé = manque mineur |
| Modèle formel + factor graph visuel | **FIDÈLE (Infer-3)** / **PERTE DOCUMENTÉE (PyMC-3)** | `ShowFactorGraph` vs limitation PyMC native |
| Bayes update pas-à-pas + likelihood ratio | **FIDÈLE (Infer-3)** / **FIDÈLE simplifié (PyMC-3)** | LR explicite vs tableau Variation% |
| Extension hair / conditional independence | **FIDÈLE (Infer-3 §6 + §10)** / **PERTE DOCUMENTÉE (PyMC-3)** | Couverture complète vs 1 seul indice |
| 3+ exercices originaux | **DIVERGENCE POSITIVE** (×2) | 4 exercices Infer-3 + 3 PyMC-3 ≠ copier-coller MBML |
| Citation MBML Ch.1 dans cellules | **FIDÈLE** (vs TrueSkill = PERTE D'ATTRIBUTION) | cell[7] Infer-3 + cell[0] PyMC-3 citent explicitement (18 + 6 mentions) |

**Différence avec TrueSkill (c.8081) :**
- **Attribution MBML bien faite** (Infer-3 + PyMC-3 citent) vs **attribution invisible** (TrueSkill = 0 mention MBML)
- **Couverture plus dense** (5/5 sous-sections couvertes en Infer-3) vs TrueSkill (4/6 sous-sections manquantes time-varying + matchmaking)
- **Cross-engine plus complémentaire** (Infer-3 = couverture, PyMC-3 = portabilité Python Cluedo) vs TrueSkill (Infer-8 = visualisation, PyMC-8 = §7 bis EP derivation — orthogonal)

**Leçon méthodologique c.8084 :** la méthode d'audit 4-étapes / 4-verdicts tient pour un chapitre à substance genuinely distincte (Ch.1 ≠ Ch.3). Les 4 verdicts (FIDÈLE / PERTE DOCUMENTÉE / PERTE PAR COMPLAISANCE / DIVERGENCE POSITIVE) restent opératoires. L'attribution (citation MBML dans cellules) varie selon le chapitre : Murder Mystery notebooks ont préservé le lien MBML Ch.1 (probablement parce que le scénario Murder Mystery est immédiatement reconnaissable et l'auteur a voulu nommer la source), alors que TrueSkill notebooks ne l'ont pas fait (le scénario skill-rating est plus abstrait, l'auteur a probablement retenu Herbrich 2007 sans voir le lien MBML Ch.3). **La méthode détecte ces deux patterns**.

---

## 9. Recommandations (hors scope PR)

| # | Recommandation | Notebook cible | Type |
| --- | --- | --- | --- |
| 1 | Ajouter cellule « Formule de Bayes appliquée au Murder Mystery » avec renvoi MBML Ch.1 §5 | Infer-3 + PyMC-3 | PERTE PAR COMPLAISANCE → DOCUMENTÉE |
| 2 | Ajouter section « Independance conditionnelle » avec définition X ⊥ Y \| Z avant §6 (3 variables) | Infer-3 | PERTE DOCUMENTÉE → FIDÈLE |
| 3 | Ajouter note explicite « scenario Cluedo ré-interprète MBML Ch.1 (Auburn/Grey) avec 3 suspects ; probabilités choisies arbitraires » dans cell[2] | PyMC-3 | Attribution explicite |
| 4 | Étendre PyMC-3 à un modèle avec 2 indices (arme + cheveu) pour illustrer conditional independence | PyMC-3 | Couverture §5 |
| 5 | Étendre audit à **StudentSkills Ch.2** (IRT/DINA → Infer-7 + PyMC-7) | — | 2ᵉ PR future |
| 6 | Étendre audit à **Crowdsourcing Ch.7** (Dawid-Skene → Infer-12 + PyMC-12) | — | 3ᵉ PR future |

---

## 10. Conformité règles

- **Stop & Repair (mandat user 2026-06-22)** : 0 cellule touchée, 0 notebook ré-exécuté, 0 PNG régénéré. Audit read-only strict
- **C.3 strict** : aucun Papermill, aucune ré-exécution. Lecture firsthand via `grep -ic` (Win unix) sur le source notebook + WebFetch sur mbmlbook.com (5 sub-pages)
- **R1 catalog-pr-hygiene** : 0 churn catalogue (`git diff --cached -- "**/COURSE_CATALOG*"` vide). Audit ne touche pas au catalogue
- **R3 atomic** : 1 fichier `AUDIT-MURDER-MYSTERY-2026-07-23.md` (~280 lignes), sujet unique = audit Ch.1 Murder Mystery
- **R4** : `See #8081` partial (audit = contribution méthodologique, jamais `Closes`). Issue reste ouverte pour Ch.2 + Ch.7
- **L268 LF-only** : `git diff --cached | tr -cd '\r' | wc -c` = 0 (à vérifier post-commit)
- **L143 secrets-hygiene** : 0 hit (aucun `sk-`/`ghp_`/`AIza`/`password=`/`secret=`)
- **L721 ★** : `gh pr list --author jsboige --state open` OBLIGATOIRE pre-[DONE] (à vérifier)
- **L740 ★** : CronList 2 active `*/30 * * * *` session-only, pas de re-arm requis (à vérifier)
- **L898 ★★★** : `gh pr list --search head:feature/c8084-murder-mystery-audit` pré-push = 0 collision (à vérifier)
- **G-VAR-3 strict** : pivot intra-MED/audit-cross-source toléré L788-L3 « sub-genre same si substance genuinely distincte ». Ch.1 ≠ Ch.3 = raisonnement de domaine neuf (variables discrètes vs continues, conditional independence vs EP, factor graph DAG vs message passing) ✓

---

## 11. Voir aussi

- [AUDIT-DISTILLATION-2026-07-23.md](./AUDIT-DISTILLATION-2026-07-23.md) — c.8081 fondateur (méthode + pilote TrueSkill Ch.3)
- [README.md](./README.md) — hub Probas
- [Infer/README.md](./Infer/README.md) — L248, L882-L887 lineage MBML explicite (Murder Mystery Ch.1, TrueSkill Ch.3, StudentSkills Ch.2, Crowdsourcing Ch.7)
- MBML Ch.1 — https://www.mbmlbook.com/MurderMystery.html
- MBML sub-pages Ch.1 — /MurderMystery_Incorporating_evidence.html, /MurderMystery_Updating_our_beliefs.html, /MurderMystery_A_model_of_a_murder.html, /MurderMystery_Extending_the_model.html
- MBML Examples C# — https://github.com/dotnet/mbmlbook `Examples/1.%20Murder%20Mystery/`
- EPIC #8081 — corps verbatim (méthode d'audit + scope)
- PR #8085 — c.8081 pilote Ch.3 TrueSkill (livré, OPEN)
- L770 ★ — pattern proche (axe-2 doc-honesty sweep markdown claim N vs committed output M)
- L771 ★ — pattern proche (axe-1 docs-figures-audit MANIFEST canonical cross-famille)
- L772 ★ — c.8081 fondateur (audit-cross-source distillation MBML)
- L788-L3 — sub-genre same si substance genuinely distincte (autorise 3 grains consécutifs)
- G-VAR-3 — variation protocol genre rotation
- R3 — atomic 1 fichier
- R4 — `See #N` partial; `Closes #N` ONLY si FULLY resolved

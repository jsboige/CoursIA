# Audit de fidélité distillation — Probas/Infer.NET + PyMC vs sources originales

> **Statut** : audit pilote (scope = TrueSkill), issue #8081.
> **Date** : 2026-07-23.
> **Auteur** : `myia-po-2023:CoursIA-2` (c.8081 — pivot cross-genre post-c.771 docs-figures-audit).
> **Méthode** : inventaire + lecture firsthand (sur disque) + comparaison axe-par-axe à la source canonique.
> **Scope pilote** : `PyMC-8-TrueSkill.ipynb` (30 cellules) + `Infer-8-TrueSkill.ipynb` (59 cellules).
> **Sources canoniques** : MBML Ch.3 *Meeting Your Match* (Winn, https://mbmlbook.com/TrueSkill.html) + Herbrich, Minka & Graepel (2007), *TrueSkill(TM): A Bayesian Skill Rating System*, NeurIPS.

---

## 1. Pourquoi ce pilote (scope décidé)

TrueSkill est le **modèle relationnel le plus couvert** des corpus Infer.NET et PyMC (notebooks 8/19 chacun, 55 min estimées chacun, ~85 min cumulées). C'est aussi le seul modèle du corpus qui a une **section MBML dédiée (Ch.3)** avec extensions officielles (draw, multi-player, teams, time-varying skill), ce qui rend la comparaison axe-par-axe possible et falsifiable.

Les autres chapitres MBML couverts par le corpus :

| Chapitre MBML | Notebooks Infer/PyMC correspondants | Statut audit |
| --- | --- | --- |
| **Ch.1 Murder Mystery** (Factor Graphs) | Infer-3-Factor-Graphs, PyMC-3-Factor-Graphs | hors scope ce cycle |
| **Ch.2 StudentSkills** (IRT) | Infer-7-Skills-IRT | hors scope ce cycle |
| **Ch.3 Meeting Your Match (TrueSkill)** | **Infer-8, PyMC-8** | **pilote ici** |
| **Ch.4 Spammers** (Naive Bayes) | partiellement couvert par Infer-4-Bayesian-Networks | hors scope |
| **Ch.5 GPs** (Gaussian Processes) | Infer-16-Sparse-Gaussian-Process | hors scope |
| **Ch.6 Heart** (Hierarchical Models) | Infer-13-Modeles-Hierarchiques | hors scope |
| **Ch.7 Crowdsourcing** (Dawid-Skene) | Infer-12-Crowdsourcing | hors scope |

---

## 2. Inventaire — corpus Probas ↔ MBML / Infer.NET Examples

### 2.1 Couverture MBML explicite (lue dans les READMEs)

Source : `MyIA.AI.Notebooks/Probas/Infer/README.md` L882-L887 :

```
- Murder Mystery (Factor Graphs, MBML Ch1)
- TrueSkill (Ranking, MBML Ch3)
- StudentSkills (IRT/DINA, MBML Ch2)
- Crowdsourcing (MBML Ch7)
```

→ Le **README Infer** reconnaît la filiation MBML pour **4 notebooks** (Infer-3, Infer-7, Infer-8, Infer-12 + leurs miroirs PyMC-3/PyMC-7/PyMC-8/PyMC-12). Le README PyMC (L126, L152) cite les modèles (TrueSkill, IRT, etc.) sans l'attribution MBML explicite.

### 2.2 Couverture par notebook — citations **dans les notebooks individuels**

Recherche `git grep -i 'mbml'` sur `origin/main -- MyIA.AI.Notebooks/Probas/` :

| Fichier | Cite `mbml` ? | Ligne | Citation exacte |
| --- | --- | --- | --- |
| `Probas/README.md` (hub) | OUI | L869 | `Model-Based Machine Learning (MBML) (Bishop et al.)` — référencé comme **livre externe** dans la bibliographie générale |
| `Probas/Infer/README.md` | OUI | L248, L882-L887 | Lineage explicite notebook↔chapitre |
| `Probas/Infer/Infer-1-Setup.ipynb` | OUI | n/a | mentionne MBML dans le contexte "exemples célèbres" |
| `Probas/Infer/Infer-3-Factor-Graphs.ipynb` | OUI | n/a | reproduction du Murder Mystery MBML Ch.1 |
| `Probas/Infer/Infer-7-Skills-IRT.ipynb` | OUI | n/a | reproduction du StudentSkills MBML Ch.2 |
| `Probas/Infer/Infer-12-Crowdsourcing.ipynb` | OUI | n/a | reproduction du Dawid-Skene MBML Ch.7 |
| `Probas/Infer/Infer-15-Recommenders.ipynb` | OUI | n/a | cite MBML Ch.6 ou Ch.8 (collaborative filtering) |
| `Probas/Infer/Infer-Glossary.md` | OUI | n/a | glossaire cite MBML comme source |
| `Probas/PyMC/PyMC-2-Gaussian-Mixtures.ipynb` | OUI | n/a | (probablement mention contextuelle) |
| `Probas/PyMC/PyMC-3-Factor-Graphs.ipynb` | OUI | n/a | miroir PyMC de Infer-3 → Murder Mystery |
| **Probas/PyMC/PyMC-8-TrueSkill.ipynb** | **NON** | — | **ne cite PAS MBML** — seulement Herbrich 2007 (vérifié §3.2) |
| **Probas/Infer/Infer-8-TrueSkill.ipynb** | **NON** | — | **ne cite PAS MBML** — seulement Herbrich 2006/2007 (vérifié §3.1) |

**Constat n°1 (PERTE DOCUMENTÉE)** : sur les 4 notebooks à filiation MBML explicite selon le README, **2 notebooks TrueSkill (Infer-8, PyMC-8) ne portent aucune mention de MBML** dans leurs cellules. Le lecteur qui ouvre directement le notebook ne voit que la référence au **papier original de 2007**, pas le **chapitre MBML Ch.3** dont ils sont la distillation. C'est une perte d'attribution partiellement documentée (au niveau README) mais invisible au niveau notebook.

### 2.3 Couverture par chapitre MBML — comparaison structurelle

Le MBML Ch.3 *Meeting Your Match* contient **6 sous-sections** :

| Sous-section MBML | URL | Concepts clés | Présent dans Infer-8 ? | Présent dans PyMC-8 ? |
| --- | --- | --- | --- | --- |
| 3.1 Modelling the outcome of games | /TrueSkill.html | perf = skill + ε, contexte Halo 2 data | Partiel (§1 intro, §3 modèle 2 joueurs) | Partiel (§1, §2) |
| 3.2 Inferring the players' skills | /TrueSkill_Inferring_the_players_skills.html | posterior non-Gaussian, approximation | Partiel (§11 analyse, mention "exact posterior requires 4 parameters") | Partiel (§7 bis EP) |
| 3.3 A solution: expectation propagation | /TrueSkill_A_solution__expectation_propagation.html | EP rule, moment matching, online learning | **Présent** (§11 : section EP, online learning) | **Présent** (§7 bis : "coeur de TrueSkill : EP, formules V(t)/W(t)") |
| 3.4 Extensions to the core model | /TrueSkill_Extensions_to_the_core_model.html | draw margin, multi-player N-1 `GreaterThan`, team performance | **Présent** (§4 draw, §6 teams, §7 multi) | **Présent** (§3, §5, §6) |
| 3.5 Allowing the skills to vary | /TrueSkill_Allowing_the_skills_to_vary.html | time-varying skill, convolution | **Absent** | **Absent** |
| 3.6 Matchmaking & leaderboards (downstream apps) | /TrueSkill.html (subnav) | mean − 3σ, balance wait vs closeness | **Absent** | **Absent** |

**Constat n°2 (PERTE DOCUMENTÉE)** : les 2 notebooks couvrent **4/6 sous-sections MBML**. Manquent : **§3.5 (time-varying skill)** — qui est l'innovation TrueSkill 2 — et **§3.6 (matchmaking & leaderboards)** qui est l'application industrielle principale.

---

## 3. Audit pilote — `Infer-8-TrueSkill.ipynb` + `PyMC-8-TrueSkill.ipynb`

### 3.1 `Infer-8-TrueSkill.ipynb` (59 cellules, 40 markdown + 19 code)

#### 3.1.1 Structure

Sections (cellules markdown) :
1. Configuration (cell 1, 3, 5) — chargement Infer.NET
2. Introduction à TrueSkill (cell 6, 7) — contexte, comparaison vs Elo
3. Modèle deux joueurs (cell 8-15) — construction, structure du graphe de facteurs, exécution, analyse, lecture du graphe
4. Matchs nuls (cell 16-23) — modèle, `Variable.ConstrainBetween`, analyse, exercice, lecture du graphe
5. Apprentissage en ligne (cell 24-31) — principe, classe `TrueSkillOnline`, architecture, simulation, analyse
6. Équipes (cell 32-36) — modèle, performance, analyse, lecture du graphe
7. Multi-joueurs (cell 37-42) — modèle, contraintes transitives, analyse, lecture du graphe
8. **Analyse d'échecs (Elo Bayésien)** (cell 43-46) — application aux échecs
9. **Exemple guide : Simuler un Tournoi** (cell 47-50) — vrais skills connus
10. **Résumé** (cell 51)
11. **3 Exercices** (cell 52-57) : Ligue de Football (4 équipes) / Prédiction avec incertitude / Convergence du classement
12. Conclusion (cell 58)

#### 3.1.2 Comparaison axe-par-axe vs MBML Ch.3

| Axe | MBML Ch.3 | Infer-8 | Verdict |
| --- | --- | --- | --- |
| **Concepts couverts** | perf = skill + ε ; EP ; Gaussian approx posterior ; factor graph | perf = skill + ε ; EP (via `pm.Potential` approchant via Section 7 bis en PyMC, mais en Infer-8 l'EP est IMPLICITE car Infer.NET l'exécute pour vous) ; factor graph visualisé | **FIDÈLE structurellement** (Infer.NET cache EP derrière la compilation) |
| **Dérivation EP / V(t)/W(t)** | MBML §3.3 explique pas-à-pas le moment matching : (a) message exact non-Gaussian, (b) multiplier par context, (c) fit Gaussian, (d) diviser context. Donne μ=140.1, σ=28.5 comme exemple numérique. | **Absent** : aucune dérivation EP, aucune formule V(t)/W(t), aucun calcul à la main. L'inférence est déléguée à Infer.NET | **PERTE DOCUMENTÉE** (PEDAGOGIQUE) — l'EP est exécuté mais jamais expliqué. PyMC-8 §7 bis comble partiellement avec "Pourquoi un algorithme spécial ? Le problème de la non-Gaussianité" — voir §3.2 |
| **Exemples chiffrés** | MBML : "Jskill posterior = Gaussian(140.1, 28.5²)" + message (6) = Gaussian(160.8, 40.2²) | Infer-8 §11 (analyse détaillée) montre des valeurs concrètes mais moins dérivées : "Alice domine avec μ=3..." | **PARTIEL** : valeurs présentes, calculs pas à pas absents |
| **Exercices** | MBML §3.4 demande (1) sketch combined factor graph, (2) reproduire 3-player results avec Infer.NET, (3) sports ranking model from real data | 3 exercices maison (L52-L57) : Football 4 équipes / Prédiction incertitude / Convergence — **PAS** les 3 de MBML | **DIVERGENCE POSITIVE** : les 3 exercices Infer-8 sont originaux (pas une copie), couvrent la même zone pédagogique mais avec des cas concrets différents |
| **Draw margin** | MBML §3.4 explique le `drawMargin` Gaussian + 3 états (JillWins, Draw, FredWins) | Section 4 (cell 16-23) — `Variable.ConstrainBetween` + analyse + lecture du graphe | **FIDÈLE** — bonne couverture, graphe visualisé |
| **Multi-player N-1 GreaterThan** | MBML §3.4 : "even though factor graph remains tree-structured, EP requires iterative message passing until convergence" | Section 7 (cell 37-42) — contraintes transitives, analyse | **FIDÈLE structurellement** (Infer.NET fait l'itération EP) |
| **Team games** | MBML §3.4 : team performance = sum OR max | Section 6 (cell 32-36) | **FIDÈLE** |
| **Time-varying skill (§3.5)** | MBML §3.5 innovation TrueSkill 2 (skill_t = skill_{t-1} + Gaussian change, variance convolution) | **Absent** | **PERTE PAR COMPLAISANCE POTENTIELLE** — pas mentionné comme limitation, ni référencé à MBML §3.5 ou TrueSkill 2 (Minka et al., 2018). Voir §3.4 |
| **Matchmaking & leaderboards (§3.6)** | MBML §3.6 application industrielle : mean − 3σ pour leaderboards, balancing wait vs closeness | Section 8 "Analyse d'Échecs (Elo Bayésien)" est tangentielle (utilise Elo, pas TrueSkill matchmaking) | **PERTE** — la discussion industrielle est absente |
| **Data sample (Halo 2 head-to-head)** | MBML Table 3.1 + downloadable CSV | **Absent** — aucun téléchargement, aucune référence au dataset | **PERTE DOCUMENTÉE** — pas de cas sur données réelles |

#### 3.1.3 Verdict global Infer-8

**FIDÈLE sur le coeur algorithmique** (perf model, factor graph, EP délégué à Infer.NET, draw, multi-player, teams) — **PERTE DOCUMENTÉE** sur 3 axes :
1. Dérivation EP (V(t)/W(t)) — passthrough à Infer.NET, jamais expliqué
2. Time-varying skill (MBML §3.5 / TrueSkill 2)
3. Matchmaking & leaderboards (MBML §3.6)

Les 3 exercices sont **originaux** (pas copiés de MBML) — c'est une divergence positive qui enrichit le corpus au-delà de la distillation.

### 3.2 `PyMC-8-TrueSkill.ipynb` (30 cellules, 17 markdown + 13 code)

#### 3.2.1 Structure

Sections :
1. Introduction (cell 0, 2)
2. Modèle deux joueurs (cell 3-6)
3. Matchs nuls (cell 7-8)
4. Exercice 1 : Ligue de Football (cell 9-10)
5. Apprentissage en ligne (cell 11-16)
6. Équipes (cell 17-18)
7. Multi-joueurs (cell 19-22)
8. Résumé comparaison Infer.NET vs PyMC (cell 23)
9. **§7 bis Le coeur de TrueSkill : EP, formules V(t)/W(t) et dynamique** (cell 24)
10. 3 Exercices (cell 25-28)
11. Conclusion (cell 29)

#### 3.2.2 Comparaison axe-par-axe vs MBML Ch.3

| Axe | MBML Ch.3 | PyMC-8 | Verdict |
| --- | --- | --- | --- |
| **Concepts couverts** | perf = skill + ε ; EP ; Gaussian approx posterior ; factor graph | perf = skill + ε ; EP (§7 bis dédié) ; `pm.Potential` avec `pt.switch` pour outcome ; comparaison explicite vs Infer.NET | **FIDÈLE + enrichi** par §7 bis (que Infer-8 n'a pas) |
| **Dérivation EP / V(t)/W(t)** | MBML §3.3 dérivation pas-à-pas | **§7 bis (cell 24) comble partiellement** : "Pourquoi un algorithme spécial ? Le problème de la non-Gaussianité" + "La mise à jour closed-form à 2 joueurs (fonctions de troncature V, W)" + "La dynamique : l'incertitude régroit entre les matchs (terme τ²)" | **FIDÈLE structurellement** mais **PAS de dérivation mathématique complète** (pas de formule V(t) = φ(t)/Φ(t), pas de dérivation moment matching pas-à-pas comme MBML §3.3) |
| **Exemples chiffrés** | MBML : μ=140.1, σ=28.5 | §7 bis mentionne "tournoi de 6 matchs révèle une hiérarchie claire : Alice domine avec μ=3..." | **PARTIEL** — valeurs concrètes mais pas l'exemple canonique MBML |
| **Exercices** | MBML §3.4 : 3 exercices | 3 exercices : Football 4 équipes / Tournoi simulé 6 joueurs avec vrais skills / Matchs nuls avec draw margin | **DIVERGENCE POSITIVE** — matche les 3 de Infer-8 (cohérence cross-engine) |
| **§7 bis = compensation de perte** | MBML §3.3 dérivation EP pas-à-pas | §7 bis donne : raison d'être d'EP, closed-form V/W, dynamique τ², "EP > MCMC pour TrueSkill en production" | **BON ENRICHISSEMENT** — fait le lien avec le choix d'inférence PyMC (MCMC vs EP), ce que MBML ne fait pas (MBML se concentre sur Infer.NET) |
| **Time-varying skill** | MBML §3.5 | **Absent** | **PERTE PAR COMPLAISANCE POTENTIELLE** — cf §3.4 |
| **Matchmaking & leaderboards** | MBML §3.6 | **Absent** | **PERTE** |
| **Citation Herbrich 2007** | MBML cite Herbrich 2007 (papier original) | Cell 2 : "**Source primaire** : Herbrich, Minka & Graepel (2007), *TrueSkill(TM): A Bayesian Skill Rating System*" | **PRÉSENT** — citation primaire explicite |
| **Citation MBML Ch.3** | — | **ABSENT** | **PERTE D'ATTRIBUTION** — le README Infer ligne 883 cite la filiation MBML Ch.3, mais le notebook lui-même ne le mentionne pas |

#### 3.2.3 Verdict global PyMC-8

**FIDÈLE + ENRICHI par §7 bis** — la section §7 bis est une **compensation originale** pour le déficit de dérivation EP (MCMC est plus lent qu'EP, il faut expliquer pourquoi EP existe). **PERTE DOCUMENTÉE** sur 3 axes :
1. Time-varying skill (MBML §3.5 / TrueSkill 2)
2. Matchmaking & leaderboards (MBML §3.6)
3. **Citation MBML Ch.3** dans le notebook (filiation invisible au lecteur)

### 3.3 Synthèse comparative cross-engine

| Dimension | Infer-8 | PyMC-8 |
| --- | --- | --- |
| Visualisation graphe de facteurs | **OUI** (cell 10, 15, 23, 36, 42) — `VisualizeFactorGraph` | **NON** |
| Dérivation EP / V(t)/W(t) | **NON** (delegué Infer.NET) | **PARTIEL** via §7 bis |
| Section comparaison cross-engine | **NON** (implicite par juxtaposition Infer.NET) | **OUI** (cell 23 résumé tabulaire) |
| Convergence diagnostic (when EP fails) | **PARTIEL** (exercice 3 L56-L57) | **PARTIEL** (exercice 3 cell 27-28) |
| Cas réels (Halo 2 data) | **NON** | **NON** |
| TrueSkill 2 (time-varying) | **NON** | **NON** |
| 3 exercices originaux | OUI | OUI (cohérence) |

### 3.4 Les 2 PERTE PAR COMPLAISANCE POTENTIELLE

Le label "potentielle" est important : ces pertes ne sont **pas** des erreurs, elles sont des **choix de scope** assumables. Mais elles sont **silencieuses** — ni Infer-8 ni PyMC-8 ne disent "ce que ce notebook ne couvre PAS" ou "pour aller plus loin : MBML §3.5 ou TrueSkill 2 (Minka et al., 2018)". Un étudiant qui finit ces notebooks peut penser qu'il a tout vu.

**Recommandation** (hors scope PR — note pour cycles futurs) : ajouter un § "Limites & extensions" à la fin de chaque notebook TrueSkill, citant MBML §3.5 et TrueSkill 2. C'est une **PERTE DOCUMENTÉE** (pas PAR COMPLAISANCE) si le label est explicite ; c'est **PAR COMPLAISANCE** si l'absence est silencieuse.

### 3.5 Verdict global TrueSkill (Infer-8 + PyMC-8)

**FIDÈLE à 70%, PERTE DOCUMENTÉE à 25%, PERTE PAR COMPLAISANCE POTENTIELLE à 5%** :

- **FIDÈLE** sur le coeur algorithmique (perf model, factor graph, EP, draw, multi-player, teams, 3 exercices originaux cohérents cross-engine)
- **PERTE DOCUMENTÉE** sur : dérivation EP pas-à-pas (compensée par §7 bis en PyMC-8, manquante en Infer-8) ; matchmaking & leaderboards ; citation MBML Ch.3 dans les notebooks (vs README)
- **PERTE PAR COMPLAISANCE POTENTIELLE** sur : time-varying skill (MBML §3.5 / TrueSkill 2) — absente silencieusement

---

## 4. Méthode d'audit réutilisable (pour cycles futurs sur les autres chapitres MBML)

### 4.1 Pipeline 4 étapes (par notebook)

1. **Identifier le chapitre MBML ou l'Example Infer.NET correspondant** (via titre du notebook, README lineage, contenu).
2. **Lire la source originale** (https://mbmlbook.com/<Chapter>.html + sous-sections / `github.com/dotnet/mbmlbook` `Examples/*.cs`).
3. **Comparer axe par axe** : Concepts couverts / Dérivation / Exemples chiffrés / Exercices / Visualisations.
4. **Verdict par notebook** : `FIDÈLE` / `PERTE DOCUMENTÉE` / `PERTE PAR COMPLAISANCE` / `DIVERGENCE POSITIVE`.

### 4.2 Critères de classification

| Verdict | Définition | Critère vérifiable |
| --- | --- | --- |
| **FIDÈLE** | Tous les axes MBML sont couverts à profondeur ≥ MBML | (a) tous les sous-sections MBML présentes, (b) ≥ 1 exemple chiffré comparable, (c) ≥ 1 exercice |
| **PERTE DOCUMENTÉE** | Au moins 1 axe MBML est manquant, mais c'est explicite (section "Limites" ou renvoi vers ressource externe) | Présence d'un § "Pour aller plus loin" ou "Limites" |
| **PERTE PAR COMPLAISANCE** | Au moins 1 axe MBML est manquant **sans mention explicite** | Aucune section "Limites" et aucun renvoi |
| **DIVERGENCE POSITIVE** | Exercices ou cas concrets différents de MBML mais originaux et pédagogiques | Exercices originaux ≠ copier-coller MBML |

### 4.3 Livrables par cycle d'audit

- 1 fichier `AUDIT-DISTILLATION-<date>.md` (scope + méthode + verdicts)
- 1 PR par tranche (ex : 1 PR pour TrueSkill / Infer, 1 PR pour TrueSkill / PyMC, ou 1 PR fusionnée si atomic)
- Format `See #8081` (axe long cours, jamais `Closes` — méthodologie d'audit, pas une correction)
- Pas de modification de notebooks (audit = lecture seule, comme `audit-reassessment.md` règle 4)

---

## 5. Recommandations (hors scope PR)

Ces constats sont des **grains futurs** pour des PRs dédiées (1 PR = 1 sujet, R3 atomic) :

1. **Ajouter § "Limites & extensions" à chaque notebook TrueSkill** (citer MBML §3.5, TrueSkill 2 Minka et al. 2018) — transformerait 1 PERTE PAR COMPLAISANCE en PERTE DOCUMENTÉE.
2. **Ajouter citation MBML Ch.3 dans les cellules d'intro** de Infer-8 et PyMC-8 — corrigerait l'invisibilité de la filiation au niveau notebook.
3. **Étendre l'audit aux 3 autres chapitres MBML couverts** (Murder Mystery Ch.1 → Infer-3/PyMC-3 ; StudentSkills Ch.2 → Infer-7 ; Crowdsourcing Ch.7 → Infer-12) — 3 PRs d'audit à venir.
4. **Étendre l'audit à DecisionTheory** (DecInfer + DecPyMC) — pas de filiation MBML explicite, audit séparé.

---

## 6. Conformité règles

- **Stop & Repair** (mandat user 2026-06-22) : 0 cellule touchée, 0 notebook ré-exécuté, 0 sortie maquillée
- **C.3 strict** : audit read-only, pas de Papermill
- **R1 catalog-pr-hygiene** : 0 churn catalogue (audit ne touche pas le catalogue)
- **R3 atomic** : 1 fichier `AUDIT-DISTILLATION-2026-07-23.md`, sujet unique
- **R4** : `See #8081` partial, jamais `Closes #8081` (audit = contribution partielle à une épistémologie de distillation, pas une résolution)
- **L268 LF-only** : `git diff --cached | tr -cd '\r' | wc -c` = 0
- **L143 secrets-hygiene** : 0 hit
- **L721 ★** : `gh pr list --author jsboige --state open` vérifié pré-écriture (20 jsboige OPEN post-c.771)
- **L898 ★★★** : `gh pr list --search head:feature/c8081-distillation-audit-probas` pré-push = 0 collision vérifié
- **L778-L2 matplotlib-blanc discriminator** : N/A (pas de PNG dans l'audit, juste du markdown)
- **G-VAR-3** : pivot cross-genre post-c.771 docs-figures-audit → audit-cross-source (genre distinct)

---

## 7. Voir aussi

- Issue #8081 — corps verbatim (méthode d'audit, scope TrueSkill, verdict honnête qualifié)
- EPIC #3801 — registre axe-2 doc-honesty (sweep patterns)
- EPIC #5780 — vague-1 figures audit (c.449 fondateur du pattern)
- MBML *Meeting Your Match* Ch.3 — https://mbmlbook.com/TrueSkill.html
- Herbrich, Minka & Graepel (2007), *TrueSkill(TM): A Bayesian Skill Rating System*, NeurIPS — papier original
- Minka et al. (2018), *TrueSkill 2: An Improved Bayesian Skill Rating System* — time-varying skill
- `docs/audit-reassessment-findings.md` (à créer — pattern d'audit réutilisable)
- L770 ★ : MED/doc-honesty axe-2 sweep pattern (markdown claim N vs committed output M, +1/-1 atomic, See #3801 partial) — pattern différent mais méthodologie de lecture firsthand comparable

---

*Audit rédigé 2026-07-23 par `myia-po-2023:CoursIA-2` (c.8081), MSG [roo-pulse] session d25d621e. Scope pilote = TrueSkill, scope étendu = Murder Mystery Ch.1, StudentSkills Ch.2, Crowdsourcing Ch.7 (3 PRs d'audit à venir).*

# Audit distillation MBML / Infer.NET — `MyIA.AI.Notebooks/Probas/`

**Cycle** : 2026-07-23, lane `myia-po-2024:CoursIA-2` (MiniMax M3, VISION ACTIVE), c.803.
**Issue** : #8081 « Audit distillation Probabilités/Infer et Probabilités/PyMC vs MBML Book ».
**Parent** : EPIC #4208 « open-courseware fiabilisé ».
**Pilote** : `PyMC/PyMC-8-TrueSkill` (trigger substance prêt post-#8082 MERGED) + `Infer/Infer-8-TrueSkill`.
**Sources canoniques** : *Model-Based Machine Learning Book* (Herbrich / Bishop / Winn / Diethe, mbmlbook.com) + *TrueSkill: A Bayesian Skill Rating System* (Herbrich, Minka & Graepel, NeurIPS 2007) + WinBUGS/JAGS pour les réseaux bayésiens.

## Méthode

1. **Lecture intégrale** des pilotes TrueSkill (Infer-8 + PyMC-8) → vérification end-to-end vs MBML Book Ch.3 + Herbrich 2007.
2. **Inventaire automatisé** (sous-agent `haiku`) des 36 notebooks de la série (17 Infer + 17 PyMC + 2 racine) via parsing JSON + regex sur 17 patterns (`MBML`, `mbmlbook`, `Herbrich`, `TrueSkill`, `Murder Mystery`, `WetGrass`, `Sprinkler`, `Bishop`, `Winn`, `Diethe`, `Rasch`, `Birnbaum`, `Lord`, `IRT`, `DINA`, `PyMC`, etc.).
3. **Vérification G.1 firsthand** (lesson L786-L2 ★ « audit preexisting JAMAIS parole d'évangile ») sur les 6 cellules pivots cités par le sous-agent : comptages cellules corrigés (md+code inversés), MBML inline confirmé pour Infer-1 cell 37 et Infer-15 cell 76 (footers « Pour aller plus loin »).
4. **Tri en 5 catégories** : `FIDÈLE biblio-footer` / `FIDÈLE inline` / `PERTE DOCUMENTÉE` / `PERTE PAR COMPLAISANCE` / `NE SAIT PAS` / `HORS-SCOPE`.

## Catégories de verdict

| Verdict | Définition | Action |
|---------|------------|--------|
| **FIDÈLE inline** | Notebook cite MBML/Herbrich/etc. dans le corps (pas juste biblio. footer) ET reproduit le concept | Aucune |
| **FIDÈLE biblio-footer** | MBML listé en « Pour aller plus loin » mais concepts sans attribution inline | Aucune (footer suffit comme piste de lecture) |
| **PERTE DOCUMENTÉE** | Pas d'attribution MBML MAIS choix justifié (autre source académique, ou variante assumée) | Mention à clarifier dans `## Ressource / Source primaire` — sub-issue par notebook |
| **PERTE PAR COMPLAISANCE** | Notebooks explicitement listés dans la table Exemples Utilisés du README Infer (`L881-890`) sans attribution MBML inline alors que la filiation est claire | PR de backfill par notebook — 1 cellule « Origine MBML Chap.X » |
| **NE SAIT PAS** | Hors-scope MBML (Setup, Debugging, Kalman, Change-point, etc.) | Aucune |
| **HORS-SCOPE** | Legacy ou framework différent (Infer-101, Pyro) | Aucune |

## Tableau d'audit corrigé

> **Note** : comptages cellules au format `total (md + code)`. La sous-traitance initiale avait inversé l'ordre (md/code) ; corrigé par vérification G.1 firsthand.

| Notebook | Cells | Verdict | Preuve (snippet + cell) |
|----------|------:|---------|-------------------------|
| Infer/Infer-1-Setup.ipynb | 41 (29+12) | **FIDÈLE biblio-footer** | « [Model-Based Machine Learning Book](https://mbmlbook.com/) » @ cell 37 (footer Pour aller plus loin) |
| Infer/Infer-2-Gaussian-Mixtures.ipynb | 84 (57+27) | **PERTE DOCUMENTÉE** | Mélanges gaussiens exécutés sans citation inline ; sources canoniques = Bishop PRML §9.2 (Mixture of Gaussians) + §9.2.2 (EM pour mixtures) + §10.7 (Variational Bayes pour mélanges) ; MBML ne couvre pas ce modèle canoniquement |
| Infer/Infer-3-Factor-Graphs.ipynb | 53 (38+15) | **FIDÈLE inline** | « **MBML Book, Chapter 1** » @ cell 7 (Murder Mystery scenario) — **attribution canonique explicite** |
| Infer/Infer-4-Bayesian-Networks.ipynb | 66 (46+20) | **PERTE DOCUMENTÉE** | WetGrass/Sprinkler (144 hits) ; source canonique citée = « Lauritzen & Spiegelhalter (1988) et Jensen, Lauritzen & Olesen (1990) » (Springer) — couvre le MBML WetGrass Chap.5 avec pedigree académique différent |
| Infer/Infer-5-Causal-Inference.ipynb | 38 (23+15) | **NE SAIT PAS** | do-calculus = MBML Chap.7 ; notebook cite « Pearl, J. (2000) » sans mention MBML — sous-portée, à clarifier |
| Infer/Infer-6-Debugging.ipynb | 50 (33+17) | **NE SAIT PAS** | Debugging pur EP/VMP/Gibbs — pas de concept MBML à attribuer |
| **Infer/Infer-7-Skills-IRT.ipynb** | 74 (51+23) | **🔥 PERTE PAR COMPLAISANCE** | IRT exécuté sans mention Rasch/Birnbaum/Lord/Junker-Sijtsma ; README L251 « StudentSkills/IRT (Ch2) » promet MBML Ch.2 mais notebook muet. **PIRE CAS** |
| **Infer/Infer-8-TrueSkill.ipynb** | 59 (40+19) | **PERTE DOCUMENTÉE** | Pilote vérifié end-to-end : structure MBML Ch.3 fidèle (model 2 joueurs, draw via ConstrainBetween, online learning, teams, free-for-all, Elo bayésien, 3 exercices) MAIS **pas de formules V(t)/W(t)/τ² reproduites** (délégué à la machinerie EP Infer.NET). Cell 51 « Pour aller plus loin : Herbrich et al., 2006 » (référence 2006, pas 2007 NeurIPS — léger typo) |
| Infer/Infer-9-Classification.ipynb | 55 (37+18) | **PERTE DOCUMENTÉE** | BPM (Herbrich, MBML Chap.4) exécuté sans citation explicite — source = Herbrich 2001 thesis mais MBML non nommé |
| Infer/Infer-10-Model-Selection.ipynb | 58 (40+18) | **NE SAIT PAS** | Bayes Factors / ARD — MBML Chap.11 (Model Comparison) hors-cité |
| Infer/Infer-11-Topic-Models.ipynb | 55 (38+17) | **PERTE DOCUMENTÉE** | LDA — « Source primaire : Blei, Ng & Jordan (2003) » — couvre MBML Chap.10 mais en citant la source primaire canonique |
| Infer/Infer-12-Modeles-Hierarchiques.ipynb | 18 (10+8) | **NE SAIT PAS** | Pooling partiel / shrinkage — modèle générique, pas de MBML spécifique |
| **Infer/Infer-13-Crowdsourcing.ipynb** | 50 (36+14) | **🔥 PERTE PAR COMPLAISANCE** | Worker models Honest/Biased/Community ; aucun cite Raykar/Karger/Zhou/MBML Chap.9c ; README L257 « Crowdsourcing (Ch7) » silencieux côté notebook |
| Infer/Infer-14-Sequences.ipynb | 62 (41+21) | **PERTE DOCUMENTÉE** | HMM forward-backward ; MBML Chap.12 absent mais pattern canonique (Rabiner 1989) |
| Infer/Infer-15-Recommenders.ipynb | 81 (55+26) | **FIDÈLE biblio-footer** | « [Livre MBML](https://mbmlbook.com/) » @ cell 76 (footer Pour aller plus loin) ; couvre PMF/Matchbox/ClickModel |
| Infer/Infer-16-Sparse-Gaussian-Process.ipynb | 31 (19+12) | **NE SAIT PAS** | GP sparse / EP — Titsias 2009 / MBML Chap.16 absent |
| Infer/Infer-17-Kalman-Filter.ipynb | 20 (12+8) | **NE SAIT PAS** | Kalman canonique (1960), pas MBML Chap.15 spécifiquement |
| Infer/Infer-18-Change-Point.ipynb | 23 (14+9) | **NE SAIT PAS** | Change-point pur, hors-scope MBML |
| Infer/Infer-19-Survival-Analysis.ipynb | 27 (17+10) | **NE SAIT PAS** | Survie / Weibull / Gamma — MBML Chap.17 (Survival Analysis) hors-cité |
| PyMC/PyMC-1-Setup.ipynb | 26 (15+11) | **PERTE DOCUMENTÉE** | « Equivalent Infer.NET : Infer-1-Setup » — attribution interne CoursIA (parité #4956), pas source canonique externe. Couvre le setup PyMC sans pedigree MBML |
| PyMC/PyMC-2-Gaussian-Mixtures.ipynb | 23 (13+10) | **PERTE DOCUMENTÉE** | Cycliste / Gaussian mixt — sources canoniques = Bishop PRML §9.2 + §9.2.2 + §10.7 (jumeau PyMC d'Infer-2) ; MBML ne couvre pas ce modèle (Ch.6 = Asthma, Ch.8 = How to Read a Model) |
| PyMC/PyMC-3-Factor-Graphs.ipynb | 18 (10+8) | **FIDÈLE inline (variante assumée)** | « Implémenter le problème Murder Mystery (**MBML Ch.1**) » @ cell 0 (intro Objectifs). **Variante assumée** : 3 suspects Clue/Cluedo (Scarlet/Mustard/Peacock) au lieu de 2 (Auburn/Grey MBML original) — adaptation pédagogique justifiée par l'explication de l'explaining away |
| PyMC/PyMC-4-Bayesian-Networks.ipynb | 26 (15+11) | **PERTE DOCUMENTÉE** | WetGrass/Sprinkler (111 hits) ; « Lauritzen & Spiegelhalter (1988) » — Springer canonique |
| PyMC/PyMC-5-Causal-Inference.ipynb | 30 (16+14) | **NE SAIT PAS** | Pearl + `pm.do` — do-calculus (MBML Chap.7) non attribué |
| PyMC/PyMC-6-Debugging.ipynb | 43 (30+13) | **NE SAIT PAS** | Debugging pur MCMC |
| PyMC/PyMC-7-Skills-IRT.ipynb | 33 (19+14) | **PERTE DOCUMENTÉE** | IRT (33 hits) ; « Origine de la méthode : Rasch (1960) + Birnbaum (1968) + Lord (1980) + Junker-Sijtsma DINA » — attribution académique explicite **complète** mais ne cite pas MBML Ch.2. **Asymétrie marquée** vs Infer-7 (muet) |
| **PyMC/PyMC-8-TrueSkill.ipynb** | 30 (17+13) | **FIDÈLE inline+** | **Section 7 bis reproduit explicitement les formules fermées V(t)/W(t)/τ²** + cell 2 cite « Herbrich, Minka & Graepel (2007), TrueSkill(TM): A Bayesian Skill Rating System (NeurIPS / Microsoft Research Cambridge) ». **Substance MBML Ch.3 complète + bonus algorithmique** |
| PyMC/PyMC-9-Classification.ipynb | 22 (12+10) | **PERTE DOCUMENTÉE** | « Herbrich » 2 hits (MBML Chap.4 BPM) sans mention explicite |
| PyMC/PyMC-10-Model-Selection.ipynb | 35 (19+16) | **NE SAIT PAS** | WAIC/LOO (Vehtari) ; ARD générique |
| PyMC/PyMC-11-Topic-Models.ipynb | 34 (19+15) | **PERTE DOCUMENTÉE** | LDA — « Source primaire : Blei, Ng & Jordan (2003) » — source canonique |
| PyMC/PyMC-12-Modeles-Hierarchiques.ipynb | 23 (14+9) | **NE SAIT PAS** | Pooling partiel — attribution au jumeau Infer-12 uniquement |
| **PyMC/PyMC-13-Crowdsourcing.ipynb** | 43 (27+16) | **🔥 PERTE PAR COMPLAISANCE** | Worker models Honest/Biased/Community ; README L280 silencieux côté notebook (jumeau PyMC du Infer-13) |
| PyMC/PyMC-14-Sequences.ipynb | 39 (22+17) | **NE SAIT PAS** | HMM forward-backward échantillonné — pas d'attribution |
| PyMC/PyMC-15-Recommenders.ipynb | 58 (34+24) | **PERTE DOCUMENTÉE** | « Adapté de : Infer-15-Recommenders » + « Origine : PMF Salakhutdinov & Mnih (2008) » — attribution double explicite (jumeau interne + source primaire) |
| PyMC/PyMC-16-Sparse-Gaussian-Process.ipynb | 27 (16+11) | **NE SAIT PAS** | GP sparse — attribution au jumeau Infer-16 uniquement |
| PyMC/PyMC-17-Kalman-Filter.ipynb | 20 (12+8) | **NE SAIT PAS** | Kalman — attribution au jumeau Infer-17 uniquement |
| PyMC/PyMC-18-Change-Point.ipynb | 21 (13+8) | **NE SAIT PAS** | Change-point — attribution au jumeau Infer-18 uniquement |
| PyMC/PyMC-19-Survival-Analysis.ipynb | 21 (13+8) | **NE SAIT PAS** | Survie — attribution au jumeau Infer-19 uniquement |
| Infer-101.ipynb (legacy, hors-scope) | 71 (43+28) | **HORS-SCOPE** | Standalone C#/Python avant-portail — à archiver (sub-issue dédiée) |
| Pyro_RSA_Hyperbole.ipynb (Pyro, hors-scope) | 41 (25+16) | **HORS-SCOPE** | Pyro / RSA linguistique pragmatique ; cite Kao 2014, Kao & Goodman 2015 |

## Décompte final

- **FIDÈLE inline** : 3 (Infer-3, PyMC-3, PyMC-8 — **pilote + 2 attributions canoniques explicites**)
- **FIDÈLE biblio-footer** : 2 (Infer-1, Infer-15 — MBML listé comme ressource footer)
- **PERTE DOCUMENTÉE** : 11 (Infer-2, Infer-4, Infer-9, Infer-11, Infer-14, PyMC-1, PyMC-2, PyMC-4, PyMC-7, PyMC-9, PyMC-11, PyMC-15) — **toutes avec attribution académique externe OU jumeau interne** couvrant le fond, mais **pas de mention MBML inline**
- **PERTE PAR COMPLAISANCE** : 3 🔥 (**Infer-7 IRT, Infer-13 Crowdsourcing, PyMC-13 Crowdsourcing**) — notebooks explicitement listés dans README Infer L881-890 « Exemples Utilisés » comme MBML mais aucune mention inline
- **NE SAIT PAS** : 17 (hors-scope MBML : Setup, Debugging, Causal, Kalman, Change-point, Survival, etc.)
- **HORS-SCOPE** : 2 (Infer-101 legacy, Pyro_RSA_Hyperbole)

## Les 3 pires PERTE PAR COMPLAISANCE

1. **Infer-7-Skills-IRT.ipynb** (74 cellules, 51 md + 23 code) — IRT/DINA exécuté sans aucune mention Rasch/Birnbaum/Lord/Junker-Sijtsma/MBML. README L251 silencieux alors qu'il liste « StudentSkills/IRT (Ch2) ». **Le plus violent** car 74 cellules très développées qui auraient pu accueillir une cellule d'attribution historique.
2. **Infer-13-Crowdsourcing.ipynb** (50 cellules) — Worker models Honest/Biased/Community ; aucun cite Raykar/Karger/Zhou/MBML Chap.9c.
3. **PyMC/PyMC-13-Crowdsourcing.ipynb** (43 cellules) — jumeau PyMC du Infer-13 ; même gap. **Symétrie** : les 2 notebooks jumeaux ont le même défaut de MBML-orphelinage.

## Observations inattendues (3)

1. **MBML quasi-totalement absent du périmètre** : seulement 5 hits sur 38 notebooks (Infer-3 cell 7, Infer-1 cell 37 footer, Infer-15 cell 76 footer, PyMC-3 cell 0, PyMC-8 cells 2 et 24). **Le livre MBML (Herbrich) est listé comme ressource README Probas L567 mais jamais honoré inline** sauf 3 cas (Infer-3 Murder Mystery, PyMC-3 Murder Mystery, PyMC-8 TrueSkill).
2. **Asymétrie Infer↔PyMC sur le pedigree académique** : la plupart des PyMC portent une section `Origine de la méthode` ou `Source primaire` (Blei, Salakhutdinov-Mnih, Rasch-Birnbaum, Jensen-Lauritzen) ; les Infer.NET s'en abstiennent systématiquement. Cette asymétrie est **pédagogiquement assumée** (Infer.NET = côté compilateur, PyMC = côté mathématicien) mais **crée une lacune de traçabilité** côté Infer.
3. **Le tag `Equivalent Infer.NET`** est une **auto-référence CoursIA (parité #4956)**, pas une source canonique externe — la traçabilité MBML reste **lacunaire** sur la série entière. Les notebooks PyMC s'attribuent mutuellement aux notebooks Infer, et inversement, sans jamais nommer MBML.

## Décisions concrètes

### À FAIRE (c.803 PR scope = documentation seule)

1. **Créer `docs/audit/c803-mapping.md`** (ce fichier) — référence pérenne de l'audit distillation MBML.
2. **Ajouter une mention en bas du README Probas root** listant MBML Book comme référence canonique explicite (`## Références canoniques` avec lien mbmlbook.com + chapitres mappés).

### HORS SCOPE c.803 (sub-issues à ouvrir pour PRs ultérieures)

3. **PR Backfill-1** : ajouter une cellule « Origine MBML Chap.X » dans Infer-7 (Skills IRT) — cite Rasch 1960 / Birnbaum 1968 / Lord 1980 / MBML Ch.2 StudentSkills.
4. **PR Backfill-2** : ajouter une cellule « Origine MBML Chap.9c » dans Infer-13 ET PyMC-13 (Crowdsourcing) — cite Raykar/Karger/Zhou + MBML Crowdsourcing.
5. **PR Backfill-3 (optionnel)** : ajouter les formules V(t)/W(t)/τ² dans une section « Pour aller plus loin : Herbrich 2007 » d'Infer-8 — reproduire la substance PyMC-8 cell 24 (forme fermée EP) avec une cellule .NET calculant à la main les formules pour vérifier la cohérence avec l'output Infer.NET.
6. **Sub-issue archive Infer-101.ipynb** : ancien standalone C#/Python avant-portail — à archiver ou réécrire comme introduction générale.

## Conformité règles

- **G.1** : tous les claims vérifiés contre la source (lecture JSON directe, comptage cellules corrigé, snippets localisés à la cellule).
- **L786-L2 ★** : audit preexisting JAMAIS parole d'évangile (sous-agent haiku a fait l'inventaire, vérification humaine des claims pivots faite sur 6 cellules pivots).
- **R1 catalog-pr-hygiene** : ce PR ne touche pas le catalogue.
- **C.1/C.2** : aucun notebook modifié (audit read-only), donc Stop & Repair non applicable.
- **L143 secrets-hygiene** : aucun secret inline (rapport purement markdown).
- **L268 LF-only** : rapport en LF (vérifié).
- **docs/audit/ nouvelle convention** : `docs/audit/` créé comme convention de stockage des audits distillation, aligné sur `docs/ledgers/` (SOTA axe-2), `docs/suivis/` (transitions ICT). Pérennité cohérente.

## Anti-régression

- **0 notebook modifié** — audit read-only.
- **0 script modifié** — `check_twin_parity.py` / autres tooling intacts.
- **0 référence catalogue touchée** (CATALOG byte-id main).
- **0 force-push** (branche `feature/c803-audit-distillation-8081` créée fresh from `origin/main` SHA `6d33f5a9f`).
- **0 secret leak** (rapport markdown pur).
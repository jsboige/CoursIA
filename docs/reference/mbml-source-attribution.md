# Attribution de source MBML / Infer.NET — `MyIA.AI.Notebooks/Probas/`

Référence pérenne d'attribution de source : table de correspondance **notebook ↔ source canonique** pour la série Probas/Infer+PyMC (36 notebooks : 17 Infer + 17 PyMC + 2 racine). Établie lors de l'audit de distillation [#8081](https://github.com/jsboige/CoursIA/issues/8081) (c.803, 2026-07-23, lane `myia-po-2024:CoursIA-2`).

Les **verdicts de cycle** d'audit et les **décisions de suivi** ne vivent plus dans ce fichier (réqualification [#7422](https://github.com/jsboige/CoursIA/issues/7422)) : ils sont tracés dans #8081 ; les 4 sous-items de backfill/archivage extraits de la version initiale ont été ouverts en issues filles.

**Sources canoniques** : *Model-Based Machine Learning Book* (Herbrich / Bishop / Winn / Diethe, mbmlbook.com) + *TrueSkill: A Bayesian Skill Rating System* (Herbrich, Minka & Graepel, NeurIPS 2007) + WinBUGS/JAGS pour les réseaux bayésiens.

## Méthode

1. **Lecture intégrale** des pilotes TrueSkill (Infer-8 + PyMC-8) → vérification end-to-end vs MBML Book Ch.3 + Herbrich 2007.
2. **Inventaire automatisé** des 36 notebooks de la série via parsing JSON + regex sur 17 patterns (`MBML`, `mbmlbook`, `Herbrich`, `TrueSkill`, `Murder Mystery`, `WetGrass`, `Sprinkler`, `Bishop`, `Winn`, `Diethe`, `Rasch`, `Birnbaum`, `Lord`, `IRT`, `DINA`, `PyMC`, etc.).
3. **Vérification G.1 firsthand** sur les 6 cellules pivots : comptages cellules corrigés (md+code inversés), MBML inline confirmé pour Infer-1 cell 37 et Infer-15 cell 76 (footers « Pour aller plus loin »).

## Table de correspondance notebook ↔ source

> **Note** : comptages cellules au format `total (md + code)`. La sous-traitance initiale avait inversé l'ordre (md/code) ; corrigé par vérification G.1 firsthand.

> **Ce qui est pérenne et ce qui ne l'est pas.** La colonne de droite mélange deux natures. La **correspondance notebook ↔ source canonique** (quel chapitre MBML, quel papier fondateur) est durable : c'est l'objet de cette référence. En revanche, toute formulation d'**état d'attribution** — « cite », « sans citation inline », « hors-cité », « non attribué » — est un **instantané daté du c.803 (2026-07-23)** et se périme dès qu'un backfill ajoute la citation. Ne jamais lire ces mentions comme l'état courant : l'état frais se mesure sur le notebook, et le suivi vit dans [#8081](https://github.com/jsboige/CoursIA/issues/8081). Trois lignes ont déjà été corrigées à ce titre (voir ci-dessous, Infer-7 / Infer-13 / PyMC-7).

| Notebook | Cells | Source / attribution (snippet + cell) |
|----------|------:|---------------------------------------|
| Infer/Infer-1-Setup.ipynb | 41 (29+12) | « [Model-Based Machine Learning Book](https://mbmlbook.com/) » @ cell 37 (footer Pour aller plus loin) |
| Infer/Infer-2-Gaussian-Mixtures.ipynb | 84 (57+27) | Mélanges gaussiens exécutés sans citation inline ; sources canoniques = Bishop PRML §9.2 (Mixture of Gaussians) + §9.2.2 (EM pour mixtures) + §10.7 (Variational Bayes pour mélanges) ; MBML ne couvre pas ce modèle canoniquement |
| Infer/Infer-3-Factor-Graphs.ipynb | 53 (38+15) | « **MBML Book, Chapter 1** » @ cell 7 (Murder Mystery scenario) — **attribution canonique explicite** |
| Infer/Infer-4-Bayesian-Networks.ipynb | 66 (46+20) | WetGrass/Sprinkler (144 hits) ; source canonique citée = « Lauritzen & Spiegelhalter (1988) et Jensen, Lauritzen & Olesen (1990) » (Springer) — couvre le MBML WetGrass Chap.5 avec pedigree académique différent |
| Infer/Infer-5-Causal-Inference.ipynb | 38 (23+15) | do-calculus = MBML Chap.7 ; notebook cite « Pearl, J. (2000) » sans mention MBML — sous-portée, à clarifier |
| Infer/Infer-6-Debugging.ipynb | 50 (33+17) | Debugging pur EP/VMP/Gibbs — pas de concept MBML à attribuer |
| **Infer/Infer-7-Skills-IRT.ipynb** | 74 (51+23) | IRT / DINA — source canonique = MBML Ch.2 (StudentSkills) + Rasch (1960), Birnbaum (1968), Lord (1980), Junker & Sijtsma (2001). Attribution **présente** aux cellules 8-9 (backfill [#8530](https://github.com/jsboige/CoursIA/pull/8530), `16376a901`) — le verdict « notebook muet / PIRE CAS » du c.803 est périmé |
| **Infer/Infer-8-TrueSkill.ipynb** | 59 (40+19) | Pilote vérifié end-to-end : structure MBML Ch.3 fidèle (model 2 joueurs, draw via ConstrainBetween, online learning, teams, free-for-all, Elo bayésien, 3 exercices) MAIS **pas de formules V(t)/W(t)/τ² reproduites** (délégué à la machinerie EP Infer.NET). Cell 51 « Pour aller plus loin : Herbrich et al., 2006 » (référence 2006, pas 2007 NeurIPS — léger typo) |
| Infer/Infer-9-Classification.ipynb | 55 (37+18) | BPM (Herbrich, MBML Chap.4) exécuté sans citation explicite — source = Herbrich 2001 thesis mais MBML non nommé |
| Infer/Infer-10-Model-Selection.ipynb | 58 (40+18) | Bayes Factors / ARD — MBML Chap.11 (Model Comparison) hors-cité |
| Infer/Infer-11-Topic-Models.ipynb | 55 (38+17) | LDA — « Source primaire : Blei, Ng & Jordan (2003) » — couvre MBML Chap.10 mais en citant la source primaire canonique |
| Infer/Infer-12-Modeles-Hierarchiques.ipynb | 18 (10+8) | Pooling partiel / shrinkage — modèle générique, pas de MBML spécifique |
| **Infer/Infer-13-Crowdsourcing.ipynb** | 50 (36+14) | Worker models Honest/Biased/Community — sources canoniques = Dawid & Skene (1979), Raykar (2010), Karger (2011) + MBML Ch.7. Citations **présentes** (backfill [#8247](https://github.com/jsboige/CoursIA/pull/8247), `0ff926ded`) — le verdict « aucun cite / silencieux » du c.803 est périmé |
| Infer/Infer-14-Sequences.ipynb | 62 (41+21) | HMM forward-backward ; MBML Chap.12 absent mais pattern canonique (Rabiner 1989) |
| Infer/Infer-15-Recommenders.ipynb | 81 (55+26) | « [Livre MBML](https://mbmlbook.com/) » @ cell 76 (footer Pour aller plus loin) ; couvre PMF/Matchbox/ClickModel |
| Infer/Infer-16-Sparse-Gaussian-Process.ipynb | 31 (19+12) | GP sparse / EP — Titsias 2009 / MBML Chap.16 absent |
| Infer/Infer-17-Kalman-Filter.ipynb | 20 (12+8) | Kalman canonique (1960), pas MBML Chap.15 spécifiquement |
| Infer/Infer-18-Change-Point.ipynb | 23 (14+9) | Change-point pur, hors-scope MBML |
| Infer/Infer-19-Survival-Analysis.ipynb | 27 (17+10) | Survie / Weibull / Gamma — MBML Chap.17 (Survival Analysis) hors-cité |
| PyMC/PyMC-1-Setup.ipynb | 26 (15+11) | « Equivalent Infer.NET : Infer-1-Setup » — attribution interne CoursIA (parité #4956), pas source canonique externe. Couvre le setup PyMC sans pedigree MBML |
| PyMC/PyMC-2-Gaussian-Mixtures.ipynb | 23 (13+10) | Cycliste / Gaussian mixt — sources canoniques = Bishop PRML §9.2 + §9.2.2 + §10.7 (jumeau PyMC d'Infer-2) ; MBML ne couvre pas ce modèle (Ch.6 = Asthma, Ch.8 = How to Read a Model) |
| PyMC/PyMC-3-Factor-Graphs.ipynb | 18 (10+8) | « Implémenter le problème Murder Mystery (**MBML Ch.1**) » @ cell 0 (intro Objectifs). **Variante assumée** : 3 suspects Clue/Cluedo (Scarlet/Mustard/Peacock) au lieu de 2 (Auburn/Grey MBML original) — adaptation pédagogique justifiée par l'explaining away |
| PyMC/PyMC-4-Bayesian-Networks.ipynb | 26 (15+11) | WetGrass/Sprinkler (111 hits) ; « Lauritzen & Spiegelhalter (1988) » — Springer canonique |
| PyMC/PyMC-5-Causal-Inference.ipynb | 30 (16+14) | Pearl + `pm.do` — do-calculus (MBML Chap.7) non attribué |
| PyMC/PyMC-6-Debugging.ipynb | 43 (30+13) | Debugging pur MCMC |
| PyMC/PyMC-7-Skills-IRT.ipynb | 33 (19+14) | IRT (33 hits) ; « Origine de la méthode : Rasch (1960) + Birnbaum (1968) + Lord (1980) + Junker-Sijtsma DINA » — pedigree académique explicite **complet**, mais **0 mention MBML** (mesuré). L'asymétrie notée au c.803 s'est **inversée** depuis #8530 : c'est désormais le jumeau PyMC qui ne relie pas au chapitre MBML Ch.2, pendant qu'Infer-7 le cite |
| **PyMC/PyMC-8-TrueSkill.ipynb** | 30 (17+13) | **Section 7 bis reproduit explicitement les formules fermées V(t)/W(t)/τ²** + cell 2 cite « Herbrich, Minka & Graepel (2007), TrueSkill(TM): A Bayesian Skill Rating System (NeurIPS / Microsoft Research Cambridge) ». **Substance MBML Ch.3 complète + bonus algorithmique** |
| PyMC/PyMC-9-Classification.ipynb | 22 (12+10) | « Herbrich » 2 hits (MBML Chap.4 BPM) sans mention explicite |
| PyMC/PyMC-10-Model-Selection.ipynb | 35 (19+16) | WAIC/LOO (Vehtari) ; ARD générique |
| PyMC/PyMC-11-Topic-Models.ipynb | 34 (19+15) | LDA — « Source primaire : Blei, Ng & Jordan (2003) » — source canonique |
| PyMC/PyMC-12-Modeles-Hierarchiques.ipynb | 23 (14+9) | Pooling partiel — attribution au jumeau Infer-12 uniquement |
| **PyMC/PyMC-13-Crowdsourcing.ipynb** | 43 (27+16) | Worker models Honest/Biased/Community (jumeau PyMC d'Infer-13) — source canonique = Dawid & Skene (1979), **citée** (53 mentions mesurées) ; Raykar / Karger / MBML Ch.7 non mentionnés, contrairement au jumeau Infer-13 |
| PyMC/PyMC-14-Sequences.ipynb | 39 (22+17) | HMM forward-backward échantillonné — pas d'attribution |
| PyMC/PyMC-15-Recommenders.ipynb | 58 (34+24) | « Adapté de : Infer-15-Recommenders » + « Origine : PMF Salakhutdinov & Mnih (2008) » — attribution double explicite (jumeau interne + source primaire) |
| PyMC/PyMC-16-Sparse-Gaussian-Process.ipynb | 27 (16+11) | GP sparse — attribution au jumeau Infer-16 uniquement |
| PyMC/PyMC-17-Kalman-Filter.ipynb | 20 (12+8) | Kalman — attribution au jumeau Infer-17 uniquement |
| PyMC/PyMC-18-Change-Point.ipynb | 21 (13+8) | Change-point — attribution au jumeau Infer-18 uniquement |
| PyMC/PyMC-19-Survival-Analysis.ipynb | 21 (13+8) | Survie — attribution au jumeau Infer-19 uniquement |
| Infer-101.ipynb (legacy, hors-scope) | 71 (43+28) | Standalone C#/Python avant-portail — à archiver (sub-issue dédiée) |
| Pyro_RSA_Hyperbole.ipynb (Pyro, hors-scope) | 41 (25+16) | Pyro / RSA linguistique pragmatique ; cite Kao 2014, Kao & Goodman 2015 |

## Notes sur la traçabilité

1. **MBML quasi-totalement absent du périmètre inline** : seulement 5 hits sur 38 notebooks (Infer-3 cell 7, Infer-1 cell 37 footer, Infer-15 cell 76 footer, PyMC-3 cell 0, PyMC-8 cells 2 et 24). Le livre MBML (Herbrich) est listé comme ressource README Probas L567 mais n'est honoré inline que dans 3 cas (Infer-3 Murder Mystery, PyMC-3 Murder Mystery, PyMC-8 TrueSkill).
2. **Asymétrie Infer↔PyMC sur le pedigree académique** : la plupart des PyMC portent une section `Origine de la méthode` ou `Source primaire` (Blei, Salakhutdinov-Mnih, Rasch-Birnbaum, Jensen-Lauritzen) ; les Infer.NET s'en abstiennent systématiquement. Cette asymétrie est pédagogiquement assumée (Infer.NET = côté compilateur, PyMC = côté mathématicien) mais crée une lacune de traçabilité côté Infer.
3. **Le tag `Equivalent Infer.NET`** est une auto-référence CoursIA (parité #4956), pas une source canonique externe — les notebooks PyMC s'attribuent mutuellement aux notebooks Infer, et inversement, sans toujours nommer MBML.

## Voir aussi

- [#8081](https://github.com/jsboige/CoursIA/issues/8081) — audit fidélité distillation Probas/ (substance, verdicts de cycle d'audit).
- [#7422](https://github.com/jsboige/CoursIA/issues/7422) — hygiène docs/, réqualification de ce fichier (déplacement `audit/` → `reference/`, retrait des verdicts/décisions de cycle, extraction des 4 sous-items en issues filles).
- Section README Probas « [Références canoniques](../../MyIA.AI.Notebooks/Probas/README.md) ».

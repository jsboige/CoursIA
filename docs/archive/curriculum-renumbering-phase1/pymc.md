> **ARCHIVED 2026-07-20** — Verdict **no-defect-found** (no-renumber) figé (cf PR #6885). EPIC #5081 phase-1 close. Document conservé pour référence historique (daté, immutable). Voir triage table c.674 [PR #7426](https://github.com/jsboige/CoursIA/pull/7426) + archive INDEX [`docs/archive/INDEX.md`](../INDEX.md). Superseded by EPIC #5081 closure. *Archivé par : po-2025 (lane CoursIA-2, c.748) — `See` partiel dispatch triage c.674 UPDATE/ARCHIVE catégorie, suite logique c.676 PR #7436.*

> **Note archive** : les liens internes vers `[Probas/Infer](infer-renumbering-phase1.md)` et `[Search](search-renumbering-phase1.md)` (L3 ci-dessous) référencent les paths d'origine `docs/curriculum/`. Ces fichiers ont été co-archivés en même temps (cf subdir `docs/archive/curriculum-renumbering-phase1/`). Le doc est preserved verbatim (transient historique) ; les liens sont volontairement non corrigés pour ne pas altérer le contenu original daté.

# Probas/PyMC — phase 1 : analyse de cohérence narrative (#5081)

Troisième série analysée pour l'EPIC #5081 (après [Probas/Infer](infer-renumbering-phase1.md)
et [Search](search-renumbering-phase1.md)). **Verdict : aucune renumérotation nécessaire
(no-defect-found)** — comme Probas/Infer.

L'EPIC #5081 cite la galerie officielle pymc.io comme squelette canonique ; l'ordre actuel
PyMC-1..19 est cohérent avec cette progression.

## Méthode

Comme pour Probas/Infer : extraction du navlink `[<< Précédent]` (prédécesseur narratif déclaré)
depuis le bloc Navigation de chaque notebook, puis vérification **topologique** — chaque
prereq déclaré doit pointer vers un numéro strictement inférieur. Couverture numérique et
intégrité du DAG vérifiées mécaniquement (script `pymc_spine.py`, 19 notebooks).

## Résultats (firsthand)

| Métrique | Valeur |
|----------|--------|
| Notebooks | 19 (PyMC-1..19) |
| Couverture numérique 1..19 | **complète, 0 absent** |
| Arêtes broken-order (prereq #≥own) | **0** → l'ordre 1→19 est un tri topologique VALIDE du DAG |
| Navlinks cassés (404) | 0 |

> Note G.1 : un premier scan `grep -iv infer` avait faussement signalé PyMC-5 manquant —
> le filtre excluant « infer » (insensible casse) rayait `PyMC-5-Causal-Inference.ipynb`.
> PyMC-5 **existe** (verified firsthand). Artefact d'outil, corrigé.

## Arc narratif (cohérent)

| Bloc | Numéros | Thème |
|------|---------|-------|
| Fondations | 1→2→3→4→5 | Setup → Gaussian Mixtures → Factor Graphs → Bayesian Networks → Causal Inference |
| Méthodologie | 6 | Debugging |
| Psychométrie / skills | 7→8→9 | Skills IRT → TrueSkill → Classification |
| Modélisation | 10→11→12 | Model Selection → Topic Models → Hiérarchiques |
| Applications | 13→14→15 | Crowdsourcing → Sequences → Recommenders |
| Avancé | 16→17→18→19 | Sparse GP → Kalman Filter → Change Point → Survival Analysis |

L'arc monte progressivement des fondations (modélisation bayésienne) vers les applications
avancées (séries temporelles, survie). Les ajouts récents (18 Change-Point, 19 Survival)
tombent à la bonne place — l'anti-pattern « numérotation d'opportunité » **ne s'applique pas**.

## Parallèle PyMC ↔ Infer.NET

PyMC (Python) et Infer.NET (C#, [analyse phase-1](infer-renumbering-phase1.md)) couvrent les
**mêmes concepts** (TrueSkill, Crowdsourcing, Change-Point, Sparse-GP, Kalman, Survival,
Topic-Models, Recommenders, IRT). Les deux séries sont **propres** (tri topo valide, arc
cohérent). La cohérence croisée confirme que la partition Probas est structurellement saine.

## Verdict — pas de renumérotation

Aucun défaut de numérotation. Les asymétries mineures de navlinks observées
(some notebooks sans `<<` déclaré, ex. PyMC-6/12/14/15/17/18/19) sont des **sujets autonomes**
sans prédécesseur linéaire direct — pas des défauts de numérotation. Un rename serait
**contre-productif** : 0 bénéfice pédagogique, coût de sweep des liens entrants (leçon
#4737→#4743).

**Coût évité** : la série Probas/PyMC sort du backlog #5081 sans action.

Récapitulatif #5081 (3 séries analysées) :
- **Probas/Infer** : no-defect-found.
- **Search** : 1 défaut de navlink (résidu périmé) réparé, 0 défaut de numérotation.
- **Probas/PyMC** : no-defect-found.

## Hors scope (transparence)

- **3 arêtes prereq sémantiquement faibles** (héritées du parallèle Infer : TrueSkill→Topic,
  HMM/Sequences→Recommenders, Debugging→Classification) = sujet de prose séparé, un rename ne
  les corrigerait pas. Éligible comme à-côté plafonné (1 PR courte clarifiant les lignes prereq).

See #5081.

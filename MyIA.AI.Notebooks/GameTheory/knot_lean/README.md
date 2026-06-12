# knot_lean — Théorie des nœuds en Lean 4

Scaffolding pour la formalisation de résultats de théorie des nœuds en Lean 4,
avec sorry stratégiques commentés (références papier + prérequis Mathlib).

## Structure

| Fichier | Contenu | sorry | Phase |
|---------|---------|-------|-------|
| `Knots/Basic.lean` | Définitions (Knot, Link, PD-code, nœuds nommés) | 3 | 1 |
| `Knots/Reidemeister.lean` | Mouvements de Reidemeister R1/R2/R3, équivalence | 8 | 1 |
| `Knots/Invariant.lean` | 3-colorabilité, crossing number, unknotting number | 7 | 1–2 |
| `Knots/Conway.lean` | Nœud de Conway (11n34), Piccirillo, dichotomie lisse/topologique | 10 | 1 (permanent) |
| `Knots/Lidman.lean` | 11n102, unknotting number = 2 | 3 | 1 (permanent) |
| `Knots/MathlibPrerequisites.lean` | Index des prérequis Mathlib manquants par tier | 0 | 1 |

**Total sorry : ~31** (dont ~15 permanents = résultats hors de portée de Mathlib actuel)

## Résultats principaux (scaffolding)

### Phase 2 — Accessible (sorry → 0 possible)

- [ ] Le trèfle est 3-colorable
- [ ] L'unknot n'est PAS 3-colorable
- [ ] La 3-colorabilité est invariante par Reidemeister
- [ ] Corollaire : le trèfle n'est pas l'unknot

### Phase 3–4 — Modéré

- [ ] Nombre de croisements du trèfle = 3
- [ ] Polynôme d'Alexander trivial pour Conway et K-T
- [ ] Polynôme de Jones

### Phase 5+ — Permanent (décennies)

- [x] `conway_not_smoothly_slice` — Piccirillo (2018), Annals 2020
- [x] `conway_topologically_slice` — Freedman (1982)
- [x] `unknotting_11n102` — Lidman (2026), arXiv:2606.12431
- [x] `reidemeister_theorem` — Reidemeister (1927)

## Dépendances externes

| Dépôt | Rôle | Statut |
|-------|------|--------|
| [shua/leanknot](https://github.com/shua/leanknot) (branche `lean4`) | Bricks/walls, tangles, braids | Candidat dépendance Lake (alignement toolchain en cours) |
| [vihdzp/combinatorial-games](https://github.com/vihdzp/combinatorial-games) | Nombres surréels, nimbers Conway | Déjà dans `conway_cgt_lean/` |
| [prathamesh-t/Tangle-Isabelle](https://github.com/prathamesh-t/Tangle-Isabelle) | Tangles en Isabelle/HOL | Référence de design |
| [Mathlib](https://github.com/leanprover-community/mathlib4) | Polynômes, catégories, topologie partielle | Dépendance Lake |

## Notebook pédagogique

`Lean-14d-Conway-Knots-and-Proofs.ipynb` (dans `SymbolicAI/Lean/`) :
- Visualisations Python des nœuds (trèfle, Conway, Kinoshita-Terasaka)
- Histoire de la preuve Piccirillo (doctorante, 1 semaine, 50 ans d'attente)
- Résultat Lidman comme cas d'étude « preuve courte mais profonde »
- Perspective de formalisation Lean (pourquoi c'est loin, ce qu'il manque)

## Références

- **Piccirillo (2018/2020)** : *The Conway knot is not slice*, Annals of Mathematics 191(2). [arXiv:1808.02923](https://arxiv.org/abs/1808.02923)
- **Lidman (2026)** : *The unknotting number of 11n102 is 2*. [arXiv:2606.12431](https://arxiv.org/abs/2606.12431)
- **Reidemeister (1927)** : Elementare Begründung der Knotentheorie
- **Fox (1962)** : A quick trip through knot theory
- **Conway (1970)** : An enumeration of knots and links
- **Freedman (1982)** : The topology of four-dimensional manifolds, J. Differential Geom.
- **Prathamesh (2015)** : *Formalising Knot Theory in Isabelle/HOL*, LNCS 9250
- **Lean AI Leaderboard** : [Conway knot not smoothly slice](https://lean-lang.org/eval/problems/conway_knot_not_smoothly_slice/)

## Voir aussi

- **Epic #2874** — Cette Epic
- **#1647** Conway Phase 2 (jeux combinatoires, GoL)
- **#1646** Grothendieck Phase 1
- **`conway_cgt_lean/`** — Tour des résultats `vihdzp/combinatorial-games`
- **`social_choice_lean/`** — Pattern scaffolding avec sorry résolus (Arrow, Sen)
- **`conway_lean/`** — Jeu de Conway en Lean

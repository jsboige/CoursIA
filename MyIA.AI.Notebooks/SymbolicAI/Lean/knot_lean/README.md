# knot_lean — Théorie des nœuds en Lean 4

Scaffolding pour la formalisation de résultats de théorie des nœuds en Lean 4,
avec sorry stratégiques commentés (références papier + prérequis Mathlib).

Epic #2874 (Phase 5 en cours). Toolchain `v4.31.0-rc1`.

## État des sorries (vérifié 2026-06-14)

Deux comptes, selon le filtre :

| Fichier | sorry réels | sorry (prose, CI) |
|---------|------------|-------------------|
| `Knots/Basic.lean` | 0 | 1 |
| `Knots/Reidemeister.lean` | 2 | 2 |
| `Knots/Invariant.lean` | 3 | 4 |
| `Knots/Conway.lean` | 8 | 11 |
| `Knots/Lidman.lean` | 3 | 5 |
| `Knots/MathlibPrerequisites.lean` | 0 | 2 |
| **Total** | **16** | **25** |

- **sorry réels** (`exact sorry`, `:= sorry`, `:= by sorry`) = ce qui manque
  vraiment comme preuve. **16** au total.
- **sorry prose** (toute ligne contenant `sorry`, filtre CI `prose-header`) =
  **baseline CI 25** (workflow `lean-knot.yml`). Ce compte inclut les
  occurrences dans les commentaires de diagnostic (ex. le commentaire sur
  `KnotDiagram.wf` dans `Basic.lean`).

La CI `.github/workflows/lean-knot.yml` gate sur le **prose-header baseline 25** :
toute PR qui ajoute un sorry réel fait monter les deux comptes et échoue la CI,
sauf justification documentée dans le body PR.

## Résultats par statut réel (vérifié contre le code)

### Prouvés (axiomes `[propext, Quot.sound]` seulement, pas `sorryAx`)

- [x] `trefoil_tricolorable` — le trèfle est 3-colorable (`Invariant.lean`)
- [x] `unknot_not_tricolorable` — l'unknot n'est PAS 3-colorable (`Invariant.lean`)
- [x] `trefoil_crossing_number` — nombre de croisements du trèfle = 3 (`Invariant.lean`,
  sous la définition provisionnelle `crossingNumberOfDiagram`)
- [x] `Reidemeister1.symm` / `Reidemeister2.symm` / `Reidemeister3.symm`,
  `reidemeister_equiv_symm`, `reidemeister_equiv_equivalence` — symétrie des
  moves et clôture réflexive-transitive (`Reidemeister.lean`)
- [x] `tricolorable_invariant_fails_under_pr1_model` — **contre-exemple certifié**
  réfutant `tricolorable_invariant` sous le modèle PR1 (diagnostic, cf. § Phase 5)
- [x] `trefoil_wf`, `unknot_wf`, `figureEight_wf` — les 3 diagrammes nommés satisfont la parité PD de `KnotDiagram.wf`

### Scaffolding (sorry, cible formelle)

- [ ] `tricolorable_invariant` — la 3-colorabilité est invariante par Reidemeister
  (**GATED sur PR1.5**, cf. § Phase 5)
- [ ] `trefoil_not_unknot` — corollaire : le trèfle n'est pas l'unknot (dépend de
  `tricolorable_invariant`)
- [ ] `unknottingNumber` — définition + calcul (nécessite minimisation sur classes
  d'équivalence, Phase 4+)
- [ ] Conway (11n34) : `conway_not_smoothly_slice` (Piccirillo 2018/Annals 2020),
  `conway_topologically_slice` (Freedman 1982), mutation Kinoshita-Terasaka —
  8 sorry, scaffolding permanent
- [ ] Lidman 11n102 : unknotting number = 2 (Heegaard-Floer) — 3 sorry, scaffolding
- [ ] `reidemeister_theorem` — équivalence Reidemeister ↔ isotopie ambiante
  (topologie PL des 3-variétés, hors portée Mathlib actuel) — 2 sorry, permanent

## Phase 5 — Re-modélisation des mouvements de Reidemeister

**Marquee theorem** : `tricolorable_invariant` (la 3-colorabilité est un invariant).
Résiste depuis plusieurs cycles. La leçon clé (pattern « intractable = énoncé
faux », cf. conway P4 / `feedback-lean-false-statement-counterexample`) : avant
de prouver, vérifier que l'énoncé est *vrai* sous le modèle courant.

**Historique (certifié, par contre-exemples prouvés) :**

1. **Modèle Phase 3** (symétrique existentiel `∃ c, surgery`) — réfuté par
   `tricolorable_invariant_fails_under_current_model` (#2915) : témoin malformé
   `⟨7,8,9,10⟩` (labels hors `[1, numEdges]`).
2. **PR1 (#2929)** — re-modélisation : `KnotDiagram.wf` (parité PD, Bool) sur les
   deux diagrammes + renommage d'edges `ρ : Fin(min) ↪ Fin(max)` swap-invariant.
   Exclut le témoin malformé. **MAIS** réfuté à nouveau par
   `tricolorable_invariant_fails_under_pr1_model` (#2938) : `wf` force le twist R1
   à n'utiliser que les 2 edges fraîches, et `ρ` est une injection libre non liée
   aux labels du nouveau crossing `c` → le twist peut CRÉER la 3-colorabilité
   ex nihilo (témoin `d₁={[⟨1,2,1,2⟩],2}` non-tricolorable ↔
   `d₂={[⟨1,2,1,2⟩,⟨3,4,3,4⟩],4}` tricolorable, connectés par un twist R1).

**PR1.5 (prochain, cible).** Renforcer les constructeurs de move pour que `ρ`
*DÉTERMINE* les labels de `c` — un vrai curl R1 sur l'arc `a` attache le nouveau
crossing à l'arc existant `a` (pas seulement aux edges fraîches), dont la
condition Fox lie les nouveaux edges à `color a`. C'est ce qui rend le lemme de
transfert (PR2) prouvable. La géométrie PD-code du curl (relabelling/split de
l'arc sous la parité `wf`) nécessite un soin justifié (conventions Adams "The
Knot Book" / shua/leanknot) — non trivial, cible multi-cycle.

Référence : Fox (1962), A quick trip through knot theory ; Adams, *The Knot Book*.

## Structure

| Fichier | Contenu | sorry réels |
|---------|---------|-------------|
| `Knots/Basic.lean` | Définitions (Knot, Link, PD-code, nœuds nommés), `KnotDiagram.wf` | 0 |
| `Knots/Reidemeister.lean` | Mouvements R1/R2/R3 (modèle Phase 5), `ReidemeisterEquiv`, symétries | 2 |
| `Knots/Invariant.lean` | 3-colorabilité (Fox), crossing number, unknotting number, contre-exemple PR1 | 3 |
| `Knots/Conway.lean` | Nœud de Conway (11n34), Piccirillo, dichotomie lisse/topologique | 8 |
| `Knots/Lidman.lean` | 11n102, unknotting number = 2 | 3 |
| `Knots/MathlibPrerequisites.lean` | Index des prérequis Mathlib manquants par tier | 0 |

## Dépendances externes

| Dépôt | Rôle | Statut |
|-------|------|--------|
| [shua/leanknot](https://github.com/shua/leanknot) (branche `lean4`) | Bricks/walls, tangles, braids | Candidat dépendance Lake (alignement toolchain en cours) |
| [vihdzp/combinatorial-games](https://github.com/vihdzp/combinatorial-games) | Nombres surréels, nimbers Conway | Déjà dans `conway_cgt_lean/` |
| [prathamesh-t/Tangle-Isabelle](https://github.com/prathamesh-t/Tangle-Isabelle) | Tangles en Isabelle/HOL | Référence de design |
| [Mathlib](https://github.com/leanprover-community/mathlib4) | Polynômes, catégories, topologie partielle | Dépendance Lake |

## Notebook pédagogique

`Lean-17-Knots-a-Conway-and-Proofs.ipynb` (dans `SymbolicAI/Lean/`) :
- Visualisations Python des nœuds (trèfle, Conway, Kinoshita-Terasaka)
- Histoire de la preuve Piccirillo (doctorante, 1 semaine, 50 ans d'attente)
- Résultat Lidman comme cas d'étude « preuve courte mais profonde »
- Perspective de formalisation Lean (pourquoi c'est loin, ce qu'il manque)

## Références

- **Piccirillo (2018/2020)** : *The Conway knot is not slice*, Annals of Mathematics 191(2). [arXiv:1808.02923](https://arxiv.org/abs/1808.02923)
- **Lidman (2026)** : *The unknotting number of 11n102 is 2*. [arXiv:2606.12431](https://arxiv.org/abs/2606.12431)
- **Reidemeister (1927)** : Elementare Begründung der Knotentheorie
- **Fox (1962)** : A quick trip through knot theory
- **Adams** : *The Knot Book* (conventions PD-code pour les curls R1)
- **Conway (1970)** : An enumeration of knots and links
- **Freedman (1982)** : The topology of four-dimensional manifolds, J. Differential Geom.
- **Doll & Hoste (1991)** : A tabulation of oriented links (parité PD-code)
- **Prathamesh (2015)** : *Formalising Knot Theory in Isabelle/HOL*, LNCS 9250
- **Lean AI Leaderboard** : [Conway knot not smoothly slice](https://lean-lang.org/eval/problems/conway_knot_not_smoothly_slice/)

## Voir aussi

- **Epic #2874** — Cette Epic (Phase 5)
- **#1647** Conway Phase 2 (jeux combinatoires, GoL)
- **#1646** Grothendieck Phase 1
- **`conway_cgt_lean/`** — Tour des résultats `vihdzp/combinatorial-games`
- **`social_choice_lean/`** — Pattern scaffolding avec sorry résolus (Arrow, Sen)
- **`conway_lean/`** — Jeu de Conway en Lean (cf. `MacroCell.wf`, pattern de la
  ré-modélisation Phase 5 `KnotDiagram.wf`)

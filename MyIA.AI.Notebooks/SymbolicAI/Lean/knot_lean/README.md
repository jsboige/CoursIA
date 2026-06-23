# knot_lean — Théorie des nœuds en Lean 4

Scaffolding pour la formalisation de résultats de théorie des nœuds en Lean 4,
avec sorry stratégiques commentés (références papier + prérequis Mathlib).

Epic #2874 (Phase 5 en cours). Toolchain `v4.31.0-rc1`.

## État des sorries (vérifié 2026-06-23, 18 réels — 16 + 2 du transfer backward PARTIEL #3124, `num` prouvé)

Deux comptes, selon le filtre :

| Fichier | sorry réels | sorry (prose, CI) |
|---------|------------|-------------------|
| `Knots/Basic.lean` | 0 | 1 |
| `Knots/Reidemeister.lean` | 2 | 2 |
| `Knots/Invariant.lean` | 5 | 6 |
| `Knots/Conway.lean` | 8 | 11 |
| `Knots/Lidman.lean` | 3 | 5 |
| `Knots/MathlibPrerequisites.lean` | 0 | 2 |
| **Total** | **18** | **27** |

- **sorry réels** (`exact sorry`, `:= sorry`, `:= by sorry`) = ce qui manque
  vraiment comme preuve. **18** au total — 16 stables + **2 du transfer backward
  PARTIEL `tricolorable_backward` (#3124)** : sous-buts `fox`/`col` laissés en
  sorry après décomposition (`num` PROUVÉ par parité `wf`, cf. § Phase 5 ;
  cœur `hcolPres` prouvé).
- **sorry prose** (toute ligne contenant `sorry`, filtre CI `prose-header`) =
  **baseline CI 27** (workflow `lean-knot.yml`, baissé de 28 après preuve `num`). Ce compte inclut les
  occurrences dans les commentaires de diagnostic (ex. le commentaire sur
  `KnotDiagram.wf` dans `Basic.lean`).

La CI `.github/workflows/lean-knot.yml` gate sur le **prose-header baseline 27**
(bump 25→28 dans #3124 pour la décomposition du transfer backward, puis **baissé à 27**
après la preuve `num` #3163) : toute PR qui ajoute un sorry réel fait monter les
deux comptes et échoue la CI, sauf justification documentée dans le body PR.

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
- [x] `Reidemeister1Connected.tricolorable_forward` (#3000, MERGED) — transfer **forward** de la 3-colorabilité d₁→d₂ sous le modèle R1 connecté (`Invariant.lean` L478, preuve complète sans sorry via `hcolF1`/`hcolF2b`/`hcolF2c`)
- [~] `Reidemeister1Connected.tricolorable_backward` (#3124, MERGED, **PARTIEL**) — transfer **backward** d₂→d₁ : `hcolPres` (préservation des couleurs sur les labels préservés, cœur constructif) **PROUVÉ** ; `num` PROUVÉ #3163 (parité `wf`) ; `fox` #3154 + `col` #3168 partiellement prouvés (un sous-cas chacun clos) ; **2 résiduels §9.1** restent en sorry (crossing modifié `Y` + kink all-distinct)

### Scaffolding (sorry, cible formelle)

- [ ] `tricolorable_invariant` — la 3-colorabilité est invariante par Reidemeister
  (**FAUX sous le modèle append+wf courant** : kink disjoint change la
  3-colorabilité = #2938. GATED sur la décision C/X du coordinateur, cf. § Phase 5)
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

### Verdict par sorry (audit G.1, 2026-06-23)

Re-vérification firsthand contre le code (`Reidemeister.lean` + `Invariant.lean`),
par sorry réel des 5 feuilles ouvertes d'`Invariant.lean`. Classe chaque feuille
en **PROUVEABLE** / **REFUTÉ** / **RESEARCH-HOLD** / **INFRASTRUCTURE** — l'état
formel réel, couple aux preuves :

| Ligne | Théorème | Verdict | Débloqueur |
|-------|----------|---------|------------|
| L116 | `tricolorable_invariant` | **REFUTÉ tel qu'énoncé** | Contre-exemple certifié `tricolorable_invariant_fails_under_pr1_model` (Invariant.lean L211) : witness `(d₁={⟨1,2,1,2⟩,2}, d₂={⟨1,2,1,2⟩,⟨3,4,3,4⟩,4})` relié par `ReidemeisterEquiv.step (ReidemeisterStep.r1 …)` (L222), `d₁` non-tricolorable, `d₂` tricolorable. Le step R1 utilise le `Reidemeister1` **libre en ρ** (Reidemeister.lean L71). Récupération = **décision de design coord** : **(C)** câbler `Reidemeister1Connected`/`Reidemeister1'` dans `ReidemeisterStep`/`ReidemeisterEquiv` (exclut les kinks disjoints — `pr1_counterexample_excluded_under_rho_determined` L317 le prouve sur le witness), ou **(X)** accepter #2938 et reframer l'invariant. |
| L743 | `trefoil_not_unknot` | **REFUTÉ par procuration** | Corollaire de L116. Même fork (C)/(X). Pas de chemin direct : `trefoil_crossing_number` est PROUVÉ mais l'invariance du crossing-number bute sur la même équivalence libre-en-ρ. |
| L799 | `Knot.unknottingNumber` | **INFRASTRUCTURE (NP-dur)** | Minimisation sur les classes d'équivalence ; gated sur une `ReidemeisterEquiv` non-triviale (fork L116). Scaffolding permanent. |
| L1330 | `fox` all-distinct §9.1 | **RESEARCH-HOLD** | Héritage Fox du crossing modifié `Y'` sous kink all-distinct. Nécessite la construction colour-symmetry / proper-arc #3003. Sous-cas **all-equal PROUVÉ** (L1280-1327, transfer par `help` per-strand). |
| L1474 | `col` all-distinct §9.1 | **RESEARCH-HOLD** | Lift ≥ 2 couleurs : la restriction naïve `col₁` peut être **monochrome** si toute la variation chromatique de `col₂` vit sur les arêtes fraîches `{n+1, n+2}` (pathologie du kink disjoint). Nécessite #3003, **ou** un contre-exemple certifié qui réfuterait le backward (non exclu). Sous-cas **all-equal PROUVÉ** (L1421-1469, par l'absurde via `h2col₂`). |

**Conclusion de l'audit.** Aucun grain de preuve tractable en 1 cycle dans
`knot_lean` : les deux feuilles « réfutées » (L116/L743) sont un **fork de design**
au coordinateur (décision (C) câblage vs (X) reframer), les deux résiduels §9.1
(L1330/L1474) sont le **noyau research-level irréductible** (construction #3003,
BG-prover ai-01), L799 est de l'infrastructure NP-dure. Le transfer R1 backward
est en revanche **complet sur son sous-cas all-equal** (`fox`+`col` PROUVÉS) et sur
`num` (parité `wf`, #3163) — seuls les modes all-distinct du kink restent ouverts.

## GF(3) linéarité & limite de soundness du modèle (2026-06-23, #3003)

Deux résultats combinatoires sur le modèle de 3-colorabilité, énoncés comme
scaffolding (cibles BG-prover) suite à la caractérisation cycle-3 (#4022) :

- **Linéarité GF(3) du condition de Fox** (`triColorFoxCondition_iff_sum_mod_three`,
  Invariant.lean) : pour trois couleurs, la condition « toutes égales OU toutes
  distinctes » équivaut à `toNat(c₁)+toNat(c₂)+toNat(c₃) ≡ 0 (mod 3)`. L'espace
  des colorations valides est donc un *sous-espace linéaire* de `(ℤ/3)^(numEdges)`.
  Vérifié empiriquement (0 désaccord sur 7,5M diagrammes wf). Décidable par
  `decide` une fois `Fintype` (Mathlib) importé — ce fichier n'importe actuellement
  que `Knots.Basic`/`Knots.Reidemeister`.
- **Lemme universel** (`tricolorability_of_two_crossings`, Invariant.lean) :
  `wf d → d.crossings.length ≥ 2 → IsTricolorable d` (par rang-nullité sur le
  système GF(3) ci-dessus). VRAI pour le modèle (0 échec pour m ∈ {2,3,4,5}).

**⚠️ SOUNDNESS — le modèle DIVERGE du Fox classique (G.9, vérifié firsthand) :**
le modèle colore des ARÊTES (`Fin numEdges`) indépendamment, SANS contrainte
d'arc-égalité (le Fox classique force l'over-strand d'un crossing à partager sa
couleur). Donc `numEdges = 2·m ≠ m arcs`, et même le **figure-8** (4 crossings,
déterminant 5, classiquement NON 3-colorable) EST edge-tricolorable dans le modèle
— witness `(0,0,0,1,0,0,1,2)` vérifié contre le `triColorConditionAt` exact.

**Conséquence stratégique :** prouver le lemme universel déchargerait les 2
sorries résiduels de #3003 (fox/col backward) MAIS rendrait `tricolorable_invariant`
TRIVIALEMENT vrai (tout diagramme wf ≥2-crossings devient tricolorable →
l'invariant ne distingue plus que l'unknot). C'est un **fork architectural** en
attente de décision coordinateur/user :

- **Path A** : prouver le lemme (décharge #3003, consacre un modèle permissif
  non-classique ; figure-8 false-positive permanent).
- **Path B** : fixer le modèle (contrainte d'arc-égalité / coloration par arcs),
  re-prouver `trefoil_tricolorable`, #3003 backward devient le transfert classique
  GÉNUINEMENT dur.

Le lemme + le pont sont énoncés (open) pour permettre l'itération BG-prover d'ai-01
sur la cible ainsi formalisée ; la décision architecturale est différée.

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

**PR1.5 (#2956, MERGED) — ρ-determiné.** Renforce les constructeurs de move
pour que `ρ` *DÉTERMINE* les labels de `c` : un curl R1 sur l'arc `a` attache le
nouveau crossing `⟨a, a, n+1, n+2⟩`. **PR1.5b (#2966, MERGED)** a livré la preuve
d'exclusion `pr1_counterexample_excluded_under_rho_determined` (gate 1 : le
re-model exclut le témoin #2938, prouvé).

**Défaut structurel découvert (2026-06-14, G.1).** Le modèle append+`wf` est
*trop faible* : un argument de parité (airtight, + 3 probes empiriques) montre
que TOUTE surgery append `d₂ = d₁ ++ [c]` avec `d₁.wf ∧ d₂.wf` force `c` à ne
référencer que les labels frais `{n+1, n+2}` (sinon un label de `d₁` dépasse
2×) → `c = ⟨n+1,n+1,n+2,n+2⟩` = un **kink disjoint** (composante unknot
séparée, 0 arête partagée avec `d₁`). Conséquences :

1. `Reidemeister1` (free-ρ, #2929) n'admet QUE des kinks disjoints — AUCUN R1
   connecté représentable. Le témoin #2938 est précisément un kink disjoint.
2. `Reidemeister1'` (#2956) force `c = ⟨a,a,n+1,n+2⟩` → l'arc `a` apparaît 4× →
   **`d₂.wf` insatisfiable → la def est VACUOUS**. La preuve d'exclusion #2966
   est trivialement vraie (la prémisse n'est jamais satisfaite).
3. R2 : idem (composantes 2-crossings disjointes). Seul **R3** (préserve
   `numEdges`, relabel un crossing) est connecté sous ce modèle.
4. `ReidemeisterEquiv` ≈ refl + kinks disjoints R1/R2 + R3 connecté. Trop faible
   pour dénouer un trèfle. `tricolorable_invariant` est FAUX (un kink disjoint
   change la 3-colorabilité = #2938).

**Option C — fix connecté, PR1.5c (#2980, MERGED 2026-06-14).** La surgery connectée
correcte est NON-append : modifier un endpoint crossing `Y` de l'arc `a`
(rename un slot `a`→`b = n+1`) ET append `C = ⟨a, b, c, c⟩` avec
`c = n+2` (monogon du kink, apparaît 2× dans `C` seul). Parité préservée :
`a` = X+C (2×), `b` = Y+C (2×), `c` = C+C (2×). `def Reidemeister1Connected`
(Reidemeister.lean) implémente cette surgery ; `reidemeister1Connected_satisfiable`
prouve un témoin concret `wf = true` des deux côtés (`d₁={[⟨1,2,3,4⟩,⟨1,2,3,4⟩],4}`
→ `d₂={[⟨1,2,3,4⟩,⟨5,2,3,4⟩,⟨1,5,6,6⟩],6}`). **ADDITIF** : ne modifie pas les
moves merged (#2929/#2956 coexistent). Option C **MERGED** (#2980) : feasibility
prouvée (témoin non-vide, `wf = true` des deux côtés).

**R3 connecté — PR1.5d (#3088, MERGED 2026-06-15).** R3 est le seul move
connecté sous le modèle append+wf (point 3 ci-dessus). Formalisé additivement
comme `Reidemeister3Determined` (Reidemeister.lean) : un slide R3 où le crossing
relabélisé `c` est contraint par slot-permutation de l'original
(`c.isSlotPermOf` = `List.Perm` décidable sur `Nat`), 4 strands préservés et
`wf`. `.implies_reidemeister3` raffine en `Reidemeister3` (embedding) ;
`reidemeister3Determined_satisfiable` prouve un témoin non-vide
(`⟨1,2,3,4⟩`→`⟨1,3,2,4⟩`, swap e2/e3). 0 sorry ajouté (scaffolding pur, R1/R2/R3
merged inchangés).

**Transfer lemma R1 connecté — forward #3000 PROUVÉ + backward #3124 PARTIEL (MERGED).**
Le transfer **forward** `tricolorable_forward` (#3000) est **prouvé** : sous le
modèle R1 connecté (Option C, `Reidemeister1Connected`), une tricoloration de `d₁`
se propage à `d₂`. Le transfer **backward** `tricolorable_backward` (#3124) est
**partiel** : `hcolPres` (préservation des couleurs sur les labels préservés
`l ∈ [1, n]`, arithmétique pure `(l-1) % numEdges` close par `rfl`) est prouvé —
c'est le cœur constructif sur lequel l'héritage Fox des crossings inchangés
s'appuie. **Deux sous-buts §9.1 restent en `sorry`** après décomposition
(instruction user 2026-06-15 : « décompose, prouve le tractable, livre avec des
sous-sorry résiduels sur lesquels ai-01 avisera »). Sur les 3 sous-buts initialement
ouverts (`fox`/`num`/`col`), `num` est **prouvé** et `fox`/`col` sont **partiellement
prouvés** (un sous-cas chacun clos) :

1. `num` — **PROUVÉ (#3163)**. `d₁.numEdges ≥ 2` par parité `wf` : `_hproper`
   fournit un crossing distinct `j ≠ i` ⟹ `crossings.length ≥ 2` ⟹
   `edges.length = 4 × length ≥ 8` ⟹ par l'absurde (`numEdges = 1`) les clauses
   (a)+(b) de `wf` forcent toutes les arêtes à `1` (comptage `count 1 = length ≥ 8`),
   contredisant la clause (b) `count 1 = 2`.
2. `fox` — **partiellement prouvé (#3154)** : les crossings **inchangés**
   héritent via `hcolPres` (miroir du forward `h_inherit`). **Résiduel §9.1** :
   le crossing **modifié `Y`** (remplacé par `Y'` dans `d₂`) nécessite la
   construction de symétrie de couleurs sous `col₁` (research-level, §9.4–§9.6,
   `Invariant.lean` L1210).
3. `col` — **partiellement prouvé (#3168)** : le mode kink **all-equal** est clos
   (les 2 couleurs distinctes de `col₂` s'embedent dans `Fin d₁.numEdges`).
   **Résiduel §9.1** : le mode kink **all-distinct** porte une couleur fraîche hors
   range `d₁`, la restriction naïve `col₁` peut être monochrome — le lift `≥ 2`
   couleurs nécessite la construction colour-symmetry / proper-arc (#3003,
   `Invariant.lean` L1354).

Ces **2 résiduels §9.1** maintiennent la **baseline CI 27** (baissée de 28 après la
preuve `num` #3163 ; bump initial 25→28 justifié dans #3124).

Le marquee `tricolorable_invariant` reste gated sur la **complétion des 2 résiduels
§9.1 backward** (puis composition forward + backward = bi-implication R1
sous le modèle connecté). Le transfer R2/R3 complet (wf-satisfabilité
non-triviale + lift RTC) reste research-level multi-PR. Décision stratégique
(C) surgery connectée profonde vs (X) accepter #2938 et reframer, ouverte.

Référence : Fox (1962), A quick trip through knot theory ; Adams, *The Knot Book*.

## Structure

| Fichier | Contenu | sorry réels |
|---------|---------|-------------|
| `Knots/Basic.lean` | Définitions (Knot, Link, PD-code, nœuds nommés), `KnotDiagram.wf` | 0 |
| `Knots/Reidemeister.lean` | Mouvements R1/R2/R3 (modèle Phase 5), `ReidemeisterEquiv`, symétries | 2 |
| `Knots/Invariant.lean` | 3-colorabilité (Fox), crossing number, unknotting number, contre-exemple PR1, transfer R1 forward (#3000) + backward PARTIEL (#3124) | 6 |
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

## Conclusion

`knot_lean` formalise en Lean 4 des résultats classiques et modernes de théorie
des nœuds — 3-colorabilité de Fox, nombre de croisements, nœud de Conway (11n34),
Lidman 11n102 — sur l'axiomatique minimale `[propext, Quot.sound]` (aucun
`sorryAx`). L'Epic #2874 (Phase 5) en est au transfer de l'invariant de
3-colorabilité sous le modèle connecté des mouvements de Reidemeister.

### Ce qui est acquis

Les **invariants locaux** sont solides : 3-colorabilité du trèfle et
non-colorabilité de l'unknot, nombre de croisements du trèfle, symétries et
clôture réflexive-transitive des moves, et la *well-formedness* paritaire
`KnotDiagram.wf` des diagrammes nommés. Le **transfer forward** de la
3-colorabilité sous R1 connecté (`#3000`) est **prouvé** sans sorry, et le
**transfer backward** (`#3124`) est **partiellement** établi : le cœur
constructif `hcolPres` et le sous-but `num` (parité `wf`, `#3163`) sont clos,
ainsi qu'un sous-cas chacun de `fox` (`#3154`) et `col` (`#3168`).

### Le verrou

Le marquee `tricolorable_invariant` reste **gated** sur deux sous-buts résiduels
§9.1 du backward : la symétrie des couleurs sur le crossing modifié `Y` (`fox`) et
le lift « all-distinct » hors range du diagramme source (`col`). Leur clôture
permettrait de composer forward + backward en une bi-implication R1 connectée
(**18 sorry réels** au total). Les résultats « lointains » — Conway non-slice
(Piccirillo), unknotting number de Lidman, théorème Reidemeister ↔ isotopie
ambiante — restent du **scaffolding permanent** : ils excèdent la portée actuelle
de Mathlib (topologie PL des 3-variétés, Heegaard-Floer).

### Leçons méthodologiques

La trajectoire Phase 5 illustre le pattern « *intractable* = énoncé faux » (cf.
`conway_lean` P4) : avant de prouver, **vérifier par contre-exemple certifié** que
l'énoncé est vrai sous le modèle courant. Trois re-modélisations successives
(Phase 3 → PR1 `wf`+ρ → PR1.5 ρ-déterminé) ont chacune été **réfutées par un
témoin prouvé** (`#2915`, `#2938`) avant que l'analyse de parité (2026-06-14) ne
révèle que le modèle append+`wf` est *structurellement trop faible* (il n'admet
que des kinks disjoints). La **surgery connectée** (Option C, `#2980` ; R3
déterminé, `#3088`) corrige ce défaut. Enfin, la **décomposition** du backward
(`#3124`) — prouver le tractable, livrer avec sous-sorry résiduels documentés — a
isolé exactement les deux constructions research-level qui restent.

### Prochaines étapes

1. Clore les **2 résiduels §9.1** (`fox`, `col`) → bi-implication R1 connectée.
2. Transfer **R2/R3** complet (wf-satisfaisabilité non-triviale + lift RTC) —
   research-level multi-PR.
3. Décision stratégique ouverte : **(C)** pousser la surgery connectée profonde,
   ou **(X)** accepter `#2938` et reframer l'invariant.
4. Scaffolding lointain : attendre l'évolution de Mathlib (3-variétés,
   Heegaard-Floer) pour Conway et Lidman.

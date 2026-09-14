# knot_lean — Théorie des nœuds en Lean 4

Scaffolding pour la formalisation de résultats de théorie des nœuds en Lean 4,
avec sorry stratégiques commentés (références papier + prérequis Mathlib).

Epic #2874 (Phase 5 en cours). Toolchain `v4.32.1` (migration post-#11325, cf #11256).

## État des sorries (vérifié 2026-09-14 contre `origin/main`, **10 réels**)

Deux comptes, selon le filtre CI :

| Fichier | sorry réels | sorry (prose, CI) |
|---------|------------|-------------------|
| `Knots/Basic.lean` | 0 | 3 |
| `Knots/Reidemeister.lean` | 2 | 2 |
| `Knots/Invariant.lean` | **0** | 5 |
| `Knots/Conway.lean` | 6 | 12 |
| `Knots/Lidman.lean` | 2 | 4 |
| `Knots/MathlibPrerequisites.lean` | 0 | 2 |
| **Total** | **10** | **28** |

- **sorry réels** = ce qui manque vraiment comme preuve. **10** au total (code-only
  après strip `--`/`/- -/`, mesuré par `scripts/lean/count_code_sorry.py` champ
  `distinct_code_sorry`, baseline CI `lean-knot.yml` recalibrée à `"10"`
  par #15082), tous stables : 0 dans `Invariant.lean`
  (`Knot.unknottingNumber` **DISCHARGÉ par #15082** : redéfini via `Nat.sInf` de
  `{n | k.UnknottableIn n}` + témoin `unknot_unknottingNumber = 0` prouvé —
  0 sorry résiduel, voir § Phase 5 / § #14992 pour la modélisation indexée
  des changements de croisement et l'accessibilité Reidemeister), 2
  `reidemeister_theorem` (PL), 6 Conway (les 2 defs `IsSmoothlySlice` /
  `IsTopologicallySlice := sorry` + 4 `exact sorry` de bornes), 2 Lidman. Les
  **2 résiduels §9.1 `fox`/`col` du backward transfer ont été DISCHARGÉS par
  #11227** : le mode kink all-distinct est **vacuus** — le kink R1 `C = ⟨a,b,c,c⟩`
  a `e₃ = e₄ = c`, la continuité d'over-strand Path B `c₂ = c₄` force
  `col₂(b) = col₂(c) = col₃`, contredisant l'exigence Fox all-distinct
  `c₂ ≠ c₃` → `absurd` clos les deux résiduels d'une ligne chacun. La
  **bi-implication R1 connectée est COMPLÈTE** (forward #3000 + backward
  #3124/#11227).

- **Baisse historique 17 → 16 → 14 → 11 → 10** : #8766 a déchargé `trefoil_not_unknot`
  (composition), #9966 a surélevé à 17 (wall du wrapper
  `tricolorable_forward_r1`), puis le wall a été déchargé (16) et #11227 a
  clos fox/col (14) ; la lecture fine par fichier au 2026-08-28 (post-strip
  commentaires, compter les `sorry` réels restants) donnait **11** : la table
  de ce README sous-comptait `tricolorable_invariant` (déjà résolu mais présenté
  comme résiduel) et sur-comptait les defs Conway comme 2 entrées distinctes
  quand le script en attribue 6 (6 déclarations à 1 `sorry` chacune — mesure
  2026-08-28 re-vérifiée le 2026-09-11). **#15082 a ensuite déchargé
  `Knot.unknottingNumber` via `Nat.sInf` (-1), amenant le baseline à 10.**
  #11276 a ajouté **sans sorry** le transfer `tricolorable_forward_r2_up`
  PROVEN + les murs nommés `r2_append_only_wall` (L1061) et
  `r3_determined_wall` (L1214) qui bornent l'iff maître sous le modèle libre.

- **Reidemeister.lean à 2 sorries réels** : `reidemeister_theorem` ×2
  (topologie PL des 3-variétés, hors portée Mathlib actuel).

- **sorry prose** = **28** (raw, any-line matchant `sorry`, fichiers FR —
  re-mesuré 2026-09-14 sur `origin/main` ; l'ancien total 37 ne se
  reproduisait plus sous cette définition). Le mode CI officiel est
  **`real`** : strippe `--` et `/- -/`, puis compte le mot-bounded
  `\bsorry\b`. La CI gate sur baseline **10** (alignée avec
  `LEAN_INVENTORY.md`, voir #13312).

La CI `.github/workflows/lean-knot.yml` gate sur le **real-mode baseline 10**
(alignement post-#13312, mesure 2026-09-10 ; historique : prose-header 25→28
dans #3124, baissée à 27 après #3163, re-bumpée à 28 par #3003 ;
switch prose-header→real à baseline 17 le 2026-07-11 ; 16 après #8766, re-17
par #9966, 16 au wall discharge, 14 après #11227, **11 après mesure
`count_code_sorry.py` 2026-08-28**, **10 après #15082** (`Knot.unknottingNumber`
DISCHARGÉ via `Nat.sInf` — voir § Phase 5 / § #14992) : toute PR qui ajoute
un sorry réel fait monter le compte real et échoue la CI, sauf justification
documentée dans le
body PR.

**Corridor Reidemeister #8696** (c.8162-c.8169, 5 PRs MERGED 2026-07-29 →
2026-08-08) : les **6 sites** où le move-surgery `with` était utilisé ont été
remplacés par des **égalités de champs** (`Reidemeister1.symm`,
`Reidemeister1'.implies_reidemeister1`, `Reidemeister2.symm`,
`Reidemeister1Connected.{shares_edge, crossings_eq}`,
`Reidemeister3Determined.implies_reidemeister3`). Conséquence pratique :
preuve directe par `⟨rfl, rfl⟩` au lieu du `obtain ⟨rfl⟩ := hsurg` (L887 ★★).
Le compte `sorry` reste à 2 dans `Reidemeister.lean` (le pair
`reidemeister_theorem`) — le corridor ne visait pas la fermeture du
`reidemeister_theorem` lui-même, qui reste gated sur la topologie PL.

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

- [x] `Reidemeister1Connected.tricolorable_forward` (#3000, MERGED) — transfer **forward** de la 3-colorabilité d₁→d₂ sous le modèle R1 connecté (`Invariant.lean` L1734, preuve complète sans sorry via `hcolF1`/`hcolF2b`/`hcolF2c`)

- [x] `trefoil_not_unknot` (#8766, MERGED) — corollaire : le trèfle n'est pas l'unknot, **PROUVÉ** par composition de `tricolorable_invariant` (désormais prouvé, #11958) + `trefoil_tricolorable` + `unknot_not_tricolorable` — plus aucun sorry, ni propre ni hérité.

- [x] `Reidemeister1Connected.tricolorable_backward` (#3124, MERGED puis **COMPLÉTÉ par #11227**) — transfer **backward** d₂→d₁ **COMPLET** : `hcolPres` (cœur constructif) + `num` (#3163, parité `wf`) + les 2 résiduels §9.1 `fox`/`col` **DISCHARGÉS par #11227** — le mode kink all-distinct est vacuus (continuité over-strand `c₂ = c₄` du kink `⟨a,b,c,c⟩` force `col₂(b) = col₂(c) = col₃`, contredisant Fox all-distinct ; `absurd` clos en une ligne chacun). Avec #3000, la **bi-implication R1 connectée est PROUVÉE**.

- [x] **Corridor Reidemeister #8696** (#9807 / #9873 / #9901 / #9913 / #9955, 5 PRs MERGED) — `Reidemeister1.symm`, `Reidemeister1'.implies_reidemeister1`, `Reidemeister2.symm`, `Reidemeister1Connected.{shares_edge, crossings_eq}`, `Reidemeister3Determined.implies_reidemeister3` : proofs par `⟨rfl, rfl⟩` après field-eqs refactor. **Aucun sorry ajouté**, **aucun sorry éliminé** (le corridor visait la clarté structurelle, pas la fermeture de théorèmes — `reidemeister_theorem` reste gated sur la topologie PL).

- [x] `tricolorable_forward_r2_up` (#11276, MERGED) — transfer **forward** de la 3-colorabilité à travers le R2 **append-only** (modèle libre historique) : **PROVEN sans sorry**. La même PR livre les **murs nommés** `r2_append_only_wall` (L1061 : le modèle R2 LIBRE est append-only avec bigon flottant — le bras descendant de l'iff maître est FAUX sous ce modèle, témoin formel) et `r3_determined_wall` (L1214) qui **bornaient l'iff maître sous le modèle libre** — la re-modélisation connectée R2/R3 qu'ils appelaient a été livrée (#11469, #11903) et le maître prouvé (#11958).

- [x] `tricolorable_invariant` (#11958, MERGED) — **le marquee** : la 3-colorabilité est invariante par équivalence de Reidemeister, prouvé par induction sur `ReidemeisterEquiv` (cas R1 : bi-implication connectée #3000/#3124 ; cas R2 : `tricolorable_invariant_r2_connected` L3234 ; cas R3 : `_r3_connected` L3520 ; maître `Invariant.lean` L3535). Ferme le front Phase 2 de #2874 — `Invariant.lean` est **sorry-free**.

- [x] `unknottingNumber` — **définition close par #15082** : redéfini via `Nat.sInf` sur `{n | k.UnknottableIn n}`, témoin `unknot_unknottingNumber = 0` prouvé, zéro sorry (`Invariant.lean` L2267). Le calcul effectif reste NP-dur (infrastructure).

### Scaffolding (sorry, cible formelle)
- [ ] Conway (11n34) : `conway_not_smoothly_slice` (Piccirillo 2018/Annals 2020),
  `conway_topologically_slice` (Freedman 1982), mutation Kinoshita-Terasaka —
  6 sorry, scaffolding permanent (les 2 sorries historiquement Open de
  `conway_trivial_alexander` et `KT_trivial_alexander` sont visés par les
  PRs #15440 / #15460 du split #14821 — voir aussi note ² de `LEAN_INVENTORY.md`)
- [ ] Lidman 11n102 : unknotting number = 2 (Heegaard-Floer) — 2 sorry, scaffolding
  (le sorry du diagramme L39 a été éliminé par #4899, PD-code 11n102 depuis KnotInfo)
- [ ] `reidemeister_theorem` — équivalence Reidemeister ↔ isotopie ambiante
  (topologie PL des 3-variétés, hors portée Mathlib actuel) — 2 sorry, permanent

### Verdict par sorry (audit G.1, re-vérifié 2026-09-14 contre `origin/main`)

Re-vérification firsthand contre le code (`Reidemeister.lean` + `Invariant.lean`).
`Invariant.lean` ne porte **plus aucun sorry réel** (master prouvé, #11958) : les
feuilles ouvertes du lake vivent dans `Reidemeister.lean` (2, topologie PL),
`Conway.lean` (6) et `Lidman.lean` (2). Classe chaque théorème nommé
en **PROUVÉ** / **OPEN (`sorry`)** / **RESEARCH-HOLD** / **INFRASTRUCTURE** —
l'état formel réel, couplé aux preuves :

> Note post-#13312 : la mesure canonique `count_code_sorry.py --lake knot_lean`
> rend `distinct_code_sorry = 10` (cf. table d'État des sorries plus haut). La
> table de Verdicts ci-dessous documente l'état **qualitatif** des théorèmes
> individuellement (OPEN/PROUVÉ/INFRASTRUCTURE), pas le décompte : elle reste
> exacte sur le verdict de chaque théorème mais peut diverger du compte agrégé
> si un théorème a été OPEN puis résolu hors table. La table d'État est
> l'autorité pour le compte, la table de Verdicts pour l'état formel par
> théorème.

| Ligne | Théorème | Verdict | Débloqueur |
|-------|----------|---------|------------|
| L3535 | `tricolorable_invariant` | **PROUVÉ (#11958)** | La jambe R1 close des deux côtés (#3000 + #3124/#11227). Le mur `r2_append_only_wall` (#11276, L1061) montrait l'iff FAUSSE sous le R2 append-only LIBRE — la **re-modélisation connectée** annoncée a été livrée et mergée : `Reidemeister2Connected` (def `Reidemeister.lean` L444) + transfert R2 connecté (#11469), transfert R3 connecté deux bras (#11903), puis induction du maître sur `ReidemeisterEquiv` (#11958). |
| ~L3569 | `trefoil_not_unknot` | **PROUVÉ (#8766)** | Corollaire dérivé par composition de `tricolorable_invariant` (prouvé, L3535) + `trefoil_tricolorable` + `unknot_not_tricolorable` — depuis #11958, la composition ne transporte plus aucun sorry. |
| L2267 | `Knot.unknottingNumber` | **INFRASTRUCTURE (NP-dur)** | Définition close par #15082 via `Nat.sInf` sur `{n | k.UnknottableIn n}` (zéro sorry, témoin `unknot_unknottingNumber = 0`) ; le **calcul effectif** (minimisation sur classes d'équivalence) reste NP-dur — infrastructure permanente. |
| ~L1581 | `fox` all-distinct §9.1 | **PROUVÉ (#11227)** | Le mode kink all-distinct est **vacuus** : le kink R1 `C = ⟨a,b,c,c⟩` a `e₃ = e₄ = c`, la continuité d'over-strand Path B `c₂ = c₄` force `col₂(b) = col₂(c) = col₃`, contredisant Fox all-distinct `c₂ ≠ c₃` → `absurd` clos le résiduel. Le backward R1 connecté est COMPLET. |
| ~L1731 | `col` all-distinct §9.1 | **PROUVÉ (#11227)** | Même argument de vacuité (une ligne). La construction colour-symmetry / proper-arc anticipée (#3003 §9.4-§9.6) n'est plus nécessaire — le cas ne survient jamais sous Path B. |

**Conclusion de l'audit (re-vérifiée 2026-09-14, post-#11958).**
Le marquee **`tricolorable_invariant` est PROUVÉ** : bi-implication R1
connectée (#3000 + #3124/#11227), transferts R2/R3 connectés (#11469,
#11903), induction du maître sur `ReidemeisterEquiv` (#11958, `Invariant.lean`
L3535). `Invariant.lean` ne porte **plus aucun sorry réel** — les 10 restants
du lake vivent dans `Reidemeister.lean` (2, topologie PL), `Conway.lean` (6)
et `Lidman.lean` (2). Les murs nommés `r2_append_only_wall` (L1061) /
`r3_determined_wall` (L1214) restent dans le code comme **témoins formels**
de pourquoi le modèle libre échoue — la re-modélisation connectée qu'ils
appelaient a été livrée. `trefoil_not_unknot` reste PROUVÉ par composition
(#8766), désormais sur un invariant lui-même prouvé.

## Path B : modèle de Fox classique restauré (2026-06-23, #3003)

**Décision : Path B implémenté.** Le modèle de 3-colorabilité colorait auparavant
des ARÊTES (`Fin numEdges`) indépendamment, sans contrainte d'arc-égalité — le Fox
classique force l'over-strand d'un crossing à partager une couleur (continuité sur
l'arc). Ce modèle permissif divergeait du Fox classique : il admettait des
tricolorations parasites (notamment le **figure-8**, classiquement NON
3-colorable, witness `(0,0,0,1,0,0,1,2)`) et rendait un « lemme universel » de
colorabilité VRAI pour le modèle mais FAUX classiquement — ce qui aurait rendu
`tricolorable_invariant` trivial (ne distinguant que l'unknot).

**Path B (mandaté 2026-06-23).** `triColorConditionAt` (Invariant.lean) porte
désormais la conjonction d'**arc-égalité** `c₂ = c₄` (les deux bouts de l'over-strand
d'un crossing portent la même couleur), en plus de la règle de Fox (toutes égales
OU toutes distinctes) sur les trois brins se rencontrant. C'EST l'invariant de Fox
classique (Fox 1962) : une coloration constante sur les arcs, avec la règle
all-equal-or-all-distinct à chaque crossing.

- **Non-régression vérifiée** : `trefoil_tricolorable` re-prouvé avec le témoin
  arc-respectant `(0,1,1,2,2,0)` (`decide`) ; le **figure-8** est désormais
  correctement REJETÉ (son ancien témoin permissif ne valide plus la conjonction
  d'arc).
- **GF(3) linéarité par-crossing** (`triColorFoxCondition_iff_sum_mod_three`,
  Invariant.lean, cycle-6) : la condition de Fox à un crossing équivaut à
  `toNat(c₁)+toNat(c₂)+toNat(c₃) ≡ 0 (mod 3)` — fait computationnel par-crossing,
  indépendant de l'arc. Conservé comme scaffolding. NB : ceci ne se lève PAS en
  lemme universel de colorabilité (cf. point suivant).
- **Lemme universel RETIRÉ** (`tricolorability_of_two_crossings`) : il est FAUX
  sous Path B — le figure-8 est bien-formé avec 4 crossings et n'est PAS
  Fox-tricolorable. Le raccourci rang-nullité n'est donc pas disponible ; la
  section « Withdrawn » d'Invariant.lean documente le retrait et le contre-exemple.

**Conséquence pour `tricolorable_invariant`.** Sous Path B, l'invariant n'est plus
trivial : une fois les 2 sous-buts résiduels §9.1 du transfer backward clos, la
composition forward + backward donne une bi-implication R1 sous le modèle connecté,
et l'invariant distingue GÉNUINEMENT le trèfle (tricolorable) de l'unknot (non) et
du figure-8 (non) — au lieu de n'isoler que l'unknot. Les 2 résiduels §9.1 ont été
clos par vacuité (#11227), et le marquee lui-même est prouvé (#11958) : la
distinction trèfle/unknot/figure-8 est désormais un corollaire exécutable de
l'invariant prouvé.

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

**Transfer lemma R1 connecté — forward #3000 + backward #3124, COMPLET (les 2 résiduels clos par #11227).**
Le transfer **forward** `tricolorable_forward` (#3000) est **prouvé** : sous le
modèle R1 connecté (Option C, `Reidemeister1Connected`), une tricoloration de `d₁`
se propage à `d₂`. Le transfer **backward** `tricolorable_backward` (#3124) est
désormais **complet** : `hcolPres` (préservation des couleurs sur les labels
préservés `l ∈ [1, n]`, arithmétique pure `(l-1) % numEdges` close par `rfl`) est
prouvé, et les **2 sous-buts §9.1** livrés en sorry résiduels (instruction user
2026-06-15 : « décompose, prouve le tractable, livre avec des sous-sorry
résiduels ») ont été **dischargés par #11227** :

1. `num` — **PROUVÉ (#3163)**. `d₁.numEdges ≥ 2` par parité `wf` : `_hproper`
   fournit un crossing distinct `j ≠ i` ⟹ `crossings.length ≥ 2` ⟹
   `edges.length = 4 × length ≥ 8` ⟹ par l'absurde (`numEdges = 1`) les clauses
   (a)+(b) de `wf` forcent toutes les arêtes à `1` (comptage `count 1 = length ≥ 8`),
   contredisant la clause (b) `count 1 = 2`.
2. `fox` — clos en deux temps : crossings inchangés via `hcolPres` (#3154), puis
   le résiduel du crossing modifié `Y` **dischargé par #11227** — le mode kink
   all-distinct est **vacuus** (continuité over-strand `c₂ = c₄` du kink
   `C = ⟨a,b,c,c⟩` force `col₂(b) = col₂(c) = col₃`, contredisant Fox
   all-distinct ; `absurd` en une ligne).
3. `col` — clos en deux temps : mode kink all-equal (#3168), puis le mode
   all-distinct **dischargé par #11227** par le même argument de vacuité — la
   construction colour-symmetry / proper-arc anticipée (#3003) n'est plus
   nécessaire : le cas ne survient jamais sous Path B.

**Conséquence : bi-implication R1 connectée PROUVÉE** (forward + backward
composés). La baseline CI est passée de 17 à **14** (real-mode ; historique
prose-header : bump 25→28 dans #3124, baissée à 27 après `num` #3163,
re-bumpée à 28 par #3003 ; switch real le 2026-07-11).

**Le mur R2 et le forward R2-up (#11276).** Le même cycle a livré, sans
aucun sorry : `tricolorable_forward_r2_up` (transfer forward à travers le R2
append-only du modèle libre historique, PROVEN), et les **murs nommés**
`r2_append_only_wall` (L1061 : le modèle R2 LIBRE est append-only avec bigon
flottant — le bras descendant de l'iff maître est FAUX sous ce modèle) et
`r3_determined_wall` (L1214). Ces murs **bornaient l'iff maître sous le
modèle libre** : la re-modélisation connectée R2/R3 qu'ils appelaient
(`Reidemeister2Connected`/`Reidemeister3Connected`) a été **livrée**
(#11469, #11903) et le marquee `tricolorable_invariant` **prouvé** (#11958).

Référence : Fox (1962), A quick trip through knot theory ; Adams, *The Knot Book*.

## Structure

| Fichier | Contenu | sorry réels |
|---------|---------|-------------|
| `Knots/Basic.lean` | Définitions (Knot, Link, PD-code, nœuds nommés), `KnotDiagram.wf` | 0 |
| `Knots/Reidemeister.lean` | Mouvements R1/R2/R3 (modèle Phase 5), `ReidemeisterEquiv`, symétries | 2 |
| `Knots/Invariant.lean` | 3-colorabilité (Fox), crossing number, contre-exemple PR1, bi-implication R1 connectée (#3000 + #3124/#11227), transfer R2-up + murs nommés (#11276), marquee `tricolorable_invariant` (#11958), `unknottingNumber` via `Nat.sInf` (#15082) | 0 |
| `Knots/Conway.lean` | Nœud de Conway (11n34), Piccirillo, dichotomie lisse/topologique | 6 |
| `Knots/Lidman.lean` | 11n102, unknotting number = 2 | 2 |
| `Knots/MathlibPrerequisites.lean` | Index des prérequis Mathlib manquants par tier | 0 |

## Dépendances externes

| Dépôt | Rôle | Statut |
|-------|------|--------|
| [shua/leanknot](https://github.com/shua/leanknot) (branche `lean4`) | Bricks/walls, tangles, braids | Candidat dépendance Lake (alignement toolchain en cours) |
| [vihdzp/combinatorial-games](https://github.com/vihdzp/combinatorial-games) | Nombres surréels, nimbers Conway | Déjà dans `conway_cgt_lean/` |
| [prathamesh-t/Tangle-Isabelle](https://github.com/prathamesh-t/Tangle-Isabelle) | Tangles en Isabelle/HOL | Référence de design |
| [Mathlib](https://github.com/leanprover-community/mathlib4) | Polynômes, catégories, topologie partielle | Dépendance Lake |

## Place dans l'écosystème — nouveauté réelle (digestion #13106, point 3)

Ce que ce lake apporte que ses dépendances **n'ont pas** :

- **Mathlib** (toolchain v4.32.1) ne fournit **aucun module de théorie des nœuds** — aucune entrée `Knot`/`Braid`/`Link` au top-level de l'arbre `Mathlib/` (mesuré 2026-08-31). Ni PD-codes, ni moves de Reidemeister, ni invariants de colorabilité : tout ce vocabulaire est défini ici, dans `Knots/Basic.lean`.
- **[shua/leanknot](https://github.com/shua/leanknot)** couvre bricks/walls, tangles, braids — pas les invariants de colorabilité ni leur transfert sous les moves.
- **[Tangle-Isabelle](https://github.com/prathamesh-t/Tangle-Isabelle)** (Prathamesh 2015) formalise en Isabelle/HOL, pas en Lean 4 ; cité comme référence de design, non consommable dans notre toolchain.

Les apports **originaux** du portage (formels et méthodologiques, pas mathématiques — les priorités mathématiques appartiennent à Fox, Reidemeister, Piccirillo, Freedman, Lidman, cf Références) :

1. Le **marquee `tricolorable_invariant`** (#11958) : la 3-colorabilité de Fox invariante par équivalence de Reidemeister, prouvée par induction sur les transferts connectés R1/R2/R3 (#3000, #3124/#11227, #11469, #11903) — à notre connaissance la première formalisation Lean de ce résultat.
2. Les **murs nommés** (`r2_append_only_wall`, `r3_determined_wall`, #11276) : des preuves formelles que l'énoncé cible est **faux** sous le modèle courant — le pattern « réfuter avant de prouver », opposé au scaffolding passif.
3. Le protocole **validation exhaustive brute-force AVANT énoncé** (R1 : 2526 diagrammes ; R2 : #11467 ; R3 : #11486), devenu le standard de la track #2874.

## Raccord au corpus et transmission (digestion #13106, points 9-10)

Trois notebooks dans `SymbolicAI/Lean/` assurent la transmission, par niveau :

| Notebook | Rôle | Transmission |
|---|---|---|
| `Lean-17a-Knots-Conway-Proofs.ipynb` | Histoire et visualisations Python (trèfle, Conway, Kinoshita-Terasaka) ; preuve Piccirillo (doctorante, 1 semaine, 50 ans d'attente) ; Lidman comme « preuve courte mais profonde » | Visualisations + récit, zéro prérequis Lean |
| `Lean-17b-Knots-Invariants-Companion.ipynb` | Companion exécutable : PD-codes, moves de Reidemeister, tricolorité de Fox — 5 exercices, exemples calculés | Exemples calculés + exercices |
| `Lean-17c-Knots-Companion-Formel.ipynb` | Companion formel : modules du lake non couverts par 17b, murs R2/R3, miroir i18n | Pont direct vers le code Lean |

**Prérequis** : aucun pour 17-a ; PD-codes élémentaires pour 17-b ; Lean 4 de base (tactiques, structures) pour 17-c.

**Revue humaine — état honnête** : à ce jour, le lake a été revu par les organes bots (Hermes, proof-integrity CI) et mergé par le coordinateur, mais **aucune revue humaine nommée du lake entier** n'a eu lieu. C'est une limite déclarée de la présente digestion (grille #13106 point 10) : la revue humaine reste à faire et à inscrire ici le moment venu.

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
- **#8766** PR : décharge `trefoil_not_unknot` (sorry 5→4) — la bascule README 17→16
- **#8696** Epic : corridor Reidemeister field-eqs (5 PRs MERGED : #9807/#9873/#9901/#9913/#9955) — proof clarity, pas de sorry change
- **#1647** Conway Phase 2 (jeux combinatoires, GoL)
- **#1646** Grothendieck Phase 1
- **`../../../GameTheory/conway_cgt_lean/`** — Tour des résultats `vihdzp/combinatorial-games`
- **`../../../GameTheory/SocialChoice/`** — Pattern scaffolding avec sorry résolus (Arrow, Sen, Voting)
- **`../conway_lean/`** — Jeu de Conway en Lean (cf. `MacroCell.wf`, pattern de la
  ré-modélisation Phase 5 `KnotDiagram.wf`)

## Conclusion

`knot_lean` formalise en Lean 4 des résultats classiques et modernes de théorie
des nœuds — 3-colorabilité de Fox, nombre de croisements, nœud de Conway (11n34),
Lidman 11n102 — sur l'axiomatique minimale `[propext, Quot.sound]` (aucun
`sorryAx`). L'Epic #2874 (Phase 5) a **fermé son front principal** : l'invariant
de 3-colorabilité est prouvé sous le modèle connecté des mouvements de
Reidemeister (`tricolorable_invariant`, #11958) — `Invariant.lean` est sorry-free.

### Ce qui est acquis

Les **invariants locaux** sont solides : 3-colorabilité du trèfle et
non-colorabilité de l'unknot, nombre de croisements du trèfle, symétries et
clôture réflexive-transitive des moves, et la *well-formedness* paritaire
`KnotDiagram.wf` des diagrammes nommés. Le **transfer forward** de la
3-colorabilité sous R1 connecté (`#3000`) est **prouvé** sans sorry, et le
**transfer backward** (`#3124` complété par `#11227`) est **établi** : le cœur
constructif `hcolPres`, le sous-but `num` (parité `wf`, `#3163`) et les 2
résiduels `fox`/`col` (mode all-distinct vacuus, `#11227`) sont clos — la
**bi-implication R1 connectée est PROUVÉE**. Le **corollaire
`trefoil_not_unknot`** (#8766) est **prouvé** par composition — et depuis
#11958, l'invariant composé est lui-même prouvé : le corollaire ne transporte
plus aucun sorry. Le **transfer forward R2-up**
(`tricolorable_forward_r2_up`, #11276) est **prouvé sans sorry**, encadré par
les murs nommés `r2_append_only_wall` (L1061)/`r3_determined_wall` (L1214)
(témoins formels du modèle libre ; **14 sorry réels** au total à l'époque de
#11227 ; baseline CI recalibrée à 10 post-#15082, cf. § État des sorries), et
le marquee `tricolorable_invariant` est **prouvé** (#11958).

Le **corridor Reidemeister #8696** (5 PRs MERGED, c.8162-c.8169) a par
ailleurs clarifié la structure des 6 sites de move-surgery en `Reidemeister.lean` :
preuves directes par `⟨rfl, rfl⟩` après field-eqs refactor — gain de lisibilité,
**zéro impact** sur le compte sorry (le corridor ne visait pas la fermeture
des théorèmes gated PL).

### Le verrou — levé

Le marquee `tricolorable_invariant` est **prouvé** (#11958). Le verrou historique
a changé de nature deux fois, et la séquence reste méthodologiquement
instructive : les résiduels §9.1 d'abord (clos par vacuité, #11227), puis le
**modèle R2 lui-même** — le mur `r2_append_only_wall` (#11276, L1061) prouve que
le constructeur `ReidemeisterStep.r2` libre (append-only) relie `emptyDiagram`
(non tricolorable) à `twoTwinCrossings` (tricolorable), rendant le bras
descendant de l'iff maître **FAUX sous le modèle libre**. La
**re-modélisation connectée R2/R3** (`Reidemeister2Connected` L444 /
`Reidemeister3Connected` L694) a alors été livrée par le protocole « validation
exhaustive AVANT preuve » (#11467/#11486), les transferts connectés prouvés
(#11469, #11903), et le maître clos par induction (#11958). Les résultats
« lointains » — Conway non-slice (Piccirillo), unknotting number de Lidman,
théorème Reidemeister ↔ isotopie ambiante — restent du **scaffolding
permanent** : ils excèdent la portée actuelle de Mathlib (topologie PL des
3-variétés, Heegaard-Floer).

### Leçons méthodologiques — chemin de découverte vs reconstruction

Ce qui suit est le **chemin de découverte** — l'ordre dans lequel les obstacles
ont été rencontrés et compris — distingué de la **reconstruction finale** que
donnent les PRs mergées et l'ordre du code : chaque re-modélisation ci-dessous
a d'abord été *réfutée* avant d'être corrigée, et cet ordre des échecs ne se
lit dans aucun diff (digestion #13106, point 7).

La trajectoire Phase 5 illustre le pattern « *intractable* = énoncé faux » (cf.
`conway_lean` P4) : avant de prouver, **vérifier par contre-exemple certifié** que
l'énoncé est vrai sous le modèle courant. Trois re-modélisations successives
(Phase 3 → PR1 `wf`+ρ → PR1.5 ρ-déterminé) ont chacune été **réfutées par un
témoin prouvé** (`#2915`, `#2938`) avant que l'analyse de parité (2026-06-14) ne
révèle que le modèle append+`wf` est *structurellement trop faible* (il n'admet
que des kinks disjoints). La **surgery connectée** (Option C, `#2980` ; R3
déterminé, `#3088`) corrige ce défaut. La **décomposition** du backward
(`#3124`) — prouver le tractable, livrer avec sous-sorry résiduels documentés —
a payé deux fois : les résiduels ont été clos par un argument de **vacuité**
(#11227 : le mode kink all-distinct ne survient jamais sous Path B — la
construction research-level anticipée était inutile), et le pattern
« validation exhaustive brute-force AVANT l'énoncé Lean » (R1 : 2526
diagrammes/24 échecs monogones ; R2 : #11467 ; R3 : #11486) est devenu le
protocole standard de la track.

### Prochaines étapes

1. ~~Livrer la re-modélisation connectée R2/R3 puis le maître~~ — **fait** :
   `Reidemeister2Connected` (#11469), transferts R3 connectés (#11903),
   `tricolorable_invariant` prouvé (#11958).
2. Poursuivre la réduction des 10 sorry restants : Conway via le split #14821
   (`conway_trivial_alexander` #15440, `KT_trivial_alexander` #15460, qui
   portent la recalibration de la baseline CI), puis Lidman 11n102.
3. Scaffolding lointain : attendre l'évolution de Mathlib (3-variétés,
   Heegaard-Floer) pour Conway et Lidman.

/-
Knots.ReidemeisterInvariance — Invariance des invariants sous Reidemeister
=========================================================================

Domicile du theoreme d'invariance : `alexanderPolynomialSigned` est invariant
sous les trois mouvements de Reidemeister (issue #16650, tranche 3 du socle
Alexander, cadrage `docs/lean/alexander-strategy/c652-reidemeister-invariance.md`).

Pourquoi un module separe : le theoreme croise `Reidemeister3Connected`
(`Knots.Reidemeister`) et `alexanderPolynomialSigned` (`Knots.Conway`).
`Knots.Conway` importe `Knots.Invariant`, qui importe `Knots.Reidemeister` —
importer `Knots.Conway` suffit donc a voir les deux, et l'inverse serait un
cycle. Ce module est le point ou les deux theories se rencontrent.

Convention i18n (EPIC #4980) : ce fichier est **FR canonique**, avec son miroir
anglais dans le sibling `ReidemeisterInvariance_en.lean`.
-/

import Knots.Conway

namespace Knots

/-! ## 1. La bifurcation `i = 0` / `i ≥ 1` (mise au point du cadrage)

Le cadrage c652 (§4.1) presente R3 comme « trivial par reindexation ». C'est
vrai **sous une condition qui n'y est pas enoncee** : que le triangle soit
entierement hors de la ligne eliminee du mineur designe.

`alexanderPolynomialSigned` supprime la **premiere** ligne (`rest` = queue de
`crossings`) et la derniere colonne du mineur. Donc :

* **`i ≥ 1`** — les trois lignes reecrites du triangle sont dans le corps de la
  matrice ; l'invariance est un argument de reindexation : la chirurgie ne
  change ni le nombre de croisements, ni le nombre d'aretes, et la partition
  d'arcs est preservee (section 2 ci-dessous). Le mineur est inchange au
  transport des colonnes pres.
* **`i = 0`** — la ligne 0 porte un sommet du triangle, et c'est precisement
  celle que le mineur designe **elimine**. La reindexation ne suffit plus : le
  mineur change de forme (des coefficients quittent les colonnes du triangle
  pour d'autres), et l'invariance ne peut se lire qu'a une **unite** `±t^k`
  pres — c'est l'argument determinant al des sections 4.2-4.3 du cadrage
  (colonne non partagee, rang du mineur augmente).

Les deux cas sont donc de nature differente et doivent etre des theoremes
distincts. Les confondre ferait passer `i = 0` pour un oubli de preuve alors que
c'est le cas ou le mineur designe change reellement de forme.

## 2. L'obligation de preservation de la partition d'arcs

L'argument de reindexation (`i ≥ 1`) repose sur une premiere que le cadrage
**suppose sans la prouver** : `arcPartition` est preservee par la chirurgie.

Precisons l'obstacle sur le temoin : la chirurgie R3 connectee reecrit les
paires `(e2, e4)` des trois croisements du triangle (cf `Conway.lean`,
`pairs := d.crossings.map (fun c => (c.e2, c.e4))`). Sur le temoin du lake
(`reidemeister3Connected_satisfiable`), ces paires coincident comme paires
**non orientees** —

    X : (2,8), (7,4), (8,6)      Y : (4,7), (2,8), (8,6)

— mais seule l'**orientation** de la paire centrale differe ((7,4) contre
(4,7)), et les croisements reecrits changent de **position** dans la liste du
repli. Le repli voit des paires orientees prises dans l'ordre de la liste :
la preservation n'y est donc **pas vide** — elle exige d'absorber l'une et
l'autre difference, par l'insensibilite a l'orientation d'une paire
(`mergePair_symm`, #17429) puis par la commutation des fusions au niveau des
classes (`mergePair_mergePair_comm_equiv`, #17646). Ce qui est preserve par
ailleurs est le **multi-ensemble des etiquettes** (docstring de
`Reidemeister3Connected`), d'ou `wf`.

Ce temoin ne suffit pas, a lui seul, a fonder la preservation generale : un
diagramme ou les paires `(e2, e4)` du triangle different reellement comme
multi-ensemble reste a exhiber. C'est le premier verrou de la tranche, avant
tout argument de reindexation.
-/

/-! ## 3. Controle : la partition d'arcs du temoin R3 est preservee

Le temoin est celui de `reidemeister3Connected_satisfiable` (litteraux repris
tel quels) : les deux diagrammes sont bien formes (`decide` sur `wf` au lake),
et leur partition d'arcs — 5 classes pour 10 aretes — est **la meme** de part et
d'autre de la chirurgie. C'est le controle positif de la section 2 : les paires
`(e2,e4)` du triangle y coincident non orientees, avec une orientation et une
position de repli differentes — le repli produit la meme partition, et c'est
`foldl_mergePair_swap` (orientation) puis `foldl_mergePair_permute_adjacent`
(transposition des positions) qui le justifient. La forme generale (sur des
diagrammes ou les paires du triangle different) est etablie en section 5.
-/

/-- Controle de la tranche 3 (etape 1) : sur la paire temoin du move R3
    connecte, la chirurgie preserve `arcPartition` — les paires `(e2,e4)` du
    triangle coincident non orientees, et le repli absorbe leurs differences
    d'orientation et de position (`foldl_mergePair_swap`,
    `foldl_mergePair_permute_adjacent`). C'est la premiere que l'argument de
    reindexation (cas `i ≥ 1`) suppose ; la forme generale est etablie par
    `Reidemeister3Connected.arcPartition_sameRel` (section 5). -/
theorem reidemeister3Connected_arcPartition_witness :
    arcPartition
        { crossings := [⟨1, 2, 7, 8⟩, ⟨3, 7, 9, 4⟩, ⟨9, 8, 5, 6⟩,
                        ⟨1, 2, 10, 10⟩, ⟨3, 4, 5, 6⟩], numEdges := 10 }
      = arcPartition
        { crossings := [⟨3, 4, 9, 7⟩, ⟨9, 2, 5, 8⟩, ⟨7, 8, 1, 6⟩,
                        ⟨1, 2, 10, 10⟩, ⟨3, 4, 5, 6⟩], numEdges := 10 } := by
  decide

/-! ## 4. Controle negatif : le mineur designe s'effondre sur le temoin Y

La section 3 etablit la **premiere** de l'argument de reindexation (la
partition d'arcs est preservee). Le controle de **conclusion** attendu — le
polynome signe du temoin est le meme des deux cotes — est **refute sur ce
temoin**, et c'est une information de cadrage, pas un echec de preuve :

* cote X, le mineur designe vaut `t³ - t²` (chiralite toute positive) ;
* cote Y, le mineur designe est **identiquement nul** — et la sonde Python
  fidele a la construction (validee sur les valeurs kernel de `trefoil` et
  `figureEight` signe) mesure la meme nullite pour chacune des cinq colonnes
  supprimables et chacune des 32 chiralites.

La cause se lit sur les lignes de la matrice : la chirurgie reecrit
`(9, 8, 5, 6)` en `(7, 8, 1, 6)`, dont toutes les etiquettes non singleton
(`7`, `8`, `6`) tombent dans la grande classe du temoin — sa ligne, comme
celle du kink `(1, 2, 10, 10)` (kink R1 exact : `e3 = e4`), ne porte plus que
sur la colonne de l'arc singleton `{1}` et sur la colonne supprimee de la
grande classe. Deux lignes proportionnelles : le rang tombe a 3 et tout
mineur `4 × 4` s'annule.

Le classique « tout mineur `(n-1) × (n-1)` de la matrice d'Alexander vaut
`± t^k · Δ` » suppose la matrice de rang `n - 1` ; le kink ajoute une
relation, et la normalisation designee (premiere ligne et derniere colonne
supprimees, **fixes**) ne survit pas a la chirurgie. Consequence pour la
section 1 : l'argument de reindexation du cas `i ≥ 1` devra soit s'entenir
de diagrammes sans kink, soit rendre le couple (ligne, colonne) supprime
adaptatif.
-/

/-- Determinant 4×4 generique, meme esprit que `det_two_aux` / `det_three_aux`
    de `Conway.lean` : expansion de Laplace le long de la premiere colonne, les
    mineurs 3×3 etant traites par `det_three_aux`. -/
theorem det_four_aux (A : Matrix (Fin 4) (Fin 4) (Polynomial ℤ)) :
    A.det = A 0 0 * (A.submatrix (Fin.succAbove 0) (Fin.succAbove 0)).det
          - A 1 0 * (A.submatrix (Fin.succAbove 1) (Fin.succAbove 0)).det
          + A 2 0 * (A.submatrix (Fin.succAbove 2) (Fin.succAbove 0)).det
          - A 3 0 * (A.submatrix (Fin.succAbove 3) (Fin.succAbove 0)).det := by
  rw [Matrix.det_succ_column_zero]
  simp (config := { decide := true }) [Fin.sum_univ_succ]
  simp (config := { decide := true }) [det_three_aux, Matrix.submatrix_apply,
    Fin.succAbove]
  ring

/-- Controle de la tranche 3 : cote X, le mineur designe du polynome signe
    (chiralite toute positive) vaut `t³ - t²` — il n'est pas degenere. C'est la
    contrepartie positive du controle negatif suivant : c'est bien la chirurgie
    qui effondre le mineur, pas une degenerescence anterieure. -/
theorem reidemeister3Connected_alexanderSigned_witness_X :
    alexanderPolynomialSigned
        { crossings := [⟨1, 2, 7, 8⟩, ⟨3, 7, 9, 4⟩, ⟨9, 8, 5, 6⟩,
                        ⟨1, 2, 10, 10⟩, ⟨3, 4, 5, 6⟩], numEdges := 10 }
        [true, true, true, true, true]
      = Polynomial.X ^ 3 - Polynomial.X ^ 2 := by
  simp only [alexanderPolynomialSigned]
  simp (config := { decide := true })
  rw [det_four_aux]
  simp only [det_three_aux]
  simp only [Matrix.submatrix_apply, Fin.succAbove, Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntrySigned, alexanderEntry,
    alexanderEntryNeg]
  ring

/-- Controle negatif de la tranche 3 : cote Y, **le meme mineur designe est
    identiquement nul** — la chirurgie R3 du temoin aligne la ligne du
    croisement reecrit `(7, 8, 1, 6)` sur celle du kink `(1, 2, 10, 10)`
    (toutes deux ne portent plus que sur l'arc singleton `{1}` et la grande
    classe supprimee), le rang tombe a 3 et le determinant s'annule (sonde :
    nullite pour les cinq colonnes supprimables et les 32 chiralites). La
    normalisation designee ne survit pas a la chirurgie sur un temoin porteur
    de kink — cf section 4 du module. -/
theorem reidemeister3Connected_alexanderSigned_witness_Y_zero :
    alexanderPolynomialSigned
        { crossings := [⟨3, 4, 9, 7⟩, ⟨9, 2, 5, 8⟩, ⟨7, 8, 1, 6⟩,
                        ⟨1, 2, 10, 10⟩, ⟨3, 4, 5, 6⟩], numEdges := 10 }
        [true, true, true, true, true]
      = 0 := by
  simp only [alexanderPolynomialSigned]
  simp (config := { decide := true })
  rw [det_four_aux]
  simp only [det_three_aux]
  simp only [Matrix.submatrix_apply, Fin.succAbove, Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntrySigned, alexanderEntry,
    alexanderEntryNeg]
/-! ## 5. Preservation generale de la partition d'arcs (premier verrou, #16650)

La chirurgie R3 connectee reecrit les trois croisements du triangle X en le
triangle Y. Lue sur les paires de passage-dessus `(e2, e4)` qui alimentent le
repli `arcPartition`, la chirurgie ne change que les **positions `i` et `i+1`**
de la liste de paires :

* triangle X — `⟨a₂,a₁,g₁,g₂⟩, ⟨a₃,g₁,g₃,b₃⟩, ⟨g₃,g₂,b₂,b₁⟩` — paires
  `(a₁,g₂), (g₁,b₃)`, puis `(g₂,b₁)` inchangee en position `i+2` ;
* triangle Y — `⟨a₃,b₃,g₃,g₁⟩, ⟨g₃,a₁,b₂,g₂⟩, ⟨g₁,g₂,a₂,b₁⟩` — paires
  `(b₃,g₁), (a₁,g₂)`, meme `(g₂,b₁)` en `i+2`.

Le passage de X a Y est donc exactement : une **transposition adjacente** des
deux premieres paires, composee d'une **symetrie interne** de la paire en
position `i` (`(g₁,b₃)` devenant `(b₃,g₁)`). La symetrie interne est absorbee
par `mergePair_symm` / `foldl_mergePair_swap` ; la transposition adjacente est
absorbee par la commutation au niveau des classes
`mergePair_mergePair_comm_equiv` (#17646) : les deux partitions intermediaires
different comme listes (contre-exemple documente sur #16650) mais portent la
meme relation « partager une classe ».

L'etape restante etablie ici : cette equivalence au niveau des classes
**traverse le reste du repli** — deux partitions qui portent la meme relation
SameClass la portent encore apres tout suffixe commun de fusions
(`sameRel_foldl`), sous l'hypothese `ClassesDisjoint` (garantie pour toute
partition issue du repli depuis les singletons, `foldl_partition_inv`).
Le resultat est la preservation **generale** de la partition d'arcs — le
« premier verrou » nomme en section 2, desormais etabli au niveau des classes.

Ce qui reste hors de ce theoreme : la remontee au niveau de la **matrice**
(l'equivalence de classes donne une permutation des colonnes du mineur, donc
une invariance du determinant au signe pres — argument a ecrire pour la
tranche `alexanderSigned_invariant_under_R3`).
-/

/-- Sous disjonction des classes, le premier disjonctif de la
    caracterisation de `SameClass` apres fusion se lit en `SameClass` purs :
    une classe commune qui n'est pas touchee, c'est `x ~ y` sans `x ~ u` ni
    `x ~ v` (l'unicite de la classe de `x` vient de la disjonction). -/
lemma exists_class_not_hit_iff {P : List (List Nat)} (hd : ClassesDisjoint P)
    {x y u v : Nat} :
    (∃ C ∈ P, x ∈ C ∧ y ∈ C ∧ ¬((C.contains u || C.contains v) = true)) ↔
      SameClass P x y ∧ ¬ SameClass P x u ∧ ¬ SameClass P x v := by
  constructor
  · rintro ⟨C, hC, hx, hy, hnot⟩
    refine ⟨⟨C, hC, hx, hy⟩, ?_, ?_⟩ <;> rintro ⟨D, hD, hxD, hzD⟩
    · by_cases hCD : C = D
      · have : (C.contains u || C.contains v) = true := by
          rw [hit_iff_mem]; exact Or.inl (by rw [hCD]; exact hzD)
        exact hnot this
      · exact hd C hC D hD hCD x hx hxD
    · by_cases hCD : C = D
      · have : (C.contains u || C.contains v) = true := by
          rw [hit_iff_mem]; exact Or.inr (by rw [hCD]; exact hzD)
        exact hnot this
      · exact hd C hC D hD hCD x hx hxD
  · rintro ⟨⟨C, hC, hx, hy⟩, h1, h2⟩
    refine ⟨C, hC, hx, hy, ?_⟩
    rw [hit_iff_mem]
    push_neg
    exact ⟨fun huC => h1 ⟨C, hC, hx, huC⟩, fun hvC => h2 ⟨C, hC, hx, hvC⟩⟩

/-- `SameClass` apres une fusion, caracterise uniquement en `SameClass` de la
    partition d'origine (sous disjonction des classes) : soit une classe
    commune hors du groupe fusionne, soit deux etiquettes happes par la
    fusion. C'est la forme qui rend l'equivalence de partitions transportable. -/
lemma sameClass_mergePair_iff_rel {P : List (List Nat)} (hd : ClassesDisjoint P)
    {u v x y : Nat} :
    SameClass (mergePair P u v) x y ↔
      (SameClass P x y ∧ ¬ SameClass P x u ∧ ¬ SameClass P x v) ∨
      ((SameClass P u x ∨ SameClass P v x) ∧ (SameClass P u y ∨ SameClass P v y)) := by
  rw [sameClass_mergePair_iff, exists_class_not_hit_iff hd,
    touches_iff_sameClass, touches_iff_sameClass]

/-- Deux partitions sont equivalentes quand elles portent la meme relation
    « partager une classe ». C'est le bon niveau d'invariance de `arcPartition`
    sous la chirurgie R3 : l'egalite des listes est refusee par le
    contre-exemple documente sur #16650, mais la relation de classes — celle
    dont la matrice d'Alexander depend — est preservee. -/
def SameRel (P Q : List (List Nat)) : Prop :=
  ∀ x y : Nat, SameClass P x y ↔ SameClass Q x y

/-- L'equivalence de partitions traverse une etape de fusion : la
    caracterisation `sameClass_mergePair_iff_rel` ne parle que de `SameClass`
    de la partition d'origine, donc deux partitions equivalentes le restent
    apres la meme fusion. -/
lemma sameRel_mergeStep {P Q : List (List Nat)} (hrel : SameRel P Q)
    (hdP : ClassesDisjoint P) (hdQ : ClassesDisjoint Q) (p : Nat × Nat) :
    SameRel (mergeStep P p) (mergeStep Q p) := by
  intro x y
  simp only [mergeStep]
  rw [sameClass_mergePair_iff_rel hdP, sameClass_mergePair_iff_rel hdQ]
  simp only [SameRel] at hrel
  simp only [hrel]

/-- L'equivalence de partitions traverse un repli complet : deux partitions
    equivalentes (et disjointes) le restent apres tout suffixe commun de
    fusions. -/
lemma sameRel_foldl {P Q : List (List Nat)} (hrel : SameRel P Q)
    (hdP : ClassesDisjoint P) (hdQ : ClassesDisjoint Q)
    (pairs : List (Nat × Nat)) :
    SameRel (pairs.foldl mergeStep P) (pairs.foldl mergeStep Q) := by
  induction pairs generalizing P Q with
  | nil => exact hrel
  | cons p ps ih =>
      rw [List.foldl_cons]
      exact ih (sameRel_mergeStep hrel hdP hdQ p)
        (classesDisjoint_mergePair hdP) (classesDisjoint_mergePair hdQ)

/-! ### Lecriture `List.set` en take/drop

La chirurgie etant un triple `List.set`, la lecture take/cons/drop de ces
reecritures est l'outil du decoupage du repli. Trois lemmes standards, prouves
par induction — les bornes sont necessaires : sur liste trop courte, `set`
est sans effet alors que le membre de droite tronque.
-/

/-- `List.set` en lecture take/cons/drop (indice borne). -/
lemma set_take_drop {α : Type} (l : List α) (i : Nat) (x : α)
    (h : i < l.length) :
    l.set i x = l.take i ++ [x] ++ l.drop (i + 1) := by
  induction l generalizing i with
  | nil => exact absurd h (Nat.not_lt_zero i)
  | cons a as ih =>
      rcases i with _ | j
      · simp
      · have hj : j < as.length := by simpa using h
        simp only [List.set_cons_succ, List.take_succ_cons, List.cons_append,
          List.drop_succ_cons, ih j hj]

/-- Reecriture d'une valeur deja en place : `set` a l'indice borne avec la
    valeur courante est l'identite. -/
lemma set_get_self {α : Type} (l : List α) (i : Nat) (h : i < l.length) :
    l.set i (l.get ⟨i, h⟩) = l := by
  rw [set_take_drop l i _ h, take_cons_drop_eq l i h]

/-- Double `List.set` consecutif en lecture take/drop. -/
lemma set2_take_drop {α : Type} (l : List α) (i : Nat) (x₀ x₁ : α)
    (h1 : i + 1 < l.length) :
    (l.set i x₀).set (i + 1) x₁ = l.take i ++ [x₀, x₁] ++ l.drop (i + 2) := by
  induction l generalizing i with
  | nil => exact absurd h1 (Nat.not_lt_zero (i + 1))
  | cons a as ih =>
      rcases i with _ | j
      · have hA : 0 < as.length := by simpa using h1
        simp only [List.set_cons_zero, List.set_cons_succ, List.cons_append,
          List.drop_succ_cons, List.drop_drop, List.nil_append, List.cons_append]
        simpa using set_take_drop as 0 x₁ hA
      · have hj : j + 1 < as.length := by simpa using h1
        simp only [List.set_cons_succ, List.take_succ_cons, List.cons_append,
          List.drop_succ_cons, ih j hj]

/-- Triple `List.set` consecutif en lecture take/drop — la forme exacte de la
    chirurgie R3 connectee lue sur la liste de paires. -/
lemma set3_take_drop {α : Type} (l : List α) (i : Nat) (x₀ x₁ x₂ : α)
    (h2 : i + 2 < l.length) :
    ((l.set i x₀).set (i + 1) x₁).set (i + 2) x₂ =
      l.take i ++ [x₀, x₁, x₂] ++ l.drop (i + 3) := by
  induction l generalizing i with
  | nil => exact absurd h2 (Nat.not_lt_zero (i + 2))
  | cons a as ih =>
      rcases i with _ | j
      · have hB : 0 + 1 < as.length := by
          simp only [List.length_cons] at h2 ⊢; omega
        have h2as := set2_take_drop as 0 x₁ x₂ hB
        simp only [List.set_cons_zero, List.set_cons_succ, List.cons_append]
        simpa using h2as
      · have hj : j + 2 < as.length := by
          simp only [List.length_cons] at h2 ⊢; omega
        simp only [List.set_cons_succ, List.take_succ_cons, List.cons_append,
          List.drop_succ_cons, ih j hj]

/-- `map` commute a `List.set` : reecrire un croisement puis projeter, ou
    projeter puis reecrire la projection, donne la meme liste de paires. -/
lemma map_set {α β : Type} (f : α → β) (l : List α) (i : Nat) (x : α) :
    (l.set i x).map f = (l.map f).set i (f x) := by
  induction l generalizing i with
  | nil => simp
  | cons a as ih =>
      rcases i with _ | j
      · simp
      · simpa using ih j

/-! ### `wf` donne `EdgesInRange`

La couverture des paires par les singletons (`crossings_covered_singles`)
exige `EdgesInRange` ; or la branche non degeneree de `wf` contient
exactement cette condition — l'extraire evite d'ajouter une hypothese ad hoc
aux mouvements de Reidemeister, qui portent deja `wf`. -/

/-- La branche non degeneree de `wf` contient exactement `EdgesInRange` : un
    diagramme bien forme non vide a toutes ses etiquettes dans la plage
    `1..numEdges`. -/
lemma wf_edgesInRange {d : KnotDiagram} (hne : d.crossings ≠ [])
    (hwf : d.wf = true) : EdgesInRange d := by
  simp only [KnotDiagram.wf, if_neg hne, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at hwf
  intro c hc
  have hall : ∀ z ∈ [c.e1, c.e2, c.e3, c.e4], 1 ≤ z ∧ z ≤ d.numEdges := by
    intro z hz
    exact hwf.1 z (List.mem_flatMap.mpr ⟨c, hc, hz⟩)
  have h1 := hall c.e1 (by simp)
  have h2 := hall c.e2 (by simp)
  have h3 := hall c.e3 (by simp)
  have h4 := hall c.e4 (by simp)
  exact ⟨h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2⟩

/-- Triple `List.set` consecutif qui re-set les valeurs deja en place :
    la chirurgie R3 vue cote `d₁` reecrit chaque position avec sa valeur
    courante. Lemme outil generique (termes closes sur des variables de
    liste), isole pour tenir le cout d'elaboration : la machinerie
    identite + decoupage s'elabore une fois pour toutes ici, sur des
    petits termes. -/
private lemma set3_self_decomp {α : Type} (L : List α) (i : Nat) (x₀ x₁ x₂ : α)
    (h0 : i < L.length) (h1 : i + 1 < L.length) (h2 : i + 2 < L.length)
    (e0 : L.get ⟨i, h0⟩ = x₀) (e1 : L.get ⟨i + 1, h1⟩ = x₁)
    (e2 : L.get ⟨i + 2, h2⟩ = x₂) :
    ((L.set i x₀).set (i + 1) x₁).set (i + 2) x₂ = L ∧
    ((L.set i x₀).set (i + 1) x₁).set (i + 2) x₂ =
      L.take i ++ [x₀, x₁, x₂] ++ L.drop (i + 3) := by
  have s0 : L.set i x₀ = L := by
    have hs := set_get_self L i h0
    rwa [e0] at hs
  have s1 : (L.set i x₀).set (i + 1) x₁ = L := by
    rw [s0]
    have hs := set_get_self L (i + 1) h1
    rwa [e1] at hs
  have s2 : ((L.set i x₀).set (i + 1) x₁).set (i + 2) x₂ = L := by
    rw [s1]
    have hs := set_get_self L (i + 2) h2
    rwa [e2] at hs
  exact ⟨s2, set3_take_drop L i x₀ x₁ x₂ h2⟩

/-- Pont get/map : la forme `List.get` (celle que produisent les `rw` de ce
    fichier) n'est pas celle de `List.getElem_map` (getElem), et le passage
    de la preuve de `i < l.length` a `i < (l.map f).length` exige un
    transport que `rw` refuse. Lemme generique par induction, isole ici pour
    garder des petits termes dans `pairs_append_forms`. -/
private lemma map_get_bridge {α β : Type} (f : α → β) (l : List α) (i : Nat)
    (h : i < l.length) (h' : i < (l.map f).length) :
    (l.map f).get ⟨i, h'⟩ = f (l.get ⟨i, h⟩) := by
  induction l generalizing i with
  | nil => exact absurd h (Nat.not_lt_zero _)
  | cons a as ih =>
      rcases i with _ | j
      · simp
      · simpa using ih j (by simpa using h) (by simpa using h')


/-- Lecture de la chirurgie R3 sur les listes de paires (e2, e4) : les deux
    listes de paires de `d₁` et `d₂` partagent prefixe et suffixe, et ne
    different que sur deux positions consecutives — transposition adjacente
    `(a₁,g₂) (g₁,b₃)` vs `(b₃,g₁) (a₁,g₂)`. La couverture des singletons est
    transportee pour les deux milieux. Lemme intermediaire du theoreme
    `arcPartition_sameRel`, separe pour tenir le cout d'elaboration : le gros
    terme `d₁.crossings.map (fun c => (c.e2, c.e4))` est plie par `set`, et la
    machinerie identite/decoupage vit dans `set3_self_decomp`. -/
private lemma pairs_append_forms {d₁ d₂ : KnotDiagram}
    (h : Reidemeister3Connected d₁ d₂) :
    ∃ A B : List (Nat × Nat), ∃ a₁ b₁ b₃ g₁ g₂ : Nat,
      d₁.crossings.map (fun c => (c.e2, c.e4)) = A ++ [(a₁, g₂), (g₁, b₃), (g₂, b₁)] ++ B ∧
      d₂.crossings.map (fun c => (c.e2, c.e4)) = A ++ [(b₃, g₁), (a₁, g₂), (g₂, b₁)] ++ B ∧
      (∀ q ∈ A ++ [(a₁, g₂), (g₁, b₃)],
        Covered ((List.range d₁.numEdges).map (fun k => [k + 1])) q.1 ∧
        Covered ((List.range d₁.numEdges).map (fun k => [k + 1])) q.2) ∧
      (∀ q ∈ A ++ [(b₃, g₁), (a₁, g₂)],
        Covered ((List.range d₁.numEdges).map (fun k => [k + 1])) q.1 ∧
        Covered ((List.range d₁.numEdges).map (fun k => [k + 1])) q.2) := by
  obtain ⟨hwf₁, _, _, _, i, hi, a₁, a₂, a₃, b₁, b₂, b₃, g₁, g₂, g₃,
      hnd, hg0, hg1, hg2, hsurg⟩ := h
  have hne : d₁.crossings ≠ [] := by
    intro hc
    rw [hc] at hi
    exact absurd hi (Nat.not_lt_zero _)
  have hEIR := wf_edgesInRange hne hwf₁
  set L := d₁.crossings.map (fun c => (c.e2, c.e4)) with hL
  have hlen : L.length = d₁.crossings.length := by
    rw [hL]
    exact List.length_map _
  have hi0 : i < L.length := by omega
  have hi1 : i + 1 < L.length := by omega
  have hi2 : i + 2 < L.length := by omega
  have hic0 : i < d₁.crossings.length := by omega
  have hic1 : i + 1 < d₁.crossings.length := by omega
  have hic2 : i + 2 < d₁.crossings.length := hi
  have hg0' : d₁.crossings.get ⟨i, hic0⟩ = { e1 := a₂, e2 := a₁, e3 := g₁, e4 := g₂ } := hg0
  have hg1' : d₁.crossings.get ⟨i + 1, hic1⟩ = { e1 := a₃, e2 := g₁, e3 := g₃, e4 := b₃ } := hg1
  have hg2' : d₁.crossings.get ⟨i + 2, hic2⟩ = { e1 := g₃, e2 := g₂, e3 := b₂, e4 := b₁ } := hg2
  have hgp0 : L.get ⟨i, hi0⟩ = (a₁, g₂) := by
    show (d₁.crossings.map (fun c => (c.e2, c.e4))).get ⟨i, hi0⟩ = (a₁, g₂)
    rw [map_get_bridge _ _ _ hic0 hi0, hg0']
  have hgp1 : L.get ⟨i + 1, hi1⟩ = (g₁, b₃) := by
    show (d₁.crossings.map (fun c => (c.e2, c.e4))).get ⟨i + 1, hi1⟩ = (g₁, b₃)
    rw [map_get_bridge _ _ _ hic1 hi1, hg1']
  have hgp2 : L.get ⟨i + 2, hi2⟩ = (g₂, b₁) := by
    show (d₁.crossings.map (fun c => (c.e2, c.e4))).get ⟨i + 2, hi2⟩ = (g₂, b₁)
    rw [map_get_bridge _ _ _ hic2 hi2, hg2']
  have hpairs₂' : d₂.crossings.map (fun c => (c.e2, c.e4)) =
      ((L.set i (b₃, g₁)).set (i + 1) (a₁, g₂)).set (i + 2) (g₂, b₁) := by
    rw [hsurg, map_set, map_set, map_set]
  obtain ⟨s2eq, hdec₁⟩ :=
    set3_self_decomp L i (a₁, g₂) (g₁, b₃) (g₂, b₁) hi0 hi1 hi2 hgp0 hgp1 hgp2
  have hdec₂ : ((L.set i (b₃, g₁)).set (i + 1) (a₁, g₂)).set (i + 2) (g₂, b₁) =
      L.take i ++ [(b₃, g₁), (a₁, g₂), (g₂, b₁)] ++ L.drop (i + 3) :=
    set3_take_drop L i _ _ _ hi2
  have hP1 : L = L.take i ++ [(a₁, g₂), (g₁, b₃), (g₂, b₁)] ++ L.drop (i + 3) := by
    rw [← hdec₁, s2eq]
  have hP2 : d₂.crossings.map (fun c => (c.e2, c.e4)) =
      L.take i ++ [(b₃, g₁), (a₁, g₂), (g₂, b₁)] ++ L.drop (i + 3) := by
    rw [hpairs₂', hdec₂]
  have hmem0 : d₁.crossings.get ⟨i, hic0⟩ ∈ d₁.crossings := List.getElem_mem hic0
  have hmem1 : d₁.crossings.get ⟨i + 1, hic1⟩ ∈ d₁.crossings := List.getElem_mem hic1
  have hEIR0 := hEIR _ hmem0
  have hEIR1 := hEIR _ hmem1
  rw [hg0] at hEIR0
  rw [hg1] at hEIR1
  obtain ⟨_, _, ha₁, ha₁', hg₁lo, hg₁hi, hg₂lo, hg₂hi⟩ := hEIR0
  obtain ⟨_, _, _, _, _, _, hb₃lo, hb₃hi⟩ := hEIR1
  have hcovA : ∀ q ∈ L.take i,
      Covered ((List.range d₁.numEdges).map (fun k => [k + 1])) q.1 ∧
      Covered ((List.range d₁.numEdges).map (fun k => [k + 1])) q.2 := by
    intro q hq
    refine crossings_covered_singles hEIR q ?_
    rw [← hL]
    exact List.mem_of_mem_take hq
  have hcovmid1 : ∀ q ∈ [(a₁, g₂), (g₁, b₃)],
      Covered ((List.range d₁.numEdges).map (fun k => [k + 1])) q.1 ∧
      Covered ((List.range d₁.numEdges).map (fun k => [k + 1])) q.2 := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨covered_singles ha₁ ha₁', covered_singles hg₂lo hg₂hi⟩
    · exact ⟨covered_singles hg₁lo hg₁hi, covered_singles hb₃lo hb₃hi⟩
  have hcovmid2 : ∀ q ∈ [(b₃, g₁), (a₁, g₂)],
      Covered ((List.range d₁.numEdges).map (fun k => [k + 1])) q.1 ∧
      Covered ((List.range d₁.numEdges).map (fun k => [k + 1])) q.2 := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨covered_singles hb₃lo hb₃hi, covered_singles hg₁lo hg₁hi⟩
    · exact ⟨covered_singles ha₁ ha₁', covered_singles hg₂lo hg₂hi⟩
  refine ⟨L.take i, L.drop (i + 3), a₁, b₁, b₃, g₁, g₂, hP1, hP2, ?_, ?_⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hcovA q hq
    · exact hcovmid1 q hq
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hcovA q hq
    · exact hcovmid2 q hq


/-- **Preservation generale de la partition d'arcs sous R3 connecte**
    (premier verrou de #16650) : si `d₂` s'obtient de `d₁` par le move
    triangulaire, les deux partitions d'arcs portent la meme relation
    « partager une classe » — pour tout couple d'etiquettes, partager une
    classe dans `arcPartition d₁` et partager une classe dans `arcPartition d₂`
    sont equivalents. La forme liste n'est PAS preservee (contre-exemple
    documente sur #16650 : deux fusions consecutives de memes paires dans
    l'ordre inverse produisent des listes differentes) ; la forme classe —
    celle dont depend la matrice d'Alexander colonne par colonne — l'est. -/
theorem Reidemeister3Connected.arcPartition_sameRel {d₁ d₂ : KnotDiagram}
    (h : Reidemeister3Connected d₁ d₂) :
    SameRel (arcPartition d₁) (arcPartition d₂) := by
  obtain ⟨A, B, a₁, b₁, b₃, g₁, g₂, hP1, hP2, hcov1, hcov2⟩ := pairs_append_forms h
  obtain ⟨hwf₁, _, _, henum, _, _⟩ := h
  rw [arcPartition_eq, arcPartition_eq, hP1, hP2]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [← henum]
  set S := (List.range d₁.numEdges).map (fun k => [k + 1]) with hS
  have hfoldA1 : (A ++ [(a₁, g₂), (g₁, b₃)]).foldl mergeStep S =
      mergeStep (mergeStep (A.foldl mergeStep S) (a₁, g₂)) (g₁, b₃) := by
    simp
  have hfoldA2 : (A ++ [(b₃, g₁), (a₁, g₂)]).foldl mergeStep S =
      mergeStep (mergeStep (A.foldl mergeStep S) (b₃, g₁)) (a₁, g₂) := by
    simp
  have hd1 := (foldl_partition_inv (P := S) (pairs := A ++ [(a₁, g₂), (g₁, b₃)])
    classesDisjoint_singles pairwise_singles hcov1).1
  have hd2 := (foldl_partition_inv (P := S) (pairs := A ++ [(b₃, g₁), (a₁, g₂)])
    classesDisjoint_singles pairwise_singles hcov2).1
  rw [hfoldA1] at hd1
  rw [hfoldA2] at hd2
  have hmid : SameRel (mergeStep (mergeStep (A.foldl mergeStep S) (a₁, g₂)) (g₁, b₃))
      (mergeStep (mergeStep (A.foldl mergeStep S) (b₃, g₁)) (a₁, g₂)) := by
    intro x y
    have hq0 : mergeStep (A.foldl mergeStep S) (b₃, g₁) =
        mergeStep (A.foldl mergeStep S) (g₁, b₃) := by
      simp only [mergeStep]
      rw [mergePair_symm]
    show SameClass (mergeStep (mergeStep (A.foldl mergeStep S) (a₁, g₂)) (g₁, b₃)) x y ↔ _
    rw [hq0]
    exact mergePair_mergePair_comm_equiv _ a₁ g₂ g₁ b₃ x y
  have hmid3 : SameRel
      (mergeStep (mergeStep (mergeStep (A.foldl mergeStep S) (a₁, g₂)) (g₁, b₃)) (g₂, b₁))
      (mergeStep (mergeStep (mergeStep (A.foldl mergeStep S) (b₃, g₁)) (a₁, g₂)) (g₂, b₁)) :=
    sameRel_mergeStep hmid hd1 hd2 (g₂, b₁)
  exact sameRel_foldl hmid3 (classesDisjoint_mergePair hd1)
    (classesDisjoint_mergePair hd2) B

/-- Corollaire de couverture : la relation de classes preservee donne
    l'equivalence des couvertures — une etiquette est portee par la partition
    d'arcs de `d₁` si et seulement si elle l'est par celle de `d₂`. -/
theorem Reidemeister3Connected.arcPartition_covered_iff {d₁ d₂ : KnotDiagram}
    (h : Reidemeister3Connected d₁ d₂) (z : Nat) :
    Covered (arcPartition d₁) z ↔ Covered (arcPartition d₂) z := by
  have heq := h.arcPartition_sameRel z z
  constructor
  · rintro ⟨C, hC, hz⟩
    obtain ⟨D, hD, hzD, _⟩ := heq.mp ⟨C, hC, hz, hz⟩
    exact ⟨D, hD, hzD⟩
  · rintro ⟨D, hD, hzD⟩
    obtain ⟨C, hC, hz, _⟩ := heq.mpr ⟨D, hD, hzD, hzD⟩
    exact ⟨C, hC, hz⟩

end Knots


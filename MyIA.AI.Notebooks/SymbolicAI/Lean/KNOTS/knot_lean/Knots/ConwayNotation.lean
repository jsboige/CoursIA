/-
  Knots.ConwayNotation — la notation de Conway pour les nœuds
  ===========================================================

  Phase 3 de l'EPIC #2874 : le LANGAGE qui engendre les nœuds rationnels.
  `Knots/Conway.lean` porte le polynôme d'Alexander/Conway et
  `Knots/ConwayPD.lean` le diagramme PD explicite du nœud de Conway 11n34 —
  ni l'un ni l'autre n'est la notation de Conway. Ce module introduit la
  notation : une suite d'entiers `[a₁, a₂, …]` (fraction de tangles), les
  aᵢ d'indice pair comptant des twists verticaux empilés au sommet, ceux
  d'indice impair des twists horizontaux ajoutés au flanc droit, puis la
  fermeture numerator (les deux brins du haut joints par un arc, ceux du
  bas pareillement).

  Méthode (celle de `Knots/ConwayPD.lean`) : la construction est validée par
  une sonde Python fidèle aux définitions du présent lake — `arcPartition`,
  `alexanderEntry`, le mineur désigné — sur unknot/3₁/4₁/5₁ avant le port
  Lean. La sonde reproduit les valeurs désignées prouvées du trèfle
  (t² − t + 1, `alexander_trefoil`) et du nœud de Conway 11n34 (−t⁶,
  `conway_trivial_alexander`).

  Ce que le maillon 1 prouve :

  - la fraction `[2, 2]` produit un diagramme bien formé de quatre
    croisements dont le polynôme désigné vaut t³ − 2t² + 2t — la valeur
    EXACTE du nœud huit `figureEightDiagram` (`alexander_figureEight`) :
    la notation désigne 4₁ (`conway_notation_22_alexander_figureEight`) ;
  - `[1]` et `[2]` désignent le nœud trivial (valeurs désignées 1 et t,
    une unité) ; la fraction vide aussi ;
  - `[3]` et `[5]` produisent des diagrammes bien formés dont les valeurs
    désignées (t², t⁴) NE SONT PAS significatives : leur projection en
    chaîne verticale porte des arêtes réflexives (fermeture joignant les
    deux sortants d'un même croisement), configuration hors des hypothèses
    d'unicité de la présentation de Wirtinger du lake (cf `ArcPartition.lean`,
    « Les lignes d'Alexander somment à zéro »). Les valeurs sont énoncées
    telles quelles, avec ce diagnostic — la désignation classique du trèfle
    attend une construction en spirale (suite du programme Phase 3).

  Ce que le maillon 2 prouve (la construction en spirale, §5) :

  - la fermeture du 2-brin à `n` demi-twists lue en spirale (dessin
    annulaire : croisement `i` portant les arêtes `(2i−1, 2i−1+n, 2i, 2i+n)`
    modulo `2n`) produit pour `n = 3` EXACTEMENT le `trefoilDiagram` du
    lake — la lecture spirale de `[3]` désigne 3₁ (valeur désignée
    `t² − t + 1`, celle d'`alexander_trefoil`) ;
  - pour `n = 5`, la même lecture désigne 5₁ (valeur désignée
    `t⁴ − t³ + t² − t + 1`, déterminant |Δ(−1)| = 5) ;
  - aucun croisement de la spirale ne porte d'arête réflexive : le défaut
    diagnostiqué sur les chaînes verticales ci-dessus est résolu par
    l'embedding annulaire.

  Convention de signe : le code PD du lake ne code pas la chiralité des
  croisements (docstring d'`alexanderEntry`) ; seul |aᵢ| est lu, et le
  miroir d'une notation partage toutes ses valeurs désignées.

  Epic #2874, Phase 3 « notation de Conway pour les nœuds ». Sibling EN :
  `Knots/ConwayNotation_en.lean` (Pattern A, docstrings traduites, corps
  byte-identical).
-/

import Knots.Basic
import Knots.Conway

namespace Knots

/-! ## 1. Tangles algébriques — un état à quatre ports

Un tangle à quatre brins est représenté par ses croisements PD partiels et
les étiquettes de ses quatre ports NW, NE, SW, SE. Le tangle nul (deux brins
verticaux) partage son étiquette entre les deux ports d'un même brin.
-/

/-- État d'un tangle algébrique : croisements partiels, étiquettes des
quatre ports, prochaine étiquette fraîche. -/
structure TangleSt where
  crossings : List PDCrossing
  nw : Nat
  ne : Nat
  sw : Nat
  se : Nat
  next : Nat

/-- Le tangle nul : deux brins verticaux, le gauche porte l'étiquette 1
(SW et NW), le droit l'étiquette 2 (SE et NE). -/
def TangleSt.zero : TangleSt := ⟨[], 1, 2, 1, 2, 3⟩

/-- Remplace l'étiquette `b` par `a` dans un croisement. -/
def relabelCross (a b : Nat) (c : PDCrossing) : PDCrossing :=
  ⟨if c.e1 = b then a else c.e1, if c.e2 = b then a else c.e2,
   if c.e3 = b then a else c.e3, if c.e4 = b then a else c.e4⟩

/-- Fusion de deux étiquettes de ports : `b` devient `a` partout. -/
def TangleSt.relabel (t : TangleSt) (a b : Nat) : TangleSt :=
  { t with crossings := t.crossings.map (relabelCross a b) }

/-- Un twist vertical au sommet : croise les deux brins du haut (le brin
venant de gauche passe au-dessous) et les échange — le brin qui entrait à
gauche ressort à droite. -/
def TangleSt.vTwist (t : TangleSt) : TangleSt :=
  { t with
    crossings := t.crossings ++ [⟨t.nw, t.ne, t.next + 1, t.next⟩]
    nw := t.next
    ne := t.next + 1
    next := t.next + 2 }

/-- Un twist horizontal au flanc droit : croise les deux brins de droite
(le brin venant du bas passe au-dessous) et les échange — le brin qui
entrait en haut ressort en bas. -/
def TangleSt.hTwist (t : TangleSt) : TangleSt :=
  { t with
    crossings := t.crossings ++ [⟨t.se, t.ne, t.next, t.next + 1⟩]
    ne := t.next
    se := t.next + 1
    next := t.next + 2 }

/-- Empile `k` twists verticaux. -/
def TangleSt.twistsV : Nat → TangleSt → TangleSt
  | 0, t => t
  | k + 1, t => t.twistsV k |>.vTwist

/-- Empile `k` twists horizontaux. -/
def TangleSt.twistsH : Nat → TangleSt → TangleSt
  | 0, t => t
  | k + 1, t => t.twistsH k |>.hTwist

/-! ## 2. La fraction de Conway

La notation `[a₁, a₂, …]` : les aᵢ d'indice pair (commençant à zéro)
comptent des twists verticaux au sommet, ceux d'indice impair des twists
horizontaux au flanc droit. La fermeture numerator joint les deux brins du
haut (NW ~ NE) puis ceux du bas (SW ~ SE). Le signe des aᵢ n'est pas lu :
le PD du lake ne code pas la chiralité, le miroir d'une notation partage
ses valeurs désignées.
-/

/-- Construction du tangle d'une notation, par alternance vertical/horizontal. -/
def conwayTangleAux : Nat → List ℤ → TangleSt → TangleSt
  | _, [], t => t
  | i, n :: rest, t =>
      let k := n.natAbs
      conwayTangleAux (i + 1) rest
        (if i % 2 = 0 then t.twistsV k else t.twistsH k)

/-- Le tangle algébrique désigné par une notation de Conway. -/
def conwayTangle (ns : List ℤ) : TangleSt :=
  conwayTangleAux 0 ns TangleSt.zero

/-- Fermeture numerator : arc du haut (NW ~ NE) puis arc du bas (SW ~ SE). -/
def TangleSt.numClosure (t : TangleSt) : TangleSt :=
  let t1 := t.relabel t.nw t.ne
  t1.relabel t1.sw t1.se

/-- Renumérote une étiquette : conserve la table des vues et le compteur. -/
def renumberStep (x : Nat) (m : List (Nat × Nat)) (k : Nat) :
    Nat × (List (Nat × Nat)) × Nat :=
  match m.lookup x with
  | some y => (y, m, k)
  | none => (k + 1, (x, k + 1) :: m, k + 1)

/-- Renumérote les croisements par première apparition de l'étiquette. -/
def renumberCrossingsAux : List PDCrossing → List (Nat × Nat) → Nat →
    List PDCrossing × List (Nat × Nat) × Nat
  | [], m, k => ([], m, k)
  | c :: cs, m, k =>
      let e1 := renumberStep c.e1 m k
      let e2 := renumberStep c.e2 e1.2.1 e1.2.2
      let e3 := renumberStep c.e3 e2.2.1 e2.2.2
      let e4 := renumberStep c.e4 e3.2.1 e3.2.2
      let rest := renumberCrossingsAux cs e4.2.1 e4.2.2
      (⟨e1.1, e2.1, e3.1, e4.1⟩ :: rest.1, rest.2.1, rest.2.2)

/-- Le diagramme désigné par une notation de Conway : le tangle de la
fraction, fermé par numerator, renuméroté en étiquettes contiguës
`1..numEdges`. -/
def conwayKnotOf (ns : List ℤ) : KnotDiagram :=
  let t := (conwayTangle ns).numClosure
  let r := renumberCrossingsAux t.crossings [] 0
  ⟨r.1, r.2.2⟩

/-- Notations nommées : les exemples du maillon. -/
def unknotNotation : List ℤ := []
def oneTwistNotation : List ℤ := [1]
def twoTwistNotation : List ℤ := [2]
def trefoilNotation : List ℤ := [3]
def figureEightNotation : List ℤ := [2, 2]
def cinquefoilNotation : List ℤ := [5]

/-! ## 3. Bonne formation

Chaque exemple produit un diagramme bien formé : chaque étiquette de
`[1, numEdges]` exactement deux fois. Décidable sur ces instances.
-/

theorem conway_wf_empty : (conwayKnotOf unknotNotation).wf = true := by
  decide

theorem conway_wf_one : (conwayKnotOf oneTwistNotation).wf = true := by
  decide

theorem conway_wf_two : (conwayKnotOf twoTwistNotation).wf = true := by
  decide

theorem conway_wf_three : (conwayKnotOf trefoilNotation).wf = true := by
  decide

theorem conway_wf_five : (conwayKnotOf cinquefoilNotation).wf = true := by
  decide

theorem conway_wf_22 : (conwayKnotOf figureEightNotation).wf = true := by
  decide

/-! ## 4. Le polynôme d'Alexander désigné des exemples

Les preuves suivent le motif d'`alexander_trefoil` : la partition d'arcs
par `decide`, puis le dépliage du mineur et `ring`. Les valeurs sont
celles de la sonde Python fidèle (header du module).
-/

/-- Déterminant 4×4 générique (même esprit que `det_two_aux` /
`det_three_aux` de `Knots/Conway.lean` : expansion de Laplace le long de la
première colonne, les mineurs 3×3 étant traités par `det_three_aux`). -/
theorem conway_det_four_aux (A : Matrix (Fin 4) (Fin 4) (Polynomial ℤ)) :
    A.det =
      A 0 0 * (A 1 1 * (A 2 2 * A 3 3 - A 2 3 * A 3 2)
             - A 1 2 * (A 2 1 * A 3 3 - A 2 3 * A 3 1)
             + A 1 3 * (A 2 1 * A 3 2 - A 2 2 * A 3 1))
      - A 1 0 * (A 0 1 * (A 2 2 * A 3 3 - A 2 3 * A 3 2)
              - A 0 2 * (A 2 1 * A 3 3 - A 2 3 * A 3 1)
              + A 0 3 * (A 2 1 * A 3 2 - A 2 2 * A 3 1))
      + A 2 0 * (A 0 1 * (A 1 2 * A 3 3 - A 1 3 * A 3 2)
              - A 0 2 * (A 1 1 * A 3 3 - A 1 3 * A 3 1)
              + A 0 3 * (A 1 1 * A 3 2 - A 1 2 * A 3 1))
      - A 3 0 * (A 0 1 * (A 1 2 * A 2 3 - A 1 3 * A 2 2)
              - A 0 2 * (A 1 1 * A 2 3 - A 1 3 * A 2 1)
              + A 0 3 * (A 1 1 * A 2 2 - A 1 2 * A 2 1)) := by
  rw [Matrix.det_succ_column_zero]
  simp (config := { decide := true }) [Fin.sum_univ_succ]
  simp (config := { decide := true }) [det_three_aux, Matrix.submatrix_apply, Fin.succAbove]
  ring

/-- La fraction vide désigne le nœud trivial : diagramme sans croisement,
déterminant vide. Le diagramme est d'abord littéralisé par `decide`
(`conwayKnotOf` est une fonction récursive que `simp only` ne calcule pas --
même rôle que `simp only [trefoilDiagram]` dans `alexander_trefoil`). -/
theorem conway_unknot_alexander :
    alexanderPolynomialAux (conwayKnotOf unknotNotation) = 1 := by
  have hc : conwayKnotOf unknotNotation = ⟨[], 0⟩ := by
    decide
  simp only [alexanderPolynomialAux, hc]

/-- Un twist fermé est un kink de R1 : le nœud trivial, valeur désignée 1
(mineur vide). -/
theorem conway_one_alexander :
    alexanderPolynomialAux (conwayKnotOf oneTwistNotation) = 1 := by
  have hc : conwayKnotOf oneTwistNotation = ⟨[⟨1, 1, 2, 2⟩], 2⟩ := by
    decide
  have hp : arcPartition (conwayKnotOf oneTwistNotation) = [[1, 2]] := by
    decide
  simp only [alexanderPolynomialAux, hp, hc]
  simp (config := { decide := true })

/-- Deux twists fermés : deux kinks de R1 enchaînés, le nœud trivial —
valeur désignée t, une unité (mineur 1×1). -/
theorem conway_two_alexander :
    alexanderPolynomialAux (conwayKnotOf twoTwistNotation) = Polynomial.X := by
  have hc : conwayKnotOf twoTwistNotation =
      ⟨[⟨1, 1, 2, 3⟩, ⟨3, 2, 4, 4⟩], 4⟩ := by
    decide
  have hp : arcPartition (conwayKnotOf twoTwistNotation) = [[1, 3], [2, 4]] := by
    decide
  simp only [alexanderPolynomialAux, hp, hc]
  simp (config := { decide := true }) [alexanderEntry]

/-- La fraction `[2, 2]` désigne le nœud huit : son diagramme (quatre
croisements, huit arêtes, aucune réflexive — les twists horizontaux
détournent les ports de la fermeture) porte la valeur désignée EXACTE de
`figureEightDiagram`, t³ − 2t² + 2t (l'artefact de chiralité documenté
en §« Divergence de la classe 4 croisements » de `Knots/Conway.lean`,
#14962 : le déterminant |Δ(−1)| = 5 = det(4₁) est bien reproduit). -/
theorem conway_notation_22_alexander :
    alexanderPolynomialAux (conwayKnotOf figureEightNotation) =
      Polynomial.X ^ 3 - (2 : Polynomial ℤ) * Polynomial.X ^ 2
        + 2 * Polynomial.X := by
  have hc : conwayKnotOf figureEightNotation =
      ⟨[⟨1, 2, 3, 4⟩, ⟨4, 3, 5, 6⟩, ⟨2, 5, 7, 8⟩, ⟨8, 7, 6, 1⟩], 8⟩ := by
    decide
  have hp : arcPartition (conwayKnotOf figureEightNotation) =
      [[2, 4], [3, 6], [5, 8], [1, 7]] := by
    decide
  simp only [alexanderPolynomialAux, hp, hc]
  simp (config := { decide := true })
  rw [det_three_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntry]
  ring

/-- Corollaire : la valeur désignée de `[2, 2]` est exactement celle du
nœud huit du lake — la notation de Conway désigne 4₁. -/
theorem conway_notation_22_alexander_figureEight :
    alexanderPolynomialAux (conwayKnotOf figureEightNotation) =
      alexanderPolynomial figureEight := by
  rw [conway_notation_22_alexander, alexander_figureEight]

/-- La fraction `[3]` (le trèfle des tables de Conway) produit ici une
projection en chaîne verticale : les arcs de fermeture joignent les deux
sortants d'un même croisement (arêtes réflexives), configuration hors des
hypothèses d'unicité de la présentation de Wirtinger — la valeur désignée
t² N'EST PAS significative (ce n'est pas une unité fois t² − t + 1 ; les
mineurs calculés valent ±1 et t²). Le nœud sous-jacent est bien 3₁ (fait
classique : la fermeture numerator du tangle à trois twists) ; sa
désignation classique exige une construction en spirale, suite du
programme de la Phase 3 — livrée au maillon 2 (§5 :
`spiral_three_designates_trefoil`). -/
theorem conway_three_designated :
    alexanderPolynomialAux (conwayKnotOf trefoilNotation) = Polynomial.X ^ 2 := by
  have hc : conwayKnotOf trefoilNotation =
      ⟨[⟨1, 1, 2, 3⟩, ⟨3, 2, 4, 5⟩, ⟨5, 4, 6, 6⟩], 6⟩ := by
    decide
  have hp : arcPartition (conwayKnotOf trefoilNotation) =
      [[1, 3], [2, 5], [4, 6]] := by
    decide
  simp only [alexanderPolynomialAux, hp, hc]
  simp (config := { decide := true })
  rw [det_two_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntry]
  ring

/-- Même diagnostic pour `[5]` (5₁ des tables) : chaîne verticale pure,
arêtes réflexives, valeur désignée t⁴ non significative — résolu au
maillon 2 (§5 : `spiral_five_alexander`). -/
theorem conway_five_designated :
    alexanderPolynomialAux (conwayKnotOf cinquefoilNotation) = Polynomial.X ^ 4 := by
  have hc : conwayKnotOf cinquefoilNotation =
      ⟨[⟨1, 1, 2, 3⟩, ⟨3, 2, 4, 5⟩, ⟨5, 4, 6, 7⟩, ⟨7, 6, 8, 9⟩, ⟨9, 8, 10, 10⟩], 10⟩ := by
    decide
  have hp : arcPartition (conwayKnotOf cinquefoilNotation) =
      [[1, 3], [2, 5], [4, 7], [6, 9], [8, 10]] := by
    decide
  simp only [alexanderPolynomialAux, hp, hc]
  simp (config := { decide := true })
  rw [conway_det_four_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntry]
  ring


/-! ## 5. La construction en spirale (maillon 2)

Le défaut du maillon 1 — la fermeture numerator en chaîne verticale joint
les deux sortants d'un même croisement (arêtes réflexives) — n'est pas un
défaut du LANGAGE mais du DESSIN : la même fraction `[n]` se dessine en
enroulant le 2-brin fermé autour d'un cylindre, chaque croisement `i`
portant les quatre arêtes `(2i−1, 2i−1+n, 2i, 2i+n)` lues modulo `2n`.
Pour `n` impair (`n ≥ 3`), la fermeture numerator du tangle `[n]` est le
nœud torique `T(2, n)` (fait classique) : `[3]` désigne 3₁, `[5]` désigne
5₁. Les valeurs désignées ci-dessous sont celles de la sonde Python du
module (header), validées avant le port.
-/

/-- Étiquette spirale : `k` lu modulo `2n`, dans `1..2n`. -/
def spiralLabel (n k : Nat) : Nat := (k - 1) % (2 * n) + 1

/-- Le croisement `i` (1-indexé) de la spirale à `n` demi-twists : les
deux arêtes entrantes `2i−1` et `2i`, les deux sortantes décalées de `n`
(un demi-tour de cylindre plus loin sur la spire). -/
def spiralCross (n i : Nat) : PDCrossing :=
  ⟨spiralLabel n (2 * i - 1), spiralLabel n (2 * i - 1 + n),
   spiralLabel n (2 * i), spiralLabel n (2 * i + n)⟩

/-- La fermeture du 2-brin à `n` demi-twists, enroulée en spirale : le
dessin annulaire de la fraction `[n]` (pour `n` impair ≥ 3, le nœud
torique `T(2, n)`), sans arête réflexive. -/
def spiralDiagram (n : Nat) : KnotDiagram :=
  ⟨(List.range n).map (fun i => spiralCross n (i + 1)), 2 * n⟩

/-! ### Bonne formation

Chaque étiquette de `1..2n` apparaît exactement deux fois, dans deux
croisements distincts — en particulier les quatre étiquettes d'un
croisement sont deux à deux distinctes : le défaut Wirtinger du maillon 1
disparaît.
-/

theorem spiral_wf_three : (spiralDiagram 3).wf = true := by
  decide

theorem spiral_wf_five : (spiralDiagram 5).wf = true := by
  decide

/-- Aucune arête réflexive dans la spirale `[3]` : les quatre étiquettes de
chaque croisement sont deux à deux distinctes. -/
theorem spiral_noReflect_three :
    (spiralDiagram 3).crossings.all (fun c =>
      c.e1 ≠ c.e2 ∧ c.e1 ≠ c.e3 ∧ c.e1 ≠ c.e4 ∧
      c.e2 ≠ c.e3 ∧ c.e2 ≠ c.e4 ∧ c.e3 ≠ c.e4) = true := by
  decide

/-- Même absence d'arête réflexive pour la spirale `[5]`. -/
theorem spiral_noReflect_five :
    (spiralDiagram 5).crossings.all (fun c =>
      c.e1 ≠ c.e2 ∧ c.e1 ≠ c.e3 ∧ c.e1 ≠ c.e4 ∧
      c.e2 ≠ c.e3 ∧ c.e2 ≠ c.e4 ∧ c.e3 ≠ c.e4) = true := by
  decide

/-! ### Les valeurs désignées des spirales

`[3]` désigne le trèfle : la spirale à trois demi-twists littéralise
EXACTEMENT le diagramme de référence du lake (`trefoilDiagram`,
`Knots/Basic.lean`) — la désignation suit par `alexander_trefoil`. `[5]`
désigne 5₁ : valeur désignée `t⁴ − t³ + t² − t + 1`, déterminant
|Δ(−1)| = 5.
-/

/-- La spirale `[3]` EST le diagramme du trèfle du lake, arête pour
arête : la lecture annulaire de la fraction `[3]` produit le PD de
référence `trefoilDiagram`. -/
theorem spiral_three_eq_trefoilDiagram :
    spiralDiagram 3 = trefoilDiagram := by
  decide

/-- La valeur désignée de la spirale `[3]` : `t² − t + 1`, calculée sur
place (motif d'`alexander_trefoil` — littéralisation, partition d'arcs,
mineur 2×2). -/
theorem spiral_three_alexander :
    alexanderPolynomialAux (spiralDiagram 3) =
      Polynomial.X ^ 2 - Polynomial.X + 1 := by
  have hc : spiralDiagram 3 =
      ⟨[⟨1, 4, 2, 5⟩, ⟨3, 6, 4, 1⟩, ⟨5, 2, 6, 3⟩], 6⟩ := by
    decide
  simp only [alexanderPolynomialAux, hc]
  simp (config := { decide := true })
  rw [det_two_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntry]
  ring

/-- Corollaire de désignation : la spirale `[3]` porte exactement le
polynôme d'Alexander du trèfle du lake — la notation désigne 3₁, le
diagnostic réflexif du maillon 1 est résolu par l'embedding annulaire. -/
theorem spiral_three_designates_trefoil :
    alexanderPolynomialAux (spiralDiagram 3) = alexanderPolynomial trefoil := by
  rw [spiral_three_alexander, alexander_trefoil]

/-- La valeur désignée de la spirale `[5]` : `t⁴ − t³ + t² − t + 1`, le
polynôme d'Alexander de 5₁ (déterminant |Δ(−1)| = 5). Le mineur 4×4 est
déplié par `conway_det_four_aux`. -/
theorem spiral_five_alexander :
    alexanderPolynomialAux (spiralDiagram 5) =
      Polynomial.X ^ 4 - Polynomial.X ^ 3 + Polynomial.X ^ 2
        - Polynomial.X + 1 := by
  have hc : spiralDiagram 5 =
      ⟨[⟨1, 6, 2, 7⟩, ⟨3, 8, 4, 9⟩, ⟨5, 10, 6, 1⟩, ⟨7, 2, 8, 3⟩,
        ⟨9, 4, 10, 5⟩], 10⟩ := by
    decide
  simp only [alexanderPolynomialAux, hc]
  simp (config := { decide := true })
  rw [conway_det_four_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntry]
  ring

end Knots

/-
  Knots.Jones — Bracket de Kauffman et polynôme de Jones sur codes PD (tranches 1-2)
  ====================================================================

  Ce fichier définit le bracket de Kauffman ⟨D⟩ d'un diagramme de noeud codé
  en PD (voir `Knots.Basic`) par somme d'états, et l'évalue sur les trois
  diagrammes nommés du lac (noeud trivial, trèfle, noeud en huit), avec les
  distinctions calculatoires trèfle ≠ noeud trivial et huit ≠ noeud trivial.

  Tranches 1 et 2 de la Phase 4 de l'EPIC #2874 (polynôme de Jones via
  bracket de Kauffman). La tranche 1 définit le bracket. La tranche 2 lit
  le signe de chaque croisement sur l'étiquetage du code PD (les arêtes
  sont numérotées dans le sens de l'orientation), en déduit le writhe, la
  normalisation de Kauffman f(D) et le polynôme de Jones V(t), et ajoute
  un critère de planarité par comptage de faces (formule d'Euler). Ce
  critère établit que le code `figureEightDiagram` de `Knots.Basic` n'est
  pas plan : c'est un noeud virtuel, dont le polynôme de Jones est celui
  du trèfle. `figureEightPlanarDiagram` fournit un code plan du noeud en
  huit, sur lequel V(t) prend la valeur du manuel.

  ## Somme d'états

  Un **état** `v` est un choix de lissage (A ou B) pour chaque croisement.
  Le lissage remplace chaque croisement `c = ⟨e1, e2, e3, e4⟩` (dessous
  entrant, dessus entrant, dessous sortant, dessus sortant — voir
  `Knots.Basic`) par deux connexions joignant les extrémités d'arêtes deux
  à deux :

  - lissage **A** (convention du module, dite A14) : relie `e1–e4` et `e2–e3` ;
  - lissage **B** : relie `e1–e2` et `e3–e4`.

  Les connexions de l'état ferment les arêtes du diagramme en un collection
  de boucles : chaque arête apparaît exactement deux fois parmi les
  connexions (condition de bon formage du code PD), donc le multigraphe
  dont les sommets sont les étiquettes d'arêtes et les arêtes sont les
  connexions est 2-régulier, et ses composantes connexes sont exactement
  les boucles de l'état.

  Le bracket est alors

  ⟨D⟩ = Σ_états A^(#A − #B) · δ^(k − 1),  δ = −A² − A⁻²,

  où `k` est le nombre de boucles de l'état. C'est la présentation par
  somme d'états de la définition récursive usuelle (développer le choix de
  lissage croisement par croisement = la récurrence skein ; chaque boucle
  fermée contribue un facteur δ = −A² − A⁻² ; le diagramme vide vaut 1).

  ## Représentation des valeurs : polynôme de Laurent creux

  Les valeurs vivent dans `LP = List (ℤ × ℤ)`, liste creuse de monômes
  (exposant, coefficient) en **forme normale** : exposants strictement
  décroissants, coefficients non nuls. Cette représentation maison est
  utilisée de préférence à `LaurentPolynomial ℤ` de Mathlib parce que les
  instances d'anneau d'`AddMonoidAlgebra` y sont noncomputable et opaques
  à la réduction du noyau (elles tirent des instances classique) : aucune
  égalité de valeur n'y est vérifiable par `rfl` ni `decide`. Avec `LP`,
  au contraire, toutes les évaluations et distinctions ci-dessous se
  vérifient par `decide` (réduction exacte dans le noyau). Un pont
  `LP → LaurentPolynomial ℤ` (par somme de monômes `T n`) est trivial à
  définir pour une tranche ultérieure si l'interopérabilité Mathlib
  devient nécessaire.

  ## Choix de convention et chiralité

  La convention A14 est choisie car sous celle-ci le trèfle du lac
  (`trefoilDiagram`, à trois croisements positifs d'après sa documentation)
  calcule la valeur du manuel pour le trèfle à main droite :
  ⟨3₁⟩ = −A⁵ − A⁻³ + A⁻⁷. La convention duale (A relie e1–e2, e3–e4)
  échange A et A⁻¹ et donne le bracket du trèfle miroir.

  ## Frontière honnête (ce que ce fichier ne prouve pas)

  - **Invariance de Reidemeister** : NON prouvée ici. Les mouvements de
    Reidemeister (`Knots.Reidemeister`) sont eux-mêmes des sorry. Le
    bracket est donc établi comme invariant de *diagramme*, pas encore de
    noeud : les théorèmes de distinction ci-dessous distinguent les
    diagrammes, et deviennent des distinctions de noeuds une fois
    l'invariance prouvée (tranche future de l'EPIC).
  - **Invariance du polynôme de Jones** : NON prouvée, pour la même
    raison. f(D) est construit pour être invariant (le facteur (−A³)^(−w)
    compense le mouvement I), mais les théorèmes `jones_*` restent des
    égalités de diagrammes.
  - **Code `figureEightDiagram` de `Knots.Basic`** : non plan
    (`figureEightDiagram_not_planar`). Sa correction touche d'autres
    modules (Conway, Invariant) et le notebook Lean-17c ; elle est suivie
    par #17595. Cette tranche ne modifie pas `Knots.Basic`.
  - **Signe lu sur l'étiquetage** : `crossingSign` suppose des arêtes
    numérotées consécutivement le long de l'orientation (convention
    KnotInfo/KnotAtlas). Sur un code qui ne la respecte pas, le signe n'a
    pas de sens (il vaut 0 quand les deux étiquettes du dessus ne sont
    pas consécutives).
  - **Sensibilité au miroir** : le writhe du miroir est l'opposé du writhe
    (`writhe_mirror`, énoncé symbolique pour tout diagramme bien formé).
    La relation V(miroir) = V(t⁻¹) n'est vérifiée que sur le trèfle
    (`jones_mirror_trefoil_eq_invert`) ; son énoncé général (bracket
    miroir = bracket en A ↔ A⁻¹) n'est pas formalisé.
-/

import Knots.Basic

namespace Knots

/-! ## Polynômes de Laurent creux (`LP`)

Liste de monômes (exposant, coefficient) en forme normale : exposants
strictement décroissants, coefficients non nuls. Toutes les opérations
sont computables et réductibles dans le noyau.
-/

/-- Type des polynômes de Laurent creux : liste (exposant, coefficient),
en forme normale (exposants strictement décroissants, coefficients non
nuls). -/
abbrev LP : Type := List (ℤ × ℤ)

/-- Insère-fusionne un monôme dans une liste `LP` triée par exposant
décroissant (forme normale préservée). -/
def lpMerge (p : ℤ × ℤ) : LP → LP
  | [] => if p.2 = 0 then [] else [p]
  | (m, d) :: rest =>
    if m > p.1 then (m, d) :: lpMerge p rest
    else if m = p.1 then (if d + p.2 = 0 then rest else (m, d + p.2) :: rest)
    else if p.2 = 0 then (m, d) :: rest else p :: (m, d) :: rest

/-- Met une liste de monômes arbitraire en forme normale. -/
def lpNorm (l : LP) : LP := l.foldl (fun acc p => lpMerge p acc) []

/-- Le monôme A^n (forme normale). -/
def monoA (n : ℤ) : LP := [(n, 1)]

/-- δ = −A² − A⁻² : la valeur d'une boucle fermée supplémentaire. -/
def deltaVar : LP := [(2, -1), (-2, -1)]

/-- Produit de deux listes de monômes (non normalisé : distribue, puis on
normalise au niveau de `bracket`). -/
def lpMul (p q : LP) : LP :=
  p.flatMap (fun (n, c) => q.map (fun (m, d) => (n + m, c * d)))

/-- Puissance (exposant naturel) d'une liste de monômes. -/
def lpPow (p : LP) : Nat → LP
  | 0 => [(0, 1)]
  | k + 1 => lpMul (lpPow p k) p

/-! ## États et lissages

Un état est un vecteur de `Bool` (`true` = lissage A, `false` = lissage B),
un Bool par croisement, dans l'ordre de `KnotDiagram.crossings`.
-/

/-- Tous les vecteurs de `Bool` de longueur `n` : l'espace des états d'un
diagramme à `n` croisements. -/
def allBoolVectors : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBoolVectors n).flatMap (fun v => [true :: v, false :: v])

/-- Les deux connexions produites par le lissage du croisement `c` dans
l'état `s`.

Convention A14 du module : le lissage A relie `e1–e4` et `e2–e3`, le
lissage B relie `e1–e2` et `e3–e4`. Voir la docstring du fichier pour la
justification (trèfle à main droite = valeur du manuel). -/
def smoothingConnections (c : PDCrossing) (s : Bool) : List (Nat × Nat) :=
  if s then [(c.e1, c.e4), (c.e2, c.e3)] else [(c.e1, c.e2), (c.e3, c.e4)]

/-- Connexions totales de l'état `v` du diagramme `d` (deux par croisement
lissé). -/
def stateConnections (d : KnotDiagram) (v : List Bool) : List (Nat × Nat) :=
  (d.crossings.zip v).flatMap (fun (c, s) => smoothingConnections c s)

/-! ## Boucles d'un état

Les boucles sont les composantes connexes du multigraphe des connexions
(sommets = étiquettes d'arêtes). Le calcul se fait par fusions successives
de classes (union-find naïf) sur la partition initialement triviale.
-/

/-- Fusionne les classes contenant les labels `a` et `b` dans une
partition de labels d'arêtes. -/
def mergeClasses (classes : List (List Nat)) (a b : Nat) : List (List Nat) :=
  let ca := classes.flatMap (fun cl => if cl.contains a then [cl] else [])
  let cb := classes.flatMap (fun cl => if cl.contains b && !cl.contains a then [cl] else [])
  let kept := classes.filter (fun cl => !cl.contains a && !cl.contains b)
  let merged := ca.flatten ++ cb.flatten
  if merged.isEmpty then kept else kept ++ [merged]

/-- Partition initiale : chaque label présent dans les connexions forme sa
propre classe. -/
def initialClasses (conns : List (Nat × Nat)) : List (List Nat) :=
  ((conns.flatMap (fun p => [p.1, p.2])).eraseDups).map (fun l => [l])

/-- Réduit la partition en fusionnant le long de chaque connexion
(carburant = nombre de connexions). -/
def buildComponents : Nat → List (Nat × Nat) → List (List Nat) → List (List Nat)
  | 0, _, acc => acc
  | _ + 1, [], acc => acc
  | fuel + 1, (a, b) :: rest, acc => buildComponents fuel rest (mergeClasses acc a b)

/-- Composantes connexes du multigraphe des connexions. -/
def connectedComponents (conns : List (Nat × Nat)) : List (List Nat) :=
  buildComponents conns.length conns (initialClasses conns)

/-- Nombre de boucles de l'état porté par les connexions `conns` (le
multigraphe étant 2-régulier pour un code PD bien formé, chaque composante
connexe est un cycle, i.e. une boucle). -/
def connectionLoops (conns : List (Nat × Nat)) : Nat :=
  (connectedComponents conns).length

/-- Nombre de boucles du diagramme `d` lissé selon l'état `v`.

Cas particulier : un diagramme sans croisement (le code PD du noeud
trivial) est un cercle unique — une seule boucle, aucune connexion. -/
def stateLoops (d : KnotDiagram) (v : List Bool) : Nat :=
  match d.crossings with
  | [] => 1
  | _ => connectionLoops (stateConnections d v)

/-! ## Bracket de Kauffman -/

/-- Monôme d'état A^(#A − #B) pour le vecteur de lissages `v`. -/
def stateMonomial (v : List Bool) : LP :=
  monoA ((v.count true : ℤ) - (v.count false : ℤ))

/-- Terme d'état : A^(#A − #B) · δ^(k−1) où `k` est le nombre de boucles
de l'état `v` du diagramme `d`. -/
def stateTerm (d : KnotDiagram) (v : List Bool) : LP :=
  lpMul (stateMonomial v) (lpPow deltaVar (stateLoops d v - 1))

/-- Bracket de Kauffman ⟨D⟩ du diagramme `d` : somme (concaténation puis
normalisation) des termes d'état sur tous les états. -/
def bracket (d : KnotDiagram) : LP :=
  lpNorm (((allBoolVectors d.crossings.length).map (stateTerm d)).flatten)

/-! ## Évaluations et distinctions (décidables)

Les valeurs sont confirmées par calcul exact dans le noyau (`decide` —
la représentation `LP` est intégralement computable). Le trèfle donne la
valeur du manuel pour le trèfle à main droite (justification de la
convention A14) ; le code `figureEightDiagram` donne A⁸ + 1 − A⁻⁴, qui
n'est pas le bracket du noeud en huit : ce code n'est pas plan (tranche 2).
-/

/-- Le bracket du diagramme du noeud trivial vaut 1 : unique état vide,
une boucle, δ⁰. -/
theorem bracket_unknotDiagram : bracket unknotDiagram = [(0, 1)] := by
  decide

/-- Valeur du bracket sur le trèfle : ⟨3₁⟩ = −A⁵ − A⁻³ + A⁻⁷ (valeur du
manuel pour le trèfle à main droite, sous la convention A14 du module). -/
theorem bracket_trefoilDiagram :
    bracket trefoilDiagram = [(5, -1), (-3, -1), (-7, 1)] := by
  decide

set_option maxRecDepth 100000 in
/-- Valeur du bracket sur le code `figureEightDiagram` : A⁸ + 1 − A⁻⁴.
Ce code n'est pas plan (`figureEightDiagram_not_planar`) : la valeur est
celle d'un noeud virtuel, pas le bracket du noeud en huit, qui vaut
A⁸ − A⁴ + 1 − A⁻⁴ + A⁻⁸ (`bracket_figureEightPlanarDiagram`). -/
theorem bracket_figureEightDiagram :
    bracket figureEightDiagram = [(8, 1), (0, 1), (-4, -1)] := by
  decide

/-- Le bracket distingue (au niveau des diagrammes) le trèfle du noeud
trivial : coefficient −1 en A⁵ contre 0. Tant que l'invariance de
Reidemeister du bracket n'est pas prouvée, ceci ne distingue pas encore
les *noeuds* — voir la frontière honnête du fichier. -/
theorem bracket_trefoil_ne_bracket_unknot :
    bracket trefoilDiagram ≠ bracket unknotDiagram := by
  decide

/-- Le bracket distingue (au niveau des diagrammes) le code
`figureEightDiagram` du noeud trivial : coefficient 1 en A⁸ contre 0 —
même caveat que `bracket_trefoil_ne_bracket_unknot`. -/
theorem bracket_figureEight_ne_bracket_unknot :
    bracket figureEightDiagram ≠ bracket unknotDiagram := by
  decide

/-! ## Tranche 2 — signe de croisement et writhe

Le code PD ne porte pas de champ de signe, mais son étiquetage le
détermine : les arêtes sont numérotées consécutivement le long de
l'orientation du noeud (convention KnotInfo/KnotAtlas), donc le brin du
dessus va de `e2` à `e4` quand `e4` suit `e2` (modulo `numEdges`), et de
`e4` à `e2` dans le cas inverse. Dans la lecture horaire du module (voir
`Knots.Basic`), le croisement est positif dans le premier cas : c'est ce
qui rend positifs les trois croisements de `trefoilDiagram`, conformément
à sa documentation.

Les commentaires de champ de `PDCrossing` nomment `e2` « dessus entrant » et
`e4` « dessus sortant » : ce n'est vrai que pour un croisement positif. Sur
un croisement négatif, le brin du dessus entre par `e4`.
-/

/-- Successeur cyclique d'une étiquette d'arête dans `[1, n]`. -/
def nextEdge (n l : Nat) : Nat := l % n + 1

/-- Signe du croisement `c` dans un diagramme à `n` arêtes : `1` si le brin
du dessus va de `e2` à `e4`, `-1` s'il va de `e4` à `e2`, `0` si
l'étiquetage ne tranche pas (étiquettes du dessus non consécutives). -/
def crossingSign (n : Nat) (c : PDCrossing) : ℤ :=
  if c.e4 = nextEdge n c.e2 then 1
  else if c.e2 = nextEdge n c.e4 then -1
  else 0

/-- Writhe du diagramme : somme des signes de ses croisements. -/
def writhe (d : KnotDiagram) : ℤ :=
  (d.crossings.map (crossingSign d.numEdges)).sum

/-- Les deux cas de `crossingSign` s'excluent : deux étiquettes de `[1, n]`
ne peuvent se suivre dans les deux sens que si `n ≤ 2`. -/
theorem nextEdge_not_both {n a b : Nat} (hn : 3 ≤ n) (ha1 : 1 ≤ a) (han : a ≤ n)
    (hb1 : 1 ≤ b) (hbn : b ≤ n) : ¬ (b = nextEdge n a ∧ a = nextEdge n b) := by
  rintro ⟨h1, h2⟩
  unfold nextEdge at h1 h2
  rcases Nat.lt_or_ge a n with ha | ha
  · rw [Nat.mod_eq_of_lt ha] at h1
    rcases Nat.lt_or_ge b n with hb | hb
    · rw [Nat.mod_eq_of_lt hb] at h2
      omega
    · have hbe : b = n := by omega
      rw [hbe, Nat.mod_self] at h2
      omega
  · have hae : a = n := by omega
    rw [hae, Nat.mod_self] at h1
    rcases Nat.lt_or_ge b n with hb | hb
    · rw [Nat.mod_eq_of_lt hb] at h2
      omega
    · omega

/-- Le miroir (échange dessus/dessous) inverse le signe d'un croisement dont
les étiquettes du dessus sont dans `[1, n]`, pour `n ≥ 3`. -/
theorem crossingSign_mirrorCrossing {n : Nat} (c : PDCrossing) (hn : 3 ≤ n)
    (h2 : 1 ≤ c.e2 ∧ c.e2 ≤ n) (h4 : 1 ≤ c.e4 ∧ c.e4 ≤ n) :
    crossingSign n (mirrorCrossing c) = - crossingSign n c := by
  have hx := nextEdge_not_both hn h2.1 h2.2 h4.1 h4.2
  change (if c.e2 = nextEdge n c.e4 then (1 : ℤ)
    else if c.e4 = nextEdge n c.e2 then -1 else 0) =
    -(if c.e4 = nextEdge n c.e2 then (1 : ℤ)
      else if c.e2 = nextEdge n c.e4 then -1 else 0)
  by_cases hA : c.e4 = nextEdge n c.e2
  · have hB : ¬ c.e2 = nextEdge n c.e4 := fun h => hx ⟨hA, h⟩
    simp only [if_neg hB, if_pos hA]
  · by_cases hB : c.e2 = nextEdge n c.e4
    · simp only [if_pos hB, if_neg hA, neg_neg]
    · simp only [if_neg hB, if_neg hA, neg_zero]

/-- Version liste de `crossingSign_mirrorCrossing` : la somme des signes
d'une liste de croisements miroirs est l'opposée de la somme initiale. -/
theorem sum_crossingSign_mirror {n : Nat} (hn : 3 ≤ n) :
    ∀ l : List PDCrossing,
      (∀ c ∈ l, (1 ≤ c.e2 ∧ c.e2 ≤ n) ∧ (1 ≤ c.e4 ∧ c.e4 ≤ n)) →
      ((l.map mirrorCrossing).map (crossingSign n)).sum = - (l.map (crossingSign n)).sum
  | [], _ => by simp
  | c :: l, h => by
    have hc := h c (by simp)
    have ih := sum_crossingSign_mirror hn l (fun c' hc' => h c' (by simp [hc']))
    simp only [List.map_cons, List.sum_cons]
    rw [crossingSign_mirrorCrossing c hn hc.1 hc.2, ih]
    omega

/-- Un diagramme bien formé a toutes ses étiquettes du dessus dans
`[1, numEdges]` (clause (a) de `KnotDiagram.wf`). -/
theorem KnotDiagram.wf_over_bounds {d : KnotDiagram} (hwf : d.wf = true) :
    ∀ c ∈ d.crossings,
      (1 ≤ c.e2 ∧ c.e2 ≤ d.numEdges) ∧ (1 ≤ c.e4 ∧ c.e4 ≤ d.numEdges) := by
  intro c hc
  have hne : d.crossings ≠ [] := List.ne_nil_of_mem hc
  unfold KnotDiagram.wf at hwf
  rw [if_neg hne] at hwf
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  have h2 : c.e2 ∈ d.edges := List.mem_flatMap.2 ⟨c, hc, by simp⟩
  have h4 : c.e4 ∈ d.edges := List.mem_flatMap.2 ⟨c, hc, by simp⟩
  exact ⟨hwf.1 _ h2, hwf.1 _ h4⟩

/-- Le writhe du miroir d'un noeud bien formé à au moins trois arêtes est
l'opposé de son writhe. Énoncé symbolique, valable pour tout diagramme. -/
theorem writhe_mirror (k : Knot) (hwf : k.diagram.wf = true)
    (hn : 3 ≤ k.diagram.numEdges) :
    writhe k.mirror.diagram = - writhe k.diagram :=
  sum_crossingSign_mirror hn k.diagram.crossings (KnotDiagram.wf_over_bounds hwf)

/-- Writhe du trèfle : ses trois croisements sont positifs. -/
theorem writhe_trefoilDiagram : writhe trefoilDiagram = 3 := by
  decide

/-- Writhe du trèfle miroir : −3, instance de `writhe_mirror`. -/
theorem writhe_mirror_trefoil : writhe trefoil.mirror.diagram = -3 := by
  rw [writhe_mirror trefoil trefoil_wf (by decide)]
  decide

/-- Writhe du code `figureEightDiagram` du lac : ses quatre croisements
sont positifs. Un diagramme minimal du noeud en huit a un writhe nul (le
noeud est amphichiral) : ce chiffre est un premier indice du défaut de ce
code, établi par `figureEightDiagram_not_planar`. -/
theorem writhe_figureEightDiagram : writhe figureEightDiagram = 4 := by
  decide

/-! ## Tranche 2 — planarité : faces de la carte combinatoire

Un code PD fixe, en chaque croisement, l'ordre cyclique des quatre
extrémités d'arêtes : c'est un système de rotation du graphe 4-régulier
sous-jacent (croisements = sommets, arêtes du code = arêtes), donc une
carte combinatoire, c'est-à-dire un plongement cellulaire dans une surface
orientée. Ses faces sont les orbites de la permutation « traverser l'arête,
puis avancer d'une position dans l'ordre cyclique du croisement
d'arrivée » sur les brins (croisement, position). Pour un diagramme
connexe à `n ≥ 1` croisements (`n` sommets, `2n` arêtes), la formule
d'Euler `n − 2n + F = 2 − 2g` donne : la carte est plane (genre `g = 0`)
si et seulement si `F = n + 2`.

Un code qui échoue à ce test ne se dessine dans aucun plan : c'est un
diagramme de noeud **virtuel** (Kauffman 1999, *Virtual knot theory*,
European Journal of Combinatorics 20, 663-690). Le bracket et le
polynôme de Jones y restent calculables, mais ne sont plus ceux d'un
noeud classique.
-/

/-- Étiquette d'arête à la position `p` (0 à 3) du croisement `c`. -/
def PDCrossing.edgeAt (c : PDCrossing) : Nat → Nat
  | 0 => c.e1
  | 1 => c.e2
  | 2 => c.e3
  | _ => c.e4

/-- Les brins du diagramme : couples (croisement, position). -/
def KnotDiagram.darts (d : KnotDiagram) : List (Nat × Nat) :=
  (List.range d.crossings.length).flatMap (fun i => (List.range 4).map (fun p => (i, p)))

/-- Étiquette d'arête portée par un brin. -/
def KnotDiagram.dartLabel (d : KnotDiagram) (x : Nat × Nat) : Nat :=
  match d.crossings[x.1]? with
  | some c => c.edgeAt x.2
  | none => 0

/-- L'autre extrémité de l'arête portée par le brin `x` (le brin lui-même
si son étiquette n'apparaît qu'une fois, cas d'un code mal formé). -/
def KnotDiagram.opposite (d : KnotDiagram) (x : Nat × Nat) : Nat × Nat :=
  match (d.darts.filter (fun y => y != x && d.dartLabel y == d.dartLabel x)).head? with
  | some y => y
  | none => x

/-- Pas de la permutation des faces : traverser l'arête, puis avancer d'une
position dans l'ordre cyclique du croisement d'arrivée. -/
def KnotDiagram.faceStep (d : KnotDiagram) (x : Nat × Nat) : Nat × Nat :=
  let y := d.opposite x
  (y.1, (y.2 + 1) % 4)

/-- Suite des brins visités depuis `y` jusqu'au retour en `x` (au plus
`fuel` pas). -/
def KnotDiagram.orbitFrom (d : KnotDiagram) (x : Nat × Nat) :
    Nat → Nat × Nat → List (Nat × Nat)
  | 0, _ => []
  | fuel + 1, y => if y = x then [] else y :: d.orbitFrom x fuel (d.faceStep y)

/-- La face contenant le brin `x` : son orbite sous `faceStep`. -/
def KnotDiagram.face (d : KnotDiagram) (x : Nat × Nat) : List (Nat × Nat) :=
  x :: d.orbitFrom x d.darts.length (d.faceStep x)

/-- Compte les faces en retirant, face après face, les brins visités. -/
def KnotDiagram.countFaces (d : KnotDiagram) : Nat → List (Nat × Nat) → Nat
  | 0, _ => 0
  | _ + 1, [] => 0
  | fuel + 1, x :: rest =>
    let f := d.face x
    1 + d.countFaces fuel (rest.filter (fun y => !f.contains y))

/-- Nombre de faces de la carte combinatoire du code PD. -/
def KnotDiagram.faceCount (d : KnotDiagram) : Nat :=
  d.countFaces d.darts.length d.darts

/-- Critère de planarité d'Euler : `F = n + 2`. Le diagramme sans
croisement (un cercle plongé) est plan par convention. -/
def KnotDiagram.planar (d : KnotDiagram) : Bool :=
  d.crossings.isEmpty || d.faceCount == d.crossings.length + 2

/-- Le trèfle a 5 faces pour 3 croisements : 3 + 2, il est plan. -/
theorem faceCount_trefoilDiagram : trefoilDiagram.faceCount = 5 := by
  decide

theorem trefoilDiagram_planar : trefoilDiagram.planar = true := by
  decide

/-- Le miroir du trèfle reste plan : échanger les positions 1 et 3 renverse
l'ordre cyclique en chaque croisement, ce qui réfléchit la carte sans en
changer les faces. -/
theorem mirror_trefoil_planar : trefoil.mirror.diagram.planar = true := by
  decide

/-- Le code `figureEightDiagram` du lac n'a que 4 faces pour 4 croisements,
au lieu des 6 d'un diagramme plan : sa carte est de genre 1 (tore). -/
theorem faceCount_figureEightDiagram : figureEightDiagram.faceCount = 4 := by
  decide

/-- **Le code `figureEightDiagram` de `Knots.Basic` n'est pas un diagramme
plan.** Il décrit un noeud virtuel : ses valeurs de bracket et de Jones ne
sont pas celles du noeud en huit (voir `jones_figureEightDiagram`). -/
theorem figureEightDiagram_not_planar : figureEightDiagram.planar = false := by
  decide

/-- Un code PD plan du noeud en huit : celui de KnotAtlas
(`X[4,2,5,1], X[8,6,1,5], X[6,3,7,4], X[2,7,3,8]`). Lu dans la
convention horaire du module, il décrit le miroir du diagramme de
KnotAtlas, qui est encore un noeud en huit puisque ce noeud est
amphichiral. -/
def figureEightPlanarDiagram : KnotDiagram where
  crossings := [
    ⟨4, 2, 5, 1⟩,
    ⟨8, 6, 1, 5⟩,
    ⟨6, 3, 7, 4⟩,
    ⟨2, 7, 3, 8⟩
  ]
  numEdges := 8

theorem figureEightPlanarDiagram_wf : figureEightPlanarDiagram.wf = true := by
  decide

theorem faceCount_figureEightPlanarDiagram : figureEightPlanarDiagram.faceCount = 6 := by
  decide

theorem figureEightPlanarDiagram_planar : figureEightPlanarDiagram.planar = true := by
  decide

/-- Deux croisements positifs et deux négatifs : writhe nul, comme attendu
d'un diagramme minimal d'un noeud amphichiral. -/
theorem writhe_figureEightPlanarDiagram : writhe figureEightPlanarDiagram = 0 := by
  decide

set_option maxRecDepth 100000 in
/-- Bracket du noeud en huit plan : A⁸ − A⁴ + 1 − A⁻⁴ + A⁻⁸, valeur du
manuel, symétrique en A ↔ A⁻¹. -/
theorem bracket_figureEightPlanarDiagram :
    bracket figureEightPlanarDiagram = [(8, 1), (4, -1), (0, 1), (-4, -1), (-8, 1)] := by
  decide

/-! ## Tranche 2 — polynôme de Jones

Le polynôme normalisé de Kauffman f(D) = (−A³)^(−w(D)) · ⟨D⟩ compense
le facteur −A^(±3) que le bracket prend sous un mouvement de Reidemeister I
(Kauffman 1987, *State models and the Jones polynomial*, Topology 26,
395-407). Le polynôme de Jones s'en déduit par A = t^(−1/4) : V(t) =
f(D)|_{A = t^(−1/4)}. Pour un noeud, tous les exposants de f(D) sont
multiples de 4 ; les théorèmes `kauffmanF_*` l'exhibent sur les
instances.
-/

/-- Polynôme normalisé de Kauffman f(D) = (−A³)^(−w(D)) · ⟨D⟩. -/
def kauffmanF (d : KnotDiagram) : LP :=
  let w := writhe d
  lpNorm (lpMul [(-3 * w, if w % 2 = 0 then 1 else -1)] (bracket d))

/-- Changement de variable A = t^(−1/4) : l'exposant `e` de A devient
`−e/4` en t (division exacte quand `e` est multiple de 4). -/
def lpAtoT (p : LP) : LP := lpNorm (p.map (fun m => (-(m.1 / 4), m.2)))

/-- Polynôme de Jones V(t) du diagramme `d`, en forme normale (variable t). -/
def jones (d : KnotDiagram) : LP := lpAtoT (kauffmanF d)

/-- Substitution t ↦ t⁻¹, qui envoie le polynôme de Jones d'un noeud sur
celui de son miroir. -/
def lpInvert (p : LP) : LP := lpNorm (p.map (fun m => (-m.1, m.2)))

theorem jones_unknotDiagram : jones unknotDiagram = [(0, 1)] := by
  decide

/-- f(3₁) = A⁻⁴ + A⁻¹² − A⁻¹⁶ : exposants multiples de 4. -/
theorem kauffmanF_trefoilDiagram :
    kauffmanF trefoilDiagram = [(-4, 1), (-12, 1), (-16, -1)] := by
  decide

/-- V(3₁) = −t⁴ + t³ + t : polynôme de Jones du trèfle à main droite. -/
theorem jones_trefoilDiagram : jones trefoilDiagram = [(4, -1), (3, 1), (1, 1)] := by
  decide

/-- V(3₁ miroir) = t⁻¹ + t⁻³ − t⁻⁴ : trèfle à main gauche. -/
theorem jones_mirror_trefoil :
    jones trefoil.mirror.diagram = [(-1, 1), (-3, 1), (-4, -1)] := by
  decide

/-- Sur le trèfle, le miroir agit sur Jones par t ↦ t⁻¹. -/
theorem jones_mirror_trefoil_eq_invert :
    jones trefoil.mirror.diagram = lpInvert (jones trefoilDiagram) := by
  decide

/-- Le polynôme de Jones distingue le diagramme du trèfle de celui de son
miroir (le bracket seul en était aussi capable, mais seul f(D) est destiné
à devenir un invariant de noeud). Même caveat que la tranche 1 : tant que
l'invariance de Reidemeister n'est pas prouvée, c'est une distinction de
diagrammes, pas encore la chiralité du trèfle. -/
theorem jones_trefoil_ne_mirror :
    jones trefoilDiagram ≠ jones trefoil.mirror.diagram := by
  decide

set_option maxRecDepth 100000 in
/-- V(4₁) = t² − t + 1 − t⁻¹ + t⁻² : valeur du manuel pour le noeud en huit. -/
theorem jones_figureEightPlanarDiagram :
    jones figureEightPlanarDiagram = [(2, 1), (1, -1), (0, 1), (-1, -1), (-2, 1)] := by
  decide

set_option maxRecDepth 100000 in
/-- Le polynôme de Jones du noeud en huit est invariant par t ↦ t⁻¹,
signature de l'amphichiralité du noeud. -/
theorem jones_figureEightPlanarDiagram_invert :
    lpInvert (jones figureEightPlanarDiagram) = jones figureEightPlanarDiagram := by
  decide

set_option maxRecDepth 100000 in
/-- Trèfle et noeud en huit ont des polynômes de Jones distincts. -/
theorem jones_figureEightPlanar_ne_trefoil :
    jones figureEightPlanarDiagram ≠ jones trefoilDiagram := by
  decide

set_option maxRecDepth 100000 in
/-- **Défaut du code `figureEightDiagram` du lac** : son polynôme de Jones
est celui du trèfle à main droite, pas celui du noeud en huit. Avec
`figureEightDiagram_not_planar`, ce théorème établit que ce code décrit un
noeud virtuel ; les valeurs de la tranche 1 calculées sur lui
(`bracket_figureEightDiagram`) portent sur ce noeud virtuel. -/
theorem jones_figureEightDiagram :
    jones figureEightDiagram = jones trefoilDiagram := by
  decide

end Knots

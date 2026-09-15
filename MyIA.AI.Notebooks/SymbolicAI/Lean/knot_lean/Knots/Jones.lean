/-
  Knots.Jones — Bracket de Kauffman sur codes PD (tranche 1)
  ====================================================================

  Ce fichier définit le bracket de Kauffman ⟨D⟩ d'un diagramme de noeud codé
  en PD (voir `Knots.Basic`) par somme d'états, et l'évalue sur les trois
  diagrammes nommés du lac (noeud trivial, trèfle, noeud en huit), avec les
  distinctions calculatoires trèfle ≠ noeud trivial et huit ≠ noeud trivial.

  Tranche 1 de la Phase 4 de l'EPIC #2874 (polynôme de Jones via bracket de
  Kauffman). La normalisation Jones (writhe) est hors de cette tranche :
  `PDCrossing` ne porte pas de champ de signe, donc le writhe n'est pas
  calculable sans étendre `Knots.Basic` (tranche future).

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
  - **Writhe / polynôme de Jones** : NON définis. `PDCrossing` n'a pas de
    champ de signe ; le writhe (et donc la normalisation f(D) =
    (−A)^(−3w)·⟨D⟩) exige d'étendre `Knots.Basic` — hors des fichiers de
    cette tranche.
  - **Sensibilité au miroir** : le bracket d'un diagramme miroir s'obtient
    en échangeant A ↔ A⁻¹ (vérifié numériquement en Python sur le trèfle,
    non formalisé ici).
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
convention A14), le noeud en huit donne A⁸ + 1 − A⁻⁴.
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
/-- Valeur du bracket sur le noeud en huit : A⁸ + 1 − A⁻⁴. -/
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

/-- Le bracket distingue (au niveau des diagrammes) le noeud en huit du
noeud trivial : coefficient 1 en A⁸ contre 0 — même caveat que
`bracket_trefoil_ne_bracket_unknot`. -/
theorem bracket_figureEight_ne_bracket_unknot :
    bracket figureEightDiagram ≠ bracket unknotDiagram := by
  decide

end Knots

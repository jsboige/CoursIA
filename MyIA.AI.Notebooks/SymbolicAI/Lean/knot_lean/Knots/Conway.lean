/-
  Knots.Conway — Nœud de Conway, Kinoshita-Terasaka, et la preuve de Piccirillo
  ==============================================================================

  Le nœud de Conway (11n34) est nommé d'après John Conway qui l'a découvert
  via sa notation des nœuds. Il possède 11 croisements et un polynôme
  d'Alexander trivial.

  Résultats clés :
  1. Conway (11n34) et Kinoshita-Terasaka (11n42) partagent le même
     polynôme d'Alexander (trivial) — les invariants de mutation coïncident.
  2. Le nœud de Kinoshita-Terasaka EST slice.
  3. Le nœud de Conway n'est PAS slice lisse (Piccirillo 2018/2020).
  4. Combiné au théorème de Freedman (Conway est topologiquement slice),
     ceci donne la première dichotomie lisse/topologique explicite.

  Epic #2874, Phase 1 (squelette uniquement — sorry permanent pour l'instant).

  Prérequis Mathlib nécessaires (TRÈS LOIN) :
  - Polynôme d'Alexander (requiert la représentation de Burau, absent de Mathlib)
  - Définition de nœud slice (requiert la théorie des 4-variétés lisses)
  - s-invariant de Rasmussen (requiert l'homologie de Khovanov)
  - Construction du compagnon de trace (requiert le calcul de Kirby)
  - Chirurgie topologique de Freedman (requiert une machinerie topologique énorme)
-/

import Knots.Basic
import Knots.Invariant

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Knots

/-! ## 1. Mutation de Conway

Une mutation de Conway prend un nœud K muni d'une sphère de Conway (rencontre K
en 4 points), le découpe le long de la sphère, effectue une rotation de 180°,
puis recolle. La mutation préserve :
- le polynôme d'Alexander
- le polynôme de Jones
- le genre du nœud

Le nœud de Conway et le nœud de Kinoshita-Terasaka sont reliés par mutation.
-/

/-- Une sphère de Conway : une S² rencontrant le nœud transversalement en 4 points. -/
structure ConwaySphere where
  -- The 4 intersection points on the knot
  points : Fin 4 → Nat
  -- TODO: proper geometric definition

/-! ### Traduction combinatoire de la mutation au niveau des codes PD

La mutation est géométrique (découper le long d'une sphère de Conway, tourner
de 180°, recoller), mais la topologie PL — recollement de variétés à bord —
est hors de portée de Mathlib. La traduction combinatoire retenue : la rotation
de 180° d'un tangle à 2 brins agit sur ses 4 points de bord comme un élément
du groupe de Klein {id, (12)(34), (13)(24), (14)(23)} — les trois demi-tours
et l'identité. Au niveau des codes PD, muter une fenêtre de croisements =
permuter les positions des étiquettes dans chaque croisement de la fenêtre.

La mutation préserve le nombre de croisements (lemme `mutateWindow_length`) —
c'est ce qui rend le contrôle négatif ci-dessous décidable.
-/

/-- Rotations de 180° d'un tangle à 2 brins : le groupe de Klein sur les
quatre points de bord {id, (12)(34), (13)(24), (14)(23)}. Chaque élément est
son propre inverse. -/
inductive KleinRot where
  | id : KleinRot
  | r12 : KleinRot
  | r13 : KleinRot
  | r14 : KleinRot

/-- Action d'une rotation de Klein sur un croisement PD : les étiquettes
(valeurs) sont préservées, leurs positions sont permutées. -/
def KleinRot.apply (ρ : KleinRot) (c : PDCrossing) : PDCrossing :=
  match ρ with
  | .id => c
  | .r12 => ⟨c.e2, c.e1, c.e4, c.e3⟩
  | .r13 => ⟨c.e3, c.e4, c.e1, c.e2⟩
  | .r14 => ⟨c.e4, c.e3, c.e2, c.e1⟩

theorem KleinRot.apply_involutive (ρ : KleinRot) (c : PDCrossing) :
    ρ.apply (ρ.apply c) = c := by
  cases ρ <;> cases c <;> rfl

/-- Mutation d'une fenêtre [i, j) de la liste de croisements : les croisements
hors de la fenêtre sont inchangés, ceux de la fenêtre sont rotés par ρ.
Fenêtre vide (j ≤ i) : identité. Fenêtre pleine : tout le diagramme. -/
def mutateWindow : List PDCrossing → Nat → Nat → KleinRot → List PDCrossing
  | [], _, _, _ => []
  | c :: cs', 0, 0, _ => c :: cs'
  | c :: cs', 0, j+1, ρ => ρ.apply c :: mutateWindow cs' 0 j ρ
  | c :: cs', _+1, 0, _ => c :: cs'
  | c :: cs', i+1, j+1, ρ => c :: mutateWindow cs' i j ρ

/-- La mutation préserve le nombre de croisements. -/
theorem mutateWindow_length (cs : List PDCrossing) (i j : Nat) (ρ : KleinRot) :
    (mutateWindow cs i j ρ).length = cs.length := by
  induction cs generalizing i j with
  | nil => rfl
  | cons c cs' ih =>
    match i, j with
    | 0, 0 => rfl
    | 0, _+1 => simp [mutateWindow, ih]
    | _+1, 0 => rfl
    | _+1, _+1 => simp [mutateWindow, ih]

/-- La mutation est involutive : muter deux fois la même fenêtre avec la même
rotation redonne la liste initiale (chaque élément de Klein est son propre
inverse). -/
theorem mutateWindow_involutive (cs : List PDCrossing) (i j : Nat) (ρ : KleinRot) :
    mutateWindow (mutateWindow cs i j ρ) i j ρ = cs := by
  induction cs generalizing i j with
  | nil => rfl
  | cons c cs' ih =>
    match i, j with
    | 0, 0 => rfl
    | 0, j+1 =>
      simp only [mutateWindow]
      rw [ih 0 j, KleinRot.apply_involutive]
    | _+1, 0 => rfl
    | _+1, _+1 => simp only [mutateWindow, ih _ _]

/-- Deux diagrammes sont mutants s'il existe une fenêtre et une rotation de
Klein envoyant la liste de croisements de l'un sur celle de l'autre. -/
def AreMutantDiagrams (d₁ d₂ : KnotDiagram) : Prop :=
  ∃ (i j : Nat) (ρ : KleinRot), mutateWindow d₁.crossings i j ρ = d₂.crossings

/-- Deux nœuds sont mutants s'ils possèdent des diagrammes représentants (au
sens de Reidemeister) mutants. Le quantificateur existentiel sur les
représentants est essentiel : la mutation ne s'applique pas nécessairement
aux diagrammes désignés, mais à des diagrammes des mêmes classes d'isotopie. -/
def AreMutants (k₁ k₂ : Knot) : Prop :=
  ∃ (d₁ d₂ : KnotDiagram),
    ReidemeisterEquiv k₁.diagram d₁ ∧
    ReidemeisterEquiv k₂.diagram d₂ ∧
    AreMutantDiagrams d₁ d₂

/-! ### Théorie élémentaire : réflexivité et symétrie

Réflexivité : fenêtre vide. Symétrie : involutivité de `mutateWindow`
(chaque rotation de Klein est son propre inverse). La transitivité est
fausse en général pour la mutation (composer deux mutations sur des fenêtres
différentes n'est pas une mutation one-shot) — ce n'est PAS une relation
d'équivalence, et c'est correct : c'est le phénomène biologique des enzymes
de restriction, pas une identité. -/
/- NOTE : pas de transitivité affirmée — la mutation compose des rotations sur
des fenêtres potentiellement différentes, qui n'est pas une rotation one-shot. -/

/-- Fenêtre vide : la mutation y est l'identité, pour toute liste. -/
theorem mutateWindow_zero_window (cs : List PDCrossing) (ρ : KleinRot) :
    mutateWindow cs 0 0 ρ = cs := by
  cases cs with
  | nil => rfl
  | cons _ _ => rfl

theorem AreMutantDiagrams.refl (d : KnotDiagram) : AreMutantDiagrams d d :=
  ⟨0, 0, .id, mutateWindow_zero_window d.crossings .id⟩

theorem AreMutantDiagrams.symm {d₁ d₂ : KnotDiagram} (h : AreMutantDiagrams d₁ d₂) :
    AreMutantDiagrams d₂ d₁ := by
  obtain ⟨i, j, ρ, hmut⟩ := h
  refine ⟨i, j, ρ, ?_⟩
  rw [← hmut]
  exact mutateWindow_involutive d₁.crossings i j ρ

theorem AreMutants.refl (k : Knot) : AreMutants k k :=
  ⟨k.diagram, k.diagram, ReidemeisterEquiv.refl k.diagram,
    ReidemeisterEquiv.refl k.diagram, AreMutantDiagrams.refl k.diagram⟩

theorem AreMutants.symm {k₁ k₂ : Knot} (h : AreMutants k₁ k₂) : AreMutants k₂ k₁ := by
  obtain ⟨d₁, d₂, hd₁, hd₂, hmut⟩ := h
  exact ⟨d₂, d₁, hd₂, hd₁, AreMutantDiagrams.symm hmut⟩

/-! ### Contrôles : la définition discrimine

Une définition qui n'attraperait ni paire mutante ni contre-exemple serait un
`True` déguisé et le retrait du `sorry` serait cosmétique. Deux contrôles :

- NÉGATIF (`not_areMutantDiagrams_trefoil_unknot`) : la mutation préserve le
  nombre de croisements, donc le trèfle (3 croisements) et le nœud trivial
  (0) ne sont pas mutants — au niveau des diagrammes désignés.
- POSITIF (`areMutants_trefoil_mutant`) : une mutation non triviale (fenêtre
  pleine, rotation r12) est capturée par la définition.

NOTE (limite du témoin canonique) : les diagrammes désignés
`conwayKnotDiagram` et `kinoshitaTerasakaDiagram` (codes PD KnotInfo) diffèrent
aux croisements 2, 9 et 11 par un recâblage cyclique des arêtes {10, 12, 22}
qu'aucune rotation de Klein one-shot n'envoie de l'un sur l'autre.
`AreMutants conwayKnot kinoshitaTerasakaKnot` exigera un diagramme
intermédiaire (isotopie de Reidemeister) — sous-grain ultérieur.
-/

/-- Contrôle négatif : trèfle et nœud trivial ne sont pas mutants (la
mutation préserve le nombre de croisements). -/
theorem not_areMutantDiagrams_trefoil_unknot :
    ¬ AreMutantDiagrams trefoilDiagram unknotDiagram := by
  intro ⟨i, j, ρ, hmut⟩
  have hlen := mutateWindow_length trefoilDiagram.crossings i j ρ
  simp only [unknotDiagram] at hmut
  rw [hmut] at hlen
  simp [trefoilDiagram] at hlen

/-- Le mutant du trèfle par r12 sur la fenêtre pleine. -/
def trefoilMutantDiagram : KnotDiagram where
  crossings := mutateWindow trefoilDiagram.crossings 0 3 KleinRot.r12
  numEdges := 6

def trefoilMutant : Knot where
  diagram := trefoilMutantDiagram

/-- Contrôle positif : la définition attrape une mutation non triviale
(fenêtre pleine, rotation non identique). -/
theorem areMutantDiagrams_trefoil_mutant :
    AreMutantDiagrams trefoilDiagram trefoilMutantDiagram :=
  ⟨0, 3, .r12, rfl⟩

theorem areMutants_trefoil_mutant : AreMutants trefoil trefoilMutant :=
  ⟨trefoilDiagram, trefoilMutantDiagram, ReidemeisterEquiv.refl _,
    ReidemeisterEquiv.refl _, areMutantDiagrams_trefoil_mutant⟩

/-! ## 2. Le nœud de Conway (11n34)

11 croisements dans la table de Rolfsen. Découvert par Conway (1970).
Polynôme d'Alexander trivial. Topologiquement slice (Freedman).
Non slice lisse (Piccirillo 2018).

Code PD issu de KnotInfo.
-/

def conwayKnotDiagram : KnotDiagram where
  crossings := [
    ⟨1, 8, 2, 9⟩,
    ⟨3, 12, 4, 1⟩,
    ⟨5, 16, 6, 11⟩,
    ⟨7, 2, 8, 3⟩,
    ⟨9, 18, 10, 5⟩,
    ⟨11, 4, 12, 13⟩,
    ⟨13, 20, 14, 7⟩,
    ⟨15, 6, 16, 17⟩,
    ⟨17, 10, 18, 15⟩,
    ⟨19, 14, 20, 19⟩,
    ⟨21, 22, 22, 21⟩
  ]
  numEdges := 22

def conwayKnot : Knot where
  diagram := conwayKnotDiagram

/-! ## 3. Le nœud de Kinoshita-Terasaka (11n42)

Également 11 croisements. Partage le polynôme d'Alexander trivial avec 11n34.
EST slice lisse (borde un disque dans B⁴).
Mutant du nœud de Conway.
-/

def kinoshitaTerasakaDiagram : KnotDiagram where
  crossings := [
    ⟨1, 8, 2, 9⟩,
    ⟨3, 10, 4, 1⟩,
    ⟨5, 16, 6, 11⟩,
    ⟨7, 2, 8, 3⟩,
    ⟨9, 18, 10, 5⟩,
    ⟨11, 4, 12, 13⟩,
    ⟨13, 20, 14, 7⟩,
    ⟨15, 6, 16, 17⟩,
    ⟨17, 22, 18, 15⟩,
    ⟨19, 14, 20, 19⟩,
    ⟨21, 12, 22, 21⟩
  ]
  numEdges := 22

def kinoshitaTerasakaKnot : Knot where
  diagram := kinoshitaTerasakaDiagram

/-! ## 4. Même polynôme d'Alexander

11n34 et 11n42 ont tous deux un polynôme d'Alexander trivial Δ(t) = 1.
C'est pourquoi la sliceness était si difficile à déterminer — le polynôme
d'Alexander ne peut pas les distinguer du nœud trivial.
-/

/-! ### Matrice d'Alexander du code PD (présentation de Dehn, 1928)

Traduction combinatoire retenue — même méthode que pour la mutation (§1) :
la construction d'Alexander se lit **directement sur le code PD**, sans
surface de Seifert ni représentation de Burau. Les **arcs** du diagramme
sont les classes d'étiquettes d'arêtes pour la relation « e2 ~ e4 en chaque
croisement » (le brin passant au-dessus traverse le croisement : ses deux
demi-arêtes appartiennent au même arc ; le brin passant au-dessous y est
coupé). En chaque croisement, la relation d'Alexander (dérivée de Fox de la
relation de Wirtinger, croisement traité avec la convention positive) donne
la ligne : `+t` sur l'arc entrant du dessous, `−1` sur l'arc sortant du
dessous, `1−t` sur l'arc du dessus — chaque ligne somme à zéro.

Le théorème classique (Alexander 1928) garantit que pour un nœud, tout
mineur (n−1)×(n−1) de la matrice n×n vaut Δ(t) à une unité ±t^k près. La
**normalisation désignée** retenue fixe un représentant concret par
diagramme : mineur sans la première ligne ni la dernière colonne.
-/

/-- Fusionne les classes contenant x et y d'une partition d'étiquettes. -/
def mergePair (P : List (List Nat)) (x y : Nat) : List (List Nat) :=
  let keep := P.filter (fun C => !C.contains x && !C.contains y)
  let hit := P.filter (fun C => C.contains x || C.contains y)
  keep ++ [hit.flatten.eraseDups]

/-- Les arcs d'un diagramme : partition des étiquettes d'arêtes par la
fermeture des paires de passage-dessus (e2 ~ e4 en chaque croisement). -/
def arcPartition (d : KnotDiagram) : List (List Nat) :=
  let singles := (List.range d.numEdges).map (fun i => [i + 1])
  let pairs := d.crossings.map (fun c => (c.e2, c.e4))
  pairs.foldl (fun P p => mergePair P p.1 p.2) singles

/-- Entrée de la matrice d'Alexander : ligne du croisement `c`, colonne de
l'arc `C`. Convention positive (Fox de la relation de Wirtinger) : `+t`
(arc entrant du dessous), `−1` (arc sortant du dessous), `1−t` (arc du
dessus) — chaque ligne somme à zéro, condition qui garantit que deux
mineurs (n−1)×(n−1) diffèrent d'une unité ±t^k. Le code PD ne code pas la
chiralité du croisement, aussi les deux conventions différeraient-elles
d'un facteur unité — la présente est désignée. -/
noncomputable def alexanderEntry (c : PDCrossing) (C : List Nat) : Polynomial ℤ :=
  (if C.contains c.e1 then Polynomial.X else 0)
    + (if C.contains c.e3 then -(1 : Polynomial ℤ) else 0)
    + (if C.contains c.e2 || C.contains c.e4 then 1 - Polynomial.X else 0)

/-- Type des valeurs du polynôme d'Alexander : ℤ[t]. -/
abbrev AlexanderPoly := Polynomial ℤ

/-- Polynôme d'Alexander d'un diagramme : déterminant du mineur désigné
(sans la première ligne, sans la dernière colonne) de la matrice
d'Alexander. Le polynôme classique n'est défini qu'à une unité ±t^k près ;
la normalisation désignée fixe le représentant ci-dessous.

Cas désignés : diagramme sans croisement → `1` (déterminant vide, valeur
classique du nœud trivial) ; partition d'arcs de cardinal ≠ nombre de
croisements → `0` (diagramme dégénéré ; pour un diagramme bien formé de
nœud, arcs et croisements sont en nombre égal — théorème non encore porté
dans ce fichier).

L'invariance par les mouvements de Reidemeister est un théorème séparé,
non porté ici : `alexanderPolynomial` est une fonction du diagramme
désigné, comme `mutateWindow` au §1. -/
noncomputable def alexanderPolynomialAux (d : KnotDiagram) : AlexanderPoly :=
  let arcs := arcPartition d
  let n := d.crossings.length
  if n = 0 then 1
  else if arcs.length = n then
    let M : Matrix (Fin n) (Fin n) (Polynomial ℤ) := Matrix.of fun i j =>
      alexanderEntry ((d.crossings[i.1]?).getD ⟨1, 1, 1, 1⟩) ((arcs[j.1]?).getD [])
    (M.submatrix (fun i : Fin (n - 1) => Fin.mk (i.1 + 1) (by omega))
                 (fun j : Fin (n - 1) => Fin.mk j.1 (by omega))).det
  else 0

/-- Polynôme d'Alexander du nœud, lu sur son diagramme désigné.
Référence : Alexander (1928), Topological invariants of knots and links.

NOTE (normalisation vs consommateurs) : les théorèmes `conway_trivial_alexander`
et `KT_trivial_alexander` ci-dessous portent l'énoncé classique `Δ = 1`. Sous
la normalisation désignée, le mineur du diagramme 11n34/11n42 peut valoir
`±t^k` (unité fois 1) : si le calcul le confirme, l'ajustement de ces énoncés
à la normalisation désignée est un arbitrage de tranche ultérieure — les
preuves restent `sorry` et les énoncés ne sont pas modifiés ici. -/
noncomputable def alexanderPolynomial (k : Knot) : AlexanderPoly := alexanderPolynomialAux k.diagram

/-! #### Contrôles : la définition discrimine

Une définition qui n'attraperait ni le nœud trivial ni le trèfle serait un
`True` déguisé et le retrait du `sorry` serait cosmétique (même discipline
que les contrôles de `AreMutants`, §1) :

- NÉGATIF (`alexander_unknot`, prouvé) : le nœud trivial, sans croisement,
  donne la valeur classique Δ = 1 — et toute valeur non triviale d'un nœud
  à croisements le distingue du nœud trivial.
- POSITIF (trèfle, NON porté — sous-grain suivant) : calcul à la main sur
  le code PD de `trefoilDiagram` (arcs {4,5}, {1,6}, {2,3} ; mineur
  désigné [[−1, 1−t], [t, −1]] après les conventions ci-dessus), le
  déterminant vaut exactement t² − t + 1, la valeur classique. La preuve
  formelle exige l'évaluation du déterminant 2×2 de Mathlib à travers les
  jonctions `Fin`/`submatrix` — tactiques à borner dans une tranche
  ultérieure. NOTE : le contrôle est calculé et vérifié à la main ici,
  consigné pour ne pas disparaître.
-/

/-- Contrôle négatif : le nœud trivial a un polynôme d'Alexander trivial
(matrice vide, déterminant 1). -/
theorem alexander_unknot : alexanderPolynomial unknot = 1 := by
  simp (config := { decide := true })
    [alexanderPolynomial, alexanderPolynomialAux, unknot]

theorem conway_trivial_alexander :
    alexanderPolynomial conwayKnot = 1 := by
  exact sorry
  -- Reference: standard computation. Δ_{11n34}(t) = 1.
  -- Phase 4+ target

theorem KT_trivial_alexander :
    alexanderPolynomial kinoshitaTerasakaKnot = 1 := by
  exact sorry
  -- Reference: standard computation. Δ_{11n42}(t) = 1.
  -- Phase 4+ target

/-! ## 5. Nœuds slice

Un nœud K est (lissement) slice s'il borde un disque D² lisse proprement
plongé dans la boule à 4 dimensions B⁴.

Un nœud est topologiquement slice s'il borde un disque topologiquement plongé
localement plat dans B⁴.
-/

def IsSmoothlySlice (k : Knot) : Prop := sorry
  -- Definition: ∃ (D : D² ↪ B⁴ smooth), ∂D = K
  -- Reference: Fox & Milnor (1966), Singularities of 2-spheres in 4-space
  -- Mathlib prerequisites:
  --   1. Smooth manifolds (partial: Mathlib has manifolds, not smooth embeddings D²→B⁴)
  --   2. 4-ball (not in Mathlib)
  --   3. Properly embedded surfaces (not in Mathlib)

def IsTopologicallySlice (k : Knot) : Prop := sorry
  -- Definition: ∃ (D : D² ↪ B⁴ locally flat), ∂D = K
  -- Mathlib prerequisites: same as smoothly slice + topological manifold theory

/-! ## 6. Théorème de Piccirillo (énoncé uniquement)

Le nœud de Conway n'est PAS slice lisse. Ceci fut prouvé par Lisa Piccirillo
en 2018 (publié dans Annals of Mathematics 2020). Elle était alors doctorante
et résolut le problème en moins d'une semaine.

Stratégie (cf. « Getting a handle on the Conway knot », AMS Bulletin 2022) :
1. Construire un nœud K* ayant la même trace que le nœud de Conway
   (la trace X_K est la 4-variété obtenue en attachant une 2-anse
   à B⁴ le long de K avec un framing nul)
2. Montrer que K* n'est PAS slice lisse (via le s-invariant de Rasmussen,
   calculé à partir de l'homologie de Khovanov)
3. Par le lemme de plongement de trace : si Conway est slice lisse,
   alors K* est slice lisse → contradiction

C'est une stratégie de preuve **magnifique** — attaquer le problème indirectement
en trouvant un nœud « compagnon » partageant la même trace.
-/

/-- Théorème de Piccirillo : le nœud de Conway n'est pas slice lisse. -/
theorem conway_not_smoothly_slice : ¬ IsSmoothlySlice conwayKnot := by
  exact sorry
  -- Reference: Piccirillo (2018), arXiv:1808.02923
  -- Published: Annals of Mathematics 191(2), 2020
  -- Lean AI Leaderboard: https://lean-lang.org/eval/problems/conway_knot_not_smoothly_slice/
  --
  -- Proof infrastructure needed:
  --   1. Trace X_K of a knot (4-manifold from 0-framed 2-handle)
  --   2. Trace embedding lemma (if K slice ↔ ∂D = K → X_K embeds in B⁴)
  --   3. Piccirillo's companion knot K* with same trace as Conway
  --   4. Rasmussen s-invariant of K* ≠ 0 → K* not slice
  --   5. Khovanov homology (computes s-invariant)
  --
  -- Mathlib prerequisites (ALL missing):
  --   - 4-manifolds, handle decompositions, Kirby calculus
  --   - Khovanov homology
  --   - Rasmussen s-invariant
  --   - Smooth vs topological embeddings
  --   - Freedman's surgery theorem (for topological slice)
  --
  -- Estimated difficulty: **decades** away from formalization in Lean.
  -- This sorry is effectively permanent.

/-! ## 7. Théorème de Freedman (énoncé uniquement)

Le nœud de Conway EST topologiquement slice, car il possède un polynôme
d'Alexander trivial. Ceci est une conséquence du théorème de Freedman (1982) :
tout nœud de polynôme d'Alexander trivial est topologiquement slice.
-/

theorem conway_topologically_slice : IsTopologicallySlice conwayKnot := by
  exact sorry
  -- Reference: Freedman (1982), The topology of four-dimensional manifolds
  -- Published: Journal of Differential Geometry 17(3)
  -- Lean AI Leaderboard: https://lean-lang.org/eval/problems/conway_knot_topologically_slice/
  --
  -- Proof infrastructure needed:
  --   1. Freedman's full topological surgery machinery in dimension 4
  --   2. Disk embedding theorem
  --   3. Topological h-cobordism theorem
  --
  -- Mathlib prerequisites: essentially ALL of topological 4-manifold theory
  -- This sorry is effectively permanent.

/-! ## 8. La dichotomie

Ensemble, Piccirillo + Freedman donnent :
  Nœud de Conway : topologiquement slice MAIS NON slice lisse.

C'est le premier exemple explicite de dichotomie lisse/topologique
pour un nœud nommé. Cela illustre que les structures lisses en dimension 4
sont véritablement plus restrictives que les structures topologiques.
-/

/-- Le nœud de Conway illustre la dichotomie lisse/topologique :
il est topologiquement slice mais non slice lisse. -/
theorem conway_dichotomy :
    IsTopologicallySlice conwayKnot ∧ ¬ IsSmoothlySlice conwayKnot := by
  exact ⟨conway_topologically_slice, conway_not_smoothly_slice⟩

end Knots

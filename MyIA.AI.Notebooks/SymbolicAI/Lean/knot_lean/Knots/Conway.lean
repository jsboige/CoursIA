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
`conwayKnotDiagram` et `kinoshitaTerasakaDiagram` (codes PD census corrigés,
cf. §2) partagent leurs cinq premiers croisements et diffèrent aux
croisements 6 à 11 — aucun envoi one-shot ne les superpose.
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

Code PD du census KnotInfo (généré par spherogram 2.4.1), **corrigé** : le
code commité par #12892 n'était pas connexe — son croisement 11
`⟨21, 22, 22, 21⟩` n'utilisait que les arêtes {21, 22}, composante isolée du
reste du diagramme, et l'arête 19 apparaissait deux fois dans son propre
croisement `⟨19, 14, 20, 19⟩`. Le contrôle `wf` (étiquettes dans [1, 22],
chacune exactement deux fois) ne voit pas la connexité : le défaut passait.
Conséquence mesurée : la ligne du croisement 11 était entièrement nulle dans
le mineur désigné → déterminant 0, et l'énoncé `conway_trivial_alexander`
d'origine (`= 1`) était faux sous la normalisation désignée. Les tuples
ci-dessous sont la rotation (t₁, t₂, t₃, t₀) des tuples census, telle que le
brin passant-dessus occupe les positions (e2, e4) de la convention du présent
fichier. Cible désignée vérifiée (sonde Python fidèle à la construction,
validée sur 3₁/4₁/5₁) : mineur = −t⁶, une unité — Δ = 1 au sens classique.
-/

def conwayKnotDiagram : KnotDiagram where
  crossings := [
    ⟨1, 4, 22, 3⟩,
    ⟨7, 2, 6, 1⟩,
    ⟨3, 8, 2, 7⟩,
    ⟨4, 12, 5, 11⟩,
    ⟨12, 6, 13, 5⟩,
    ⟨16, 9, 15, 8⟩,
    ⟨9, 21, 10, 20⟩,
    ⟨17, 11, 18, 10⟩,
    ⟨13, 19, 14, 18⟩,
    ⟨19, 15, 20, 14⟩,
    ⟨22, 17, 21, 16⟩
  ]
  numEdges := 22

/-- Contrôle : le code corrigé est bien formé au sens `wf` (chaque étiquette
de [1, 22] exactement deux fois). Le code non connexe précédent passait
aussi ce contrôle — c'est le contrôle d'arcs qui distingue. -/
theorem conway_wf : conwayKnotDiagram.wf = true := by
  decide

/-- Contrôle : la partition d'arcs du code corrigé — 11 arcs couvrant les 22
arêtes, condition de non-dégénérescence du mineur d'Alexander (le code non
connexe précédent produisait un arc isolé {21, 22} absorbé par la colonne
éliminée du mineur désigné). Énoncé en §4 (`conway_arcPartition`). -/

def conwayKnot : Knot where
  diagram := conwayKnotDiagram

/-! ## 3. Le nœud de Kinoshita-Terasaka (11n42)

Également 11 croisements. Partage le polynôme d'Alexander trivial avec 11n34.
EST slice lisse (borde un disque dans B⁴).
Mutant du nœud de Conway.

Code PD census corrigé comme en §2 (le code précédent était connexe mais
portait des arêtes répétées intra-croisement aux croisements 10 et 11 —
`⟨19, 14, 20, 19⟩` et `⟨21, 12, 22, 21⟩` — donnant un mineur désigné non
unitaire de degré 7, faux pour Δ = 1). Même rotation (t₁, t₂, t₃, t₀).
Cible désignée vérifiée : mineur = t⁵, une unité.
-/

def kinoshitaTerasakaDiagram : KnotDiagram where
  crossings := [
    ⟨1, 4, 22, 3⟩,
    ⟨7, 2, 6, 1⟩,
    ⟨3, 8, 2, 7⟩,
    ⟨4, 12, 5, 11⟩,
    ⟨12, 6, 13, 5⟩,
    ⟨17, 9, 18, 8⟩,
    ⟨9, 15, 10, 14⟩,
    ⟨20, 11, 19, 10⟩,
    ⟨14, 19, 13, 18⟩,
    ⟨15, 21, 16, 20⟩,
    ⟨21, 17, 22, 16⟩
  ]
  numEdges := 22

/-- Contrôle `wf` du code KT corrigé (cf. `conway_wf`). -/
theorem kinoshitaTerasaka_wf : kinoshitaTerasakaDiagram.wf = true := by
  decide

/-- Contrôle : partition d'arcs du code KT corrigé — 11 arcs, même structure
que Conway aux croisements 1-5 (arcs partagés), divergente au-delà. Énoncé
en §4 (`kinoshitaTerasaka_arcPartition`). -/

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

/-! #### Le fait de Fox : la paire de dessus partage une classe d'arcs

La docstring d'`alexanderEntry` avance que « chaque ligne somme à zéro ».
Ce n'est pas une propriété de la ligne seule : c'est la conséquence d'un fait
structurel de `arcPartition` — en chaque croisement, les deux étiquettes de
dessus `e2` et `e4` appartiennent à une même classe. `mergePair` fusionne
précisément cette paire, et le repli ne fait ensuite qu'unir des classes,
jamais en scinder une : c'est la traduction combinatoire de la relation de
Wirtinger. Les lemmes qui suivent l'établissent pour tout diagramme dont les
étiquettes d'arêtes vivent dans la plage `1..numEdges` (cf `EdgesInRange`).
-/

/-- Deux étiquettes d'arêtes partagent une classe de la partition `P`. -/
def SameClass (P : List (List Nat)) (x y : Nat) : Prop :=
  ∃ C ∈ P, x ∈ C ∧ y ∈ C

/-- L'étiquette `z` est portée par au moins une classe de `P`. -/
def Covered (P : List (List Nat)) (z : Nat) : Prop := ∃ C ∈ P, z ∈ C

/-- Étape du repli de `arcPartition` : fusionner la paire de dessus. -/
def mergeStep (P : List (List Nat)) (p : Nat × Nat) : List (List Nat) :=
  mergePair P p.1 p.2

/-- Forme dépliée de `mergePair` : les classes intactes, puis la classe
fusionnée. -/
lemma mergePair_eq (P : List (List Nat)) (x y : Nat) :
    mergePair P x y =
      (P.filter (fun C => !C.contains x && !C.contains y)) ++
      [(P.filter (fun C => C.contains x || C.contains y)).flatten.eraseDups] := rfl

/-- La classe fusionnée porte toute étiquette d'une classe du filtre `hit`. -/
lemma mem_merged {P : List (List Nat)} {C : List Nat} {z x y : Nat}
    (hC : C ∈ P) (hz : z ∈ C) (hxy : (C.contains x || C.contains y) = true) :
    z ∈ (P.filter (fun C => C.contains x || C.contains y)).flatten.eraseDups := by
  rw [List.mem_eraseDups, List.mem_flatten]
  exact ⟨C, List.mem_filter.mpr ⟨hC, hxy⟩, hz⟩

/-- Une classe qui ne porte ni `x` ni `y` reste intacte dans `keep`. -/
lemma keep_filter {P : List (List Nat)} {C : List Nat} {x y : Nat}
    (hC : C ∈ P) (hmem : ¬(C.contains x || C.contains y) = true) :
    C ∈ (P.filter (fun C => !C.contains x && !C.contains y)) := by
  refine List.mem_filter.mpr ⟨hC, ?_⟩
  simpa using hmem

/-- `mergePair` ne fait pas disparaître une étiquette déjà couverte. -/
lemma covered_mergePair {P : List (List Nat)} {x y z : Nat} (h : Covered P z) :
    Covered (mergePair P x y) z := by
  obtain ⟨C, hC, hz⟩ := h
  by_cases hmem : (C.contains x || C.contains y) = true
  · refine ⟨_, ?_, mem_merged hC hz hmem⟩
    rw [mergePair_eq, List.mem_append]; right; exact List.mem_singleton.mpr rfl
  · refine ⟨C, ?_, hz⟩
    rw [mergePair_eq, List.mem_append]; left
    exact keep_filter hC hmem

/-- `mergePair` ne scinde aucune classe : deux étiquettes qui partageaient une
classe continuent de la partager. -/
lemma sameClass_mergePair {P : List (List Nat)} {x y a b : Nat}
    (h : SameClass P a b) : SameClass (mergePair P x y) a b := by
  obtain ⟨C, hC, ha, hb⟩ := h
  by_cases hmem : (C.contains x || C.contains y) = true
  · refine ⟨_, ?_, mem_merged hC ha hmem, mem_merged hC hb hmem⟩
    rw [mergePair_eq, List.mem_append]; right; exact List.mem_singleton.mpr rfl
  · refine ⟨C, ?_, ha, hb⟩
    rw [mergePair_eq, List.mem_append]; left
    exact keep_filter hC hmem

/-- `mergePair` réunit effectivement `x` et `y` dans une même classe, dès lors
que l'un et l'autre sont couverts (le filtre `hit` n'est alors pas vide et la
classe fusionnée les porte tous les deux). -/
lemma sameClass_mergePair_self {P : List (List Nat)} {x y : Nat}
    (hx : Covered P x) (hy : Covered P y) : SameClass (mergePair P x y) x y := by
  obtain ⟨Cx, hCx, hx'⟩ := hx
  obtain ⟨Cy, hCy, hy'⟩ := hy
  have hmx : (Cx.contains x || Cx.contains y) = true := by
    rw [Bool.or_eq_true]; left; exact List.contains_iff_mem.mpr hx'
  have hmy : (Cy.contains x || Cy.contains y) = true := by
    rw [Bool.or_eq_true]; right; exact List.contains_iff_mem.mpr hy'
  refine ⟨_, ?_, mem_merged hCx hx' hmx, mem_merged hCy hy' hmy⟩
  rw [mergePair_eq, List.mem_append]; right; exact List.mem_singleton.mpr rfl

/-- Le repli préserve l'appartenance partagée. -/
lemma sameClass_foldl {pairs : List (Nat × Nat)} {P : List (List Nat)} {a b : Nat}
    (h : SameClass P a b) : SameClass (pairs.foldl mergeStep P) a b := by
  induction pairs generalizing P with
  | nil => exact h
  | cons p ps ih => rw [List.foldl_cons]; exact ih (sameClass_mergePair h)

/-- Toute paire rencontrée pendant le repli finit dans une même classe. -/
lemma sameClass_foldl_of_mem {pairs : List (Nat × Nat)} {P : List (List Nat)}
    (hcover : ∀ q ∈ pairs, Covered P q.1 ∧ Covered P q.2) :
    ∀ q ∈ pairs, SameClass (pairs.foldl mergeStep P) q.1 q.2 := by
  induction pairs generalizing P with
  | nil => intro q hq; simp at hq
  | cons p ps ih =>
      intro q hq
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hq with rfl | hqs
      · exact sameClass_foldl (sameClass_mergePair_self
          (hcover q (List.mem_cons.mpr (Or.inl rfl))).1
          (hcover q (List.mem_cons.mpr (Or.inl rfl))).2)
      · exact ih (P := mergeStep P p)
          (fun r hr => ⟨covered_mergePair (hcover r (List.mem_cons.mpr (Or.inr hr))).1,
                        covered_mergePair (hcover r (List.mem_cons.mpr (Or.inr hr))).2⟩)
          q hqs

/-- Toute étiquette de la plage `1..n` est couverte par les singletons initiaux. -/
lemma covered_singles {n z : Nat} (h1 : 1 ≤ z) (h2 : z ≤ n) :
    Covered ((List.range n).map (fun i => [i + 1])) z := by
  refine ⟨[z], ?_, by simp⟩
  rw [List.mem_map]
  exact ⟨z - 1, by rw [List.mem_range]; omega, by simp only [Nat.sub_add_cancel h1]⟩

/-- Les quatre étiquettes d'arête de chaque croisement vivent dans la plage
`1..numEdges` du diagramme. -/
def EdgesInRange (d : KnotDiagram) : Prop :=
  ∀ c ∈ d.crossings, 1 ≤ c.e1 ∧ c.e1 ≤ d.numEdges ∧
    1 ≤ c.e2 ∧ c.e2 ≤ d.numEdges ∧
    1 ≤ c.e3 ∧ c.e3 ≤ d.numEdges ∧
    1 ≤ c.e4 ∧ c.e4 ≤ d.numEdges

/-- Le repli de `arcPartition` en forme de `foldl` sur `mergeStep`. -/
lemma arcPartition_eq (d : KnotDiagram) :
    arcPartition d = (d.crossings.map (fun c => (c.e2, c.e4))).foldl mergeStep
      ((List.range d.numEdges).map (fun i => [i + 1])) := rfl

/-- **Le fait de Fox** : en chaque croisement d'un diagramme à étiquettes en
plage, les deux étiquettes de dessus appartiennent à une même classe de la
partition d'arcs. C'est ce fait — et non la seule garde de cardinal de
`alexanderPolynomialAux` — qui porte la somme de ligne nulle de la matrice
d'Alexander (cf `alexanderEntry_sum_zero` ci-dessous). -/
theorem arcPartition_sameClass_overStrand (d : KnotDiagram) (h : EdgesInRange d)
    {c : PDCrossing} (hc : c ∈ d.crossings) :
    SameClass (arcPartition d) c.e2 c.e4 := by
  rw [arcPartition_eq]
  have hcover : ∀ q ∈ d.crossings.map (fun c => (c.e2, c.e4)),
      Covered ((List.range d.numEdges).map (fun i => [i + 1])) q.1 ∧
      Covered ((List.range d.numEdges).map (fun i => [i + 1])) q.2 := by
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨c', hc', rfl⟩ := hq
    obtain ⟨_, _, h2lo, h2hi, _, _, h4lo, h4hi⟩ := h c' hc'
    exact ⟨covered_singles h2lo h2hi, covered_singles h4lo h4hi⟩
  exact sameClass_foldl_of_mem hcover (c.e2, c.e4) (List.mem_map.mpr ⟨c, hc, rfl⟩)

/-- Contrôle : la partition d'arcs du code Conway corrigé — 11 arcs couvrant
les 22 arêtes (condition de non-dégénérescence du mineur d'Alexander : la
garde `arcs'.length = rest.length + 1` de `alexanderPolynomialAux` passe).
Le code non connexe précédent produisait un arc isolé {21, 22} absorbé par
la colonne éliminée du mineur désigné → déterminant 0. -/
theorem conway_arcPartition :
    arcPartition conwayKnotDiagram =
      [[13], [22], [3, 4], [1, 2], [5, 6], [9, 7, 8], [20, 21], [10, 11, 12],
       [18, 19], [14, 15], [16, 17]] := by
  decide

/-- Contrôle : partition d'arcs du code KT corrigé — 11 arcs, structure
partagée avec Conway sur les croisements 1-5, divergente au-delà. -/
theorem kinoshitaTerasaka_arcPartition :
    arcPartition kinoshitaTerasakaDiagram =
      [[13], [22], [3, 4], [1, 2], [5, 6], [9, 7, 8], [14, 15], [10, 11, 12],
       [18, 19], [20, 21], [16, 17]] := by
  decide

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

/-! #### Les lignes d'Alexander somment à zéro

Sous les hypothèses d'unicité — chaque étiquette du dessous portée par
exactement une classe, la paire de dessus rencontrant exactement une classe —
chaque ligne de la matrice d'Alexander somme à zéro : `t − 1 + (1 − t) = 0`.
C'est ce fait qui rend le mineur (n−1)×(n−1) indépendant, à un signe près, du
choix de la colonne frappée : l'affirmation normative de la docstring
d'`alexanderEntry` devient ici un théorème. `arcPartition_sameClass_overStrand`
fournit la moitié combinatoire (la paire de dessus partage une classe) ;
la vérification que `arcPartition` satisfait les hypothèses d'unicité
(`countP` = 1 par étiquette) est établie dans la section suivante
(`arcPartition_countP_label`).
-/

/-- Somme d'une carte indicatrice : le `w` est compté une fois par classe
porteuse. -/
lemma sum_map_indicator (P : List (List Nat)) (p : List Nat → Bool) (w : Polynomial ℤ) :
    (P.map (fun C => if p C then w else 0)).sum = w * (P.countP p : Polynomial ℤ) := by
  induction P with
  | nil => simp
  | cons D Ps ih =>
      by_cases hD : p D = true
      · simp only [List.map_cons, List.sum_cons, ih, List.countP_cons, hD, if_true]
        push_cast
        ring
      · simp only [List.map_cons, List.sum_cons, ih, List.countP_cons, hD, Bool.false_eq_true,
          if_false]
        push_cast
        ring

/-- La somme d'une carte à trois termes se distribue sur les trois sommes. -/
lemma sum_map_three (P : List (List Nat)) (f g h : List Nat → Polynomial ℤ) :
    (P.map (fun C => f C + g C + h C)).sum =
      (P.map f).sum + (P.map g).sum + (P.map h).sum := by
  induction P with
  | nil => simp
  | cons D Ps ih => simp only [List.map_cons, List.sum_cons, ih]; abel

/-- **Somme de ligne nulle** : si chaque étiquette du dessous est portée par
exactement une classe et si la paire de dessus rencontre exactement une
classe, alors la ligne d'`alexanderEntry` somme à zéro. C'est le fait de Fox
qui rend le mineur (n−1)×(n−1) indépendant, à un signe près, du choix de la
colonne frappée — le socle demandé par See #14962 avant toute correction de
normalisation. -/
theorem alexanderEntry_sum_zero (P : List (List Nat)) (c : PDCrossing)
    (h1 : P.countP (fun C => C.contains c.e1) = 1)
    (h3 : P.countP (fun C => C.contains c.e3) = 1)
    (h24 : P.countP (fun C => C.contains c.e2 || C.contains c.e4) = 1) :
    (P.map (alexanderEntry c)).sum = 0 := by
  have hmap : (P.map (alexanderEntry c)) = P.map (fun C : List Nat =>
      ((if C.contains c.e1 then (Polynomial.X : Polynomial ℤ) else 0)
        + (if C.contains c.e3 then (-(1 : Polynomial ℤ)) else 0)
        + (if C.contains c.e2 || C.contains c.e4 then (1 : Polynomial ℤ) - Polynomial.X
           else 0))) := by
    congr 1
  rw [hmap, sum_map_three, sum_map_indicator, h1, sum_map_indicator, h3, sum_map_indicator, h24]
  push_cast
  ring

/-! #### `arcPartition` est une partition : l'unicité `countP` = 1

La section précédente reposait sur des hypothèses d'unicité (`countP` = 1).
Cette section les établit pour la vraie `arcPartition` : les classes sont deux
à deux disjointes (un invariant que `mergePair` préserve), sans doublon, et
couvrent toute la plage `1..numEdges`. Il en découle que chaque ligne de la
matrice d'Alexander somme à zéro sans hypothèse additionnelle — le résiduel
nommé sur See #14962 est levé. -/

/-- Deux classes distinctes de `P` sont disjointes. -/
def ClassesDisjoint (P : List (List Nat)) : Prop :=
  ∀ C ∈ P, ∀ D ∈ P, C ≠ D → ∀ z, z ∈ C → z ∉ D

/-- Les singletons initiaux sont deux à deux disjoints. -/
lemma classesDisjoint_singles {n : Nat} :
    ClassesDisjoint ((List.range n).map (fun i => [i + 1])) := by
  intro C hC D hD hne z hzC hzD
  rw [List.mem_map] at hC hD
  obtain ⟨i, hi, rfl⟩ := hC
  obtain ⟨j, hj, rfl⟩ := hD
  simp only [List.mem_singleton] at hzC hzD
  exact hne (by congr 1; omega)

/-- Le filtre `keep` (classes ne portant ni `x` ni `y`) ne rencontre jamais le
bloc fusionné : un `z` d'une classe intacte n'appartient à aucune classe touchée. -/
lemma not_mem_merged_of_keep {P : List (List Nat)} {C : List Nat} {x y z : Nat}
    (hP : ClassesDisjoint P)
    (hC : C ∈ P) (hkeep : (C.contains x || C.contains y) ≠ true) :
    z ∈ C → z ∉ (P.filter (fun D => D.contains x || D.contains y)).flatten.eraseDups := by
  intro hz hmem
  rw [List.mem_eraseDups, List.mem_flatten] at hmem
  obtain ⟨D, hD, hzD⟩ := hmem
  rw [List.mem_filter] at hD
  obtain ⟨hDP, hDhit⟩ := hD
  have hne : C ≠ D := by
    intro heq; subst heq; exact hkeep hDhit
  exact hP C hC D hDP hne z hz hzD

/-- `mergePair` préserve la disjonction des classes. -/
lemma classesDisjoint_mergePair {P : List (List Nat)} {x y : Nat}
    (hP : ClassesDisjoint P) : ClassesDisjoint (mergePair P x y) := by
  intro C hC D hD hne z hzC hzD
  rw [mergePair_eq, List.mem_append] at hC hD
  rcases hC with hC | hC <;> rcases hD with hD | hD
  · rw [List.mem_filter] at hC hD
    exact hP C hC.1 D hD.1 hne z hzC hzD
  · rw [List.mem_filter] at hC
    rw [List.mem_singleton] at hD
    subst hD
    refine not_mem_merged_of_keep hP hC.1 ?_ hzC hzD
    cases hA : C.contains x <;> cases hB : C.contains y <;> simp_all
  · rw [List.mem_filter] at hD
    rw [List.mem_singleton] at hC
    subst hC
    refine not_mem_merged_of_keep hP hD.1 ?_ hzD hzC
    cases hA : D.contains x <;> cases hB : D.contains y <;> simp_all
  · rw [List.mem_singleton] at hC hD
    exact hne (hC.trans hD.symm)

/-- La disjonction des classes survit au repli complet. -/
lemma classesDisjoint_foldl {pairs : List (Nat × Nat)} {P : List (List Nat)}
    (h : ClassesDisjoint P) : ClassesDisjoint (pairs.foldl mergeStep P) := by
  induction pairs generalizing P with
  | nil => exact h
  | cons p ps ih => rw [List.foldl_cons]; exact ih (classesDisjoint_mergePair h)

/-- Les singletons initiaux sont deux à deux distincts. -/
lemma pairwise_singles {n : Nat} :
    ((List.range n).map (fun i => [i + 1])).Pairwise (fun C D => C ≠ D) :=
  List.Pairwise.map (fun i => [i + 1])
    (fun a b h heq => by
      injection heq with h1
      exact h (by omega))
    List.nodup_range

/-- Une étiquette couverte reste dans le bloc fusionné. -/
lemma mem_merged_of_covered {P : List (List Nat)} {x y : Nat} (hx : Covered P x) :
    x ∈ (P.filter (fun C => C.contains x || C.contains y)).flatten.eraseDups := by
  obtain ⟨C, hCP, hx'⟩ := hx
  refine List.mem_eraseDups.mpr (List.mem_flatten.mpr ⟨C, ?_, hx'⟩)
  refine List.mem_filter.mpr ⟨hCP, ?_⟩
  rw [Bool.or_eq_true]
  exact Or.inl (List.contains_iff_mem.mpr hx')

/-- `mergePair` préserve l'absence de doublon : le bloc fusionné, qui porte `x`,
ne peut pas être une classe intacte, qui ne porte pas `x`. -/
lemma pairwise_mergePair {P : List (List Nat)} {x y : Nat}
    (hnd : P.Pairwise (fun C D => C ≠ D)) (hx : Covered P x) :
    (mergePair P x y).Pairwise (fun C D => C ≠ D) := by
  rw [mergePair_eq, List.pairwise_append]
  have hkeep : (P.filter (fun C => !C.contains x && !C.contains y)).Pairwise
      (fun C D => C ≠ D) := List.Pairwise.filter _ hnd
  refine ⟨hkeep, List.pairwise_singleton _ _, ?_⟩
  intro C hC D hDm
  rw [List.mem_filter] at hC
  obtain ⟨hCP, hcond⟩ := hC
  have hfx : C.contains x = false := by
    cases hA : C.contains x <;> cases hB : C.contains y <;> simp_all
  rw [List.mem_singleton] at hDm
  intro heq
  subst heq
  subst hDm
  have h1 : ((P.filter (fun C => C.contains x || C.contains y)).flatten.eraseDups).contains x = true :=
    List.contains_iff_mem.mpr (mem_merged_of_covered hx)
  rw [h1] at hfx
  exact Bool.noConfusion hfx

/-- Les deux invariants de partition traversent le repli complet. -/
lemma foldl_partition_inv {pairs : List (Nat × Nat)} {P : List (List Nat)}
    (hd : ClassesDisjoint P) (hnd : P.Pairwise (fun C D => C ≠ D))
    (hcov : ∀ q ∈ pairs, Covered P q.1 ∧ Covered P q.2) :
    ClassesDisjoint (pairs.foldl mergeStep P) ∧
      (pairs.foldl mergeStep P).Pairwise (fun C D => C ≠ D) := by
  induction pairs generalizing P with
  | nil => exact ⟨hd, hnd⟩
  | cons p ps ih =>
      rw [List.foldl_cons]
      refine ih (classesDisjoint_mergePair hd)
        (pairwise_mergePair hnd (hcov p (List.mem_cons_self ..)).1) ?_
      intro q hq
      have hc := hcov q (List.mem_cons_of_mem _ hq)
      exact ⟨covered_mergePair hc.1, covered_mergePair hc.2⟩

/-- La couverture d'une étiquette survit au repli complet. -/
lemma covered_foldl {pairs : List (Nat × Nat)} {P : List (List Nat)} {z : Nat}
    (h : Covered P z) : Covered (pairs.foldl mergeStep P) z := by
  induction pairs generalizing P with
  | nil => exact h
  | cons p ps ih => rw [List.foldl_cons]; exact ih (covered_mergePair h)

/-- Une liste deux-à-deux distincte dont tous les éléments valent `a` est de
longueur au plus un. -/
lemma pairwise_all_eq_length_le_one {α : Type} {l : List α} {a : α}
    (hnd : l.Pairwise (fun x y => x ≠ y)) (hall : ∀ x ∈ l, x = a) : l.length ≤ 1 := by
  cases l with
  | nil => simp
  | cons b t =>
      cases t with
      | nil => simp
      | cons c t' =>
          exfalso
          have hbc : b = c := (hall b (by simp)).trans (hall c (by simp)).symm
          cases hnd with
          | cons hhead _ => exact absurd hbc (hhead c (by simp))

/-- Pont `countP`/`filter`, autonome. -/
lemma countP_length_filter {α : Type} {p : α → Bool} (l : List α) :
    l.countP p = (l.filter p).length := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      by_cases h : p a = true
      · simp [h, ih]
      · simp [h, ih]

/-- **Unicité sous-strand** : dans une partition sans doublon, une étiquette
couverte appartient à exactement une classe. -/
lemma countP_contains_eq_one {P : List (List Nat)} {z : Nat}
    (hd : ClassesDisjoint P) (hnd : P.Pairwise (fun C D => C ≠ D)) (hcov : Covered P z) :
    P.countP (fun C => C.contains z) = 1 := by
  obtain ⟨C₀, hC₀P, hz₀⟩ := hcov
  have hfC₀ : C₀ ∈ P.filter (fun C => C.contains z) :=
    List.mem_filter.mpr ⟨hC₀P, List.contains_iff_mem.mpr hz₀⟩
  have hall : ∀ D ∈ P.filter (fun C => C.contains z), D = C₀ := by
    intro D hD
    rw [List.mem_filter] at hD
    obtain ⟨hDP, hzD⟩ := hD
    rw [List.contains_iff_mem] at hzD
    by_contra hne
    exact hd C₀ hC₀P D hDP (Ne.symm hne) z hz₀ hzD
  have hndf : (P.filter (fun C => C.contains z)).Pairwise (fun C D => C ≠ D) :=
    List.Pairwise.filter _ hnd
  have hge : 0 < (P.filter (fun C => C.contains z)).length := List.length_pos_of_mem hfC₀
  have hle : (P.filter (fun C => C.contains z)).length ≤ 1 :=
    pairwise_all_eq_length_le_one hndf hall
  rw [countP_length_filter]
  omega

/-- **Unicité over-strand** : si `x` et `y` partagent une classe d'une partition
sans doublon, exactement une classe porte `x` ou `y`. -/
lemma countP_over_eq_one {P : List (List Nat)} {x y : Nat}
    (hd : ClassesDisjoint P) (hnd : P.Pairwise (fun C D => C ≠ D)) (hsc : SameClass P x y) :
    P.countP (fun C => C.contains x || C.contains y) = 1 := by
  obtain ⟨C₀, hC₀P, hx₀, hy₀⟩ := hsc
  have hfC₀ : C₀ ∈ P.filter (fun C => C.contains x || C.contains y) := by
    refine List.mem_filter.mpr ⟨hC₀P, ?_⟩
    rw [Bool.or_eq_true]
    exact Or.inl (List.contains_iff_mem.mpr hx₀)
  have hall : ∀ D ∈ P.filter (fun C => C.contains x || C.contains y), D = C₀ := by
    intro D hD
    rw [List.mem_filter] at hD
    obtain ⟨hDP, horD⟩ := hD
    rw [Bool.or_eq_true] at horD
    rcases horD with hxD | hyD
    · rw [List.contains_iff_mem] at hxD
      by_contra hne
      exact hd C₀ hC₀P D hDP (Ne.symm hne) x hx₀ hxD
    · rw [List.contains_iff_mem] at hyD
      by_contra hne
      exact hd C₀ hC₀P D hDP (Ne.symm hne) y hy₀ hyD
  have hndf : (P.filter (fun C => C.contains x || C.contains y)).Pairwise
      (fun C D => C ≠ D) := List.Pairwise.filter _ hnd
  have hge : 0 < (P.filter (fun C => C.contains x || C.contains y)).length :=
    List.length_pos_of_mem hfC₀
  have hle : (P.filter (fun C => C.contains x || C.contains y)).length ≤ 1 :=
    pairwise_all_eq_length_le_one hndf hall
  rw [countP_length_filter]
  omega

/-- Chaque paire du repli est couverte par les singletons initiaux. -/
lemma crossings_covered_singles {d : KnotDiagram} (h : EdgesInRange d) :
    ∀ q ∈ d.crossings.map (fun c => (c.e2, c.e4)),
      Covered ((List.range d.numEdges).map (fun i => [i + 1])) q.1 ∧
      Covered ((List.range d.numEdges).map (fun i => [i + 1])) q.2 := by
  intro q hq
  rw [List.mem_map] at hq
  obtain ⟨c', hc', rfl⟩ := hq
  obtain ⟨_, _, h2lo, h2hi, _, _, h4lo, h4hi⟩ := h c' hc'
  exact ⟨covered_singles h2lo h2hi, covered_singles h4lo h4hi⟩

/-- Toute étiquette de la plage `1..numEdges` est couverte par la partition. -/
lemma arcPartition_covered {d : KnotDiagram} {z : Nat}
    (hz1 : 1 ≤ z) (hz2 : z ≤ d.numEdges) :
    Covered (arcPartition d) z := by
  rw [arcPartition_eq]
  exact covered_foldl (covered_singles hz1 hz2)

/-- **`arcPartition` est une partition** : classes disjointes, sans doublon. -/
theorem arcPartition_classes (d : KnotDiagram) (h : EdgesInRange d) :
    ClassesDisjoint (arcPartition d) ∧
      (arcPartition d).Pairwise (fun C D => C ≠ D) := by
  rw [arcPartition_eq]
  exact foldl_partition_inv classesDisjoint_singles pairwise_singles
    (crossings_covered_singles h)

/-- **L'hypothèse `h1`/`h3` est un théorème** : chaque étiquette de la plage
est portée par exactement une classe de `arcPartition`. -/
theorem arcPartition_countP_label (d : KnotDiagram) (h : EdgesInRange d) {z : Nat}
    (hz1 : 1 ≤ z) (hz2 : z ≤ d.numEdges) :
    (arcPartition d).countP (fun C => C.contains z) = 1 := by
  obtain ⟨hd, hnd⟩ := arcPartition_classes d h
  exact countP_contains_eq_one hd hnd (arcPartition_covered hz1 hz2)

/-- **Somme de ligne inconditionnelle** : pour tout diagramme à étiquettes en
plage, chaque ligne de la matrice d'Alexander somme à zéro — la boucle entre
le fait de Fox et la somme nulle se referme, sans hypothèse d'unicité restée
à la main du lecteur. -/
theorem alexanderRow_sum_zero (d : KnotDiagram) (h : EdgesInRange d)
    {c : PDCrossing} (hc : c ∈ d.crossings) :
    ((arcPartition d).map (alexanderEntry c)).sum = 0 := by
  obtain ⟨h1lo, h1hi, _, _, h3lo, h3hi, _, _⟩ := h c hc
  exact alexanderEntry_sum_zero (arcPartition d) c
    (arcPartition_countP_label d h h1lo h1hi)
    (arcPartition_countP_label d h h3lo h3hi)
    (countP_over_eq_one (arcPartition_classes d h).1 (arcPartition_classes d h).2
      (arcPartition_sameClass_overStrand d h hc))

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
  match d.crossings, arcs with
  | [], _ => 1
  | _ :: rest, arcs' =>
      if arcs'.length = rest.length + 1 then
        (Matrix.of fun (i j : Fin rest.length) =>
          alexanderEntry ((rest[i.1]?).getD ⟨1, 1, 1, 1⟩) ((arcs'[j.1]?).getD [])).det
      else 0

/-- Polynôme d'Alexander du nœud, lu sur son diagramme désigné.
Référence : Alexander (1928), Topological invariants of knots and links.

NOTE (normalisation vs consommateurs) : les théorèmes `conway_trivial_alexander`
et `KT_trivial_alexander` ci-dessous portent le contenu classique `Δ = 1`.
Sous la normalisation désignée, le mineur du diagramme vaut une **unité**
`±t^k` (unité fois 1). L'arbitrage différé par la note d'origine est tranché :
le calcul (sonde Python fidèle à la construction, codes census corrigés §2-§3)
donne −t⁶ pour 11n34 et t⁵ pour 11n42 — les énoncés portent désormais la
valeur désignée exacte, une unité étant l'incarnation normalisée de Δ = 1.
Les preuves (déterminant kernel 10×10 sur ℤ[t]) restent `sorry`, sur des
énoncés désormais vrais. -/
noncomputable def alexanderPolynomial (k : Knot) : AlexanderPoly := alexanderPolynomialAux k.diagram

/-! #### Contrôles : la définition discrimine

Une définition qui n'attraperait ni le nœud trivial ni le trèfle serait un
`True` déguisé et le retrait du `sorry` serait cosmétique (même discipline
que les contrôles de `AreMutants`, §1) :

- NÉGATIF (`alexander_unknot`, prouvé) : le nœud trivial, sans croisement,
  donne la valeur classique Δ = 1 — et toute valeur non triviale d'un nœud
  à croisements le distingue du nœud trivial.
- POSITIF (`alexander_trefoil`, prouvé) : le trèfle retrouve exactement la
  valeur classique Δ(t) = t² − t + 1 sous la normalisation désignée
  (mineur [[−1, 1−t], [t, −1]]).
-/

/-- Contrôle négatif : le nœud trivial a un polynôme d'Alexander trivial
(matrice vide, déterminant 1). -/
theorem alexander_unknot : alexanderPolynomial unknot = 1 := by
  simp (config := { decide := true })
    [alexanderPolynomial, alexanderPolynomialAux, unknot, unknotDiagram]

/-- Déterminant 2×2 générique (cas particulier de l'expansion de Laplace :
Mathlib v4.32.1 ne fournit plus `Matrix.det_two`). -/
theorem det_two_aux (M : Matrix (Fin 2) (Fin 2) (Polynomial ℤ)) :
    M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := by
  rw [Matrix.det_succ_column_zero]
  simp [Matrix.det_unique, Fin.sum_univ_two]
  ring

/-- Déterminant 3×3 générique (même esprit que `det_two_aux` : expansion de
Laplace le long de la première colonne, les mineurs 2×2 étant traités par
`det_two_aux`). -/
theorem det_three_aux (A : Matrix (Fin 3) (Fin 3) (Polynomial ℤ)) :
    A.det = A 0 0 * (A 1 1 * A 2 2 - A 1 2 * A 2 1)
          - A 1 0 * (A 0 1 * A 2 2 - A 0 2 * A 2 1)
          + A 2 0 * (A 0 1 * A 1 2 - A 0 2 * A 1 1) := by
  rw [Matrix.det_succ_column_zero]
  simp (config := { decide := true }) [Fin.sum_univ_succ]
  simp (config := { decide := true }) [det_two_aux, Matrix.submatrix_apply, Fin.succAbove]
  ring

/-- Contrôle positif : le trèfle retrouve la valeur classique t² − t + 1
sous la normalisation désignée (mineur sans première ligne ni dernière
colonne). -/
theorem alexander_trefoil :
    alexanderPolynomial trefoil = Polynomial.X ^ 2 - Polynomial.X + 1 := by
  have hp : arcPartition trefoilDiagram = [[4, 5], [1, 6], [2, 3]] := by
    decide
  simp only [alexanderPolynomial, alexanderPolynomialAux, trefoil, hp]
  simp only [trefoilDiagram]
  simp (config := { decide := true })
  rw [det_two_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntry]
  ring

/-- Corollaire de discrimination : le polynôme d'Alexander distingue le
trèfle du nœud trivial — première non-trivialité du développement, obtenue
en combinant les deux contrôles ci-dessus (c'est la propriété qui vend
l'invariant : une valeur non constante sur les classes de nœuds). -/
theorem trefoil_ne_unknot_alexander :
    alexanderPolynomial trefoil ≠ alexanderPolynomial unknot := by
  rw [alexander_trefoil, alexander_unknot]
  intro h
  have h2 := congrArg (fun p : Polynomial ℤ => p.coeff 2) h
  simp [Polynomial.coeff_X] at h2

/-- Invariance sous mutation : le mutant du trèfle (fenêtre pleine, r12) a le
même polynôme d'Alexander que le trèfle — le polynôme d'Alexander est
invariant par mutation (Conway 1970), et le trèfle étant amphichiral, son
mutant reste un trèfle. -/
theorem alexander_trefoilMutant :
    alexanderPolynomial trefoilMutant = Polynomial.X ^ 2 - Polynomial.X + 1 := by
  have hp : arcPartition trefoilMutantDiagram = [[1, 2], [3, 4], [5, 6]] := by
    decide
  simp only [alexanderPolynomial, alexanderPolynomialAux, trefoilMutant, hp]
  dsimp [trefoilMutantDiagram, mutateWindow, KleinRot.apply, trefoilDiagram]
  simp (config := { decide := true })
  rw [det_two_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntry]
  ring

/-- Contrôle de discrimination sur le nœud en huit (4_1) : sous la
normalisation désignée (mineur sans première ligne ni dernière colonne), la
fonction rend −2·t² + 2·t − 1 sur le câblage brut corrigé.

Remarque d'honnêteté : cette valeur n'est PAS le polynôme d'Alexander
classique de 4_1 (qui vaut ±t² ∓ 3·t ± 1, soit t² − 3·t + 1 à un facteur
unité près) ; le théorème mesure la valeur réellement produite par la
fonction désignée sur un câblage à 4 croisements qui forme une boucle
unique. Le trèfle (t² − t + 1) et le déterminant |P(−1)| = 5 = det(4_1)
sont bien reproduits, mais la forme du polynôme diverge du classique sur la
classe à 4 croisements — anomalie documentée exhaustivement (2736 câblages
orientés testés, dont le câblage DT [4,6,8,2]) dans l'issue de suivi ouverte
avec ce PR. La divergence est formalisée ci-dessous
(`alexander_figureEight_not_classical` : pas une unité) et réparée par la
variante signée (`alexander_figureEight_signed` : le classique exact).
-/
theorem alexander_figureEight :
    alexanderPolynomial figureEight =
      - (2 : Polynomial ℤ) * Polynomial.X ^ 2 + 2 * Polynomial.X - 1 := by
  have hp : arcPartition figureEightDiagram = [[3, 4], [5, 6], [7, 8], [1, 2]] := by
    decide
  simp only [alexanderPolynomial, alexanderPolynomialAux, figureEight, hp]
  simp only [figureEightDiagram]
  simp (config := { decide := true })
  rw [det_three_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntry]
  ring

/-! #### Divergence de la classe 4 croisements — diagnostic et variante signée

Diagnostic de l'anomalie #14962 : la ligne `alexanderEntry` est la ligne de
Fox d'un croisement **positif** (dérivée de la relation de Wirtinger
`x_o x_i x_o⁻¹ = x_out`, abélianisée). Le code PD ne codant pas la chiralité,
la matrice non signée traite chaque croisement comme positif. Sur un
diagramme tout positif — le trèfle `3_1` de `Basic.lean`, dont les trois
croisements sont documentés positifs — la matrice EST la matrice d'Alexander
et le mineur désigné retrouve le classique. Sur le nœud en huit `4_1`
(amphichiral, deux croisements de chaque signe dans tout diagramme alterné
minimal), la matrice est fausse sur les croisements négatifs : le mineur
rend `−2t² + 2t − 1`, hors de la classe d'unités du classique `t² − 3t + 1`
(ci-dessous `alexander_figureEight_not_classical`) — la divergence n'est
donc PAS un artefact de représentant (une symétrisation ou une normalisation
de Conway `Δ(1) = 1` ne peut pas la réparer), mais un artefact de chiralité.
Le déterminant, lui, survit : `|P(−1)| = 5 = det(4_1)`
(`alexander_figureEight_eval_neg_one`).

La variante signée `alexanderPolynomialSigned` reçoit la chiralité en
donnée et restitue le classique sur le huit : l'étiquetage alterné du
diagramme DT-dérivé rend exactement `t² − 3t + 1`, son miroir
`t · (t² − 3t + 1)` — même classe d'unités, comme l'exige l'amphichiralité. -/

/-- Ligne d'Alexander d'un croisement **négatif** : dérivée de Fox de la
relation de Wirtinger miroir `x_o⁻¹ x_i x_o = x_out`, multipliée par
l'unité `t` pour rester polynomiale — `+1` sur l'arc entrant du dessous,
`−t` sur l'arc sortant du dessous, `t−1` sur l'arc du dessus. Chaque ligne
somme à zéro, comme pour `alexanderEntry`. -/
noncomputable def alexanderEntryNeg (c : PDCrossing) (C : List Nat) : Polynomial ℤ :=
  (if C.contains c.e1 then 1 else 0)
    + (if C.contains c.e3 then -Polynomial.X else 0)
    + (if C.contains c.e2 || C.contains c.e4 then Polynomial.X - 1 else 0)

/-- Ligne d'Alexander signée : `true` (croisement positif) → `alexanderEntry`,
`false` (croisement négatif) → `alexanderEntryNeg`. -/
noncomputable def alexanderEntrySigned (c : PDCrossing) (s : Bool)
    (C : List Nat) : Polynomial ℤ :=
  if s then alexanderEntry c C else alexanderEntryNeg c C

/-- Polynôme d'Alexander signé d'un diagramme : même mineur désigné que
`alexanderPolynomialAux`, chaque croisement portant son signe (liste des
signes parallèle aux croisements ; le signe du premier croisement est
inutilisé — sa ligne est éliminée par le mineur, `getD true` neutre). -/
noncomputable def alexanderPolynomialSigned (d : KnotDiagram)
    (signs : List Bool) : AlexanderPoly :=
  let arcs := arcPartition d
  match d.crossings, arcs with
  | [], _ => 1
  | _ :: rest, arcs' =>
      if arcs'.length = rest.length + 1 then
        (Matrix.of fun (i j : Fin rest.length) =>
          alexanderEntrySigned ((rest[i.1]?).getD ⟨1, 1, 1, 1⟩)
            ((signs[i.1 + 1]?).getD true) ((arcs'[j.1]?).getD [])).det
      else 0

/-- La divergence n'est pas une unité : la valeur désignée sur le nœud en
huit n'est égale à `ε · t^k · (t² − 3t + 1)` pour AUCUNE unité `ε = ±1` et
aucun exposant `k`. Preuve par évaluations : en `0`, la valeur désignée rend
`−1` ce qui force `k = 0` puis `ε = −1` ; en `2`, elle rend `−5` alors que
`ε · 2^k · (2² − 3·2 + 1)` vaut alors `1`. -/
theorem alexander_figureEight_not_classical :
    ¬ ∃ (k : ℕ) (ε : ℤ), ε * ε = 1 ∧
      alexanderPolynomial figureEight =
        Polynomial.C ε * Polynomial.X ^ k * (Polynomial.X ^ 2 - 3 * Polynomial.X + 1) := by
  rintro ⟨k, ε, -, h⟩
  rcases k with _ | k
  · have h0 := congrArg (Polynomial.eval 0) h
    have h2 := congrArg (Polynomial.eval 2) h
    rw [alexander_figureEight, pow_zero] at h0 h2
    simp only [Polynomial.eval_one, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X, pow_two, mul_one,
      mul_zero, add_zero, zero_add, zero_sub] at h0 h2
    norm_num at h0 h2
    omega
  · have h0 := congrArg (Polynomial.eval 0) h
    rw [alexander_figureEight, pow_succ] at h0
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_C, Polynomial.eval_X, pow_two, mul_assoc, mul_zero, zero_mul,
      mul_one, add_zero, zero_add, zero_sub] at h0
    norm_num at h0

/-- Le déterminant du nœud survit à la divergence : la valeur désignée en
`−1` vaut `−5`, donc `|P(−1)| = 5 = det(4_1)` (classique : pour un nœud,
`det = |Δ(−1)|` ; `4_1` est amphichiral). Le mineur non signé perd la forme
du polynôme mais pas sa valeur en `−1`. -/
theorem alexander_figureEight_eval_neg_one :
    (alexanderPolynomial figureEight).eval (-1) = -5 := by
  rw [alexander_figureEight]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, pow_two, mul_zero, mul_one, add_zero, zero_add, zero_sub]
  norm_num

/-- La variante signée restitue le classique sur le nœud en huit :
l'étiquetage alterné `[−, +, −, +]` du diagramme DT-dérivé rend
exactement `t² − 3t + 1` sous le même mineur désigné, et son miroir
`[+, −, +, −]` rend `t · (t² − 3t + 1)` — même classe d'unités, comme
l'exige l'amphichiralité de `4_1`. -/
theorem alexander_figureEight_signed :
    alexanderPolynomialSigned figureEightDiagram [false, true, false, true]
      = Polynomial.X ^ 2 - 3 * Polynomial.X + 1 := by
  simp only [alexanderPolynomialSigned, figureEightDiagram]
  simp (config := { decide := true })
  rw [det_three_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntrySigned, alexanderEntry, alexanderEntryNeg]
  ring

/-- Miroir du précédent : l'étiquetage alterné opposé `[+, −, +, −]` rend
`t · (t² − 3t + 1)` — même classe d'unités, comme l'exige l'amphichiralité
(les deux diagrammes miroirs représentent le même nœud). -/
theorem alexander_figureEight_signed_mirror :
    alexanderPolynomialSigned figureEightDiagram [true, false, true, false]
      = Polynomial.X * (Polynomial.X ^ 2 - 3 * Polynomial.X + 1) := by
  simp only [alexanderPolynomialSigned, figureEightDiagram]
  simp (config := { decide := true })
  rw [det_three_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntrySigned, alexanderEntry, alexanderEntryNeg]
  ring

/-- Polynôme d'Alexander trivial du nœud de Conway — contenu classique
Δ(t) = 1 ; sous la normalisation désignée, le mineur vaut l'unité −t⁶
(arbitrage de la note de §4 tranché : valeur désignée exacte). -/
theorem conway_trivial_alexander :
    alexanderPolynomial conwayKnot = -(Polynomial.X ^ 6) := by
  exact sorry
  -- Target verified externally (census PD code spherogram 2.4.1, rotation
  -- (e2,e4)=over-strand; probe validated on 3_1/4_1/5_1): minor = -t^6, a unit.
  -- Proof: kernel determinant of the 10x10 sparse matrix over Z[t] -- follow-up tranche.

/-- Polynôme d'Alexander trivial du nœud de Kinoshita-Terasaka — contenu
classique Δ(t) = 1 ; sous la normalisation désignée, le mineur vaut
l'unité t⁵. -/
theorem KT_trivial_alexander :
    alexanderPolynomial kinoshitaTerasakaKnot = Polynomial.X ^ 5 := by
  exact sorry
  -- Target verified externally (same probe): minor = t^5, a unit.
  -- Proof: kernel determinant 10x10 -- follow-up tranche.

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

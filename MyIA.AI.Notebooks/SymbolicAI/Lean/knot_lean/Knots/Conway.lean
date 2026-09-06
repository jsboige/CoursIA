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
`conway_trivial_alexander` est prouvé ci-dessous (déterminant kernel 10×10 sur
ℤ[t] : élimination de Gauss déterministe plus une étape composite au coin
k=8, le coin n'étant pas éliminable par transvections seules — voir le corps
de la preuve) ; seul `KT_trivial_alexander` (t⁵ pour 11n42) reste `sorry`. -/
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 32000000 in
/-- Polynôme d'Alexander trivial du nœud de Conway — contenu classique
Δ(t) = 1 ; sous la normalisation désignée, le mineur vaut l'unité −t⁶
(arbitrage de la note de §4 tranché : valeur désignée exacte). -/
theorem conway_trivial_alexander :
    alexanderPolynomial conwayKnot = -(Polynomial.X ^ 6) := by
  have hp := conway_arcPartition
  simp only [alexanderPolynomial, alexanderPolynomialAux, conwayKnot, hp]
  simp only [conwayKnotDiagram]
  have hlen : ([[13], [22], [3, 4], [1, 2], [5, 6], [9, 7, 8], [20, 21],
      [10, 11, 12], [18, 19], [14, 15], [16, 17]] : List (List Nat)).length =
      ([⟨7, 2, 6, 1⟩, ⟨3, 8, 2, 7⟩, ⟨4, 12, 5, 11⟩, ⟨12, 6, 13, 5⟩,
      ⟨16, 9, 15, 8⟩, ⟨9, 21, 10, 20⟩, ⟨17, 11, 18, 10⟩,
      ⟨13, 19, 14, 18⟩, ⟨19, 15, 20, 14⟩, ⟨22, 17, 21, 16⟩] : List PDCrossing).length + 1 := by
    decide
  rw [if_pos hlen]
  show (Matrix.of fun (i j : Fin 10) => alexanderEntry
        ([⟨7, 2, 6, 1⟩, ⟨3, 8, 2, 7⟩, ⟨4, 12, 5, 11⟩, ⟨12, 6, 13, 5⟩,
      ⟨16, 9, 15, 8⟩, ⟨9, 21, 10, 20⟩, ⟨17, 11, 18, 10⟩,
      ⟨13, 19, 14, 18⟩, ⟨19, 15, 20, 14⟩, ⟨22, 17, 21, 16⟩][i.1]?.getD ⟨1, 1, 1, 1⟩)
        ([[13], [22], [3, 4], [1, 2], [5, 6], [9, 7, 8], [20, 21],
      [10, 11, 12], [18, 19], [14, 15], [16, 17]][j.1]?.getD [])).det = -(Polynomial.X ^ 6)
  set A0 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h0
  have hM0 : (Matrix.of fun (i j : Fin 10) => alexanderEntry
        ([⟨7, 2, 6, 1⟩, ⟨3, 8, 2, 7⟩, ⟨4, 12, 5, 11⟩, ⟨12, 6, 13, 5⟩,
      ⟨16, 9, 15, 8⟩, ⟨9, 21, 10, 20⟩, ⟨17, 11, 18, 10⟩,
      ⟨13, 19, 14, 18⟩, ⟨19, 15, 20, 14⟩, ⟨22, 17, 21, 16⟩][i.1]?.getD ⟨1, 1, 1, 1⟩)
        ([[13], [22], [3, 4], [1, 2], [5, 6], [9, 7, 8], [20, 21],
      [10, 11, 12], [18, 19], [14, 15], [16, 17]][j.1]?.getD [])) = A0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp (config := { decide := true }) [Matrix.of_apply,
        alexanderEntry, h0] <;>
      first
      | rfl
      | ring
  rw [hM0]
  set A1 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h1
  have e1 : A1 = A0.updateRow 7 (A0 7 + ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ) • A0 3) := by
    rw [h1, h0]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d1 : A1.det = A0.det := by
    rw [e1, Matrix.det_updateRow_add_smul_self A0 (by decide : ((7 : Fin 10) ≠ 3)) ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  set A2 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h2
  have e2 : A2 = A1.updateRow 3 (A1 3 + (1 : Polynomial ℤ) • A1 0) := by
    rw [h2, h1]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d2 : A2.det = A1.det := by
    rw [e2, Matrix.det_updateRow_add_smul_self A1 (by decide : ((3 : Fin 10) ≠ 0)) (1 : Polynomial ℤ)]
  set A3 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h3
  have e3 : A3 = A2.updateRow 0 (A2 0 + (-1 : Polynomial ℤ) • A2 3) := by
    rw [h3, h2]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d3 : A3.det = A2.det := by
    rw [e3, Matrix.det_updateRow_add_smul_self A2 (by decide : ((0 : Fin 10) ≠ 3)) (-1 : Polynomial ℤ)]
  set A4 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h4
  have e4 : A4 = A3.updateRow 3 (A3 3 + (1 : Polynomial ℤ) • A3 0) := by
    rw [h4, h3]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d4 : A4.det = A3.det := by
    rw [e4, Matrix.det_updateRow_add_smul_self A3 (by decide : ((3 : Fin 10) ≠ 0)) (1 : Polynomial ℤ)]
  set A5 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h5
  have e5 : A5 = A4.updateRow 3 (A4 3 + ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A4 1) := by
    rw [h5, h4]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d5 : A5.det = A4.det := by
    rw [e5, Matrix.det_updateRow_add_smul_self A4 (by decide : ((3 : Fin 10) ≠ 1)) ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A6 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h6
  have e6 : A6 = A5.updateCol 3 (fun r => A5 r 3 + (1 : Polynomial ℤ) • A5 r 1) := by
    rw [h6, h5]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d6 : A6.det = A5.det := by
    rw [e6, Matrix.det_updateCol_add_smul_self A5 (by decide : ((3 : Fin 10) ≠ 1)) (1 : Polynomial ℤ)]
  set A7 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h7
  have e7 : A7 = A6.updateCol 1 (fun r => A6 r 1 + (-1 : Polynomial ℤ) • A6 r 3) := by
    rw [h7, h6]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d7 : A7.det = A6.det := by
    rw [e7, Matrix.det_updateCol_add_smul_self A6 (by decide : ((1 : Fin 10) ≠ 3)) (-1 : Polynomial ℤ)]
  set A8 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h8
  have e8 : A8 = A7.updateCol 3 (fun r => A7 r 3 + (1 : Polynomial ℤ) • A7 r 1) := by
    rw [h8, h7]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d8 : A8.det = A7.det := by
    rw [e8, Matrix.det_updateCol_add_smul_self A7 (by decide : ((3 : Fin 10) ≠ 1)) (1 : Polynomial ℤ)]
  set A9 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h9
  have e9 : A9 = A8.updateRow 7 (A8 7 + (-1 : Polynomial ℤ) • A8 4) := by
    rw [h9, h8]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d9 : A9.det = A8.det := by
    rw [e9, Matrix.det_updateRow_add_smul_self A8 (by decide : ((7 : Fin 10) ≠ 4)) (-1 : Polynomial ℤ)]
  set A10 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h10
  have e10 : A10 = A9.updateRow 8 (A9 8 + ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A9 4) := by
    rw [h10, h9]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d10 : A10.det = A9.det := by
    rw [e10, Matrix.det_updateRow_add_smul_self A9 (by decide : ((8 : Fin 10) ≠ 4)) ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A11 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h11
  have e11 : A11 = A10.updateRow 4 (A10 4 + (1 : Polynomial ℤ) • A10 2) := by
    rw [h11, h10]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d11 : A11.det = A10.det := by
    rw [e11, Matrix.det_updateRow_add_smul_self A10 (by decide : ((4 : Fin 10) ≠ 2)) (1 : Polynomial ℤ)]
  set A12 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h12
  have e12 : A12 = A11.updateRow 2 (A11 2 + (-1 : Polynomial ℤ) • A11 4) := by
    rw [h12, h11]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d12 : A12.det = A11.det := by
    rw [e12, Matrix.det_updateRow_add_smul_self A11 (by decide : ((2 : Fin 10) ≠ 4)) (-1 : Polynomial ℤ)]
  set A13 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h13
  have e13 : A13 = A12.updateRow 4 (A12 4 + (1 : Polynomial ℤ) • A12 2) := by
    rw [h13, h12]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d13 : A13.det = A12.det := by
    rw [e13, Matrix.det_updateRow_add_smul_self A12 (by decide : ((4 : Fin 10) ≠ 2)) (1 : Polynomial ℤ)]
  set A14 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h14
  have e14 : A14 = A13.updateCol 9 (fun r => A13 r 9 + (1 : Polynomial ℤ) • A13 r 2) := by
    rw [h14, h13]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d14 : A14.det = A13.det := by
    rw [e14, Matrix.det_updateCol_add_smul_self A13 (by decide : ((9 : Fin 10) ≠ 2)) (1 : Polynomial ℤ)]
  set A15 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h15
  have e15 : A15 = A14.updateCol 2 (fun r => A14 r 2 + (-1 : Polynomial ℤ) • A14 r 9) := by
    rw [h15, h14]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d15 : A15.det = A14.det := by
    rw [e15, Matrix.det_updateCol_add_smul_self A14 (by decide : ((2 : Fin 10) ≠ 9)) (-1 : Polynomial ℤ)]
  set A16 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h16
  have e16 : A16 = A15.updateCol 9 (fun r => A15 r 9 + (1 : Polynomial ℤ) • A15 r 2) := by
    rw [h16, h15]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d16 : A16.det = A15.det := by
    rw [e16, Matrix.det_updateCol_add_smul_self A15 (by decide : ((9 : Fin 10) ≠ 2)) (1 : Polynomial ℤ)]
  set A17 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h17
  have e17 : A17 = A16.updateRow 7 (A16 7 + ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A16 6) := by
    rw [h17, h16]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d17 : A17.det = A16.det := by
    rw [e17, Matrix.det_updateRow_add_smul_self A16 (by decide : ((7 : Fin 10) ≠ 6)) ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A18 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h18
  have e18 : A18 = A17.updateRow 8 (A17 8 + ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ) • A17 6) := by
    rw [h18, h17]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d18 : A18.det = A17.det := by
    rw [e18, Matrix.det_updateRow_add_smul_self A17 (by decide : ((8 : Fin 10) ≠ 6)) ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  set A19 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h19
  have e19 : A19 = A18.updateRow 6 (A18 6 + (1 : Polynomial ℤ) • A18 3) := by
    rw [h19, h18]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d19 : A19.det = A18.det := by
    rw [e19, Matrix.det_updateRow_add_smul_self A18 (by decide : ((6 : Fin 10) ≠ 3)) (1 : Polynomial ℤ)]
  set A20 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h20
  have e20 : A20 = A19.updateRow 3 (A19 3 + (-1 : Polynomial ℤ) • A19 6) := by
    rw [h20, h19]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d20 : A20.det = A19.det := by
    rw [e20, Matrix.det_updateRow_add_smul_self A19 (by decide : ((3 : Fin 10) ≠ 6)) (-1 : Polynomial ℤ)]
  set A21 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h21
  have e21 : A21 = A20.updateRow 6 (A20 6 + (1 : Polynomial ℤ) • A20 3) := by
    rw [h21, h20]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d21 : A21.det = A20.det := by
    rw [e21, Matrix.det_updateRow_add_smul_self A20 (by decide : ((6 : Fin 10) ≠ 3)) (1 : Polynomial ℤ)]
  set A22 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h22
  have e22 : A22 = A21.updateCol 8 (fun r => A21 r 8 + (1 : Polynomial ℤ) • A21 r 3) := by
    rw [h22, h21]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d22 : A22.det = A21.det := by
    rw [e22, Matrix.det_updateCol_add_smul_self A21 (by decide : ((8 : Fin 10) ≠ 3)) (1 : Polynomial ℤ)]
  set A23 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h23
  have e23 : A23 = A22.updateCol 3 (fun r => A22 r 3 + (-1 : Polynomial ℤ) • A22 r 8) := by
    rw [h23, h22]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d23 : A23.det = A22.det := by
    rw [e23, Matrix.det_updateCol_add_smul_self A22 (by decide : ((3 : Fin 10) ≠ 8)) (-1 : Polynomial ℤ)]
  set A24 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h24
  have e24 : A24 = A23.updateCol 8 (fun r => A23 r 8 + (1 : Polynomial ℤ) • A23 r 3) := by
    rw [h24, h23]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d24 : A24.det = A23.det := by
    rw [e24, Matrix.det_updateCol_add_smul_self A23 (by decide : ((8 : Fin 10) ≠ 3)) (1 : Polynomial ℤ)]
  set A25 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h25
  have e25 : A25 = A24.updateRow 5 (A24 5 + ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A24 9) := by
    rw [h25, h24]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d25 : A25.det = A24.det := by
    rw [e25, Matrix.det_updateRow_add_smul_self A24 (by decide : ((5 : Fin 10) ≠ 9)) ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A26 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h26
  have e26 : A26 = A25.updateRow 8 (A25 8 + (-1 : Polynomial ℤ) • A25 9) := by
    rw [h26, h25]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d26 : A26.det = A25.det := by
    rw [e26, Matrix.det_updateRow_add_smul_self A25 (by decide : ((8 : Fin 10) ≠ 9)) (-1 : Polynomial ℤ)]
  set A27 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h27
  have e27 : A27 = A26.updateRow 9 (A26 9 + (1 : Polynomial ℤ) • A26 4) := by
    rw [h27, h26]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d27 : A27.det = A26.det := by
    rw [e27, Matrix.det_updateRow_add_smul_self A26 (by decide : ((9 : Fin 10) ≠ 4)) (1 : Polynomial ℤ)]
  set A28 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h28
  have e28 : A28 = A27.updateRow 4 (A27 4 + (-1 : Polynomial ℤ) • A27 9) := by
    rw [h28, h27]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d28 : A28.det = A27.det := by
    rw [e28, Matrix.det_updateRow_add_smul_self A27 (by decide : ((4 : Fin 10) ≠ 9)) (-1 : Polynomial ℤ)]
  set A29 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h29
  have e29 : A29 = A28.updateRow 9 (A28 9 + (1 : Polynomial ℤ) • A28 4) := by
    rw [h29, h28]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d29 : A29.det = A28.det := by
    rw [e29, Matrix.det_updateRow_add_smul_self A28 (by decide : ((9 : Fin 10) ≠ 4)) (1 : Polynomial ℤ)]
  set A30 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h30
  have e30 : A30 = A29.updateCol 6 (fun r => A29 r 6 + (1 : Polynomial ℤ) • A29 r 4) := by
    rw [h30, h29]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d30 : A30.det = A29.det := by
    rw [e30, Matrix.det_updateCol_add_smul_self A29 (by decide : ((6 : Fin 10) ≠ 4)) (1 : Polynomial ℤ)]
  set A31 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h31
  have e31 : A31 = A30.updateCol 4 (fun r => A30 r 4 + (-1 : Polynomial ℤ) • A30 r 6) := by
    rw [h31, h30]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d31 : A31.det = A30.det := by
    rw [e31, Matrix.det_updateCol_add_smul_self A30 (by decide : ((4 : Fin 10) ≠ 6)) (-1 : Polynomial ℤ)]
  set A32 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h32
  have e32 : A32 = A31.updateCol 6 (fun r => A31 r 6 + (1 : Polynomial ℤ) • A31 r 4) := by
    rw [h32, h31]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d32 : A32.det = A31.det := by
    rw [e32, Matrix.det_updateCol_add_smul_self A31 (by decide : ((6 : Fin 10) ≠ 4)) (1 : Polynomial ℤ)]
  set A33 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h33
  have e33 : A33 = A32.updateRow 7 (A32 7 + ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ) • A32 6) := by
    rw [h33, h32]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d33 : A33.det = A32.det := by
    rw [e33, Matrix.det_updateRow_add_smul_self A32 (by decide : ((7 : Fin 10) ≠ 6)) ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)]
  set A34 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h34
  have e34 : A34 = A33.updateRow 9 (A33 9 + (-1 : Polynomial ℤ) • A33 6) := by
    rw [h34, h33]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d34 : A34.det = A33.det := by
    rw [e34, Matrix.det_updateRow_add_smul_self A33 (by decide : ((9 : Fin 10) ≠ 6)) (-1 : Polynomial ℤ)]
  set A35 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h35
  have e35 : A35 = A34.updateRow 6 (A34 6 + (1 : Polynomial ℤ) • A34 5) := by
    rw [h35, h34]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d35 : A35.det = A34.det := by
    rw [e35, Matrix.det_updateRow_add_smul_self A34 (by decide : ((6 : Fin 10) ≠ 5)) (1 : Polynomial ℤ)]
  set A36 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h36
  have e36 : A36 = A35.updateRow 5 (A35 5 + (-1 : Polynomial ℤ) • A35 6) := by
    rw [h36, h35]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d36 : A36.det = A35.det := by
    rw [e36, Matrix.det_updateRow_add_smul_self A35 (by decide : ((5 : Fin 10) ≠ 6)) (-1 : Polynomial ℤ)]
  set A37 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h37
  have e37 : A37 = A36.updateRow 6 (A36 6 + (1 : Polynomial ℤ) • A36 5) := by
    rw [h37, h36]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d37 : A37.det = A36.det := by
    rw [e37, Matrix.det_updateRow_add_smul_self A36 (by decide : ((6 : Fin 10) ≠ 5)) (1 : Polynomial ℤ)]
  set A38 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h38
  have e38 : A38 = A37.updateCol 6 (fun r => A37 r 6 + (1 : Polynomial ℤ) • A37 r 5) := by
    rw [h38, h37]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d38 : A38.det = A37.det := by
    rw [e38, Matrix.det_updateCol_add_smul_self A37 (by decide : ((6 : Fin 10) ≠ 5)) (1 : Polynomial ℤ)]
  set A39 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h39
  have e39 : A39 = A38.updateCol 5 (fun r => A38 r 5 + (-1 : Polynomial ℤ) • A38 r 6) := by
    rw [h39, h38]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d39 : A39.det = A38.det := by
    rw [e39, Matrix.det_updateCol_add_smul_self A38 (by decide : ((5 : Fin 10) ≠ 6)) (-1 : Polynomial ℤ)]
  set A40 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h40
  have e40 : A40 = A39.updateCol 6 (fun r => A39 r 6 + (1 : Polynomial ℤ) • A39 r 5) := by
    rw [h40, h39]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d40 : A40.det = A39.det := by
    rw [e40, Matrix.det_updateCol_add_smul_self A39 (by decide : ((6 : Fin 10) ≠ 5)) (1 : Polynomial ℤ)]
  set A41 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 4 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 3 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - 2 * Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h41
  have e41 : A41 = A40.updateRow 7 (A40 7 + ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ) • A40 6) := by
    rw [h41, h40]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d41 : A41.det = A40.det := by
    rw [e41, Matrix.det_updateRow_add_smul_self A40 (by decide : ((7 : Fin 10) ≠ 6)) ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ)]
  set A42 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 4 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 3 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - 2 * Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h42
  have e42 : A42 = A41.updateRow 8 (A41 8 + ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ) • A41 6) := by
    rw [h42, h41]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d42 : A42.det = A41.det := by
    rw [e42, Matrix.det_updateRow_add_smul_self A41 (by decide : ((8 : Fin 10) ≠ 6)) ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)]
  set A43 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 4 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 3 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - 2 * Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h43
  have e43 : A43 = A42.updateRow 9 (A42 9 + ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A42 6) := by
    rw [h43, h42]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d43 : A43.det = A42.det := by
    rw [e43, Matrix.det_updateRow_add_smul_self A42 (by decide : ((9 : Fin 10) ≠ 6)) ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A44 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 4 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 4 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 3 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - 2 * Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h44
  have e44 : A44 = A43.updateCol 7 (fun r => A43 r 7 + (1 : Polynomial ℤ) • A43 r 6) := by
    rw [h44, h43]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d44 : A44.det = A43.det := by
    rw [e44, Matrix.det_updateCol_add_smul_self A43 (by decide : ((7 : Fin 10) ≠ 6)) (1 : Polynomial ℤ)]
  set A45 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 4 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 3 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - 2 * Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h45
  have e45 : A45 = A44.updateCol 6 (fun r => A44 r 6 + (-1 : Polynomial ℤ) • A44 r 7) := by
    rw [h45, h44]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d45 : A45.det = A44.det := by
    rw [e45, Matrix.det_updateCol_add_smul_self A44 (by decide : ((6 : Fin 10) ≠ 7)) (-1 : Polynomial ℤ)]
  set A46 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 4 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 3 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - 2 * Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h46
  have e46 : A46 = A45.updateCol 7 (fun r => A45 r 7 + (1 : Polynomial ℤ) • A45 r 6) := by
    rw [h46, h45]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d46 : A46.det = A45.det := by
    rw [e46, Matrix.det_updateCol_add_smul_self A45 (by decide : ((7 : Fin 10) ≠ 6)) (1 : Polynomial ℤ)]
  set A47 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 3 * Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + 2 * Polynomial.X ^ 4 - Polynomial.X ^ 5 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h47
  have e47 : A47 = A46.updateRow 7 (A46 7 + ((-1 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ) • A46 9) := by
    rw [h47, h46]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d47 : A47.det = A46.det := by
    rw [e47, Matrix.det_updateRow_add_smul_self A46 (by decide : ((7 : Fin 10) ≠ 9)) ((-1 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)]
  set A48 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 3 * Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + 2 * Polynomial.X ^ 4 - Polynomial.X ^ 5 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 - Polynomial.X ^ 3 + 2 * Polynomial.X ^ 4 - Polynomial.X ^ 5 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h48
  have e48 : A48 = A47.updateRow 9 (A47 9 + (1 : Polynomial ℤ) • A47 7) := by
    rw [h48, h47]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d48 : A48.det = A47.det := by
    rw [e48, Matrix.det_updateRow_add_smul_self A47 (by decide : ((9 : Fin 10) ≠ 7)) (1 : Polynomial ℤ)]
  set A49 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 - Polynomial.X ^ 3 + 2 * Polynomial.X ^ 4 - Polynomial.X ^ 5 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h49
  have e49 : A49 = A48.updateRow 7 (A48 7 + (-1 : Polynomial ℤ) • A48 9) := by
    rw [h49, h48]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d49 : A49.det = A48.det := by
    rw [e49, Matrix.det_updateRow_add_smul_self A48 (by decide : ((7 : Fin 10) ≠ 9)) (-1 : Polynomial ℤ)]
  set A50 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 3 * Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + 2 * Polynomial.X ^ 4 - Polynomial.X ^ 5 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h50
  have e50 : A50 = A49.updateRow 9 (A49 9 + (1 : Polynomial ℤ) • A49 7) := by
    rw [h50, h49]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d50 : A50.det = A49.det := by
    rw [e50, Matrix.det_updateRow_add_smul_self A49 (by decide : ((9 : Fin 10) ≠ 7)) (1 : Polynomial ℤ)]
  set A51 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 3 * Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + 2 * Polynomial.X ^ 4 - Polynomial.X ^ 5 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 3 * Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)]
  ] with h51
  have e51 : A51 = A50.updateCol 9 (fun r => A50 r 9 + (1 : Polynomial ℤ) • A50 r 7) := by
    rw [h51, h50]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d51 : A51.det = A50.det := by
    rw [e51, Matrix.det_updateCol_add_smul_self A50 (by decide : ((9 : Fin 10) ≠ 7)) (1 : Polynomial ℤ)]
  set A52 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + 2 * Polynomial.X ^ 4 - Polynomial.X ^ 5 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 3 * Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)]
  ] with h52
  have e52 : A52 = A51.updateCol 7 (fun r => A51 r 7 + (-1 : Polynomial ℤ) • A51 r 9) := by
    rw [h52, h51]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d52 : A52.det = A51.det := by
    rw [e52, Matrix.det_updateCol_add_smul_self A51 (by decide : ((7 : Fin 10) ≠ 9)) (-1 : Polynomial ℤ)]
  set A53 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + 2 * Polynomial.X ^ 4 - Polynomial.X ^ 5 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 3 * Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)]
  ] with h53
  have e53 : A53 = A52.updateCol 9 (fun r => A52 r 9 + (1 : Polynomial ℤ) • A52 r 7) := by
    rw [h53, h52]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d53 : A53.det = A52.det := by
    rw [e53, Matrix.det_updateCol_add_smul_self A52 (by decide : ((9 : Fin 10) ≠ 7)) (1 : Polynomial ℤ)]
  set A54 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X ^ 3 + 3 * Polynomial.X ^ 4 - 6 * Polynomial.X ^ 5 + 8 * Polynomial.X ^ 6 - 7 * Polynomial.X ^ 7 + 4 * Polynomial.X ^ 8 - Polynomial.X ^ 9 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 - 4 * Polynomial.X ^ 3 + 7 * Polynomial.X ^ 4 - 10 * Polynomial.X ^ 5 + 8 * Polynomial.X ^ 6 - 4 * Polynomial.X ^ 7 + Polynomial.X ^ 8 : Polynomial ℤ)]
  ] with h54
  have e54 : A54 = A53.updateRow 9 (((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ) • A53 9) := by
    rw [h54, h53]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have eself : A53.updateRow 9 (A53 9) = A53 := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> simp [Matrix.updateRow_apply]
  have d54 : A54.det = ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ) * A53.det := by
    rw [e54, Matrix.det_updateRow_smul A53 9 ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ) (A53 9), eself]
  set A55 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X ^ 4 : Polynomial ℤ)]
  ] with h55
  have e55 : A55 = A54.updateRow 9 (A54 9 + ((0 : Polynomial ℤ) - Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 - 2 * Polynomial.X ^ 4 + Polynomial.X ^ 5 : Polynomial ℤ) • A54 8) := by
    rw [h55, h54]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d55 : A55.det = A54.det := by
    rw [e55, Matrix.det_updateRow_add_smul_self A54 (by decide : ((9 : Fin 10) ≠ 8)) ((0 : Polynomial ℤ) - Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 - 2 * Polynomial.X ^ 4 + Polynomial.X ^ 5 : Polynomial ℤ)]
  have hchain : A55.det = ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ) * A0.det := by
    rw [d55, d54, d53, d52, d51, d50, d49, d48, d47, d46, d45, d44, d43, d42, d41, d40, d39, d38, d37, d36, d35, d34, d33, d32, d31, d30, d29, d28, d27, d26, d25, d24, d23, d22, d21, d20, d19, d18, d17, d16, d15, d14, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]
  have hT : A55.BlockTriangular id := by
    intro i j hij
    rw [h55]
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hij (by decide)
      | simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
  have hdiag : (∏ i, A55 i i) = ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ) * ( -(Polynomial.X ^ 6)) := by
    rw [h55]
    simp only [Fin.prod_univ_succ, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.isValue]
    have htail : ∀ g : Fin 0 → Polynomial ℤ, (∏ i, g i) = 1 := fun g =>
      Finset.prod_eq_one (fun x _ => Fin.elim0 x)
    rw [htail _]
    ring
  have ha : ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ) ≠ 0 := by
    intro hz
    have c1 := congrArg (fun p : Polynomial ℤ => p.coeff 1) hz
    simp [Polynomial.coeff_sub, Polynomial.coeff_add,
      Polynomial.coeff_X_pow] at c1
  have key : ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ) * A0.det = ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ) * (-(Polynomial.X ^ 6)) := by
    rw [← hchain, Matrix.det_of_upperTriangular hT, hdiag]
  exact mul_left_cancel₀ ha key

set_option maxRecDepth 8000 in
set_option maxHeartbeats 32000000 in
/-- Polynôme d'Alexander trivial du nœud de Kinoshita-Terasaka — contenu
classique Δ(t) = 1 ; sous la normalisation désignée, le mineur vaut
l'unité t⁵ (même discipline que `conway_trivial_alexander` : élimination
de Gauss déterministe sur ℤ[t] par transvections uniquement, déterminant
invariant de proche en proche — chaque `d_k` est `det_updateRow_add_smul_self`). -/
theorem KT_trivial_alexander :
    alexanderPolynomial kinoshitaTerasakaKnot = Polynomial.X ^ 5 := by
  have hp := kinoshitaTerasaka_arcPartition
  simp only [alexanderPolynomial, alexanderPolynomialAux, kinoshitaTerasakaKnot, hp]
  simp only [kinoshitaTerasakaDiagram]
  have hlen : ([[13], [22], [3, 4], [1, 2], [5, 6], [9, 7, 8], [14, 15], [10, 11, 12], [18, 19], [20, 21], [16, 17]] : List (List Nat)).length =
      ([⟨7, 2, 6, 1⟩, ⟨3, 8, 2, 7⟩, ⟨4, 12, 5, 11⟩, ⟨12, 6, 13, 5⟩, ⟨17, 9, 18, 8⟩, ⟨9, 15, 10, 14⟩, ⟨20, 11, 19, 10⟩, ⟨14, 19, 13, 18⟩, ⟨15, 21, 16, 20⟩, ⟨21, 17, 22, 16⟩] : List PDCrossing).length + 1 := by
    decide
  rw [if_pos hlen]
  show (Matrix.of fun (i j : Fin 10) => alexanderEntry
        ([⟨7, 2, 6, 1⟩, ⟨3, 8, 2, 7⟩, ⟨4, 12, 5, 11⟩, ⟨12, 6, 13, 5⟩, ⟨17, 9, 18, 8⟩, ⟨9, 15, 10, 14⟩, ⟨20, 11, 19, 10⟩, ⟨14, 19, 13, 18⟩, ⟨15, 21, 16, 20⟩, ⟨21, 17, 22, 16⟩][i.1]?.getD ⟨1, 1, 1, 1⟩)
        ([[13], [22], [3, 4], [1, 2], [5, 6], [9, 7, 8], [14, 15], [10, 11, 12], [18, 19], [20, 21], [16, 17]][j.1]?.getD [])).det = Polynomial.X ^ 5
  set A0 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h0
  have hM0 : (Matrix.of fun (i j : Fin 10) => alexanderEntry
        ([⟨7, 2, 6, 1⟩, ⟨3, 8, 2, 7⟩, ⟨4, 12, 5, 11⟩, ⟨12, 6, 13, 5⟩, ⟨17, 9, 18, 8⟩, ⟨9, 15, 10, 14⟩, ⟨20, 11, 19, 10⟩, ⟨14, 19, 13, 18⟩, ⟨15, 21, 16, 20⟩, ⟨21, 17, 22, 16⟩][i.1]?.getD ⟨1, 1, 1, 1⟩)
        ([[13], [22], [3, 4], [1, 2], [5, 6], [9, 7, 8], [14, 15], [10, 11, 12], [18, 19], [20, 21], [16, 17]][j.1]?.getD [])) = A0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp (config := { decide := true }) [Matrix.of_apply,
        alexanderEntry, h0] <;>
      first
      | rfl
      | ring
  rw [hM0]
  set A1 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h1
  have e1 : A1 = A0.updateRow 0 (A0 0 + ((1 : Polynomial ℤ) : Polynomial ℤ) • A0 3) := by
    rw [h1, h0]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d1 : A1.det = A0.det := by
    rw [e1, Matrix.det_updateRow_add_smul_self A0 (by decide : ((0 : Fin 10) ≠ 3)) ((1 : Polynomial ℤ) : Polynomial ℤ)]
  set A2 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h2
  have e2 : A2 = A1.updateRow 3 (A1 3 + ((-1 : Polynomial ℤ) : Polynomial ℤ) • A1 0) := by
    rw [h2, h1]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d2 : A2.det = A1.det := by
    rw [e2, Matrix.det_updateRow_add_smul_self A1 (by decide : ((3 : Fin 10) ≠ 0)) ((-1 : Polynomial ℤ) : Polynomial ℤ)]
  set A3 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h3
  have e3 : A3 = A2.updateRow 7 (A2 7 + ((-1 : Polynomial ℤ) : Polynomial ℤ) • A2 0) := by
    rw [h3, h2]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d3 : A3.det = A2.det := by
    rw [e3, Matrix.det_updateRow_add_smul_self A2 (by decide : ((7 : Fin 10) ≠ 0)) ((-1 : Polynomial ℤ) : Polynomial ℤ)]
  set A4 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h4
  have e4 : A4 = A3.updateRow 1 (A3 1 + ((1 : Polynomial ℤ) : Polynomial ℤ) • A3 9) := by
    rw [h4, h3]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d4 : A4.det = A3.det := by
    rw [e4, Matrix.det_updateRow_add_smul_self A3 (by decide : ((1 : Fin 10) ≠ 9)) ((1 : Polynomial ℤ) : Polynomial ℤ)]
  set A5 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h5
  have e5 : A5 = A4.updateRow 9 (A4 9 + ((-1 : Polynomial ℤ) : Polynomial ℤ) • A4 1) := by
    rw [h5, h4]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d5 : A5.det = A4.det := by
    rw [e5, Matrix.det_updateRow_add_smul_self A4 (by decide : ((9 : Fin 10) ≠ 1)) ((-1 : Polynomial ℤ) : Polynomial ℤ)]
  set A6 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h6
  have e6 : A6 = A5.updateRow 9 (A5 9 + ((1 : Polynomial ℤ) : Polynomial ℤ) • A5 2) := by
    rw [h6, h5]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d6 : A6.det = A5.det := by
    rw [e6, Matrix.det_updateRow_add_smul_self A5 (by decide : ((9 : Fin 10) ≠ 2)) ((1 : Polynomial ℤ) : Polynomial ℤ)]
  set A7 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h7
  have e7 : A7 = A6.updateRow 7 (A6 7 + ((-1 : Polynomial ℤ) : Polynomial ℤ) • A6 3) := by
    rw [h7, h6]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d7 : A7.det = A6.det := by
    rw [e7, Matrix.det_updateRow_add_smul_self A6 (by decide : ((7 : Fin 10) ≠ 3)) ((-1 : Polynomial ℤ) : Polynomial ℤ)]
  set A8 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h8
  have e8 : A8 = A7.updateRow 3 (A7 3 + ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A7 9) := by
    rw [h8, h7]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d8 : A8.det = A7.det := by
    rw [e8, Matrix.det_updateRow_add_smul_self A7 (by decide : ((3 : Fin 10) ≠ 9)) ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A9 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h9
  have e9 : A9 = A8.updateRow 3 (A8 3 + ((1 : Polynomial ℤ) : Polynomial ℤ) • A8 9) := by
    rw [h9, h8]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d9 : A9.det = A8.det := by
    rw [e9, Matrix.det_updateRow_add_smul_self A8 (by decide : ((3 : Fin 10) ≠ 9)) ((1 : Polynomial ℤ) : Polynomial ℤ)]
  set A10 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h10
  have e10 : A10 = A9.updateRow 9 (A9 9 + ((-1 : Polynomial ℤ) : Polynomial ℤ) • A9 3) := by
    rw [h10, h9]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d10 : A10.det = A9.det := by
    rw [e10, Matrix.det_updateRow_add_smul_self A9 (by decide : ((9 : Fin 10) ≠ 3)) ((-1 : Polynomial ℤ) : Polynomial ℤ)]
  set A11 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h11
  have e11 : A11 = A10.updateRow 4 (A10 4 + ((1 : Polynomial ℤ) : Polynomial ℤ) • A10 7) := by
    rw [h11, h10]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d11 : A11.det = A10.det := by
    rw [e11, Matrix.det_updateRow_add_smul_self A10 (by decide : ((4 : Fin 10) ≠ 7)) ((1 : Polynomial ℤ) : Polynomial ℤ)]
  set A12 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h12
  have e12 : A12 = A11.updateRow 7 (A11 7 + ((-1 : Polynomial ℤ) : Polynomial ℤ) • A11 4) := by
    rw [h12, h11]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d12 : A12.det = A11.det := by
    rw [e12, Matrix.det_updateRow_add_smul_self A11 (by decide : ((7 : Fin 10) ≠ 4)) ((-1 : Polynomial ℤ) : Polynomial ℤ)]
  set A13 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h13
  have e13 : A13 = A12.updateRow 4 (A12 4 + ((1 : Polynomial ℤ) : Polynomial ℤ) • A12 9) := by
    rw [h13, h12]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d13 : A13.det = A12.det := by
    rw [e13, Matrix.det_updateRow_add_smul_self A12 (by decide : ((4 : Fin 10) ≠ 9)) ((1 : Polynomial ℤ) : Polynomial ℤ)]
  set A14 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 3 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h14
  have e14 : A14 = A13.updateRow 9 (A13 9 + ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A13 4) := by
    rw [h14, h13]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d14 : A14.det = A13.det := by
    rw [e14, Matrix.det_updateRow_add_smul_self A13 (by decide : ((9 : Fin 10) ≠ 4)) ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A15 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 3 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h15
  have e15 : A15 = A14.updateRow 5 (A14 5 + ((-1 : Polynomial ℤ) : Polynomial ℤ) • A14 7) := by
    rw [h15, h14]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d15 : A15.det = A14.det := by
    rw [e15, Matrix.det_updateRow_add_smul_self A14 (by decide : ((5 : Fin 10) ≠ 7)) ((-1 : Polynomial ℤ) : Polynomial ℤ)]
  set A16 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 3 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h16
  have e16 : A16 = A15.updateRow 7 (A15 7 + ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A15 5) := by
    rw [h16, h15]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d16 : A16.det = A15.det := by
    rw [e16, Matrix.det_updateRow_add_smul_self A15 (by decide : ((7 : Fin 10) ≠ 5)) ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A17 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 4 * Polynomial.X - 7 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 4 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h17
  have e17 : A17 = A16.updateRow 9 (A16 9 + ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 3 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ) • A16 5) := by
    rw [h17, h16]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d17 : A17.det = A16.det := by
    rw [e17, Matrix.det_updateRow_add_smul_self A16 (by decide : ((9 : Fin 10) ≠ 5)) ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 3 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ)]
  set A18 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 4 * Polynomial.X - 7 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 4 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h18
  have e18 : A18 = A17.updateRow 6 (A17 6 + ((1 : Polynomial ℤ) : Polynomial ℤ) • A17 7) := by
    rw [h18, h17]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d18 : A18.det = A17.det := by
    rw [e18, Matrix.det_updateRow_add_smul_self A17 (by decide : ((6 : Fin 10) ≠ 7)) ((1 : Polynomial ℤ) : Polynomial ℤ)]
  set A19 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 4 * Polynomial.X - 7 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 4 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h19
  have e19 : A19 = A18.updateRow 7 (A18 7 + ((-1 : Polynomial ℤ) : Polynomial ℤ) • A18 6) := by
    rw [h19, h18]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d19 : A19.det = A18.det := by
    rw [e19, Matrix.det_updateRow_add_smul_self A18 (by decide : ((7 : Fin 10) ≠ 6)) ((-1 : Polynomial ℤ) : Polynomial ℤ)]
  set A20 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 4 * Polynomial.X - 7 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 4 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h20
  have e20 : A20 = A19.updateRow 6 (A19 6 + ((2 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A19 8) := by
    rw [h20, h19]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d20 : A20.det = A19.det := by
    rw [e20, Matrix.det_updateRow_add_smul_self A19 (by decide : ((6 : Fin 10) ≠ 8)) ((2 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A21 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 4 * Polynomial.X - 7 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 4 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), (0 : Polynomial ℤ)]
  ] with h21
  have e21 : A21 = A20.updateRow 8 (A20 8 + ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A20 6) := by
    rw [h21, h20]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d21 : A21.det = A20.det := by
    rw [e21, Matrix.det_updateRow_add_smul_self A20 (by decide : ((8 : Fin 10) ≠ 6)) ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A22 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + 2 * Polynomial.X - 7 * Polynomial.X ^ 2 + 10 * Polynomial.X ^ 3 - 5 * Polynomial.X ^ 4 + Polynomial.X ^ 5 : Polynomial ℤ), ((2 : Polynomial ℤ) - 10 * Polynomial.X + 23 * Polynomial.X ^ 2 - 26 * Polynomial.X ^ 3 + 17 * Polynomial.X ^ 4 - 6 * Polynomial.X ^ 5 + Polynomial.X ^ 6 : Polynomial ℤ)]
  ] with h22
  have e22 : A22 = A21.updateRow 9 (A21 9 + ((1 : Polynomial ℤ) - 4 * Polynomial.X + 7 * Polynomial.X ^ 2 - 4 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ) • A21 6) := by
    rw [h22, h21]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d22 : A22.det = A21.det := by
    rw [e22, Matrix.det_updateRow_add_smul_self A21 (by decide : ((9 : Fin 10) ≠ 6)) ((1 : Polynomial ℤ) - 4 * Polynomial.X + 7 * Polynomial.X ^ 2 - 4 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)]
  set A23 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - 7 * Polynomial.X ^ 2 + 10 * Polynomial.X ^ 3 - 5 * Polynomial.X ^ 4 + Polynomial.X ^ 5 : Polynomial ℤ), ((2 : Polynomial ℤ) - 9 * Polynomial.X + 24 * Polynomial.X ^ 2 - 26 * Polynomial.X ^ 3 + 17 * Polynomial.X ^ 4 - 6 * Polynomial.X ^ 5 + Polynomial.X ^ 6 : Polynomial ℤ)]
  ] with h23
  have e23 : A23 = A22.updateRow 9 (A22 9 + ((-1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A22 7) := by
    rw [h23, h22]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d23 : A23.det = A22.det := by
    rw [e23, Matrix.det_updateRow_add_smul_self A22 (by decide : ((9 : Fin 10) ≠ 7)) ((-1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A24 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + 2 * Polynomial.X - 8 * Polynomial.X ^ 2 + 17 * Polynomial.X ^ 3 - 15 * Polynomial.X ^ 4 + 6 * Polynomial.X ^ 5 - Polynomial.X ^ 6 : Polynomial ℤ), ((2 : Polynomial ℤ) - 12 * Polynomial.X + 33 * Polynomial.X ^ 2 - 50 * Polynomial.X ^ 3 + 43 * Polynomial.X ^ 4 - 23 * Polynomial.X ^ 5 + 7 * Polynomial.X ^ 6 - Polynomial.X ^ 7 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - 7 * Polynomial.X ^ 2 + 10 * Polynomial.X ^ 3 - 5 * Polynomial.X ^ 4 + Polynomial.X ^ 5 : Polynomial ℤ), ((2 : Polynomial ℤ) - 9 * Polynomial.X + 24 * Polynomial.X ^ 2 - 26 * Polynomial.X ^ 3 + 17 * Polynomial.X ^ 4 - 6 * Polynomial.X ^ 5 + Polynomial.X ^ 6 : Polynomial ℤ)]
  ] with h24
  have e24 : A24 = A23.updateRow 7 (A23 7 + ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A23 9) := by
    rw [h24, h23]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d24 : A24.det = A23.det := by
    rw [e24, Matrix.det_updateRow_add_smul_self A23 (by decide : ((7 : Fin 10) ≠ 9)) ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A25 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 15 * Polynomial.X ^ 2 + 27 * Polynomial.X ^ 3 - 20 * Polynomial.X ^ 4 + 7 * Polynomial.X ^ 5 - Polynomial.X ^ 6 : Polynomial ℤ), ((4 : Polynomial ℤ) - 21 * Polynomial.X + 57 * Polynomial.X ^ 2 - 76 * Polynomial.X ^ 3 + 60 * Polynomial.X ^ 4 - 29 * Polynomial.X ^ 5 + 8 * Polynomial.X ^ 6 - Polynomial.X ^ 7 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - 7 * Polynomial.X ^ 2 + 10 * Polynomial.X ^ 3 - 5 * Polynomial.X ^ 4 + Polynomial.X ^ 5 : Polynomial ℤ), ((2 : Polynomial ℤ) - 9 * Polynomial.X + 24 * Polynomial.X ^ 2 - 26 * Polynomial.X ^ 3 + 17 * Polynomial.X ^ 4 - 6 * Polynomial.X ^ 5 + Polynomial.X ^ 6 : Polynomial ℤ)]
  ] with h25
  have e25 : A25 = A24.updateRow 7 (A24 7 + ((1 : Polynomial ℤ) : Polynomial ℤ) • A24 9) := by
    rw [h25, h24]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d25 : A25.det = A24.det := by
    rw [e25, Matrix.det_updateRow_add_smul_self A24 (by decide : ((7 : Fin 10) ≠ 9)) ((1 : Polynomial ℤ) : Polynomial ℤ)]
  set A26 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 15 * Polynomial.X ^ 2 + 27 * Polynomial.X ^ 3 - 20 * Polynomial.X ^ 4 + 7 * Polynomial.X ^ 5 - Polynomial.X ^ 6 : Polynomial ℤ), ((4 : Polynomial ℤ) - 21 * Polynomial.X + 57 * Polynomial.X ^ 2 - 76 * Polynomial.X ^ 3 + 60 * Polynomial.X ^ 4 - 29 * Polynomial.X ^ 5 + 8 * Polynomial.X ^ 6 - Polynomial.X ^ 7 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + 8 * Polynomial.X ^ 2 - 17 * Polynomial.X ^ 3 + 15 * Polynomial.X ^ 4 - 6 * Polynomial.X ^ 5 + Polynomial.X ^ 6 : Polynomial ℤ), ((-2 : Polynomial ℤ) + 12 * Polynomial.X - 33 * Polynomial.X ^ 2 + 50 * Polynomial.X ^ 3 - 43 * Polynomial.X ^ 4 + 23 * Polynomial.X ^ 5 - 7 * Polynomial.X ^ 6 + Polynomial.X ^ 7 : Polynomial ℤ)]
  ] with h26
  have e26 : A26 = A25.updateRow 9 (A25 9 + ((-1 : Polynomial ℤ) : Polynomial ℤ) • A25 7) := by
    rw [h26, h25]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d26 : A26.det = A25.det := by
    rw [e26, Matrix.det_updateRow_add_smul_self A25 (by decide : ((9 : Fin 10) ≠ 7)) ((-1 : Polynomial ℤ) : Polynomial ℤ)]
  set A27 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 15 * Polynomial.X ^ 2 + 27 * Polynomial.X ^ 3 - 20 * Polynomial.X ^ 4 + 7 * Polynomial.X ^ 5 - Polynomial.X ^ 6 : Polynomial ℤ), ((4 : Polynomial ℤ) - 21 * Polynomial.X + 57 * Polynomial.X ^ 2 - 76 * Polynomial.X ^ 3 + 60 * Polynomial.X ^ 4 - 29 * Polynomial.X ^ 5 + 8 * Polynomial.X ^ 6 - Polynomial.X ^ 7 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 3 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X : Polynomial ℤ)]
  ] with h27
  have e27 : A27 = A26.updateRow 9 (A26 9 + ((1 : Polynomial ℤ) - 7 * Polynomial.X + 10 * Polynomial.X ^ 2 - 5 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ) • A26 8) := by
    rw [h27, h26]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d27 : A27.det = A26.det := by
    rw [e27, Matrix.det_updateRow_add_smul_self A26 (by decide : ((9 : Fin 10) ≠ 8)) ((1 : Polynomial ℤ) - 7 * Polynomial.X + 10 * Polynomial.X ^ 2 - 5 * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℤ)]
  set A28 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 15 * Polynomial.X ^ 2 + 27 * Polynomial.X ^ 3 - 20 * Polynomial.X ^ 4 + 7 * Polynomial.X ^ 5 - Polynomial.X ^ 6 : Polynomial ℤ), ((4 : Polynomial ℤ) - 21 * Polynomial.X + 57 * Polynomial.X ^ 2 - 76 * Polynomial.X ^ 3 + 60 * Polynomial.X ^ 4 - 29 * Polynomial.X ^ 5 + 8 * Polynomial.X ^ 6 - Polynomial.X ^ 7 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X : Polynomial ℤ)]
  ] with h28
  have e28 : A28 = A27.updateRow 8 (A27 8 + ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A27 9) := by
    rw [h28, h27]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d28 : A28.det = A27.det := by
    rw [e28, Matrix.det_updateRow_add_smul_self A27 (by decide : ((8 : Fin 10) ≠ 9)) ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A29 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 15 * Polynomial.X ^ 2 + 27 * Polynomial.X ^ 3 - 20 * Polynomial.X ^ 4 + 7 * Polynomial.X ^ 5 - Polynomial.X ^ 6 : Polynomial ℤ), ((4 : Polynomial ℤ) - 21 * Polynomial.X + 57 * Polynomial.X ^ 2 - 76 * Polynomial.X ^ 3 + 60 * Polynomial.X ^ 4 - 29 * Polynomial.X ^ 5 + 8 * Polynomial.X ^ 6 - Polynomial.X ^ 7 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X : Polynomial ℤ)]
  ] with h29
  have e29 : A29 = A28.updateRow 8 (A28 8 + ((1 : Polynomial ℤ) : Polynomial ℤ) • A28 9) := by
    rw [h29, h28]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d29 : A29.det = A28.det := by
    rw [e29, Matrix.det_updateRow_add_smul_self A28 (by decide : ((8 : Fin 10) ≠ 9)) ((1 : Polynomial ℤ) : Polynomial ℤ)]
  set A30 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((2 : Polynomial ℤ) - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((2 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - 15 * Polynomial.X ^ 2 + 27 * Polynomial.X ^ 3 - 20 * Polynomial.X ^ 4 + 7 * Polynomial.X ^ 5 - Polynomial.X ^ 6 : Polynomial ℤ), ((4 : Polynomial ℤ) - 21 * Polynomial.X + 57 * Polynomial.X ^ 2 - 76 * Polynomial.X ^ 3 + 60 * Polynomial.X ^ 4 - 29 * Polynomial.X ^ 5 + 8 * Polynomial.X ^ 6 - Polynomial.X ^ 7 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 3 : Polynomial ℤ)]
  ] with h30
  have e30 : A30 = A29.updateRow 9 (A29 9 + ((-1 : Polynomial ℤ) : Polynomial ℤ) • A29 8) := by
    rw [h30, h29]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d30 : A30.det = A29.det := by
    rw [e30, Matrix.det_updateRow_add_smul_self A29 (by decide : ((9 : Fin 10) ≠ 8)) ((-1 : Polynomial ℤ) : Polynomial ℤ)]
  have hchain : A30.det = A0.det := by
    rw [d30, d29, d28, d27, d26, d25, d24, d23, d22, d21, d20, d19, d18, d17, d16, d15, d14, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]
  have hT : A30.BlockTriangular id := by
    intro i j hij
    rw [h30]
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hij (by decide)
      | simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
  have hdiag : (∏ i, A30 i i) = Polynomial.X ^ 5 := by
    rw [h30]
    simp only [Fin.prod_univ_succ, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.isValue]
    have htail : ∀ g : Fin 0 → Polynomial ℤ, (∏ i, g i) = 1 := fun g =>
      Finset.prod_eq_one (fun x _ => Fin.elim0 x)
    rw [htail _]
    ring
  rw [← hchain, Matrix.det_of_upperTriangular hT, hdiag]


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

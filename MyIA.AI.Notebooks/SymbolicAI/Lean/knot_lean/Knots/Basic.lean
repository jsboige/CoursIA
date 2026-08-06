/-
Knots.Basic — Fondations combinatoires de la theorie des noeuds
=============================================================

Scaffolding pour la theorie des noeuds en Lean 4, inspire par :
- shua/leanknot (https://github.com/shua/leanknot, branche Lean 4)
- Prathamesh (2015), Formalising Knot Theory in Isabelle/HOL

Convention : namespace `Knots`, theoremes commentes avec references.
Epic #2874, Phase 1.

Prerequis Mathlib necessaires :
- Representations combinatoires des diagrammes planaires (PD-codes)
- Codes de Gauss / notation Dowker-Thistlethwaite
- Theorie des graphes de base pour les graphes de croisements
-/

import Mathlib.Tactic

/-
  Convention i18n (EPIC #4980, decision user 2026-07-04) : ce fichier est **FR canonique**,
  avec son miroir anglais dans le fichier sibling `Basic_en.lean` (modele sibling pair
  ratifie 2026-07-04, cf `code-style.md` §Lean i18n). Les enonces de theoremes,
  les tactiques Lean, les noms de lemmes et les references Mathlib restent en anglais
  (compat Mathlib 4) ; seules les docstrings de module et ce bloc d'en-tete different
  entre les deux fichiers.
-/

namespace Knots

/-! ## 1. Croisement et CrossingType

Un croisement dans un diagramme de noeud comporte deux brins : l'un passe au-dessus,
l'autre en dessous. Le signe distingue les croisements positifs (droitiers) des
croisements negatifs (gauchers).
-/

inductive CrossingType where
  | positive : CrossingType  -- croisement par-dessus venant de gauche
  | negative : CrossingType  -- croisement par-dessus venant de droite
  deriving BEq, DecidableEq, Repr

instance : Repr CrossingType := ⟨fun ct _ =>
  match ct with
  | .positive => "+"
  | .negative => "-"⟩

/-! ## 2. Croisement

Un croisement est identifie par son indice dans un diagramme et possede un type.
-/

structure Crossing where
  index : Nat
  crossingType : CrossingType
  deriving BEq, DecidableEq, Repr

/-! ## 3. Segment de brin

Entre deux croisements (ou d'un croisement vers lui-meme), un segment de brin
relie des positions. Nous etiquetons les positions comme "entrantes" ou
"sortantes" pour chaque bras du croisement.
-/

inductive Arm where
  | over_in : Arm
  | over_out : Arm
  | under_in : Arm
  | under_out : Arm
  deriving BEq, DecidableEq, Repr

/-! ## 4. Code de diagramme planaire (PD)

Un croisement est encode par quatre etiquettes d'arete se rencontrant en ce
croisement, lues dans le sens trigonometrique inverse a partir du brin entrant
du dessous.

Reference : https://katlas.org/wiki/Planar_Diagrams
-/

structure PDCrossing where
  -- Quatre etiquettes d'arete, sens trigonometrique inverse depuis le brin entrant du dessous
  e1 : Nat  -- dessous entrant
  e2 : Nat  -- dessus entrant
  e3 : Nat  -- dessous sortant
  e4 : Nat  -- dessus sortant
  deriving BEq, Repr

/-- Un diagramme de noeud est une liste de croisements PD avec un nombre de croisements. -/
structure KnotDiagram where
  crossings : List PDCrossing
  numEdges : Nat
  -- La bonne formation est le predicat autonome `KnotDiagram.wf` (section 11),
  -- file comme hypothese `(hwf : d.wf = true)` sur les mouvements de Reidemeister.
  -- Ce n'est volontairement PAS un champ : un mouvement de Reidemeister construit
  -- un diagramme intermediaire dont la bonne formation ne vaut que sous les
  -- hypotheses de la relation, donc un invariant intrinseque rendrait le mouvement
  -- non statable (voir la rationale de conception sur l'issue #8604).
  deriving Repr

/-! ## 5. Noeud

Un noeud est une classe d'equivalence de diagrammes de noeud modulo les mouvements
de Reidemeister et l'isotopie planaire. Pour l'instant, nous le representons comme
un emballage autour d'un diagramme, l'equivalence etant definie mais pas encore
reliee aux mouvements de Reidemeister.
-/

structure Knot where
  diagram : KnotDiagram
  deriving Repr

/-! ## 6. Lien

Un lien generalise le noeud a plusieurs composantes. Represente comme un code PD
avec plusieurs courbes fermees.
-/

structure Link where
  diagram : KnotDiagram
  numComponents : Nat
  -- Au moins 1 composante (noeud = lien avec 1 composante)
  hpos : numComponents ≥ 1
  deriving Repr

/-- Un noeud est un lien avec exactement une composante. -/
def Knot.toLink (k : Knot) : Link where
  diagram := k.diagram
  numComponents := 1
  hpos := by omega

/-! ## 7. Noeuds nommes

Le noeud le plus simple : le noeud trivial (sans croisement).
-/

def unknotDiagram : KnotDiagram where
  crossings := []
  numEdges := 1

def unknot : Knot where
  diagram := unknotDiagram

/- Le noeud de trefoil (3_1), le noeud non trivial le plus simple.

Nombre de croisements 3, trois croisements positifs (trefoil a main droite).
Code PD issu de KnotInfo : [[1,4,2,5],[3,6,4,1],[5,2,6,3]]
-/
def trefoilDiagram : KnotDiagram where
  crossings := [
    ⟨1, 4, 2, 5⟩,  -- croisement 1
    ⟨3, 6, 4, 1⟩,  -- croisement 2
    ⟨5, 2, 6, 3⟩   -- croisement 3
  ]
  numEdges := 6

def trefoil : Knot where
  diagram := trefoilDiagram

/- Le noeud en huit (4_1), le noeud le plus simple avec un nombre de croisements de 4.

Code PD issu de KnotInfo : [[1,5,2,4],[3,8,4,2],[5,1,6,7],[7,3,8,6]]
-/
def figureEightDiagram : KnotDiagram where
  crossings := [
    ⟨1, 5, 2, 4⟩,
    ⟨3, 8, 4, 2⟩,
    ⟨5, 1, 6, 7⟩,
    ⟨7, 3, 8, 6⟩
  ]
  numEdges := 8

def figureEight : Knot where
  diagram := figureEightDiagram

/-! ## 8. Image miroir

Refleter un noeud en inversant tous les signes de croisement (permuter dessus/dessous).
-/

def mirrorCrossing (c : PDCrossing) : PDCrossing where
  e1 := c.e1
  e2 := c.e4  -- permuter le dessus et le dessous
  e3 := c.e3
  e4 := c.e2

def Knot.mirror (k : Knot) : Knot where
  diagram := {
    crossings := k.diagram.crossings.map mirrorCrossing
    numEdges := k.diagram.numEdges
  }

/-! ## 9. Nombre de croisements (croisements minimaux)

Le nombre de croisements est le nombre minimal de croisements parmi tous les diagrammes
representant le meme noeud. Ceci requiert l'equivalence, que nous n'avons pas encore.
-/

def Knot.crossingNumberOfDiagram (k : Knot) : Nat :=
  k.diagram.crossings.length

/-- Nombre de croisements.

**Definition Phase 3 (borne superieure provisoire).** Le vrai nombre de croisements
est le nombre *minimal* de croisements parmi tous les diagrammes equivalents a `k`
sous les mouvements de Reidemeister. Calculer ce minimum requiert :
  - une equivalence de Reidemeister pleinement concrete (chirurgie sur les codes PD), et
  - une minimisation (min de finset sur le quotient des diagrammes).

Aucun des deux n'est encore disponible (les mouvements de Reidemeister sont encore
abstraits, cf. `Reidemeister.lean`). Comme definition *provisoire et conservatrice*,
nous prenons le compte de croisements du diagramme courant du noeud. C'est une
**borne superieure** sur le vrai nombre de croisements (Reidemeister I ne peut
qu'ajouter des croisements, jamais reduire sous le diagramme minimal), il est donc
sur de l'utiliser comme estimation superieure.

Pour les noeuds nommes dont les diagrammes standard sont deja minimaux (noeud trivial
= 0, trefoil = 3, noeud en huit = 4), ceci coincide avec le vrai nombre de
croisements. Le theoreme `trefoil_crossing_number` dans `Invariant.lean` s'appuie sur
cette definition provisoire.

A faire Phase 4+ : remplacer par le vrai minimum une fois l'equivalence concrete de
Reidemeister + la minimisation par finset en place.
-/
def Knot.crossingNumber (k : Knot) : Nat :=
  k.crossingNumberOfDiagram

/-! ## 10. Connectivite / adjacence depuis le code PD

Extraire quelles aretes connectent quels croisements.
-/

/-- Obtenir toutes les aretes utilisees dans un diagramme. -/
def KnotDiagram.edges (d : KnotDiagram) : List Nat :=
  d.crossings.flatMap fun c => [c.e1, c.e2, c.e3, c.e4]

/-- Nombre de croisements dans un diagramme. -/
def KnotDiagram.numCrossings (d : KnotDiagram) : Nat :=
  d.crossings.length

/-! ## 11. Predicat de bonne formation (Phase 5)

Un code PD est bien forme lorsque (a) toute etiquette d'arete est dans `[1, numEdges]`,
et (b) toute etiquette apparaissant le fait exactement deux fois — chaque arc a deux
extremites, une a chaque croisement qu'il rencontre (Doll & Hoste, 1991). Un diagramme
degenere sans croisement a une liste d'aretes vide, donc les deux conditions sont
satisfaites vacuellement.

Ceci est un *predicat autonome a valeur Bool* (pas un champ `KnotDiagram`), calque sur
`MacroCell.wf` dans `conway_lean` (HashlifeCorrectness.lean). Il est file comme
hypothese `(hwf : d.wf = true)` sur les mouvements de Reidemeister remodeles
(voir `Reidemeister.lean`), ce qui exclut les temoins mal formes qui refutaient
`tricolorable_invariant` sous le modele existentiel symetrique de la Phase 3
(voir le diagnostic sur `tricolorable_invariant` dans `Invariant.lean`).
-/

/-- Bonne formation pour un code PD (valeur Bool, calque sur `MacroCell.wf`).

Un veritable code PD satisfait la **condition de parite** : toute etiquette d'arete
dans `[1, numEdges]` apparait exactement deux fois parmi les extremites de
croisement — chaque arc a deux extremites, une a chaque croisement qu'il rencontre
(donc `2 * numEdges = 4 * numCrossings`, i.e. `numEdges = 2 * numCrossings` pour les
diagrammes non degeneres).

Un diagramme degenere sans croisement n'a pas d'extremites d'arete ; sa liste
d'aretes est vide, et la condition de parite est vacuellement satisfaite pour tout
`numEdges ≤ 1` (le noeud trivial est represente avec un arc, `numEdges := 1`).

Le predicat est file comme `(hwf : d.wf = true)` sur les mouvements de Reidemeister
remodeles (`Reidemeister.lean`), excluant les temoins mal formes qui refutaient
`tricolorable_invariant` sous le modele existentiel symetrique de la Phase 3 (le
temoin `⟨7,8,9,10⟩` a des etiquettes hors de `[1, numEdges]` ; un diagramme a arete
pendante a une etiquette dans `[1, numEdges]` qui n'apparait jamais). Voir le
diagnostic sur `tricolorable_invariant` dans `Invariant.lean`. -/
def KnotDiagram.wf (d : KnotDiagram) : Bool :=
  if d.crossings = [] then
    decide (d.numEdges ≤ 1)
  else
    -- (a) toute etiquette apparaissant dans un croisement est dans [1, numEdges]
    d.edges.all (fun l => decide (1 ≤ l ∧ l ≤ d.numEdges)) &&
    -- (b) toute etiquette dans [1, numEdges] apparait exactement deux fois (parite)
    (List.range d.numEdges).all (fun i => decide (d.edges.count (i + 1) = 2))

theorem unknot_wf : unknotDiagram.wf = true := by
  -- 0 croisements -> branche degeneree : numEdges = 1 ≤ 1.
  decide

theorem trefoil_wf : trefoilDiagram.wf = true := by
  -- 3 croisements, etiquettes {1,..,6} apparaissant chacune exactement deux fois.
  decide

theorem figureEight_wf : figureEightDiagram.wf = true := by
  -- 4 croisements, etiquettes {1,..,8} apparaissant chacune exactement deux fois.
  decide

/-! ## 12. Le miroir preserve la bonne formation (Issue #8604, sous-piste #8644)

`mirrorCrossing` permute `e2 ↔ e4` (brins dessus/dessous). La liste d'etiquettes
a 4 elements resultante `[e1, e4, e3, e2]` est une permutation de
`[e1, e2, e3, e4]`. Les deux listes sont des `List Nat` concretes a 4 elements
et le multi-ensemble est identique, donc l'invariant de compte par etiquette est
preserve.

Nous etablissons ceci pour chaque **noeud nomme** (cas decidable concret) ci-dessous.
La generalisation polymorphe (`∀ (c : PDCrossing), Perm [...] [...]`)
est reservee a la lane competent en Lean (po-2026) — le travail de preuve requiert
une analyse de cas manuelle non triviale sur 4 etiquettes avec collisions possibles,
hors de portee pour un worker non specialise (cf. post-mortem d'echec CI
`Basic.lean:218` de la PR hwell-replace abandonnee ; le polymorphisme sur
`PDCrossing` empeche `decide` de clore de tels buts directement, car `decide`
n'est pas un prover universel sur les variables libres).
-/

/-- Le miroir du noeud trivial est bien forme : trivialement, l'image de `[]` est `[]`,
    et `numEdges = 1 ≤ 1`. -/
theorem mirror_unknot_wf : unknot.mirror.diagram.wf = true := by
  decide

/-- Le miroir du trefoil est bien forme : la permutation de slots
    `e2 ↔ e4` preserve le multi-ensemble d'etiquettes, donc la verification de
    parite voit encore chacun de `1..6` exactement deux fois parmi les 3 croisements
    miroires. -/
theorem mirror_trefoil_wf : trefoil.mirror.diagram.wf = true := by
  decide

/-- Le miroir du noeud en huit est bien forme : meme raisonnement que pour le
    trefoil mais avec 4 croisements et les etiquettes `1..8` apparaissant chacune
    exactement deux fois dans la liste miroire. -/
theorem mirror_figureEight_wf : figureEight.mirror.diagram.wf = true := by
  decide

/-! ## 13. `mirror_wf_preserves` polymorphe (Issue #8644)

Les lemmes sur noeuds nommes ci-dessus deleguent la preservation de bonne formation
de facon concrete. Cette section remonte le meme argument a un enonce de lemme
**polymorphe** valable pour *n'importe quel* `KnotDiagram` dont la bonne formation
tient. L'idee-cle est que `mirrorCrossing` ne fait que permuter deux etiquettes
(dessus ↔ dessous), donc la liste d'etiquettes a 4 elements par croisement est une
Permutation d'elle-meme — l'invariant de compte par etiquette est preserve
*symboliquement*, pas seulement sur les instances.

Ceci est la generalisation polymorphe que le post-mortem d'echec CI
`Basic.lean:218` de la PR hwell-replace abandonnee ne pouvait pas deleguer :
`decide` ne clot pas les buts polymorphes sur variables libres. La preuve ici est
**ecrite a la main** utilisant `Perm.swap`
+ `Perm.cons` + `Subperm.count_le` + `Subperm.antisymm` :
la liste a 4 elements `[e1, e4, e3, e2]` est une permutation de
`[e1, e2, e3, e4]` (transposition `e2 ↔ e4` aux positions 1..2). La version v4.31.0-rc1
de Mathlib/Batteries ne declare PAS encore `List.perm_iff_count` — l'equivalent
`Perm → ∀ a, count a l₁ = count a l₂` est reconstruit ici a partir de
`Perm.subperm` + `Subperm.count_le` (une direction) + `Subperm.symm`
+ `Subperm.antisymm` (les deux directions). Trois lemmes intermediaires exposent
proprement la reecriture par croisement ; le `mirror_wf_preserves` de tete
les colle a travers `KnotDiagram.wf`.

Le travail restant consiste a coller ce fait par croisement a travers la
definition de `KnotDiagram.wf` : le multi-ensemble d'aretes du diagramme (un seul
`flatMap` sur les croisements) et la verification de parite par etiquette se closent
ensuite par reecriture sans `decide` sur le lemme `mirrorCrossing_preserves_count`.
-/

open List in
/-- Les deux listes d'etiquettes a 4 elements sont des permutations l'une de l'autre.
    Etabli par trois transpositions adjacentes. -/
theorem mirrorCrossing_perm (c : PDCrossing) :
    [c.e1, c.e4, c.e3, c.e2] ~ [c.e1, c.e2, c.e3, c.e4] := by
  -- Chemin : [e1, e4, e3, e2] ~ [e1, e4, e2, e3] ~ [e1, e2, e4, e3] ~ [e1, e2, e3, e4]
  -- Chaque etape est une transposition adjacente unique, prefixee par le prefixe inchange.
  -- NB : en v4.31.0-rc1, `Perm.swap x y l : y :: x :: l ~ x :: y :: l` (la docstring
  -- affichee pretend `x :: y :: l ~ y :: x :: l` mais le constructeur reel produit la
  -- direction OPPOSEE — verifie empiriquement via le message d'erreur de compilation).
  have p1 : [c.e1, c.e4, c.e3, c.e2] ~ [c.e1, c.e4, c.e2, c.e3] :=
    Perm.cons c.e1 (Perm.cons c.e4 (Perm.swap c.e2 c.e3 []))
  have p2 : [c.e1, c.e4, c.e2, c.e3] ~ [c.e1, c.e2, c.e4, c.e3] :=
    Perm.cons c.e1 (Perm.swap c.e2 c.e4 [c.e3])
  have p3 : [c.e1, c.e2, c.e4, c.e3] ~ [c.e1, c.e2, c.e3, c.e4] :=
    Perm.cons c.e1 (Perm.cons c.e2 (Perm.swap c.e3 c.e4 []))
  exact (p1.trans p2).trans p3

open List in
/-- Preservation du compte d'etiquettes par croisement : permuter `e2 ↔ e4` ne
    change pas le multi-ensemble des etiquettes dans la liste a 4 elements. Ecrit a la
    main (v4.31.0-rc1 manque `List.perm_iff_count`) : utiliser `List.Perm.subperm` (qui
    donne `List.Subperm` dans les deux directions par symetrie) + `Subperm.count_le`
    pour borner chaque cote, puis `le_antisymm` pour conclure l'egalite. -/
theorem mirrorCrossing_preserves_count (c : PDCrossing) (l : Nat) :
    ([c.e1, c.e4, c.e3, c.e2]).count l = ([c.e1, c.e2, c.e3, c.e4]).count l := by
  have hab : [c.e1, c.e4, c.e3, c.e2] <+~ [c.e1, c.e2, c.e3, c.e4] :=
    (mirrorCrossing_perm c).subperm
  have hba : [c.e1, c.e2, c.e3, c.e4] <+~ [c.e1, c.e4, c.e3, c.e2] :=
    (mirrorCrossing_perm c).symm.subperm
  exact le_antisymm (hab.count_le l) (hba.count_le l)

/-- Auxiliaire : `Multiset.count a (ofList (l1 ++ l2))` se scinde additivement en
    tete + queue. Ceci est le remplacement base sur `Multiset` pour le theoreme
    `List.count_append` manquant en v4.31.0-rc1. -/
theorem count_lift_append {α : Type*} [DecidableEq α] (a : α) (l1 l2 : List α) :
    (Multiset.ofList (l1 ++ l2)).count a =
      (Multiset.ofList l1).count a + (Multiset.ofList l2).count a := by
  induction l1 with
  | nil => rw [List.nil_append, Multiset.coe_nil, Multiset.count_zero, Nat.zero_add]
  | cons x xs ih =>
    show (Multiset.ofList (x :: (xs ++ l2))).count a =
         (Multiset.ofList (x :: xs)).count a + (Multiset.ofList l2).count a
    -- Convertir `↑(x :: ys)` en `x ::ₘ ↑ys` pour que `Multiset.count_cons` corresponde.
    rw [← Multiset.cons_coe, ← Multiset.cons_coe]
    rw [Multiset.count_cons, Multiset.count_cons]
    rw [ih]
    omega

/-- Preservation du compte d'etiquettes par diagramme : `mirror` sur les croisements
    du diagramme ne change pas le multi-ensemble des etiquettes d'aretes apparaissant
    dans le flat-map des extremites d'etiquettes. Par induction sur la liste de
    croisements, utilisant `mirrorCrossing_preserves_count` pour l'etape cons.

    v4.31.0-rc1 ne declare PAS `List.count_append` ni `List.count_cons`.
    Strategie : convertir l'egalite de `List.count` en une egalite de `Multiset.count`
    via `Multiset.coe_count`, prouver l'egalite de `Multiset` par induction,
    ou la decomposition `++` devient `count_lift_append`
    (le remplacement auxiliaire base sur `Multiset` pour `List.count_append`). -/

theorem mirror_diag_preserves_count (d : KnotDiagram) (l : Nat) :
    ((d.crossings.map mirrorCrossing).flatMap
       (fun c => [c.e1, c.e2, c.e3, c.e4])).count l =
      (d.crossings.flatMap (fun c => [c.e1, c.e2, c.e3, c.e4])).count l := by
  -- Reecris les deux cotes de la forme `List.count` vers la forme `Multiset.count` via
  -- `← Multiset.coe_count` (la direction symm : `l'.count a = Multiset.count a ↑l'`).
  rw [← Multiset.coe_count, ← Multiset.coe_count]
  induction d.crossings with
  | nil =>
    -- Les deux `flatMap` sur `[]` se reduisent a `↑[] = 0` ; les comptes sont egaux par `rfl`.
    rw [List.map_nil, List.flatMap_nil, Multiset.coe_nil]
  | cons hd tl ih =>
    -- Distribuer le `flatMap` de cons pour exposer `tete ++ queue`.
    show (Multiset.ofList
        ([hd.e1, hd.e4, hd.e3, hd.e2] ++
          (tl.map mirrorCrossing).flatMap (fun c => [c.e1, c.e2, c.e3, c.e4]))).count l =
      (Multiset.ofList
        ([hd.e1, hd.e2, hd.e3, hd.e4] ++
          tl.flatMap (fun c => [c.e1, c.e2, c.e3, c.e4]))).count l
    -- Appliquer `count_lift_append` pour scinder additivement en tete + queue.
    rw [count_lift_append, count_lift_append]
    -- Convertir les quatre termes en forme `List.count`.
    rw [Multiset.coe_count, Multiset.coe_count,
        Multiset.coe_count, Multiset.coe_count]
    -- Les comptes de la liste de tete sont egaux par `mirrorCrossing_preserves_count hd l` (symm).
    rw [← mirrorCrossing_preserves_count hd l]
    -- Les comptes de la liste de queue sont egaux par l'HR.
    -- NB : `ih` est en forme `Multiset.count` (apres les reecritures initiales en tete
    -- de theoreme) ; le but est en forme `List.count` (apres les 4 conversions
    -- ci-dessus), donc nous convertissons l'HR pour correspondre avant de l'appliquer.
    rw [Multiset.coe_count, Multiset.coe_count] at ih
    rw [ih]

/-- Auxiliaire : la liste des extremites d'etiquettes du miroir d'un diagramme de noeud. -/
def mirror_diag_edges (d : KnotDiagram) : List Nat :=
  (d.crossings.map mirrorCrossing).flatMap
    (fun c : PDCrossing => [c.e1, c.e2, c.e3, c.e4])

/-- **Corollaire polymorphe de tete** — `Subperm` par etiquette (Issue #8644).

Pour tout `KnotDiagram d`, la liste d'etiquettes produite par `mirror` est un
`Subperm` de l'original (et vice-versa). Resulte de l'egalite de compte bilaterale
etablie par `mirror_diag_preserves_count`.

Ceci est la **generalisation polymorphe** que `decide` ne peut pas deleguer
sur les variables libres (`decide` n'est pas un prover universel).
La preuve utilise `mirror_diag_preserves_count` pour fournir la
borne dans chaque direction. -/
theorem mirror_edges_subperm (d : KnotDiagram) (l : Nat) :
    (mirror_diag_edges d).count l ≤ d.edges.count l ∧
    d.edges.count l ≤ (mirror_diag_edges d).count l := by
  exact ⟨le_of_eq (mirror_diag_preserves_count d l),
         le_of_eq (mirror_diag_preserves_count d l).symm⟩

/-- **Theoreme polymorphe de tete** — `mirror` preserve `KnotDiagram.wf`
    (sous-piste Issue #8644, portee deferee, aucun `sorry` introduit).

Ceci est le *lemme polymorphe vedette* appele par `#8644`. La preuve
est ecrite a la main et file a travers :
  - l'identite de `Knot.mirror` sur `numEdges` (le miroir preserve `numEdges`
    en tant que champ) ;
  - `mirror_edges_subperm` (preservation du compte par etiquette via
    la cascade `mirror_diag_preserves_count`) ;
  - la branche degeneree/non-degeneree de `KnotDiagram.wf` pour se reduire
    a la verification de parite + la verification de plage, chacune close par
    l'egalite derivee de `Subperm` correspondante.

**Reduction de portee honnete** : clore le but polymorphe complet
requiert une chaine `Subperm.antisymm`-puis-`Perm`-puis-verification-de-plage
qui est un travail multi-cycles pour une lane Lean-CPU uniquement. Cette PR livre la
**preservation du compte par diagramme** (`mirror_diag_preserves_count`,
`mirror_edges_subperm`) — la piece polymorphe manquante — et laisse
la cloture de `mirror_wf_preserves : ∀ d, d.wf = true → d.mirror.wf = true`
a une lane competent en Lean en tant que sous-piste `#8644`.

Pour les instances de noeuds nommes (cas decidable concret), la cloture
reste deleguee par `decide` (cf. `mirror_unknot_wf`,
`mirror_trefoil_wf`, `mirror_figureEight_wf` dans la section 12 ci-dessus). -/
theorem mirror_wf_preserves_partial (d : KnotDiagram) :
    (∀ l, ((d.crossings.map mirrorCrossing).flatMap
              (fun c => [c.e1, c.e2, c.e3, c.e4])).count l =
            (d.crossings.flatMap
              (fun c => [c.e1, c.e2, c.e3, c.e4])).count l) := by
  intro l
  exact mirror_diag_preserves_count d l

/-! ## 14. Cloture : `mirror` preserve `KnotDiagram.wf` (Issue #8644)

La section 13 a prouve la permutation par croisement `mirrorCrossing_perm` et la
preservation du compte par diagramme `mirror_diag_preserves_count`. Cette section
clot le theoreme polymorphe differe a la lane competent en Lean par la PR #8667 :
`mirror` preserve `KnotDiagram.wf` pour **n'importe quel** noeud.

La voie la plus propre remonte `mirrorCrossing_perm` a une permutation de diagramme
complet `mirror_edges_perm` via `List.Perm.flatMap` — `mirror` ne fait que permuter
`e2 ↔ e4` au sein de chaque croisement, donc la liste d'aretes obtenue par flat-map
est une permutation de l'original. D'une permutation, a la fois le `count` par
etiquette (verification de parite) et `all` (verification de plage) sont preserves
directement, et `mirror` preserve `numEdges` par identite de champ. Donc
`KnotDiagram.wf` — qui ne depend que de `numEdges` plus le multi-ensemble d'aretes —
est invariant sous le miroir. Pas de `sorry`, pas de `decide` sur variables libres.
-/

open List in
/-- La liste d'aretes du diagramme miroire est une permutation de celle de l'original.
    Remonte la permutation par croisement `mirrorCrossing_perm` a travers le
    flat-map : `(cs.map mirrorCrossing).flatMap F ~ cs.flatMap F` car chaque
    `F (mirrorCrossing c) ~ F c` (les listes a 4 elements `[e1,e4,e3,e2]` et
    `[e1,e2,e3,e4]` sont des permutations, `mirrorCrossing_perm`). -/
theorem mirror_edges_perm (d : KnotDiagram) :
    mirror_diag_edges d ~ d.edges := by
  show (d.crossings.map mirrorCrossing).flatMap (fun c => [c.e1, c.e2, c.e3, c.e4]) ~
       d.crossings.flatMap (fun c => [c.e1, c.e2, c.e3, c.e4])
  rw [List.flatMap_map]
  -- Apres `(map f).flatMap g = flatMap (g ∘ f)`, la fonction par croisement est
  -- defeq `fun c => [c.e1, c.e4, c.e3, c.e2]` (mirrorCrossing permute e2 ↔ e4).
  exact List.Perm.flatMap_left d.crossings (fun c _ => mirrorCrossing_perm c)

open List in
/-- `mirror` preserve `KnotDiagram.wf` (cloture Issue #8644).

`mirrorCrossing` permute `e2 ↔ e4`, donc `mirror_diag_edges d` est une permutation de
`d.edges` (`mirror_edges_perm`) ; `KnotDiagram.wf` ne depend que du multi-ensemble
d'aretes (verification de plage sur le support via `all`, verification de parite sur
le `count` par etiquette) plus `numEdges`, et le miroir preserve `numEdges` par
identite de champ. Ceci est la generalisation polymorphe complete que `decide` ne
pouvait pas deleguer sur les variables libres — ici closee a la main. -/
theorem mirror_wf_preserves (k : Knot) (h : k.diagram.wf = true) :
    k.mirror.diagram.wf = true := by
  -- Identites de champ du diagramme miroire (defeq).
  have hmcross : k.mirror.diagram.crossings = k.diagram.crossings.map mirrorCrossing := rfl
  have hmnum   : k.mirror.diagram.numEdges = k.diagram.numEdges := rfl
  have hmedges : k.mirror.diagram.edges = mirror_diag_edges k.diagram := rfl
  -- Permutation de diagramme complet de la liste d'aretes.
  have hp : mirror_diag_edges k.diagram ~ k.diagram.edges := mirror_edges_perm k.diagram
  -- Egalite de compte par etiquette entre aretes miroires et originales
  -- (utilise `mirror_diag_preserves_count` de la section 13, qui reconstruit deja
  -- la preservation de compte que le `List.perm_iff_count` manquant de v4.31.0-rc1
  -- donnerait directement).
  have hc (l : Nat) : k.mirror.diagram.edges.count l = k.diagram.edges.count l := by
    rw [hmedges]; exact mirror_diag_preserves_count k.diagram l
  -- Le miroir preserve la vacuite de la liste de croisements.
  have hem : k.mirror.diagram.crossings = [] ↔ k.diagram.crossings = [] := by
    rw [hmcross]; exact List.map_eq_nil_iff
  -- Deplier `wf` des deux cotes.
  simp only [KnotDiagram.wf] at h ⊢
  by_cases he : k.diagram.crossings = []
  · -- Branche degeneree : le miroir est vide aussi ; les deux if se reduisent a `numEdges ≤ 1`.
    have hme := hem.mpr he
    simp only [hme, he, if_true, hmnum] at h ⊢
    exact h
  · -- Branche non-degeneree : le miroir est non-vide aussi.
    have hme : k.mirror.diagram.crossings ≠ [] := fun H => he (hem.mp H)
    simp only [hme, he, if_false, hmnum] at h ⊢
    rw [Bool.and_eq_true] at h ⊢
    obtain ⟨h_all, h_par⟩ := h
    refine ⟨?_, ?_⟩
    · -- Verification de plage : le predicat ne depend pas de la position, seulement de
      -- l'appartenance, donc transportons-le ponctuellement via `Perm.mem_iff` (le plus ancien
      -- lemme de perm — survit aux montees de version ; ne s'appuie pas sur `Perm.all_eq`).
      rw [hmedges]
      rw [List.all_eq_true] at h_all ⊢
      intro x hx
      exact h_all x (hp.mem_iff.mp hx)
    · -- Verification de parite : le `count` par etiquette est invariant sous permutation.
      have heq : (fun i => decide (k.mirror.diagram.edges.count (i + 1) = 2)) =
                 (fun i => decide (k.diagram.edges.count (i + 1) = 2)) := by
        funext i; rw [hc]
      rw [heq]; exact h_par

/-! ## 15. Retrospective sur la chaine de preuve `mirror_wf_preserves` (rationale, post-cloture)

La cloture de la section 14 ci-dessus etait le **lemme terminal** d'une chaine de 4 PR
qui a commence par le post-mortem de l'echec #8643. La retrospective
ci-dessous documente la chaine afin que les futurs contributeurs puissent la naviguer
sans refaire les memes impasses.

**La chaine en quatre etapes :**

1. **PR #8643 (FERMEE)** — premiere tentative de `mirror_wf_preserves`
   utilisant `decide` sur le but polymorphe `KnotDiagram`. La tactique
   `decide` requiert une instance `Decidable` et le type de but incluait
   des variables libres (`crossings : List PDCrossing`, `numEdges : Nat`) ;
   `decide` ne peut pas decider un tel but. Mode d'echec catastrophique
   `Invalid field 'mirror' on KnotDiagram` car le but se referait
   a `Knot.mirror` (un champ `Knot`) mais etait enonce au niveau
   `KnotDiagram`. PR fermee, sous-issue #8644 ouverte.

2. **PR #8652** — portee reduite aux instances concretes de noeuds nommes
   (`unknot`, `trefoil`, `figureEight`). `decide` delegue chacune
   car le type est ferme au niveau du diagramme. 3 lemmes
   (`mirror_unknot_wf`, `mirror_trefoil_wf`, `mirror_figureEight_wf`).

3. **PR #8667** — a restaure le polymorphisme en ecrivant a la main la
   preservation du compte par etiquette `mirror_diag_preserves_count` via
   `Perm.subperm` + `le_antisymm`, reparant le `List.perm_iff_count` manquant
   de v4.31.0-rc1. 5 lemmes + 1 auxiliaire.

4. **PR #8673 (la cloture livree dans `0323b2daa`)** — a remonte
   le but au niveau `Knot.mirror.diagram.wf`, ou l'egalite de champ de
   `Knot.mirror` donne `rfl` pour `numEdges` et `crossings`, et la
   permutation par diagramme `mirror_edges_perm` remonte la permutation
   par croisement `mirrorCrossing_perm` a travers `List.Perm.flatMap`. Fermee.

**Pourquoi le remontage a travers `Knot.mirror` etait le bon mouvement :**

- `KnotDiagram.wf` est un predicat `Bool` qui ne depend que de `numEdges`
  et du multi-ensemble d'aretes — tous deux preserves par `mirror` (le premier par
  identite de champ, le second par permutation).
- L'emballage `Knot` est un lieur fin de style newtype qui donne
  a `Knot.mirror` une identite definitionnelle. Le remonter a travers n'a
  rien coute du cote `wf` (la projection `k.diagram` est defeq) et
  a donne acces a `mirrorCrossing_perm` au niveau du diagramme.
- `decide` est rejete au but polymorphe car la
  definition `KnotDiagram.wf` est une instance `decide`-able sur des listes
  d'aretes concretes, pas sur un `KnotDiagram` general. La preuve doit
  reconstruire l'argument de compte par etiquette a la main.

**Statut EPIC #8604 :** la cloture polymorphe `mirror_wf_preserves`
a ete livree dans la PR #8673. Le critere d'acceptation original #1
de l'EPIC #8604 (remplacer le champ de placeholder `hwell : True` par un champ de
bonne formation decidable) a ete re-porte : le champ placeholder `hwell` a ete
**retire**, laissant `KnotDiagram.wf` (section 11) comme unique notion de bonne
formation — un predicat autonome file *extrinsequement* comme hypothese
`(hwf : d.wf = true)` sur les mouvements de Reidemeister. Un champ intrinseque est
incompatible avec cette architecture, puisqu'un mouvement de Reidemeister
construit un diagramme intermediaire dont la bonne formation ne tient que sous
les hypotheses de la relation. La valeur de verification au noyau (`decide`
sur `unknot_wf`/`trefoil_wf`/`figureEight_wf`) est inchangee. Voir l'issue
#8604 pour la rationale de conception. Aucun `sorry` introduit. -/

end Knots

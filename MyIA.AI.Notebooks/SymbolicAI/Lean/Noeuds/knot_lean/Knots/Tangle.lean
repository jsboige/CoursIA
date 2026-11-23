/-
Knots.Tangle — Tangles à quatre extrémités (convention Conway)
==============================================================

Définition des tangles pour la théorie des nœuds en Lean 4 : un tangle est la
portion de diagramme vivant dans un disque dont le bord rencontre exactement
quatre demi-arêtes ouvertes, aux points NW, NE, SW et SE (convention de la
notation de Conway). Ce module couvre la Phase 3, case « définition des
tangles » de l'EPIC #2874.

Références :
- J. H. Conway, *An enumeration of knots and links, and some of their
  algebraic properties* (1970), Computational Problems in Abstract Algebra
- L. H. Kauffman, *On Knots* (1987), chap. 12 (tangle fractions)
- shua/leanknot (https://github.com/shua/leanknot, branche Lean 4) — la
  section « tangles » y est citée comme brique à venir, non encore intégrée

Convention : namespace `Knots`, énoncés et tactiques en anglais (compat
Mathlib 4), docstrings en français.

Prerequis Mathlib : aucun nouveau (le module se construit sur `Knots.Basic`).
-/

import Knots.Basic
import Mathlib.Tactic

/-
  Convention i18n (EPIC #4980, decision user 2026-07-04) : ce fichier est **FR canonique**,
  avec son miroir anglais dans le fichier sibling `Tangle_en.lean` (modele sibling pair
  ratifie 2026-07-04, cf `code-style.md` §Lean i18n). Les enonces de theoremes,
  les tactiques Lean, les noms de lemmes et les references Mathlib restent en anglais
  (compat Mathlib 4) ; seules les docstrings de module et ce bloc d'en-tete different
  entre les deux fichiers.
-/

namespace Knots

/-! ## 1. La structure `Tangle`

Un tangle est représenté, comme les diagrammes de `Knots.Basic`, par un code
PD : la liste de ses croisements internes. La différence avec un
`KnotDiagram` est le bord : au lieu d'une courbe fermée, quatre demi-arêtes
ouvertes terminent aux points NW, NE, SW et SE du disque.

Les quatre champs de bord portent les **étiquettes** des demi-arêtes ouvertes.
Deux points de bord portant la même étiquette dénotent un arc interne du
tangle reliant ces deux points sans rencontrer de croisement (un arc
« bord-à-bord », invisible dans le code PD qui ne code que les croisements) :
c'est le cas du tangle nul, dont les deux arcs relient NW-NE et SW-SE.
-/

structure Tangle where
  -- Croisements internes du tangle (code PD, cf `Knots.Basic` section 4)
  crossings : List PDCrossing
  /-- Étiquette de la demi-arête ouverte au point nord-ouest du disque. -/
  nw : Nat
  /-- Étiquette de la demi-arête ouverte au point nord-est du disque. -/
  ne : Nat
  /-- Étiquette de la demi-arête ouverte au point sud-ouest du disque. -/
  sw : Nat
  /-- Étiquette de la demi-arête ouverte au point sud-est du disque. -/
  se : Nat
  deriving BEq, DecidableEq, Repr

/-! ## 2. Arêtes et bonne formation

Le predicat de bonne formation transpose la parite PD de `KnotDiagram.wf`
(`Knots.Basic` section 11) au bord ouvert : **toute etiquette apparaissant**
— dans un croisement ou a un point de bord — **a exactement deux
extremites**, comptees toutes listes confondues. Une demi-arête ouverte
compte une fois dans `crossingEdges` (le croisement qu'elle rejoint) et une
fois dans `boundary` ; une arête interne compte deux fois dans
`crossingEdges` ; un arc bord-à-bord compte deux fois dans `boundary`.

Contrairement à `KnotDiagram.wf`, la contiguïté des étiquettes sur
`[1, numEdges]` n'est PAS exigée : les compositions (section 6) recollent des
paires d'étiquettes et libèrent les étiquettes sources, qui deviennent des
trous dans l'intervalle — la parité par étiquette utilisée est la condition
qui survit à la composition, et la convention des codes PD standards (labels
arbitraires) la cautionne. Les clôtures (section 7), elles, retournent dans
le modèle `KnotDiagram` contigu et y re-compressent les étiquettes
explicitement.
-/

/-- Toutes les extrémités d'arêtes portées par les croisements du tangle. -/
def Tangle.crossingEdges (t : Tangle) : List Nat :=
  t.crossings.flatMap fun c => [c.e1, c.e2, c.e3, c.e4]

/-- Les quatre étiquettes de bord, dans l'ordre NW, NE, SW, SE. -/
def Tangle.boundary (t : Tangle) : List Nat :=
  [t.nw, t.ne, t.sw, t.se]

/-- Nombre total d'arêtes : chaque arête a deux extrémités, les quatre
extrémités de bord comprises (4·n + 4 extrémités pour n croisements).
Sert de décalage pour juxtaposer deux codes PD disjoints (section 6). -/
def Tangle.numEdges (t : Tangle) : Nat :=
  (t.crossingEdges.length + 4) / 2

/-- Bonne formation d'un tangle (valeur Bool) : toute étiquette apparaissant
dans `crossingEdges ++ boundary` y apparaît exactement deux fois. -/
def Tangle.wf (t : Tangle) : Bool :=
  (t.crossingEdges ++ t.boundary).all (fun e =>
    decide ((t.crossingEdges ++ t.boundary).count e = 2))

/-! ## 3. Tangles nommés

Les trois tangles de base de l'algèbre de Conway : le tangle nul `0`
(deux arcs horizontaux), le tangle infini `∞` (deux arcs verticaux) et le
tangle `1` (un croisement vertical, générateur des tangles entiers).
-/

/-- Le tangle nul `0` de Conway : deux arcs horizontaux, aucun croisement.
L'arc supérieur relie NW à NE (étiquette 1), l'inférieur SW à SE (étiquette 2). -/
def zeroTangle : Tangle where
  crossings := []
  nw := 1
  ne := 1
  sw := 2
  se := 2

/-- Le tangle infini `∞` : deux arcs verticaux, aucun croisement.
L'arc gauche relie NW à SW (étiquette 1), le droit NE à SE (étiquette 2). -/
def infinityTangle : Tangle where
  crossings := []
  nw := 1
  ne := 2
  sw := 1
  se := 2

/-- Le tangle `1` : un croisement vertical dont les quatre bras rejoignent
les quatre points de bord. Brin dessous SW → NE (e1 = 1, e3 = 3), brin
dessus NW → SE (e2 = 2, e4 = 4). -/
def oneTangle : Tangle where
  crossings := [⟨1, 2, 3, 4⟩]
  nw := 2
  ne := 3
  sw := 1
  se := 4

/-- Le miroir du tangle `1` : même géométrie, dessus et dessous échangés
(cf `mirrorCrossing` dans `Knots.Basic`). C'est le tangle `-1`. -/
def oneTangleMirror : Tangle where
  crossings := [mirrorCrossing ⟨1, 2, 3, 4⟩]
  nw := 2
  ne := 3
  sw := 1
  se := 4

theorem zeroTangle_wf : zeroTangle.wf = true := by
  -- Deux arcs bord-a-bord : chaque etiquette compte deux fois au bord.
  decide

theorem infinityTangle_wf : infinityTangle.wf = true := by
  decide

theorem oneTangle_wf : oneTangle.wf = true := by
  -- Quatre demi-aretes ouvertes : 1 (croisement) + 1 (bord) = 2 chacune.
  decide

theorem oneTangleMirror_wf : oneTangleMirror.wf = true := by
  decide

/-! ## 4. Rotation

La rotation d'un demi-tour (symétrie centrale du disque) échange NW ↔ SE et
NE ↔ SW. Les croisements internes sont inchangés : une rotation plane
préserve le type (signe) de chaque croisement. C'est l'involution qui fonde
les fractions de Conway — la notation de Conway (case suivante de l'EPIC)
l'exploitera.

La preuve de préservation de `wf` passe par une permutation : le bord après
rotation est le bord renversé, et `crossingEdges ++ boundary` est donc
permuté — le comptage par étiquette (invariant de `List.Perm.count`) et
l'appartenance (invariant de `List.Perm.mem_iff`, lemme auxiliaire
`all_list_congr`) transportent le prédicat.
-/

/-- Lemme auxiliaire : deux listes en permutation ont même `all` dès que
les prédicats sont extensionnellement égaux. (Via `List.all_eq_true` et
`List.Perm.mem_iff` — ce Mathlib n'expose pas de `List.Perm.all`.) -/
private theorem all_list_congr {α : Type*} {l₁ l₂ : List α} (h : List.Perm l₁ l₂)
    (f g : α → Bool) (hfg : ∀ x, f x = g x) : l₁.all f = l₂.all g := by
  have hf : f = g := funext hfg
  rw [hf]
  cases h1 : l₁.all g with
  | true =>
      cases h2 : l₂.all g with
      | true => rfl
      | false =>
          have hfwd : l₂.all g = true :=
            List.all_eq_true.mpr (fun x hx =>
              List.all_eq_true.mp h1 x (h.mem_iff.mpr hx))
          rw [hfwd] at h2
          exact Bool.noConfusion h2
  | false =>
      cases h2 : l₂.all g with
      | true =>
          have hback : l₁.all g = true :=
            List.all_eq_true.mpr (fun x hx =>
              List.all_eq_true.mp h2 x (h.mem_iff.mp hx))
          rw [hback] at h1
          exact Bool.noConfusion h1
      | false => rfl

/-- Rotation d'un demi-tour : NW ↔ SE, NE ↔ SW, croisements inchangés. -/
def Tangle.rotate (t : Tangle) : Tangle where
  crossings := t.crossings
  nw := t.se
  ne := t.sw
  sw := t.ne
  se := t.nw

/-- La rotation est une involution, littéralement sur le code. -/
theorem tangle_rotate_involutive (t : Tangle) : t.rotate.rotate = t := by
  simp [Tangle.rotate]

/-- La rotation préserve la bonne formation : `crossingEdges` est inchangé
et `boundary` est renversé (donc permuté), or `List.Perm.count` transporte
le comptage par étiquette et le lemme auxiliaire `all_list_congr` transporte
le `all`. -/
theorem tangle_rotate_wf (t : Tangle) : t.rotate.wf = t.wf := by
  have hb : List.Perm t.rotate.boundary t.boundary :=
    List.reverse_perm [t.nw, t.ne, t.sw, t.se]
  have hp : List.Perm (t.rotate.crossingEdges ++ t.rotate.boundary)
      (t.crossingEdges ++ t.boundary) := hb.append_left _
  show (t.rotate.crossingEdges ++ t.rotate.boundary).all _
      = (t.crossingEdges ++ t.boundary).all _
  refine all_list_congr hp _ _ (fun l => ?_)
  rw [hp.count l]

/-! ## 5. Ré-étiquetage

Deux briques de ré-étiquetage : la substitution **simultanée** de deux
étiquettes (une fonction des étiquettes vers les étiquettes, sans
interférence entre sources — contrairement à des substitutions enchaînées),
et le décalage uniforme utilisé pour juxtaposer deux codes PD disjoints.
-/

/-- Substitution simultanée de deux étiquettes : `s₁ ↦ d₁`, `s₂ ↦ d₂`,
les autres inchangées. Les sources `s₁ ≠ s₂` rendent la substitution sans
interférence. -/
def relabel2 (s₁ d₁ s₂ d₂ l : Nat) : Nat :=
  if l = s₁ then d₁ else if l = s₂ then d₂ else l

/-- Application d'un ré-étiquetage point par point à un croisement. -/
def PDCrossing.relabel (f : Nat → Nat) (c : PDCrossing) : PDCrossing where
  e1 := f c.e1
  e2 := f c.e2
  e3 := f c.e3
  e4 := f c.e4

/-- Décalage uniforme de toutes les étiquettes d'un croisement. -/
def PDCrossing.shift (k : Nat) (c : PDCrossing) : PDCrossing where
  e1 := c.e1 + k
  e2 := c.e2 + k
  e3 := c.e3 + k
  e4 := c.e4 + k

/-- Décalage uniforme de toutes les étiquettes d'un tangle (croisements et
bord) : produit un code aux étiquettes disjointes de l'original. -/
def Tangle.shift (k : Nat) (t : Tangle) : Tangle where
  crossings := t.crossings.map (fun c => c.shift k)
  nw := t.nw + k
  ne := t.ne + k
  sw := t.sw + k
  se := t.se + k

theorem tangle_shift_numCrossings (k : Nat) (t : Tangle) :
    (t.shift k).crossings.length = t.crossings.length := by
  simp [Tangle.shift]

/-! ## 6. Composition verticale et horizontale

La composition verticale empile `t₁` au-dessus de `t₂` en recollant le bord
sud de `t₁` (SW, SE) au bord nord de `t₂` (NW, NE). La composition
horizontale (produit tensoriel) juxtapose `t₁` à gauche de `t₂` en
recollant le bord est de `t₁` au bord ouest de `t₂`.

Le recollement se fait en trois temps : décalage des étiquettes de `t₂`
hors du domaine de `t₁`, puis substitution simultanée des deux paires
d'étiquettes recollées — appliquée aux croisements de `t₂` **et** aux deux
champs de bord de `t₂` conservés dans le résultat (l'étiquette d'un bord
conservé peut précisément être une étiquette recollée, cf `0 ⊗ 0` où le NE
du résultat est le NW recollé de `t₂`). Les étiquettes sources recollées
disparaissent du code : c'est pourquoi `Tangle.wf` (section 2) n'exige pas
la contiguïté des étiquettes.

La construction est **correcte sous précondition** que les quatre bords de
`t₂` soient des demi-arêtes ouvertes distinctes (régime algébrique) : deux
points de bord de `t₂` portant la même étiquette (arc bord-à-bord nord) ne
peuvent pas être recollés à deux points distincts de `t₁` par un simple
ré-étiquetage — ce cas exige une construction par cas, hors périmètre de ce
module (cf section 8).
-/

/-- Les quatre points de bord portent des étiquettes distinctes : le
régime algébrique où chaque bord est une demi-arête ouverte rejoignant un
croisement. -/
def Tangle.hasDistinctBoundary (t : Tangle) : Bool :=
  decide (t.nw ≠ t.ne ∧ t.nw ≠ t.sw ∧ t.nw ≠ t.se ∧
          t.ne ≠ t.sw ∧ t.ne ≠ t.se ∧ t.sw ≠ t.se)

/-- Composition verticale : `t₁` au-dessus, bord sud de `t₁` recollé au
bord nord de `t₂` (SW₁ = NW₂, SE₁ = NE₂). -/
def Tangle.vcompose (t₁ t₂ : Tangle) : Tangle :=
  let t₂' := t₂.shift t₁.numEdges
  let r := relabel2 t₂'.nw t₁.sw t₂'.ne t₁.se
  { crossings := t₁.crossings ++
      t₂'.crossings.map (fun c => c.relabel r)
    nw := t₁.nw
    ne := t₁.ne
    sw := r t₂'.sw
    se := r t₂'.se }

/-- Composition horizontale (produit tensoriel) : `t₁` à gauche, bord est
de `t₁` recollé au bord ouest de `t₂` (NE₁ = NW₂, SE₁ = SW₂). -/
def Tangle.hcompose (t₁ t₂ : Tangle) : Tangle :=
  let t₂' := t₂.shift t₁.numEdges
  let r := relabel2 t₂'.nw t₁.ne t₂'.sw t₁.se
  { crossings := t₁.crossings ++
      t₂'.crossings.map (fun c => c.relabel r)
    nw := t₁.nw
    ne := r t₂'.ne
    sw := t₁.sw
    se := r t₂'.se }

theorem tangle_vcompose_numCrossings (t₁ t₂ : Tangle) :
    (Tangle.vcompose t₁ t₂).crossings.length
      = t₁.crossings.length + t₂.crossings.length := by
  simp [Tangle.vcompose, List.length_append, List.length_map,
    tangle_shift_numCrossings]

theorem tangle_hcompose_numCrossings (t₁ t₂ : Tangle) :
    (Tangle.hcompose t₁ t₂).crossings.length
      = t₁.crossings.length + t₂.crossings.length := by
  simp [Tangle.hcompose, List.length_append, List.length_map,
    tangle_shift_numCrossings]

/-- Exemple : le produit tensoriel `0 ⊗ 0` (quatre arcs parallèles) est
bien formé, et sans croisement. -/
theorem zeroTensorZero_wf : (Tangle.hcompose zeroTangle zeroTangle).wf = true := by
  decide

/-- Exemple : la composition verticale `1 ∘ 1` (deux croisements empilés)
est bien formée — c'est le tangle entier 2 de Conway. -/
theorem oneVOne_wf : (Tangle.vcompose oneTangle oneTangle).wf = true := by
  decide

/-! ## 7. Clôtures

Deux façons canoniques de fermer un tangle en diagramme fermé
(cf Kauffman, *On Knots*, chap. 12) :

- la **clôture numérateur** ferme NW-NE par un arc extérieur au-dessus du
  disque et SW-SE par un arc en dessous ;
- la **clôture dénominateur** ferme NW-SW à gauche et NE-SE à droite.

Dans le code PD, un arc de fermeture n'est pas un croisement : la fermeture
fusionne chaque paire d'étiquettes de bord par substitution simultanée,
puis **compresse canoniquement** les étiquettes — le modèle `KnotDiagram`
exige la contiguïté `[1, numEdges]` (cf `KnotDiagram.wf`), que la fusion
seule ne produit pas (le dénominateur du tangle `1` utilise `{2, 3}` avant
compression). La compression renomme chaque étiquette par son **rang
croissant** : 1 + le nombre d'étiquettes distinctes des croisements
strictement inférieures — strictement croissante, donc injective sur les
étiquettes utilisées, et `numEdges` compte ces étiquettes distinctes. (Le
`List.dedup` de Mathlib — défini via `pwFilter` — a été écarté : sa
réduction coince au noyau, mesuré au build sur `decide`.) Aucun croisement
n'est ajouté.

Le diagramme produit est dégénéré (sans croisement) pour les tangles sans
croisement — le modèle `KnotDiagram` du lac ne distingue alors pas le
nombre d'arcs résiduels (cf `KnotDiagram.wf`, branche dégénérée) ; la
clôture numérateur du tangle nul, géométriquement un entrelacs à deux
composantes, sort comme un diagramme dégénéré à zéro arête. Ce plafond du
modèle est documenté, pas maquillé.
-/

/-- Plus grande étiquette portée par les croisements du tangle (0 si aucun). -/
def Tangle.maxLabel (t : Tangle) : Nat :=
  t.crossingEdges.foldl Nat.max 0

/-- Nombre d'étiquettes distinctes parmi les extrémités de croisements —
le rang maximal que la compression canonique attribue. -/
def Tangle.numDistinctLabels (t : Tangle) : Nat :=
  ((List.range (t.maxLabel + 1)).filter (fun x => t.crossingEdges.contains x)).length

/-- Fonction d'étiquette compressée : l'étiquette `l` devient 1 + le nombre
d'étiquettes distinctes des croisements strictement inférieures à `l`.
Strictement croissante, donc injective sur les étiquettes utilisées ; la
k-ième plus petite étiquette reçoit le rang k, bord à bord avec
`numDistinctLabels`. -/
def Tangle.canonicalRelabel (t : Tangle) (l : Nat) : Nat :=
  ((List.range l).filter (fun x => t.crossingEdges.contains x)).length + 1

/-- Fusion des paires NW-NE et SW-SE dans les croisements (brique de la
clôture numérateur) : les deux étiquettes de chaque paire recollée
deviennent identiques ; les champs de bord suivent. -/
def Tangle.fuseNumerator (t : Tangle) : Tangle where
  crossings := t.crossings.map (fun c => c.relabel (relabel2 t.ne t.nw t.se t.sw))
  nw := t.nw
  ne := t.nw
  sw := t.sw
  se := t.sw

/-- Fusion des paires NW-SW et NE-SE (brique de la clôture dénominateur). -/
def Tangle.fuseDenominator (t : Tangle) : Tangle where
  crossings := t.crossings.map (fun c => c.relabel (relabel2 t.sw t.nw t.se t.ne))
  nw := t.nw
  ne := t.ne
  sw := t.nw
  se := t.ne

/-- Clôture numérateur : fusionne NW-NE et SW-SE, compresse les étiquettes,
renvoie le diagramme fermé. Aucun croisement n'est ajouté. -/
def Tangle.numeratorClosure (t : Tangle) : KnotDiagram where
  crossings :=
    t.fuseNumerator.crossings.map (fun c => c.relabel t.fuseNumerator.canonicalRelabel)
  numEdges := t.fuseNumerator.numDistinctLabels

/-- Clôture dénominateur : fusionne NW-SW et NE-SE, compresse. -/
def Tangle.denominatorClosure (t : Tangle) : KnotDiagram where
  crossings :=
    t.fuseDenominator.crossings.map
      (fun c => c.relabel t.fuseDenominator.canonicalRelabel)
  numEdges := t.fuseDenominator.numDistinctLabels

theorem numeratorClosure_numCrossings (t : Tangle) :
    (Tangle.numeratorClosure t).numCrossings = t.crossings.length := by
  simp [Tangle.numeratorClosure, Tangle.fuseNumerator, KnotDiagram.numCrossings,
    List.length_map]

theorem denominatorClosure_numCrossings (t : Tangle) :
    (Tangle.denominatorClosure t).numCrossings = t.crossings.length := by
  simp [Tangle.denominatorClosure, Tangle.fuseDenominator, KnotDiagram.numCrossings,
    List.length_map]

/-- La clôture numérateur du tangle `1` est bien formée : un croisement,
deux arêtes (chaque paire de demi-arêtes ouvertes fusionnée, puis
compressée sur `[1, 2]`). -/
theorem oneTangle_numerator_wf :
    (oneTangle.numeratorClosure).wf = true := by
  decide

/-- La clôture dénominateur du tangle `1` est bien formée (les étiquettes
`{2, 3}` de la fusion nue sont compressées sur `[1, 2]`). -/
theorem oneTangle_denominator_wf :
    (oneTangle.denominatorClosure).wf = true := by
  decide

/-- La clôture numérateur du tangle miroir `-1` est bien formée. -/
theorem oneTangleMirror_numerator_wf :
    (oneTangleMirror.numeratorClosure).wf = true := by
  decide

/-- Les clôtures du tangle nul sont dégénérées et bien formées au sens de
la branche dégénérée de `KnotDiagram.wf` (aucun croisement). -/
theorem zeroTangle_numerator_wf :
    (zeroTangle.numeratorClosure).wf = true := by
  decide

/-! ## 8. Ce que ce module ne dit pas (périmètre assumé)

Les identités de l'algèbre des tangles — `vcompose` associatif, `zeroTangle`
neutre à isotopie près, `rotate` échangeant numérateur et dénominateur —
tiennent **à isotopie près**, pas à égalité de code PD : deux tangles
composés différemment produisent des étiquetages différents du même objet
géométrique. Le lac ne dispose pas encore d'une relation d'équivalence de
tangles jouant le rôle de `ReidemeisterEquiv` pour les diagrammes ; la
livrer est le travail du grain suivant (notation de Conway, case 3 de la
Phase 3), qui posera `TangleEquiv` et réduira ces identités.

Le caractère bien formé des clôtures au sens polymorphe (pour tout tangle
bien formé à bords distincts) est également différé : il exige la stricte
monotonie du rang de compression (injectivité sur les étiquettes) et la
préservation des comptages par paires à travers la compression —
ingrédients du grain suivant.

Les théorèmes livrés ici sont donc exacts : involutivité littérale de
`rotate`, préservation polymorphe de `wf` par `rotate`, comptages de
compositions et de clôtures, bonne formation des exemples canoniques et de
leurs compositions/clôtures.
-/

end Knots

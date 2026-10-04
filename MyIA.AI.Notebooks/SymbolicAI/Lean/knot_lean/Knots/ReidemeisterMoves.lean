/-
Knots.ReidemeisterMoves — suite de mouvements vérifiable par le noyau
=====================================================================

Organe manquant nommé par l'arbitrage du 30/09 (issue #18611, Epic #1453,
point 3) : une **suite de mouvements de Reidemeister vérifiable par le noyau**,
côté combinatoire. Jusqu'ici, `ReidemeisterStep` est un `Prop` — une preuve,
impossible à exécuter ou à certifier depuis un certificat externe. Ce module
introduit la couche **donnée** :

* un inductif `ReidemeisterMove` (R1 création/suppression de boucle,
  R2 ajout/retrait de paires, R3 triangle) portant les deux diagrammes ;
* des vérificateurs `verifyR1Fwd` / `verifyR2Fwd` / `verifyR3Fwd : Bool` qui
  **décident** les relations `Reidemeister1Connected` / `Reidemeister2Connected`
  / `Reidemeister3Connected` par extraction des témoins (aucune énumération
  au-delà de l'indice de chirurgie : le kink est lu en fin de liste, le
  croisement réécrit à son index) ;
* un vérificateur de chaîne `verifyMoves : List ReidemeisterMove → … → Bool`
  et le connecteur `movesConnects d₁ d₂` (liste certifiée + well-formedness) ;
* le théorème de **soundness** `movesConnects_sound` : un certificat Bool qui
  passe le vérificateur se compile en une preuve de `ReidemeisterEquiv`.
  C'est ce qui donne aux 14 `sorry` restants du lake (Reidemeister:1053,
  Lidman:80/100, Slice:42/55/82/118, et leurs jumeaux `_en`) un langage où
  *exprimer et vérifier* leurs témoins.

Pourquoi la soundness suffit (et pourquoi la complétude est reportée) : le
vérificateur extrait les témoins exactement dans la forme de la chirurgie des
définitions (kink en dernière position, `List.set` au croisement réécrit),
donc `Reidemeister1Connected d d' → verifyR1Fwd d d' = true` doit aussi tenir ;
la preuve formelle de cette direction (complétude) est laissée en travail
ultérieur documenté, la valeur immédiate étant la direction certificat →
preuve.

Choix de structure des vérificateurs : les croisements sont lus par
`crossingAt` (`Option.getD`, défaut neutre hors bornes) et non par `match`
sur `l[i]?` — un `match` interne rendrait l'inversion de la soundness
dépendante (l'élimination d'un scrutant présent dans une hypothèse sous un
`match` échoue). Les lectures hors bornes sont de toute façon rejetées par
les équations de chirurgie, et le défaut neutre ne peut jamais fabriquer un
faux positif : chaque clause testée est réinjectée telle quelle dans le
témoin de la définition cible.

Théorèmes-témoins sur partitions d'arcs (point 1 de #18611, miroir des
`reidemeister3Connected_*`) : `SameRel` nu est **faux** sous R1/R2 — les
labels frais `n+1…` sont couverts d'un seul côté, et le renommage d'un slot
`e2`/`e4` détruit un lien de Wirtinger ancien (la classe d'arcs se raffine,
l'arc se subdivise). Ce module introduit `SameRelOn n` (restriction aux
étiquettes communes ≤ n) et `RefinesOn n` (raffinement), prouvés par `decide`
sur les trois témoins satisfiables du lake.

Convention i18n (EPIC #4980) : ce fichier est **FR canonique**, avec son
miroir anglais dans le sibling `ReidemeisterMoves_en.lean`.
-/

import Knots.Conway
import Knots.ReidemeisterInvariance

namespace Knots

/-! ## 1. `SameRelOn` et `RefinesOn` — l'invariance de partition bornée aux étiquettes communes

`SameRel` (ReidemeisterInvariance) exige la même relation de classes pour
TOUTES les étiquettes. Sous R1/R2, les labels frais `d₁.numEdges + k` ne sont
couverts que par le diagramme agrandi : `SameRel` nu échoue mécaniquement.
La bonne lecture de l'invariance est **bornée aux étiquettes communes** —
c'est la forme sous laquelle le témoin R3 de la section 5 de
`ReidemeisterInvariance.lean` se généralise aux moves qui changent
`numEdges`.
-/

/-- Deux partitions portent la même relation de classes sur les étiquettes
    `≤ n` (étiquettes communes aux deux diagrammes d'une chirurgie R1/R2).
    Affaiblissement de `SameRel` : la restriction aux anciennes étiquettes. -/
def SameRelOn (n : Nat) (P Q : List (List Nat)) : Prop :=
  ∀ ⦃x y : Nat⦄, x ≤ n → y ≤ n → (SameClass P x y ↔ SameClass Q x y)

/-- La partition `fine` raffine la partition `coarse` sur les étiquettes
    `≤ n` : toute classe commune de `fine` vit dans une classe de `coarse`.
    C'est la forme correcte de l'effet R1/R2 sur les partitions d'arcs —
    le renommage d'un slot `e2`/`e4` peut détruire un lien de Wirtinger
    ancien (raffinement), jamais en créer un. -/
def RefinesOn (n : Nat) (fine coarse : List (List Nat)) : Prop :=
  ∀ ⦃x y : Nat⦄, x ≤ n → y ≤ n → (SameClass fine x y → SameClass coarse x y)

/-- `SameRel` implique sa restriction bornée : le pont depuis le théorème
    général R3 (`Reidemeister3Connected.arcPartition_sameRel`) vers les
    théorèmes-témoins de ce module. -/
lemma SameRel.sameRelOn {P Q : List (List Nat)} (h : SameRel P Q) (n : Nat) :
    SameRelOn n P Q := fun _ _ _ _ => h _ _

/-- `SameClass` est décidable : la définition est une existence bornée dans
    une liste littérale, les `Nat` sont à égalité décidable. C'est le véhicule
    des théorèmes-témoins prouvés par `decide` (section 6). -/
instance decidableSameClass {P : List (List Nat)} {x y : Nat} :
    Decidable (SameClass P x y) := by
  unfold SameClass
  infer_instance

/-- Réduction d'un quantificateur borné `∀ x ≤ n` à une énumération finie :
    le véhicule des théorèmes-témoins prouvés par `decide` (le domaine des
    partitions est littéral, seul le quantificateur est infini). -/
lemma forall_le_iff_all_range {n : Nat} {p : Nat → Prop} [DecidablePred p] :
    (∀ x, x ≤ n → p x) ↔ (List.range (n + 1)).all (fun x => decide (p x)) = true := by
  constructor
  · intro h
    exact List.all_eq_true.mpr fun x hx =>
      decide_eq_true (h x (Nat.lt_succ_iff.mp (List.mem_range.mp hx)))
  · intro h x hx
    exact of_decide_eq_true
      (List.all_eq_true.mp h x (List.mem_range.mpr (Nat.lt_succ_iff.mpr hx)))

/-! ## 2. L'inductif `ReidemeisterMove` — le mouvement comme donnée

`ReidemeisterStep` est un `Prop` : il vit dans `Prop`, éliminé uniquement par
les preuves. L'organe demandé par #18611 est la version **donnée** du pas —
constructible, sérialisable, vérifiable par une fonction `Bool`. Chaque
constructeur porte les deux diagrammes ; la nature du mouvement (R1 boucle,
R2 paire, R3 triangle) est le constructeur lui-même.
-/

/-- Un mouvement de Reidemeister comme **donnée** : la nature du mouvement
    (boucle R1, paire R2, triangle R3) et les diagrammes source/cible. La
    well-formedness n'est PAS un champ — elle se vérifie (`verifyMove`) et se
    certifie (`movesConnects_sound`), calque du choix de conception de
    `KnotDiagram.wf` (Basic.lean, issue #8604). -/
inductive ReidemeisterMove : Type where
  /-- Création/suppression d'une boucle (kink). -/
  | r1 (source target : KnotDiagram) : ReidemeisterMove
  /-- Ajout/retrait d'une paire de croisements (bigon). -/
  | r2 (source target : KnotDiagram) : ReidemeisterMove
  /-- Glissement triangulaire. -/
  | r3 (source target : KnotDiagram) : ReidemeisterMove
  deriving Repr

/-- Diagramme source du mouvement (projection non générée automatiquement :
    un inductif à trois constructeurs n'a pas de champs communs projectables,
    la projection se définit par filtrage). -/
def ReidemeisterMove.source : ReidemeisterMove → KnotDiagram
  | .r1 s _ => s
  | .r2 s _ => s
  | .r3 s _ => s

/-- Diagramme cible du mouvement. -/
def ReidemeisterMove.target : ReidemeisterMove → KnotDiagram
  | .r1 _ t => t
  | .r2 _ t => t
  | .r3 _ t => t

/-! ## 3. Les vérificateurs par mouvement

Principe d'extraction (pas d'énumération) : la chirurgie des définitions
connectées place le kink en **dernière** position de `d₂.crossings` et
réécrit le croisement d'extrémité **à son index** via `List.set`. Le
vérificateur lit donc le kink par `getLast?`, le croisement réécrit par
`crossingAt`, et n'énumère que l'indice `i` — polynomial par pas, adapté
aux petits diagrammes visés par #18611.

Les relations `isRenameOf` / `isDoubleRenameOf` / `hasEdge` sont des `Prop`
définies par conjonctions/disjonctions d'égalités `Nat` : sans instance
`Decidable` déclarée, `decide` ne les voit pas (l'instance ne traverse pas la
delta-réduction d'une `def`). Les trois instances ci-dessous les exposent —
même remède que le `unfold … ; decide` des témoins de `Reidemeister.lean`,
sous forme réutilisable.
-/

/-- Lecture sûre d'un croisement par index : le croisement à l'indice `i`
    s'il existe, sinon un défaut neutre. Évite les `match` internes dans les
    vérificateurs (inversion soundness non dépendante) ; une lecture hors
    bornes ne peut pas produire de faux positif car chaque clause testée est
    réinjectée telle quelle dans le témoin de la définition cible. -/
def crossingAt (l : List PDCrossing) (i : Nat) : PDCrossing :=
  l[i]?.getD ⟨0, 0, 0, 0⟩

/-- `PDCrossing.isRenameOf` est décidable (conjonctions/disjonctions
    d'égalités `Nat` après delta-réduction). -/
instance decidableIsRenameOf (Y' c : PDCrossing) (a b : Nat) :
    Decidable (Y'.isRenameOf c a b) := by
  unfold PDCrossing.isRenameOf
  infer_instance

/-- `PDCrossing.isDoubleRenameOf` est décidable. -/
instance decidableIsDoubleRenameOf (Y' c : PDCrossing) (a o₁ o₂ : Nat) :
    Decidable (Y'.isDoubleRenameOf c a o₁ o₂) := by
  unfold PDCrossing.isDoubleRenameOf
  infer_instance

/-- `PDCrossing.hasEdge` est décidable. -/
instance decidableHasEdge (c : PDCrossing) (z : Nat) :
    Decidable (c.hasEdge z) := by
  unfold PDCrossing.hasEdge
  infer_instance

/-- Vérificateur Bool de `Reidemeister1Connected d d'` (direction avant
    uniquement : `d'` est le diagramme agrandi du kink). Extrait `a` du kink
    terminal `⟨a, n+1, n+2, n+2⟩`, `Y'` du croisement à l'indice énuméré,
    puis re-teste chaque clause de la définition : `wf` des deux côtés,
    `numEdges + 2`, bornes et appartenance de `a`, arc propre (`∃ j ≠ i`),
    `isRenameOf`, et l'équation de chirurgie via `dropLast`. -/
def verifyR1Fwd (d d' : KnotDiagram) : Bool :=
  d.wf && d'.wf && decide (d'.numEdges = d.numEdges + 2) &&
  match d'.crossings.getLast? with
  | none => false
  | some K =>
    decide (K.e2 = d.numEdges + 1 ∧ K.e3 = d.numEdges + 2 ∧ K.e4 = d.numEdges + 2 ∧
      1 ≤ K.e1 ∧ K.e1 ≤ d.numEdges ∧ K.e1 ∈ d.edges) &&
    (List.range d.crossings.length).any fun i =>
      decide (d'.crossings.dropLast = d.crossings.set i (crossingAt d'.crossings.dropLast i)) &&
      decide ((crossingAt d'.crossings.dropLast i).isRenameOf
        (crossingAt d.crossings i) K.e1 (d.numEdges + 1)) &&
      (List.range d.crossings.length).any fun j =>
        decide (j ≠ i ∧ (crossingAt d.crossings j).hasEdge K.e1)

/-- Vérificateur Bool de `Reidemeister2Connected d d'` (direction avant).
    Extrait `a` des deux bigons terminaux `⟨a, n+1, n+1, n+2⟩` et
    `⟨a, n+3, n+3, n+4⟩`, `Y'` du croisement à l'indice énuméré, puis
    re-teste chaque clause : `wf`, `numEdges + 4`, bornes et appartenance
    de `a`, `isDoubleRenameOf`, chirurgie via double `dropLast`. -/
def verifyR2Fwd (d d' : KnotDiagram) : Bool :=
  d.wf && d'.wf && decide (d'.numEdges = d.numEdges + 4) &&
  match d'.crossings.getLast? with
  | none => false
  | some K₂ =>
    decide (K₂.e2 = d.numEdges + 3 ∧ K₂.e3 = d.numEdges + 3 ∧ K₂.e4 = d.numEdges + 4 ∧
      1 ≤ K₂.e1 ∧ K₂.e1 ≤ d.numEdges ∧ K₂.e1 ∈ d.edges) &&
    match d'.crossings.dropLast.getLast? with
    | none => false
    | some K₁ =>
      decide (K₁.e1 = K₂.e1 ∧ K₁.e2 = d.numEdges + 1 ∧ K₁.e3 = d.numEdges + 1 ∧
        K₁.e4 = d.numEdges + 2) &&
      (List.range d.crossings.length).any fun i =>
        decide (d'.crossings.dropLast.dropLast =
          d.crossings.set i (crossingAt d'.crossings.dropLast.dropLast i)) &&
        decide ((crossingAt d'.crossings.dropLast.dropLast i).isDoubleRenameOf
          (crossingAt d.crossings i) K₂.e1 (d.numEdges + 2) (d.numEdges + 4))

/-- Vérificateur Bool de `Reidemeister3Connected d d'` (direction avant).
    Énumère l'indice `i` du sommet du triangle, lit les trois croisements
    consécutifs de `d` (layout X `⟨a₂,a₁,g₁,g₂⟩`, `⟨a₃,g₁,g₃,b₃⟩`,
    `⟨g₃,g₂,b₂,b₁⟩`), contrôle le partage des labels internes entre les
    trois sommets (égalités de champs), le `Nodup` des neuf labels, et
    l'équation de chirurgie du triple `List.set`. -/
def verifyR3Fwd (d d' : KnotDiagram) : Bool :=
  d.wf && d'.wf && decide (d.crossings.length = d'.crossings.length) &&
  decide (d.numEdges = d'.numEdges) &&
  (List.range d.crossings.length).any fun i =>
    decide (i + 2 < d.crossings.length ∧
      (crossingAt d.crossings (i + 1)).e2 = (crossingAt d.crossings i).e3 ∧
      (crossingAt d.crossings (i + 2)).e1 = (crossingAt d.crossings (i + 1)).e3 ∧
      (crossingAt d.crossings (i + 2)).e2 = (crossingAt d.crossings i).e4 ∧
      List.Nodup [(crossingAt d.crossings i).e1, (crossingAt d.crossings i).e2,
        (crossingAt d.crossings (i + 1)).e1, (crossingAt d.crossings (i + 1)).e4,
        (crossingAt d.crossings (i + 2)).e3, (crossingAt d.crossings (i + 2)).e4,
        (crossingAt d.crossings i).e3, (crossingAt d.crossings i).e4,
        (crossingAt d.crossings (i + 1)).e3] ∧
      d'.crossings = ((d.crossings.set i
          ⟨(crossingAt d.crossings (i + 1)).e1, (crossingAt d.crossings (i + 1)).e4,
            (crossingAt d.crossings (i + 1)).e3, (crossingAt d.crossings i).e3⟩).set (i + 1)
        ⟨(crossingAt d.crossings (i + 1)).e3, (crossingAt d.crossings i).e2,
          (crossingAt d.crossings (i + 2)).e3, (crossingAt d.crossings i).e4⟩).set (i + 2)
        ⟨(crossingAt d.crossings i).e3, (crossingAt d.crossings i).e4,
          (crossingAt d.crossings i).e1, (crossingAt d.crossings (i + 2)).e4⟩)

/-- Vérificateur Bool d'un pas élémentaire, direction-neutral : la relation
    `Reidemeister1Connected` est bipolar (le move et son inverse), le pas
    accepte l'une ou l'autre orientation — miroir exact de la disjonction
    des constructeurs de `ReidemeisterStep`. -/
def verifyR1 (d d' : KnotDiagram) : Bool := verifyR1Fwd d d' || verifyR1Fwd d' d

/-- Pendant R2 de `verifyR1`. -/
def verifyR2 (d d' : KnotDiagram) : Bool := verifyR2Fwd d d' || verifyR2Fwd d' d

/-- Vérificateur Bool du move triangulaire. La direction inverse
    (`Reidemeister3ConnectedInv`) réécrit le triangle Y en X — acceptée en
    testant les deux orientations du layout X. -/
def verifyR3 (d d' : KnotDiagram) : Bool := verifyR3Fwd d d' || verifyR3Fwd d' d

/-- Vérificateur Bool d'un mouvement : `true` ssi le mouvement est un pas
    de Reidemeister **connecté** bien formé dans l'une ou l'autre direction. -/
def verifyMove (m : ReidemeisterMove) : Bool :=
  match m with
  | .r1 src tgt => verifyR1 src tgt
  | .r2 src tgt => verifyR2 src tgt
  | .r3 src tgt => verifyR3 src tgt

/-! ## 4. La chaîne vérifiée — `verifyMoves` et `movesConnects`

Une suite de mouvements connecte `d₁` à `d₂` si elle forme une chaîne
continue dont chaque maillon passe `verifyMove`. La well-formedness n'est
pas une donnée de la liste : elle **est** le `= true` du vérificateur.
-/

/-- Vérifie qu'une suite de mouvements forme une chaîne continue de `start`
    à `end` dont chaque maillon est un pas de Reidemeister connecté bien
    formé. Cas de base : la liste vide exige `start = end` (réflexivité). -/
def verifyMoves : List ReidemeisterMove → KnotDiagram → KnotDiagram → Bool
  | [], start, end_ => decide (start = end_)
  | m :: ms, start, end_ =>
    decide (m.source = start) && verifyMove m && verifyMoves ms m.target end_

/-- Le connecteur de #18611 : `movesConnects d₁ d₂` est la proposition
    « la liste `ms` est un certificat de well-formedness reliant `d₁` à `d₂` »
    — liste certifiée de mouvements, vérifiable par le noyau. -/
def movesConnects (ms : List ReidemeisterMove) (d₁ d₂ : KnotDiagram) : Prop :=
  verifyMoves ms d₁ d₂ = true

/-! ## 5. Soundness — un certificat Bool se compile en preuve

Le théorème central de l'organe : `verifyMoves ms d₁ d₂ = true` implique
`ReidemeisterEquiv d₁ d₂`. La preuve recompose la chaîne maillon par
maillon ; chaque maillon reconstruit le témoin existentiel de la définition
connectée à partir des données extraites par le vérificateur. Deux briques
d'inversion : le split du `getLast?` du kink se fait AVANT le dépliage du
vérificateur (le scrutant n'est alors dans aucune hypothèse, l'élimination
est libre), et les lectures indexées se convertissent par
`List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩` (aucun `cases` sur un scrutant
présent dans une hypothèse). La reconstitution « préfixe réécrit ++ kink(s) »
s'appuie sur `List.getLast?_eq_some_iff` (`l.getLast? = some K ↔ ∃ M,
l = M ++ [K]`).
-/

/-- Soundness du vérificateur R1 (direction avant) : si le vérificateur
    accepte `(d, d')`, alors `Reidemeister1Connected d d'` tient — le témoin
    existentiel de la définition (indice, arc `a`, croisement réécrit `Y'`,
    renommage `ρ`, arc propre `j`) est reconstruit depuis les données que le
    vérificateur a extraites. -/
theorem verifyR1Fwd_sound {d d' : KnotDiagram} (h : verifyR1Fwd d d' = true) :
    Reidemeister1Connected d d' := by
  cases hK : d'.crossings.getLast? with
  | none => simp [verifyR1Fwd, hK] at h
  | some K =>
    simp only [verifyR1Fwd, hK, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hwf1, hwf2⟩, hn⟩, hform, hanyi⟩ := h
    obtain ⟨hb, hc, hc', ha1, han, hmem⟩ := of_decide_eq_true hform
    rw [List.any_eq_true] at hanyi
    obtain ⟨i, hi_mem, hbody⟩ := hanyi
    have hi : i < d.crossings.length := List.mem_range.mp hi_mem
    have hY2 : d.crossings[i]? = some d.crossings[i] :=
      List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
    simp only [Bool.and_eq_true, crossingAt, hY2, Option.getD_some] at hbody
    obtain ⟨⟨hsurg, hrename⟩, hanyj⟩ := hbody
    rw [List.any_eq_true] at hanyj
    obtain ⟨j, hj_mem, hj_body⟩ := hanyj
    have hj : j < d.crossings.length := List.mem_range.mp hj_mem
    have hcj : d.crossings[j]? = some d.crossings[j] :=
      List.getElem?_eq_some_iff.mpr ⟨hj, rfl⟩
    simp only [crossingAt, hcj, Option.getD_some] at hj_body
    obtain ⟨hjne, hhas⟩ := of_decide_eq_true hj_body
    -- la forme du kink reconstituée (eta structurel puis champs)
    have heta : K = ⟨K.e1, K.e2, K.e3, K.e4⟩ := rfl
    have hKform : K = ⟨K.e1, d.numEdges + 1, d.numEdges + 2, d.numEdges + 2⟩ :=
      heta.trans (by simp [hb, hc, hc'])
    -- reconstitution de la chirurgie : préfixe réécrit ++ kink
    obtain ⟨M, hM⟩ := List.getLast?_eq_some_iff.mp hK
    set Y' := crossingAt d'.crossings.dropLast i with hY'def
    have hsurg' : d'.crossings.dropLast = d.crossings.set i Y' :=
      of_decide_eq_true hsurg
    have hMeq : M = d.crossings.set i Y' := by
      have h2 : (M ++ [K]).dropLast = d.crossings.set i Y' := by
        rw [← hM]; exact hsurg'
      simp at h2
      exact h2
    have hchirurgie : d'.crossings =
        d.crossings.set i Y' ++
        [⟨K.e1, d.numEdges + 1, d.numEdges + 2, d.numEdges + 2⟩] := by
      rw [hM, hMeq, hKform]
    have hρ : Fin d.numEdges ↪ Fin (d.numEdges + 2) :=
      ⟨fun k => ⟨k.val, by omega⟩, fun x y hxy => by
        injection hxy with hv; exact Fin.ext hv⟩
    exact ⟨hwf1, hwf2, ⟨⟨i, hi⟩, K.e1, Y', hρ,
      ha1, han, hmem,
      ⟨⟨j, hj⟩, Fin.ne_of_val_ne hjne, hhas⟩,
      of_decide_eq_true hrename, hchirurgie,
      of_decide_eq_true hn⟩⟩

/-- Soundness du vérificateur R2 (direction avant) : même mécanique que R1
    avec les deux bigons terminaux et le double `dropLast`. -/
theorem verifyR2Fwd_sound {d d' : KnotDiagram} (h : verifyR2Fwd d d' = true) :
    Reidemeister2Connected d d' := by
  cases hK₂ : d'.crossings.getLast? with
  | none => simp [verifyR2Fwd, hK₂] at h
  | some K₂ =>
    cases hK₁ : d'.crossings.dropLast.getLast? with
    | none => simp [verifyR2Fwd, hK₂, hK₁] at h
    | some K₁ =>
      simp only [verifyR2Fwd, hK₂, hK₁, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hwf1, hwf2⟩, hn⟩, hform₂, hform₁, hanyi⟩ := h
      obtain ⟨hb₂, hc₂, hd₂, ha1, han, hmem⟩ := of_decide_eq_true hform₂
      obtain ⟨ha_eq, hb₁, hc₁, hd₁⟩ := of_decide_eq_true hform₁
      rw [List.any_eq_true] at hanyi
      obtain ⟨i, hi_mem, hbody⟩ := hanyi
      have hi : i < d.crossings.length := List.mem_range.mp hi_mem
      have hY2 : d.crossings[i]? = some d.crossings[i] :=
        List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
      simp only [Bool.and_eq_true, crossingAt, hY2, Option.getD_some] at hbody
      obtain ⟨hsurg, hrename⟩ := hbody
      -- formes des deux kinks reconstituées (eta structurel puis champs)
      have heta₁ : K₁ = ⟨K₁.e1, K₁.e2, K₁.e3, K₁.e4⟩ := rfl
      have hK₁form : K₁ = ⟨K₂.e1, d.numEdges + 1, d.numEdges + 1, d.numEdges + 2⟩ :=
        heta₁.trans (by simp [ha_eq, hb₁, hc₁, hd₁])
      have heta₂ : K₂ = ⟨K₂.e1, K₂.e2, K₂.e3, K₂.e4⟩ := rfl
      have hK₂form : K₂ = ⟨K₂.e1, d.numEdges + 3, d.numEdges + 3, d.numEdges + 4⟩ :=
        heta₂.trans (by simp [hb₂, hc₂, hd₂])
      -- les deux niveaux de reconstitution
      set Y' := crossingAt d'.crossings.dropLast.dropLast i with hY'def
      obtain ⟨M₂, hM₂⟩ := List.getLast?_eq_some_iff.mp hK₂
      have hdrop₂ : d'.crossings.dropLast = M₂ := by rw [hM₂]; simp
      obtain ⟨M₁, hM₁⟩ := List.getLast?_eq_some_iff.mp hK₁
      have hM₁eq : M₁ = d.crossings.set i Y' := by
        have h2 : (M₁ ++ [K₁]).dropLast = d.crossings.set i Y' := by
          rw [← hM₁]; exact of_decide_eq_true hsurg
        simp at h2
        exact h2
      have hM₂eq : M₂ = d.crossings.set i Y' ++
          [⟨K₂.e1, d.numEdges + 1, d.numEdges + 1, d.numEdges + 2⟩] := by
        rw [← hdrop₂, hM₁, hM₁eq, hK₁form]
      have hchirurgie : d'.crossings =
          d.crossings.set i Y' ++
          [⟨K₂.e1, d.numEdges + 1, d.numEdges + 1, d.numEdges + 2⟩,
           ⟨K₂.e1, d.numEdges + 3, d.numEdges + 3, d.numEdges + 4⟩] := by
        rw [hM₂, hM₂eq, hK₂form, List.append_assoc]
        rfl
      have hρ : Fin d.numEdges ↪ Fin (d.numEdges + 4) :=
        ⟨fun k => ⟨k.val, by omega⟩, fun x y hxy => by
          injection hxy with hv; exact Fin.ext hv⟩
      exact ⟨hwf1, hwf2, ⟨⟨i, hi⟩, K₂.e1, Y', hρ,
        ha1, han, hmem, of_decide_eq_true hrename, hchirurgie,
        of_decide_eq_true hn⟩⟩

/-- Soundness du vérificateur R3 (direction avant) : les trois lectures
    indexées fournissent les neuf labels du triangle, les égalités de
    partage des labels internes et le `Nodup` sont décidés, et l'équation du
    triple `List.set` est la chirurgie même de la définition. -/
theorem verifyR3Fwd_sound {d d' : KnotDiagram} (h : verifyR3Fwd d d' = true) :
    Reidemeister3Connected d d' := by
  simp only [verifyR3Fwd, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hwf1, hwf2⟩, hlen⟩, hedges⟩, hany⟩ := h
  rw [List.any_eq_true] at hany
  obtain ⟨i, hi_mem, hbody⟩ := hany
  have hi : i < d.crossings.length := List.mem_range.mp hi_mem
  obtain ⟨hi2, he₁, he₂, he₃, hnodup, hchirurgie⟩ := of_decide_eq_true hbody
  have hilt : i + 1 < d.crossings.length := by omega
  have h₁ : d.crossings[i]? = some d.crossings[i] :=
    List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
  have h₂ : d.crossings[i + 1]? = some d.crossings[i + 1] :=
    List.getElem?_eq_some_iff.mpr ⟨hilt, rfl⟩
  have h₃ : d.crossings[i + 2]? = some d.crossings[i + 2] :=
    List.getElem?_eq_some_iff.mpr ⟨hi2, rfl⟩
  -- réduction des lectures indexées en accès directs
  have hval₁ : crossingAt d.crossings i = d.crossings[i] := by
    simp only [crossingAt, h₁, Option.getD_some]
  have hval₂ : crossingAt d.crossings (i + 1) = d.crossings[i + 1] := by
    simp only [crossingAt, h₂, Option.getD_some]
  have hval₃ : crossingAt d.crossings (i + 2) = d.crossings[i + 2] := by
    simp only [crossingAt, h₃, Option.getD_some]
  simp only [hval₁, hval₂, hval₃] at he₁ he₂ he₃ hnodup hchirurgie
  -- les neuf labels sont les champs des trois croisements ; les équations de
  -- lecture se ferment par eta structurel, le partage des labels internes
  -- (he₁ he₂ he₃) réécrit les slots concernés
  have hget₁ : d.crossings[i] =
      ⟨(d.crossings[i]).e1, (d.crossings[i]).e2, (d.crossings[i]).e3,
        (d.crossings[i]).e4⟩ := rfl
  have hget₂ : d.crossings[i + 1] =
      ⟨(d.crossings[i + 1]).e1, (d.crossings[i]).e3, (d.crossings[i + 1]).e3,
        (d.crossings[i + 1]).e4⟩ := by rw [← he₁]
  have hget₃ : d.crossings[i + 2] =
      ⟨(d.crossings[i + 1]).e3, (d.crossings[i]).e4, (d.crossings[i + 2]).e3,
        (d.crossings[i + 2]).e4⟩ := by rw [← he₂, ← he₃]
  exact ⟨hwf1, hwf2, of_decide_eq_true hlen, of_decide_eq_true hedges, i, hi2,
    (d.crossings[i]).e2, (d.crossings[i]).e1, (d.crossings[i + 1]).e1,
    (d.crossings[i + 2]).e4, (d.crossings[i + 2]).e3, (d.crossings[i + 1]).e4,
    (d.crossings[i]).e3, (d.crossings[i]).e4, (d.crossings[i + 1]).e3,
    hnodup, hget₁, hget₂, hget₃, hchirurgie⟩

/-- Soundness du vérificateur de pas : un mouvement accepté est un
    `ReidemeisterStep` (dans l'une ou l'autre direction, comme le
    constructeur correspondant). -/
theorem verifyMove_sound {m : ReidemeisterMove} (h : verifyMove m = true) :
    ReidemeisterStep m.source m.target := by
  cases m with
  | r1 d d' =>
    simp only [ReidemeisterMove.source, ReidemeisterMove.target, verifyMove,
      verifyR1] at h ⊢
    rcases Bool.or_eq_true_iff.mp h with h' | h'
    · exact ReidemeisterStep.r1 (Or.inl (verifyR1Fwd_sound h'))
    · exact ReidemeisterStep.r1 (Or.inr (verifyR1Fwd_sound h'))
  | r2 d d' =>
    simp only [ReidemeisterMove.source, ReidemeisterMove.target, verifyMove,
      verifyR2] at h ⊢
    rcases Bool.or_eq_true_iff.mp h with h' | h'
    · exact ReidemeisterStep.r2 (Or.inl (verifyR2Fwd_sound h'))
    · exact ReidemeisterStep.r2 (Or.inr (verifyR2Fwd_sound h'))
  | r3 d d' =>
    simp only [ReidemeisterMove.source, ReidemeisterMove.target, verifyMove,
      verifyR3] at h ⊢
    rcases Bool.or_eq_true_iff.mp h with h' | h'
    · exact ReidemeisterStep.r3 (Or.inl (verifyR3Fwd_sound h'))
    · exact ReidemeisterStep.r3 (Or.inr (verifyR3Fwd_sound h'))

/-- Soundness du vérificateur de chaîne : une suite acceptée est une preuve
    de `ReidemeisterEquiv` — l'organe complet de #18611, point 2. -/
theorem verifyMoves_sound {ms : List ReidemeisterMove} {d₁ d₂ : KnotDiagram}
    (h : verifyMoves ms d₁ d₂ = true) : ReidemeisterEquiv d₁ d₂ := by
  induction ms generalizing d₁ with
  | nil =>
    have := of_decide_eq_true h
    subst this
    exact ReidemeisterEquiv.refl _
  | cons m ms ih =>
    simp only [verifyMoves, Bool.and_eq_true] at h
    obtain ⟨⟨hsrc, hmove⟩, hrest⟩ := h
    have hsrc' := of_decide_eq_true hsrc
    rw [← hsrc']
    exact ReidemeisterEquiv.trans
      (ReidemeisterEquiv.step (verifyMove_sound hmove)) (ih hrest)

/-- **Le théorème de l'organe** : un certificat `List ReidemeisterMove` qui
    passe le vérificateur se compile en preuve d'équivalence de Reidemeister.
    La moitié combinatoire (⇐) du `reidemeister_theorem` réenoncée : sans
    variétés PL ni isotopie ambiante, un chemin certifié Bool suffit à
    établir `KnotEquiv`. -/
theorem movesConnects_sound {ms : List ReidemeisterMove} {d₁ d₂ : KnotDiagram}
    (h : movesConnects ms d₁ d₂) : ReidemeisterEquiv d₁ d₂ :=
  verifyMoves_sound h

/-! ## 6. Théorèmes-témoins sur partitions d'arcs (point 1 de #18611)

Miroir des `reidemeister3Connected_*` pour R1 puis R2, prouvés par
`decide` sur les témoins satisfiables du lake. Pourquoi des témoins et pas
des théorèmes généraux : le renommage d'un slot `e2`/`e4` détruit un lien
de Wirtinger ancien (la classe d'arcs se raffine), donc l'égalité de relation
(`SameRelOn`) n'est vraie que lorsque le renommage porte sur `e1`/`e3` —
c'est le cas du témoin R1 ; le témoin R2 illustre le raffinement général
(`RefinesOn`), qui est la forme correcte de l'effet des moves de
subdivision sur les partitions d'arcs.
-/

/-- Témoin R1 : sur la paire `reidemeister1Connected_satisfiable`, la
    relation de classes d'arcs est préservée sur les étiquettes communes
    (le renommage du témoin porte sur `e1`, qui ne compte pas dans le repli
    `arcPartition`). -/
theorem reidemeister1Connected_arcPartition_sameRelOn_witness :
    SameRelOn 4
      (arcPartition { crossings := [⟨1,2,3,4⟩, ⟨1,2,3,4⟩], numEdges := 4 })
      (arcPartition { crossings := [⟨1,2,3,4⟩, ⟨5,2,3,4⟩, ⟨1,5,6,6⟩],
                      numEdges := 6 }) := by
  intro x y hx hy
  have hall : ((List.range 5).all fun x =>
    (List.range 5).all fun y =>
      decide (SameClass (arcPartition
          { crossings := [⟨1,2,3,4⟩, ⟨1,2,3,4⟩], numEdges := 4 }) x y ↔
        SameClass (arcPartition
          { crossings := [⟨1,2,3,4⟩, ⟨5,2,3,4⟩, ⟨1,5,6,6⟩], numEdges := 6 }) x y)) = true := by
    decide
  have hx5 := List.all_eq_true.mp hall x (List.mem_range.mpr (by omega))
  exact of_decide_eq_true (List.all_eq_true.mp hx5 y (List.mem_range.mpr (by omega)))

/-- Témoin R2 : la partition d'arcs du diagramme agrandi **raffine** celle
    du diagramme source sur les étiquettes communes — le renommage du slot
    `e2` (paire `(1,3)` devenue `(8,3)`) détache l'arc `1` de la classe
    `{1,3,4}` ; aucune classe ancienne n'est fusionnée. C'est la forme
    générale correcte de l'effet R1/R2 sur les partitions d'arcs. -/
theorem reidemeister2Connected_arcPartition_refinesOn_witness :
    RefinesOn 4
      (arcPartition { crossings := [⟨6,8,2,3⟩, ⟨2,3,4,4⟩, ⟨1,5,5,6⟩, ⟨1,7,7,8⟩],
                      numEdges := 8 })
      (arcPartition { crossings := [⟨1,1,2,3⟩, ⟨2,3,4,4⟩], numEdges := 4 }) := by
  intro x y hx hy hxy
  have hall : ((List.range 5).all fun x =>
    (List.range 5).all fun y =>
      decide (¬ SameClass (arcPartition
          { crossings := [⟨6,8,2,3⟩, ⟨2,3,4,4⟩, ⟨1,5,5,6⟩, ⟨1,7,7,8⟩],
            numEdges := 8 }) x y ∨
        SameClass (arcPartition
          { crossings := [⟨1,1,2,3⟩, ⟨2,3,4,4⟩], numEdges := 4 }) x y)) = true := by
    decide
  have hx5 := List.all_eq_true.mp hall x (List.mem_range.mpr (by omega))
  rcases of_decide_eq_true (List.all_eq_true.mp hx5 y (List.mem_range.mpr (by omega))) with h' | h'
  · exact absurd hxy h'
  · exact h'

/-- Témoin R3 : instance bornée du théorème général
    `Reidemeister3Connected.arcPartition_sameRel` (le move triangulaire
    préserve `numEdges`, donc `SameRel` nu se restreint trivialement). -/
theorem reidemeister3Connected_arcPartition_sameRelOn_witness :
    SameRelOn 10
      (arcPartition { crossings := [⟨1,2,7,8⟩, ⟨3,7,9,4⟩, ⟨9,8,5,6⟩,
                       ⟨1,2,10,10⟩, ⟨3,4,5,6⟩], numEdges := 10 })
      (arcPartition { crossings := [⟨3,4,9,7⟩, ⟨9,2,5,8⟩, ⟨7,8,1,6⟩,
                       ⟨1,2,10,10⟩, ⟨3,4,5,6⟩], numEdges := 10 }) :=
  (reidemeister3Connected_satisfiable.arcPartition_sameRel).sameRelOn 10

/-- Démonstration end-to-end de l'organe sur le témoin R3 : le certificat
    unaire `[r3 X Y]` passe le vérificateur (kernel `decide` : lecture des
    trois croisements, `Nodup`, triple `List.set` sur littéraux), et
    `movesConnects_sound` le compile en `ReidemeisterEquiv X Y`. -/
theorem reidemeister3Connected_witness_movesConnects :
    movesConnects
      [ReidemeisterMove.r3
        { crossings := [⟨1,2,7,8⟩, ⟨3,7,9,4⟩, ⟨9,8,5,6⟩,
                         ⟨1,2,10,10⟩, ⟨3,4,5,6⟩], numEdges := 10 }
        { crossings := [⟨3,4,9,7⟩, ⟨9,2,5,8⟩, ⟨7,8,1,6⟩,
                         ⟨1,2,10,10⟩, ⟨3,4,5,6⟩], numEdges := 10 }]
      { crossings := [⟨1,2,7,8⟩, ⟨3,7,9,4⟩, ⟨9,8,5,6⟩,
                       ⟨1,2,10,10⟩, ⟨3,4,5,6⟩], numEdges := 10 }
      { crossings := [⟨3,4,9,7⟩, ⟨9,2,5,8⟩, ⟨7,8,1,6⟩,
                       ⟨1,2,10,10⟩, ⟨3,4,5,6⟩], numEdges := 10 } := by
  unfold movesConnects
  decide

/-! ## 7. Complétude (⇐) — le témoin canonique tranche

Le header documente la complétude (`Reidemeister1Connected d d' →
verifyR1Fwd d d' = true`) comme travail ultérieur, appuyée sur un argument
de plausibilité : le vérificateur extrait les témoins exactement dans la
forme de la chirurgie des définitions. Les deux examples bornés suivants
**mesurent** cet alignement sur le cas décisif soulevé par le forensic du
03/10 (#18611) : le kink NON terminal. Verdict mesuré : les deux langages
parlent la même chirurgie — la complétude par maillon est un **lemme à
prouver** (induction sur l'existentiel de la définition), pas un énoncé
à affaiblir. -/

/-- Direction complétude tenue sur le témoin canonique : la paire (d₁, d₂)
    dont `reidemeister1Connected_satisfiable` (Reidemeister.lean) prouve
    qu'elle satisfait la Prop passe le vérificateur Bool. Côté Prop le kink
    est ajouté par `++ [C]` (donc toujours en fin de liste), côté Bool il
    est lu par `getLast?` — même forme, kernel `decide` rend vrai. -/
example : verifyR1Fwd
    { crossings := [⟨1,2,3,4⟩, ⟨1,2,3,4⟩], numEdges := 4 }
    { crossings := [⟨1,2,3,4⟩, ⟨5,2,3,4⟩, ⟨1,5,6,6⟩], numEdges := 6 }
    = true := by decide

/-- Le kink NON terminal n'est pas un trou de complétude : la Prop
    l'exclut d'office (la chirurgie est `set i Y' ++ [C]`, le kink est
    TOUJOURS en fin de liste) et le vérificateur le refuse pareillement.
    Ici les croisements sont exactement ceux du témoin ci-dessus, seul
    l'ordre diffère : le kink `⟨1,5,6,6⟩` est inséré à l'indice 1, avant
    le croisement réécrit `⟨5,2,3,4⟩`. `verifyR1` (les deux orientations)
    rend faux : le pas R1 est refusé pour cette paire dans les deux
    langages. Portée volontairement bornée : cet exemple tranche le pas
    R1 seul — il n'établit PAS que la paire soit dépourvue de toute chaîne
    de moves (la clôture transitive, par exemple via une réécriture R3
    d'indices intérieurs, n'est ni prouvée ni réfutée ici). Cohérence
    Prop/Bool sur le pas, pas un défaut de l'organe. -/
example : verifyR1
    { crossings := [⟨1,2,3,4⟩, ⟨1,2,3,4⟩], numEdges := 4 }
    { crossings := [⟨1,2,3,4⟩, ⟨1,5,6,6⟩, ⟨5,2,3,4⟩], numEdges := 6 }
    = false := by decide

end Knots

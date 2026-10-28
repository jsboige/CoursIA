/-
Knots.ReidemeisterAny — langue de moves étendue : kink/bigon sans fraîcheur
===========================================================================

Issue #22359 (parent Epic #1453, suite désignée de #18611 dont l'organe est
livré par #22240). Tranche 1 du grain multi-cycle : **la langue** et ses
vérificateurs, l'embedding R1/R2/R3 de la langue existante, des témoins kernel,
et le cadre de décision borné. La recherche de témoin / certificat négatif
étendu sur le corpus 11n102 (réplique Python, bornes ≤ 13 croisements,
excursions ≤ +2) est la tranche suivante, pas ce fichier.

## Constat fondateur (mesuré, cf #22359)

La langue connectée de `Knots.ReidemeisterMoves` est **append-only avec labels
frais en queue** : tout move descendant retire un kink `⟨a, b, c, c⟩` dont les
labels `b`, `c` sont exactement les deux plus grands du diagramme. Ce n'est pas
une hypothèse ajoutée, c'est une **conséquence de la parité `wf`** : chaque
étiquette apparaît exactement deux fois, donc un retrait littéral (sans
renumérotation) tue exactement deux labels, qui doivent alors vider
l'intervalle `[1, numEdges]` — c'est-à-dire être les deux plus grands. Le
certificat négatif `no_fourDistinct_certificate_unknots_11n102` (#20017) et la
mesure de provenance #18611 (138 623 états, les 11 croisements d'origine
présents dans tout état atteint) mesurent exactement cette clôture.

## Ce que ce module livre

1. `canon` — la **forme canonique à renommage près** (renumérotation par ordre
   de première apparition) : le quotient qui manque à la langue connectée ;
2. `verifyKinkDownAny` / `verifyBigonDownAny` — retraits R1/R2 où la seule
   contrainte de forme est la **silhouette** (kink `e3 = e4`, bigon `e2 = e3`)
   et où le résultat est comparé **à renommage près** — c'est le levier
   #22359 : la compaction de labels devient exprimable, la fraîcheur cesse
   d'être recouvrée par `wf` ;
3. `AnyMove` + `verifyAnyMove` + `verifyAnyMoves` + `movesConnectsAny` — la
   chaîne certifiée Bool sur la langue étendue (R3 réutilisé tel quel : il ne
   connaît pas la fraîcheur) ;
4. l'**embedding R1/R2/R3** : tout pas R1, R2 ou R3 accepté par l'ancien
   vérificateur est accepté par le nouveau (théorème, pas mesure) ;
5. des **témoins kernel** : une descente `_any` authentique à labels non frais
   (labels mourants {2, 3} ≠ deux plus grands {3, 4}, compaction 4 → 2), les
   descentes au diagramme vide (kink dégénéré côté R1, paire de bigons
   terminaux côté R2), et le passage de la paire R1
   historique par la nouvelle langue ;
6. `anyBoundedConnects` — le **cadre de décision borné** sur l'énumération
   `allDiagrams` (#22240) : atteignabilité dans le graphe des moves `_any`.

## Résidus déclarés (tranches suivantes du grain, pas des angles morts)

- **soundness `_any` → `ReidemeisterEquiv`** : un retrait `_any` est un R1/R2
  à renommage près ; le sceller exige « le renommage préserve le type du
  nœud » (une `AnyEquiv` + lemme de pont) ;
- l'équivalence `canon l = canon l' ↔ ∃ bijection d'étiquettes` est la
  justification de conception, **non prouvée ici** — le noyau ne consomme que
  l'égalité `canon` ;
- la complétude de l'énumération reste le résidu de #22240, inchangé.

Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier est le
**FR canonique**, avec son miroir anglais dans le sibling
`ReidemeisterAny_en.lean` (modèle sibling pair). Les énoncés de théorèmes, les
tactiques Lean, les noms de lemmes et les références Mathlib restent en anglais
(compat Mathlib 4) ; seules les docstrings et commentaires diffèrent.
-/

import Knots.Basic
import Knots.ReidemeisterMoves
import Knots.BoundedEnumeration

namespace Knots.AnyMoves

open Knots.Bounded

/-! ## 1. La forme canonique à renommage près

Le quotient de la représentation par renommage d'étiquettes : chaque étiquette
reçoit un numéro par ordre de première apparition. Deux listes de croisements
ont même `canon` exactement quand elles se correspondent par une bijection
d'étiquettes — justification de conception (non prouvée ici, voir l'en-tête) ;
le noyau ne consomme que l'égalité.
-/

/-- Association étiquette → numéro canonique : numéro déjà vu, ou
    `taille + 1` si première apparition. -/
private def canonLabel (seen : List (Nat × Nat)) (x : Nat) :
    Nat × List (Nat × Nat) :=
  match seen.lookup x with
  | some v => (v, seen)
  | none => (seen.length + 1, seen ++ [(x, seen.length + 1)])

/-- Renumérote une suite d'étiquettes en filant l'état des vues. -/
private def canonSlots : List (Nat × Nat) → List Nat → List Nat × List (Nat × Nat)
  | _, [] => ([], [])
  | seen, x :: xs =>
    let (v, seen') := canonLabel seen x
    let (ys, seen'') := canonSlots seen' xs
    (v :: ys, seen'')

/-- Forme canonique d'une liste de croisements : chaque étiquette remplacée par
    son rang de première apparition. Fonction totale, structurelle, évaluable
    par le noyau sur les littéraux. -/
def canon (l : List PDCrossing) : List (List Nat) :=
  go l []
where
  go : List PDCrossing → List (Nat × Nat) → List (List Nat)
    | [], _ => []
    | c :: cs, seen =>
      let (ys, seen') := canonSlots seen [c.e1, c.e2, c.e3, c.e4]
      ys :: go cs seen'

/-- La forme canonique du vide est le vide. -/
theorem canon_nil : canon [] = [] := rfl

/-! ## 2. Les retraits `_any` — silhouette seule, comparaison à renommage près

Le retrait R1 `_any` : le diagramme large porte un croisement terminal de
silhouette kink (`e3 = e4`), son retrait fusionne l'arc `K.e2` dans l'arc
`K.e1` (un slot réécrit), et le reste est comparé à la cible **via `canon`**.
Contrairement au retrait connecté de `ReidemeisterMoves`, aucune égalité de
fraîcheur n'est exigée : la parité `wf` de la cible arbitre seule la
comptabilité des labels mourants.
-/

/-- Remplace dans un croisement toute étiquette égale à `x` par `y`
    (les quatre slots ; `wf` garantit au plus un slot touché par label). -/
private def subLabel (c : PDCrossing) (x y : Nat) : PDCrossing :=
  ⟨if c.e1 = x then y else c.e1, if c.e2 = x then y else c.e2,
    if c.e3 = x then y else c.e3, if c.e4 = x then y else c.e4⟩

/-- Remplacement double en une passe : `x₁ → y₁` et `x₂ → y₂` (R2). Une seule
    passe pour ne pas réécrire le résultat du premier remplacement. -/
private def subLabel2 (c : PDCrossing) (x₁ y₁ x₂ y₂ : Nat) : PDCrossing :=
  ⟨sub1 c.e1, sub1 c.e2, sub1 c.e3, sub1 c.e4⟩
where
  sub1 (v : Nat) : Nat := if v = x₁ then y₁ else if v = x₂ then y₂ else v

/-- Vérificateur Bool du retrait `_any` d'un kink terminal : silhouette
    `K.e3 = K.e4` seule (la fraîcheur des labels de `verifyR1Fwd` est LEVÉE),
    longueur `+1`, fusion `K.e2 → K.e1` en un slot réécrit, comparaison du
    reste à la cible **à renommage près** (`canon`). Le cas « reste vide »
    couvre la descente d'un unique croisement vers le diagramme dégénéré. -/
def verifyKinkDownAny (D d : KnotDiagram) : Bool :=
  D.wf && d.wf &&
  match D.crossings.getLast? with
  | none => false
  | some K =>
    decide (K.e3 = K.e4 ∧ d.crossings.length + 1 = D.crossings.length) &&
    ((D.crossings.dropLast = [] &&
        decide (canon D.crossings.dropLast = canon d.crossings)) ||
      (List.range D.crossings.dropLast.length).any fun i =>
        let M := (D.crossings.dropLast).set i
          (subLabel (crossingAt D.crossings.dropLast i) K.e2 K.e1)
        decide (canon M = canon d.crossings))

/-- Vérificateur Bool du retrait `_any` d'une paire de bigons terminaux :
    silhouettes `e2 = e3` sur les deux croisements terminaux, arc commun
    `K₁.e1 = K₂.e1`, longueur `+2`, double fusion `o₁ → a` / `o₂ → a`
    (où `a = K₂.e1`, `o₁ = K₁.e4`, `o₂ = K₂.e4`) en un slot réécrit, reste
    comparé à renommage près. -/
def verifyBigonDownAny (D d : KnotDiagram) : Bool :=
  D.wf && d.wf &&
  match D.crossings.getLast? with
  | none => false
  | some K₂ =>
    match D.crossings.dropLast.getLast? with
    | none => false
    | some K₁ =>
      decide (K₂.e2 = K₂.e3 ∧ K₁.e2 = K₁.e3 ∧ K₁.e1 = K₂.e1 ∧
        d.crossings.length + 2 = D.crossings.length) &&
      ((D.crossings.dropLast.dropLast = [] &&
          decide (canon D.crossings.dropLast.dropLast = canon d.crossings)) ||
        (List.range D.crossings.dropLast.dropLast.length).any fun i =>
          let M := (D.crossings.dropLast.dropLast).set i
            (subLabel2 (crossingAt D.crossings.dropLast.dropLast i)
              K₁.e4 K₂.e1 K₂.e4 K₂.e1)
          decide (canon M = canon d.crossings))

/-! ## 3. L'inductif `AnyMove` et la chaîne certifiée

Même architecture que `ReidemeisterMove` : la nature du mouvement est le
constructeur, la well-formedness n'est pas un champ — elle est le `= true` du
vérificateur. R3 est réutilisé tel quel (`verifyR3` de `ReidemeisterMoves`) :
le move triangulaire ne crée pas de labels, il n'a pas de contraignant de
fraîcheur à lever. Le pas `_any` est direction-neutral : la création est le
retrait lu dans l'autre sens.
-/

/-- Un mouvement de la langue étendue : kink (R1) ou bigon (R2) **sans
    contrainte de fraîcheur**, ou triangle (R3, inchangé). -/
inductive AnyMove : Type where
  /-- Création/retrait d'un kink, à renommage près. -/
  | r1Any (source target : KnotDiagram) : AnyMove
  /-- Ajout/retrait d'une paire de bigons, à renommage près. -/
  | r2Any (source target : KnotDiagram) : AnyMove
  /-- Glissement triangulaire (identique à la langue connectée). -/
  | r3Any (source target : KnotDiagram) : AnyMove
  deriving Repr

/-- Diagramme source du mouvement. -/
def AnyMove.source : AnyMove → KnotDiagram
  | .r1Any s _ => s
  | .r2Any s _ => s
  | .r3Any s _ => s

/-- Diagramme cible du mouvement. -/
def AnyMove.target : AnyMove → KnotDiagram
  | .r1Any _ t => t
  | .r2Any _ t => t
  | .r3Any _ t => t

/-- Vérificateur Bool d'un pas `_any`, direction-neutral : le retrait dans
    l'une ou l'autre orientation (la création est l'inverse du retrait). -/
def verifyAnyMove (m : AnyMove) : Bool :=
  match m with
  | .r1Any s t => verifyKinkDownAny t s || verifyKinkDownAny s t
  | .r2Any s t => verifyBigonDownAny t s || verifyBigonDownAny s t
  | .r3Any s t => verifyR3 s t

/-- Vérifie qu'une suite `_any` forme une chaîne continue de `start` à `end_`
    dont chaque maillon passe `verifyAnyMove`. Cas de base : liste vide exige
    `start = end_` (réflexivité), comme la langue connectée. -/
def verifyAnyMoves : List AnyMove → KnotDiagram → KnotDiagram → Bool
  | [], start, end_ => decide (start = end_)
  | m :: ms, start, end_ =>
    decide (m.source = start) && verifyAnyMove m && verifyAnyMoves ms m.target end_

/-- Le connecteur #22359 : `movesConnectsAny d₁ d₂` est la proposition « la
    liste `ms` est un certificat de la langue étendue reliant `d₁` à `d₂` » —
    liste vérifiable par le noyau. La soundness vers `ReidemeisterEquiv`
    (retrait `_any` = R1/R2 à renommage près) est un résidu désigné, voir
    l'en-tête. -/
def movesConnectsAny (ms : List AnyMove) (d₁ d₂ : KnotDiagram) : Prop :=
  verifyAnyMoves ms d₁ d₂ = true

/-! ## 4. Embedding R1/R2/R3 — la langue connectée est une sous-langue

L'ancien vérificateur R1 exige les égalités de fraîcheur `K.e2 = m + 1`,
`K.e3 = K.e4 = m + 2` ; la silhouette `_any` (`K.e3 = K.e4`) en est une
conséquence immédiate, et la chirurgie littérale de l'ancien retrait rend le
résultat **inchangé** (renumérotation identité), donc `canon`-égal. Tout
maillon R1 ou R3 connecté est donc un maillon `_any`. Le cas R2 est prouvé
ci-dessous, dans la même section : le schéma de fraîcheur y est un double
renommage, défait en une seule passe par `subLabel2`.
-/

/-- Fusion d'un slot : si `v` est le label frais `b` là où l'original portait
    `a`, la fusion le rend à `a` ; sinon il était inchangé. Brique générique
    de l'embedding R1 (quatre slots, même preuve). -/
private theorem slot_merge {v w a b : Nat}
    (hr : v = w ∨ (v = b ∧ w = a)) (hw : w ≠ b) :
    (if v = b then a else v) = w := by
  rcases hr with h | ⟨hb', hwa⟩
  · rw [h, if_neg hw]
  · rw [hb', if_pos rfl, hwa]

/-- Les étiquettes d'un croisement du diagramme sont dans `d.edges`
    (l'appartenance alimente la borne `≤ numEdges` du plumbing). -/
private theorem mem_edges_of_mem_crossings {d : KnotDiagram}
    {c : PDCrossing} (hc : c ∈ d.crossings) :
    c.e1 ∈ d.edges ∧ c.e2 ∈ d.edges ∧ c.e3 ∈ d.edges ∧ c.e4 ∈ d.edges := by
  unfold KnotDiagram.edges
  simp only [List.mem_flatMap]
  exact ⟨⟨c, hc, by simp⟩, ⟨c, hc, by simp⟩, ⟨c, hc, by simp⟩, ⟨c, hc, by simp⟩⟩

/-- La borne d'étiquette : dans un diagramme bien formé, toute étiquette d'un
    croisement est dans `[1, numEdges]`. -/
private theorem label_le_of_wf {d : KnotDiagram} (hwf : d.wf = true)
    {c : PDCrossing} (hc : c ∈ d.crossings) :
    1 ≤ c.e1 ∧ c.e1 ≤ d.numEdges ∧ 1 ≤ c.e2 ∧ c.e2 ≤ d.numEdges ∧
    1 ≤ c.e3 ∧ c.e3 ≤ d.numEdges ∧ 1 ≤ c.e4 ∧ c.e4 ≤ d.numEdges := by
  unfold KnotDiagram.wf at hwf
  by_cases hnil : d.crossings = []
  · rw [hnil] at hc; exact absurd hc (by simp)
  · rw [if_neg hnil, Bool.and_eq_true] at hwf
    obtain ⟨hall, _⟩ := hwf
    obtain ⟨m1, m2, m3, m4⟩ := mem_edges_of_mem_crossings hc
    have ball (l : Nat) (hl : l ∈ d.edges) : 1 ≤ l ∧ l ≤ d.numEdges :=
      of_decide_eq_true (List.all_eq_true.mp hall l hl)
    have b1 := ball _ m1
    have b2 := ball _ m2
    have b3 := ball _ m3
    have b4 := ball _ m4
    exact ⟨b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2⟩

/-- Lecture d'un croisement réécrit : dans `l.set i Y`, l'indice `i` lit
    `Y`. Miroir du `getElem?` de `ReidemeisterMoves` pour la chirurgie
    descendante. -/
private theorem crossingAt_set_self (l : List PDCrossing) (i : Nat)
    (Y : PDCrossing) (h : i < l.length) : crossingAt (l.set i Y) i = Y := by
  have h1 : (l.set i Y)[i]? = some Y :=
    List.getElem?_eq_some_iff.mpr ⟨by rwa [List.length_set], by simp⟩
  simp only [crossingAt, h1, Option.getD_some]

/-- Réécrire un croisement par lui-même est l'identité (pour `List.set`). -/
private theorem set_self_mem {l : List PDCrossing} {i : Nat}
    (h : i < l.length) : l.set i l[i] = l := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i' =>
      simp only [List.length_cons] at h
      have hi' : i' < xs.length := by omega
      have hget : (x :: xs)[i' + 1] = xs[i'] := by simp
      rw [hget]
      show x :: xs.set i' xs[i'] = x :: xs
      rw [ih hi']

/-- **Embedding R1** : tout pas accepté par `verifyR1Fwd` (petit `d`, grand
    `D`) est un retrait `_any` accepté. La preuve déplie l'ancien
    vérificateur, constate la silhouette (conséquence des égalités de
    fraîcheur), et montre que la fusion `K.e2 → K.e1` défait exactement le
    renommage `isRenameOf` — le reste réécrit est littéralement le petit
    diagramme, donc `canon`-égal à lui-même. -/
theorem verifyR1Fwd_implies_verifyKinkDownAny {d D : KnotDiagram}
    (h : verifyR1Fwd d D = true) : verifyKinkDownAny D d = true := by
  cases hK : D.crossings.getLast? with
  | none => simp [verifyR1Fwd, hK] at h
  | some K =>
    simp only [verifyR1Fwd, hK, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hwf1, hwf2⟩, hn⟩, hform, hanyi⟩ := h
    obtain ⟨hb, hc3, hc4, ha1, han, hmem⟩ := of_decide_eq_true hform
    rw [List.any_eq_true] at hanyi
    obtain ⟨i, hi_mem, hbody⟩ := hanyi
    have hi : i < d.crossings.length := List.mem_range.mp hi_mem
    have hY2 : d.crossings[i]? = some d.crossings[i] :=
      List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
    simp only [Bool.and_eq_true, crossingAt, hY2, Option.getD_some] at hbody
    obtain ⟨⟨hsurg, hrename⟩, _⟩ := hbody
    -- la silhouette kink est conséquence de la fraîcheur
    have hsil : K.e3 = K.e4 := by omega
    -- décomposition terminale et longueur
    obtain ⟨M, hM⟩ := List.getLast?_eq_some_iff.mp hK
    have hdrop : D.crossings.dropLast
        = d.crossings.set i (crossingAt D.crossings.dropLast i) :=
      of_decide_eq_true hsurg
    have hlenM : M = d.crossings.set i (crossingAt D.crossings.dropLast i) := by
      have h2 : (M ++ [K]).dropLast
          = d.crossings.set i (crossingAt D.crossings.dropLast i) := by
        rw [← hM]; exact hdrop
      simpa using h2
    have hlen : d.crossings.length + 1 = D.crossings.length := by
      rw [hM, hlenM, List.length_append, List.length_singleton, List.length_set]
    -- la fusion défait le renommage, slot par slot
    have hsub : subLabel (crossingAt D.crossings.dropLast i) K.e2 K.e1
        = d.crossings[i] := by
      rw [hb]  -- K.e2 = d.numEdges + 1 : le label du renommage
      -- la borne : toute étiquette du croisement réécrit est ≤ numEdges
      have hmemi : d.crossings[i] ∈ d.crossings := by simp
      have hbounds := label_le_of_wf hwf1 hmemi
      obtain ⟨_, b2, _, b4, _, b6, _, b8⟩ := hbounds
      unfold subLabel
      have hrn := of_decide_eq_true hrename
      unfold PDCrossing.isRenameOf at hrn
      obtain ⟨r1, r2, r3, r4⟩ := hrn
      have hec : (d.crossings[i] : PDCrossing) =
          ⟨d.crossings[i].e1, d.crossings[i].e2, d.crossings[i].e3,
            d.crossings[i].e4⟩ := rfl
      rw [hec, PDCrossing.mk.injEq]
      exact ⟨slot_merge r1 (by omega), slot_merge r2 (by omega),
        slot_merge r3 (by omega), slot_merge r4 (by omega)⟩
    -- assemblage du vérificateur _any
    simp only [verifyKinkDownAny, hK, hwf2, hwf1, Bool.true_and]
    rw [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.any_eq_true]
    refine ⟨⟨hsil, hlen⟩, Or.inr ⟨i, ?_, ?_⟩⟩
    · rw [hdrop, List.length_set]
      exact hi_mem
    · show decide (canon ((D.crossings.dropLast).set i
          (subLabel (crossingAt D.crossings.dropLast i) K.e2 K.e1)) =
          canon d.crossings) = true
      rw [hdrop, crossingAt_set_self _ _ _ hi, List.set_set, hsub,
        set_self_mem hi]
      simp

/-- Embedding du pas R1, orientation-neutral. -/
theorem verifyR1_implies_verifyAnyMove (s t : KnotDiagram)
    (h : verifyR1 s t = true) : verifyAnyMove (.r1Any s t) = true := by
  simp only [verifyAnyMove]
  rcases Bool.or_eq_true_iff.mp h with h' | h'
  · exact Bool.or_eq_true_iff.mpr (Or.inl (verifyR1Fwd_implies_verifyKinkDownAny h'))
  · exact Bool.or_eq_true_iff.mpr (Or.inr (verifyR1Fwd_implies_verifyKinkDownAny h'))

/-- Embedding du pas R3 : définitionnel (le vérificateur est réutilisé tel
    quel). -/
theorem verifyR3_implies_verifyAnyMove (s t : KnotDiagram)
    (h : verifyR3 s t = true) : verifyAnyMove (.r3Any s t) = true := h

/-- Fusion double d'un slot : si `v` est l'un des labels frais `o₁`/`o₂` là où
    l'original portait `a`, la fusion le rend à `a` ; sinon il était inchangé.
    Brique générique de l'embedding R2 (quatre slots, même preuve que
    `slot_merge` pour R1). -/
private theorem slot_merge2 {v w a o₁ o₂ : Nat}
    (hr : v = w ∨ (v = o₁ ∧ w = a) ∨ (v = o₂ ∧ w = a))
    (hw₁ : w ≠ o₁) (hw₂ : w ≠ o₂) (ho : o₂ ≠ o₁) :
    (if v = o₁ then a else if v = o₂ then a else v) = w := by
  rcases hr with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h, if_neg hw₁, if_neg hw₂]
  · rw [h1, if_pos rfl, h2]
  · rw [if_neg (by omega), h1, if_pos rfl, h2]

/-- **Embedding R2** : tout pas accepté par `verifyR2Fwd` (petit `d`, grand
    `D`) est un retrait `_any` accepté. La preuve déplie l'ancien
    vérificateur, lit les silhouettes des bigons terminaux (conséquence des
    égalités de fraîcheur), et montre que la double fusion
    `K₁.e4 → K₂.e1` / `K₂.e4 → K₂.e1` défait exactement le double renommage
    `isDoubleRenameOf` — le croisement réécrit redevient littéralement celui
    du petit diagramme, donc le reste réécrit est `canon`-égal à la cible.
    Le double arc `a` vit dans un seul croisement du petit diagramme, et la
    passe simple `subLabel2` (chaque slot testé contre les deux cibles de
    fusion) suffit à défaire le renommage des deux slots. -/
theorem verifyR2Fwd_implies_verifyBigonDownAny {d D : KnotDiagram}
    (h : verifyR2Fwd d D = true) : verifyBigonDownAny D d = true := by
  cases hK₂ : D.crossings.getLast? with
  | none => simp [verifyR2Fwd, hK₂] at h
  | some K₂ =>
    cases hK₁ : D.crossings.dropLast.getLast? with
    | none => simp [verifyR2Fwd, hK₂, hK₁] at h
    | some K₁ =>
      simp only [verifyR2Fwd, hK₂, hK₁, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hwf1, hwf2⟩, hn⟩, hform₂, hform₁, hanyi⟩ := h
      obtain ⟨hb2, hb3, hb4, ha1, han, hmem⟩ := of_decide_eq_true hform₂
      obtain ⟨hc1, hc2, hc3, hc4⟩ := of_decide_eq_true hform₁
      rw [List.any_eq_true] at hanyi
      obtain ⟨i, hi_mem, hbody⟩ := hanyi
      have hi : i < d.crossings.length := List.mem_range.mp hi_mem
      have hY2 : d.crossings[i]? = some d.crossings[i] :=
        List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
      simp only [Bool.and_eq_true, crossingAt, hY2, Option.getD_some] at hbody
      obtain ⟨hsurg, hrename⟩ := hbody
      -- les silhouettes bigon sont conséquence de la fraîcheur
      have hsil₂ : K₂.e2 = K₂.e3 := by omega
      have hsil₁ : K₁.e2 = K₁.e3 := by omega
      -- chirurgie et longueur (deux dropLast retirent la paire terminale)
      have hrest : D.crossings.dropLast.dropLast
          = d.crossings.set i (crossingAt D.crossings.dropLast.dropLast i) :=
        of_decide_eq_true hsurg
      have hrestlen : D.crossings.dropLast.dropLast.length
          = d.crossings.length := by
        rw [hrest, List.length_set]
      have hneD : D.crossings ≠ [] := fun hc => by
        rw [hc] at hK₂; simp at hK₂
      have hne₁ : D.crossings.dropLast ≠ [] := fun hc => by
        rw [hc] at hK₁; simp at hK₁
      have hlen : d.crossings.length + 2 = D.crossings.length := by
        have h1 : D.crossings.dropLast.length = D.crossings.length - 1 :=
          List.length_dropLast
        have h2 : D.crossings.dropLast.dropLast.length
            = D.crossings.dropLast.length - 1 := List.length_dropLast
        have hpD : 0 < D.crossings.length :=
          List.length_pos_iff_ne_nil.mpr hneD
        have hp₁ : 0 < D.crossings.dropLast.length :=
          List.length_pos_iff_ne_nil.mpr hne₁
        omega
      -- la double fusion défait le renommage, slot par slot : les labels
      -- frais o1 = K1.e4, o2 = K2.e4 sont d'abord recalés sur l'épellation
      -- numérotée du renommage (n+2 / n+4), puis chaque slot fusionne
      have hsub : subLabel2 (crossingAt D.crossings.dropLast.dropLast i)
            K₁.e4 K₂.e1 K₂.e4 K₂.e1 = d.crossings[i] := by
        rw [hc4, hb4]
        have hmemi : d.crossings[i] ∈ d.crossings := by simp
        have hbounds := label_le_of_wf hwf1 hmemi
        obtain ⟨_, b2, _, b4, _, b6, _, b8⟩ := hbounds
        have hrn := of_decide_eq_true hrename
        unfold PDCrossing.isDoubleRenameOf at hrn
        obtain ⟨r1, r2, r3, r4⟩ := hrn
        unfold subLabel2 subLabel2.sub1
        have hec : (d.crossings[i] : PDCrossing) =
            ⟨d.crossings[i].e1, d.crossings[i].e2, d.crossings[i].e3,
              d.crossings[i].e4⟩ := rfl
        rw [hec, PDCrossing.mk.injEq]
        exact ⟨slot_merge2 r1 (by omega) (by omega) (by omega),
          slot_merge2 r2 (by omega) (by omega) (by omega),
          slot_merge2 r3 (by omega) (by omega) (by omega),
          slot_merge2 r4 (by omega) (by omega) (by omega)⟩
      -- assemblage du vérificateur _any
      simp only [verifyBigonDownAny, hK₂, hK₁, hwf2, hwf1, Bool.true_and]
      rw [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.any_eq_true]
      refine ⟨⟨hsil₂, hsil₁, hc1, hlen⟩, Or.inr ⟨i, ?_, ?_⟩⟩
      · rw [hrestlen]
        exact hi_mem
      · show decide (canon ((D.crossings.dropLast.dropLast).set i
            (subLabel2 (crossingAt D.crossings.dropLast.dropLast i)
              K₁.e4 K₂.e1 K₂.e4 K₂.e1)) = canon d.crossings) = true
        rw [hrest, crossingAt_set_self _ _ _ hi, List.set_set, hsub,
          set_self_mem hi]
        simp

/-- Embedding du pas R2, orientation-neutral. -/
theorem verifyR2_implies_verifyAnyMove (s t : KnotDiagram)
    (h : verifyR2 s t = true) : verifyAnyMove (.r2Any s t) = true := by
  simp only [verifyAnyMove]
  rcases Bool.or_eq_true_iff.mp h with h' | h'
  · exact Bool.or_eq_true_iff.mpr (Or.inl (verifyR2Fwd_implies_verifyBigonDownAny h'))
  · exact Bool.or_eq_true_iff.mpr (Or.inr (verifyR2Fwd_implies_verifyBigonDownAny h'))

/-! ## 5. Témoins kernel

Quatre faces de la langue : une descente `_any` **authentique** (labels
mourants non frais, compaction), les descentes au diagramme vide — kink
dégénéré côté R1, paire de bigons terminaux côté R2 (bornes inférieures de
la langue) —, et le passage de la paire R1 historique
(`reidemeister1Connected_satisfiable`) par la nouvelle langue — l'embedding
en acte.
-/

/-- **Témoin `_any` non frais** : le grand diagramme porte le kink terminal
    `⟨1,2,3,3⟩` ; son retrait fusionne l'arc `2` dans l'arc `1` et tue les
    labels `{2, 3}` — qui ne sont PAS les deux plus grands (`{3, 4}`) : la
    cible survivante porte le label `4`, renuméroté `2` par la comparaison
    `canon`. Ce pas est REFUSÉ par la langue connectée (fraîcheur recouvrée
    par `wf`) et accepté ici — le levier #22359 en un pas. -/
theorem verifyKinkDownAny_witness_nonFresh :
    verifyKinkDownAny
      { crossings := [⟨4, 1, 4, 2⟩, ⟨1, 2, 3, 3⟩], numEdges := 4 }
      { crossings := [⟨2, 1, 2, 1⟩], numEdges := 2 } := by
  decide

/-- Le même pas scellé en certificat de chaîne : la langue étendue relie le
    grand diagramme au petit en un maillon. -/
theorem movesConnectsAny_witness_nonFresh :
    movesConnectsAny
      [AnyMove.r1Any
        { crossings := [⟨4, 1, 4, 2⟩, ⟨1, 2, 3, 3⟩], numEdges := 4 }
        { crossings := [⟨2, 1, 2, 1⟩], numEdges := 2 }]
      { crossings := [⟨4, 1, 4, 2⟩, ⟨1, 2, 3, 3⟩], numEdges := 4 }
      { crossings := [⟨2, 1, 2, 1⟩], numEdges := 2 } := by
  unfold movesConnectsAny
  decide

/-- **Descente au diagramme vide** : l'unique croisement `⟨1,1,2,2⟩` est un
    kink dégénéré (silhouette `e3 = e4`, fusion triviale `a = b`), son
    retrait laisse le vide — le cas « reste vide » du vérificateur. -/
theorem verifyKinkDownAny_witness_empty :
    verifyKinkDownAny
      { crossings := [⟨1, 1, 2, 2⟩], numEdges := 2 }
      { crossings := [], numEdges := 0 } := by
  decide

/-- **Témoin R2 `_any`** : la paire de bigons terminaux `⟨1,2,2,4⟩` /
    `⟨1,3,3,4⟩` (arcs jumeaux `2` et `3`, entrée `1` et sortie `4` communes)
    se retire entièrement — cible le diagramme vide, cas « reste vide » du
    vérificateur. La surface `r2Any` exercée sur un littéral, en symétrie du
    kink dégénéré ci-dessus. -/
theorem verifyBigonDownAny_witness_empty :
    verifyBigonDownAny
      { crossings := [⟨1, 2, 2, 4⟩, ⟨1, 3, 3, 4⟩], numEdges := 4 }
      { crossings := [], numEdges := 0 } := by
  decide

/-- **Le pas `r2Any` scellé en maillon** : la même paire passe le
    vérificateur direction-neutral de la langue étendue. -/
theorem verifyR2_witness_passes_any :
    verifyAnyMove (AnyMove.r2Any
      { crossings := [⟨1, 2, 2, 4⟩, ⟨1, 3, 3, 4⟩], numEdges := 4 }
      { crossings := [], numEdges := 0 }) := by
  decide

/-- **L'embedding en acte** : la paire témoin R1 de la langue connectée
    (`verifyR1Fwd`, cf `ReidemeisterMoves` §7) passe la langue étendue —
    la fraîcheur rend la comparaison `canon` triviale (identité). -/
theorem verifyR1_witness_passes_any :
    verifyAnyMove (AnyMove.r1Any
      { crossings := [⟨1, 2, 3, 4⟩, ⟨1, 2, 3, 4⟩], numEdges := 4 }
      { crossings := [⟨1, 2, 3, 4⟩, ⟨5, 2, 3, 4⟩, ⟨1, 5, 6, 6⟩],
                      numEdges := 6 }) := by
  decide

/-! ## 6. Le cadre de décision borné

L'énumération `allDiagrams n` (#22240) fournit l'univers ; les moves `_any`
définissent le graphe ; l'atteignabilité est décidable par fermeture de
voisinage bornée par la taille de l'univers. Le noyau n'évalue ce cadre qu'aux
petites bornes ; la recherche effective aux bornes du corpus 11n102 (≤ 13
croisements, excursions ≤ +2) passe par la réplique Python — tranche 2 du
grain, cf #20017 pour le précédent.
-/

/-- Voisins `_any` dans l'univers borné : tous les diagrammes de l'énumération
    à un pas `_any` de `d`. -/
private def anyNeighbors (n : Nat) (d : KnotDiagram) : List KnotDiagram :=
  (allDiagrams n).filter fun d' =>
    verifyAnyMove (AnyMove.r1Any d d') ||
    verifyAnyMove (AnyMove.r2Any d d') ||
    verifyAnyMove (AnyMove.r3Any d d')

/-- Fermeture par voisinage : au plus la taille de l'univers tours
    (chaînes sans répétition), dédupliquée à chaque tour. -/
private def anyClosure (n : Nat) : Nat → List KnotDiagram → List KnotDiagram
  | 0, reached => reached
  | k + 1, reached =>
    anyClosure n k ((reached.flatMap (anyNeighbors n) ++ reached).eraseDups)

/-- Décision bornée de la connectivité `_any` : `d₂` est-il atteignable
    depuis `d₁` dans le graphe des moves `_any` sur `allDiagrams n` ? Cadre
    décidable — l'évaluation kernel est réservée aux petites bornes, la
    recherche du corpus 11n102 passe par la réplique Python (tranche 2). -/
def anyBoundedConnects (n : Nat) (d₁ d₂ : KnotDiagram) : Bool :=
  (anyClosure n ((allDiagrams n).length + 1) [d₁]).contains d₂

/-- Le cadre s'exécute : dans l'univers `allDiagrams 1`, le kink dégénéré
    `⟨1,1,2,2⟩` atteint le diagramme vide — la descente du témoin §5 au sein
    de l'énumération, décidée par le noyau. -/
theorem demo_anyBoundedConnects_empty :
    anyBoundedConnects 1
      { crossings := [⟨1, 1, 2, 2⟩], numEdges := 2 }
      { crossings := [], numEdges := 0 } = true := by
  decide

end Knots.AnyMoves

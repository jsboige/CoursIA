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
- l'équivalence `canon l = canon l' ↔ ∃ bijection d'étiquettes` : la moitié
  **invariance** (`canon (mapC σ l) = canon l` pour `σ` injective) est prouvée
  en §7 (`canon_map_eq`) ; la réciproque (**extraction** du renommage depuis
  l'égalité `canon`) reste résidu — elle exigera un invariant `SeenNodup` sur
  le fil des vues. La tranche 3 corrige au passage la base de `canonSlots`
  (l'état survivait à la liste vide) : sans lui, la renumérotation repartait à
  zéro à chaque croisement et l'égalité `canon` acceptait des recâblages
  inter-croisements — contre-exemple scellé en §7 ;
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
reçoit un numéro par ordre de **première apparition, filé d'un croisement à
l'autre**. Deux listes de croisements ont même `canon` exactement quand elles
se correspondent par une bijection d'étiquettes — justification de conception
(moitié invariance prouvée en §7, réciproque résidu, voir l'en-tête) ; le
noyau ne consomme que l'égalité.
-/

/-- Association étiquette → numéro canonique : numéro déjà vu, ou
    `taille + 1` si première apparition. -/
private def canonLabel (seen : List (Nat × Nat)) (x : Nat) :
    Nat × List (Nat × Nat) :=
  match seen.lookup x with
  | some v => (v, seen)
  | none => (seen.length + 1, seen ++ [(x, seen.length + 1)])

/-- Renumérote une suite d'étiquettes en filant l'état des vues. La base
    `[]` **restitue le fil** : sans cela, chaque croisement repartait d'un
    état vide et la renumérotation devenait par-croisement — l'égalité
    `canon` acceptait alors des recâblages inter-croisements (contre-exemple
    scellé en §7). -/
private def canonSlots : List (Nat × Nat) → List Nat → List Nat × List (Nat × Nat)
  | seen, [] => ([], seen)
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

/-! ## 7. Le pont canon — correctif du filage + moitié invariance (tranche 3)

Le filage de l'état des vues était cassé à la base : `canonSlots` rendait
`([], [])` sur la liste vide, jetant l'état accumulé — la renumérotation
repartait à zéro à **chaque croisement**, et l'égalité `canon` acceptait des
cibles qui recâblent les connexions inter-croisements (le contre-exemple
ci-dessous l'acceptait, et il ne correspond à aucun renommage du résultat de
chirurgie). La base rend désormais le fil (`| seen, [] => ([], seen)`), la
sémantique documentée depuis la section 1 — premier rang de première
apparition **global**.

Cette tranche scelle le correctif et livre la **moitié invariance** du pont :

* `canon_map_eq` — renommer par une **injection** ne change pas la forme
  canonique : le rang de première apparition ne dépend pas du nom de
  l'étiquette, seulement de l'ordre d'apparition. C'est la direction que
  consomme la soundness (`_any` → `ReidemeisterEquiv`) : le certificat porté
  par le vérificateur est stable par renommage.

La réciproque (**extraction** : deux listes de même `canon` se correspondent
par une injection) reste résidu — elle exigera un invariant `SeenNodup` sur le
fil des vues (le rang n'est injectif que si les clés déjà vues sont distinctes).
-/

/-- Renommage d'une liste de croisements : `π` appliquée aux quatre slots de
    chaque croisement. -/
private def mapC (π : Nat → Nat) (l : List PDCrossing) : List PDCrossing :=
  l.map fun c => ⟨π c.e1, π c.e2, π c.e3, π c.e4⟩

/-- `lookup` commute au renommage des clés : chercher `π x` dans l'image d'une
    liste de paires par `π` (sur les clés), c'est chercher `x` dans la liste —
    à injectivité de `π` près sur les clés. -/
private theorem lookup_map_key {π : Nat → Nat} (hπ : Function.Injective π)
    (l : List (Nat × Nat)) (x : Nat) (w : Nat) (h : l.lookup x = some w) :
    (l.map fun p => (π p.1, p.2)).lookup (π x) = some w := by
  induction l with
  | nil => simp at h
  | cons p t ih =>
    -- `List.lookup` déplie en `match` Bool sur `a == k` : on réduit le
    -- discriminateur par les lemmes core `beq_self_eq_true` /
    -- `beq_eq_false_iff_ne`, l'injectivité arbitre le cas π.
    by_cases hpx : x = p.1
    · subst hpx
      simp only [List.lookup, beq_self_eq_true] at h
      simp only [List.map_cons, List.lookup, beq_self_eq_true]
      exact h
    · have hb : (x == p.1) = false := by
        rw [beq_eq_false_iff_ne]; exact hpx
      simp only [List.lookup, hb] at h
      have hne : (π x == π p.1) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun hc => hpx (hπ hc)
      simp only [List.map_cons, List.lookup, hne]
      exact ih h

/-- Miroir du précédent pour le cas absent : si `x` n'est clé nulle part,
    `π x` non plus dans l'image — à injectivité de `π` près. -/
private theorem lookup_map_key_none {π : Nat → Nat} (hπ : Function.Injective π)
    (l : List (Nat × Nat)) (x : Nat) (h : l.lookup x = none) :
    (l.map fun p => (π p.1, p.2)).lookup (π x) = none := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    by_cases hpx : x = p.1
    · subst hpx
      simp only [List.lookup, beq_self_eq_true] at h
      simp at h
    · have hb : (x == p.1) = false := by
        rw [beq_eq_false_iff_ne]; exact hpx
      simp only [List.lookup, hb] at h
      have hne : (π x == π p.1) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun hc => hpx (hπ hc)
      simp only [List.map_cons, List.lookup, hne]
      exact ih h

/-- Une étape de `canonSlots`, cas « étiquette déjà vue » : le numéro est la
    valeur déjà enregistrée, l'état ne bouge pas. Forme sans `let` (les deux
    composantes du résultat sont les projections d'une seule évaluation). -/
private theorem canonSlots_cons_of_some {seen : List (Nat × Nat)} {x v : Nat}
    {xs : List Nat} (h : seen.lookup x = some v) :
    canonSlots seen (x :: xs) =
      (v :: (canonSlots seen xs).1, (canonSlots seen xs).2) := by
  simp only [canonSlots, canonLabel, h]

/-- Une étape de `canonSlots`, cas « première apparition » : numéro
    `taille + 1`, l'état s'enrichit de la nouvelle association. -/
private theorem canonSlots_cons_of_none {seen : List (Nat × Nat)} {x : Nat}
    {xs : List Nat} (h : seen.lookup x = none) :
    canonSlots seen (x :: xs) =
      ((seen.length + 1) :: (canonSlots (seen ++ [(x, seen.length + 1)]) xs).1,
        (canonSlots (seen ++ [(x, seen.length + 1)]) xs).2) := by
  simp only [canonSlots, canonLabel, h]

/-- Le cœur du pont : quand les fils d'état sont corrélés par `π` (les clés
    renommées, les numéros canoniques inchangés), les numéros produits sont
    **égaux** des deux côtés et les fils restent corrélés. Le rang de première
    apparition ne dépend pas du nom de l'étiquette. -/
private theorem canonSlots_congr {π : Nat → Nat} (hπ : Function.Injective π)
    (xs : List Nat) :
    ∀ seen seen' : List (Nat × Nat),
      seen' = seen.map (fun p => (π p.1, p.2)) →
      (canonSlots seen' (xs.map π)).1 = (canonSlots seen xs).1 ∧
      (canonSlots seen' (xs.map π)).2 =
        (canonSlots seen xs).2.map (fun p => (π p.1, p.2)) := by
  induction xs with
  | nil =>
    intro seen seen' hcorr
    simp only [List.map_nil]
    exact ⟨rfl, hcorr⟩
  | cons x xs ih =>
    intro seen seen' hcorr
    simp only [List.map_cons]
    cases hlk : seen.lookup x with
    | some v =>
      have hlk' : seen'.lookup (π x) = some v := by
        rw [hcorr, lookup_map_key hπ seen x v hlk]
      rw [canonSlots_cons_of_some hlk, canonSlots_cons_of_some hlk']
      -- états inchangés : la corrélation hcorr elle-même nourrit l'IH
      obtain ⟨ys, ys'⟩ := ih _ _ hcorr
      exact ⟨congrArg (List.cons v) ys, ys'⟩
    | none =>
      have hlk' : seen'.lookup (π x) = none := by
        rw [hcorr, lookup_map_key_none hπ seen x hlk]
      have hlen : seen'.length = seen.length := by
        rw [hcorr, List.length_map]
      have hcorr2 : seen' ++ [(π x, seen'.length + 1)] =
          (seen ++ [(x, seen.length + 1)]).map (fun p => (π p.1, p.2)) := by
        rw [hcorr, List.map_append, List.map_singleton]
        simp
      rw [canonSlots_cons_of_none hlk, canonSlots_cons_of_none hlk']
      obtain ⟨ys, ys'⟩ := ih _ _ hcorr2
      rw [hlen] at ys ys' ⊢
      exact ⟨congrArg (List.cons _) ys, ys'⟩

/-- Une étape de `canon.go`, sans `let` : la forme canonique d'une liste de
    croisements est le quadruplet des numéros canoniques du premier croisement,
    puis le fil des suivants. (Zéta + projections : définitionnel.) -/
private theorem canon_go_cons (c : PDCrossing) (cs : List PDCrossing)
    (seen : List (Nat × Nat)) :
    canon.go (c :: cs) seen =
      (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).1
        :: canon.go cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2 := rfl

/-- Le cœur du pont, niveau croisements : sur des fils d'état corrélés, la
    forme canonique d'une liste renommée est celle de la liste. -/
private theorem canon_go_congr {π : Nat → Nat} (hπ : Function.Injective π)
    (l : List PDCrossing) :
    ∀ seen seen' : List (Nat × Nat),
      seen' = seen.map (fun p => (π p.1, p.2)) →
      canon.go (mapC π l) seen' = canon.go l seen := by
  induction l with
  | nil => intro _ _ _; rfl
  | cons c cs ih =>
    intro seen seen' hcorr
    have hmap : mapC π (c :: cs) =
        ⟨π c.e1, π c.e2, π c.e3, π c.e4⟩ :: mapC π cs := by simp [mapC]
    obtain ⟨hnums, hcorr2⟩ :=
      canonSlots_congr hπ [c.e1, c.e2, c.e3, c.e4] seen seen' hcorr
    rw [hmap, canon_go_cons, canon_go_cons,
      show [π c.e1, π c.e2, π c.e3, π c.e4] = [c.e1, c.e2, c.e3, c.e4].map π from by
        simp,
      hnums, ih _ _ hcorr2]

/-- **Moitié invariance du pont** : renommer une liste de croisements par une
    injection ne change pas sa forme canonique — le rang de première
    apparition ne dépend pas du nom de l'étiquette, seulement de l'ordre
    d'apparition. C'est la direction que consomme la soundness : un pas
    vérifié l'est pour toute la classe de renommage de ses opérandes. -/
theorem canon_map_eq {π : Nat → Nat} (hπ : Function.Injective π)
    (l : List PDCrossing) : canon (mapC π l) = canon l :=
  canon_go_congr hπ l [] [] rfl

/-- **Contre-exemple scellant le correctif du filage** : la source est le grand
    côté de la paire R1 historique (`verifyR1_witness_passes_any`) ; la cible
    `d` garde les mêmes silhouettes mais recâble les connexions
    inter-croisements — le slot `e1` du second croisement passe de `1` à `3`,
    ce qui n'est le fait d'**aucun** renommage du résultat de chirurgie
    `[⟨1,2,3,4⟩, ⟨1,2,3,4⟩]` (un renommage préserverait l'égalité des slots
    `e1` des deux croisements). Sous le filage global, `canon` distingue les
    deux et le vérificateur REFUSE. Avant le correctif, la base
    `_, [] => ([], [])` remettait la numérotation à zéro à chaque croisement :
    les deux formes canoniales tombaient sur `[[1,2,3,4], [1,2,3,4]]` et ce
    pas était ACCEPTÉ — le défaut, scellé ici par le noyau. -/
theorem verifyKinkDownAny_rejects_crossRewire :
    verifyKinkDownAny
      { crossings := [⟨1, 2, 3, 4⟩, ⟨5, 2, 3, 4⟩, ⟨1, 5, 6, 6⟩],
        numEdges := 6 }
      { crossings := [⟨1, 2, 3, 4⟩, ⟨3, 4, 1, 2⟩], numEdges := 4 } = false := by
  decide


/-! ## 8. Socle de la moitié extraction (tranche 4, en cours)

La réciproque de `canon_map_eq` — même forme canonique ⇒ la cible est un
renommage de la source — exige que le fil des vues soit un état **fidèle** :
clés distinctes (une étiquette, un rang), valeurs distinctes et bornées (un
rang, une étiquette ; les rangs vivent entre `1` et la taille du fil). Ces
invariants sont de construction : `canonLabel` n'ajoute une clé que si elle
est absente, et le rang ajouté est `taille + 1`, donc frais. Cette section
pose le vocabulaire et la préservation des clés ; la préservation des valeurs
puis le théorème d'extraction suivent (tranches suivantes).
-/

/-- `List.lookup` n'échoue que sur une clé absente — par induction, pour ne
    dépendre d'aucun lemme socle au nom incertain. -/
private theorem lookup_none_iff_not_mem_key (x : Nat) :
    ∀ seen : List (Nat × Nat),
      seen.lookup x = none ↔ x ∉ seen.map Prod.fst := by
  intro seen
  induction seen with
  | nil => simp
  | cons p t ih =>
    by_cases hpx : x = p.1
    · subst hpx
      simp
    · have hb : (x == p.1) = false := by
        rw [beq_eq_false_iff_ne]; exact hpx
      simp only [List.lookup, hb, List.map_cons, List.mem_cons, not_or]
      exact ⟨fun h => ⟨hpx, ih.mp h⟩, fun h => ih.mpr h.2⟩

/-- État fidèle, clés : une étiquette n'a qu'un rang (le fil ne duplique pas
    les clés). -/
private def SeenKeysNodup (seen : List (Nat × Nat)) : Prop :=
  (seen.map Prod.fst).Nodup

/-- État fidèle, valeurs : un rang n'appartient qu'à une étiquette. -/
private def SeenValsNodup (seen : List (Nat × Nat)) : Prop :=
  (seen.map Prod.snd).Nodup

/-- État fidèle, bornage : les rangs vivent entre `1` et la taille du fil. -/
private def SeenValsBounded (seen : List (Nat × Nat)) : Prop :=
  ∀ p ∈ seen, 0 < p.2 ∧ p.2 ≤ seen.length

/-- `canonLabel` préserve la fidélité des clés : une clé présente n'est pas
    réajoutée, une clé absente est ajoutée une seule fois. -/
private theorem canonLabel_keys_nodup {seen : List (Nat × Nat)} {x : Nat}
    (h : SeenKeysNodup seen) : SeenKeysNodup (canonLabel seen x).2 := by
  unfold canonLabel
  cases hlk : seen.lookup x with
  | some v => exact h
  | none =>
    have hx : x ∉ seen.map Prod.fst :=
      (lookup_none_iff_not_mem_key x seen).mp hlk
    unfold SeenKeysNodup
    rw [List.map_append, List.map_singleton]
    exact List.Nodup.append h (by simp)
      (by intro a ha
          simp only [List.mem_singleton]
          exact fun hax => hx (hax ▸ ha))

/-- Le filage d'une suite d'étiquettes préserve la fidélité des clés
    (induction sur la suite, état initial arbitraire). -/
private theorem canonSlots_keys_nodup {seen : List (Nat × Nat)} {xs : List Nat}
    (h : SeenKeysNodup seen) : SeenKeysNodup (canonSlots seen xs).2 := by
  induction xs generalizing seen with
  | nil => exact h
  | cons y ys ih =>
    cases hlk : seen.lookup y with
    | some v =>
      rw [canonSlots_cons_of_some hlk]
      exact ih h
    | none =>
      have hlab : (canonLabel seen y).2 = seen ++ [(y, seen.length + 1)] := by
        unfold canonLabel; rw [hlk]
      have hk' := canonLabel_keys_nodup (seen := seen) (x := y) h
      rw [hlab] at hk'
      rw [canonSlots_cons_of_none hlk]
      exact ih hk'


/-! ## 9. La fidélité des VALEURS (tranche 4, en cours)

La moitié « extraction » a besoin de plus que la préservation des clés : il
faut que les **valeurs** du fil soient, elles aussi, fidèles — un rang par
étiquette, et des rangs dans `1 … taille`. Ce sont les invariants
`SeenValsNodup` et `SeenValsBounded` posés en §8.

La clef du raisonnement est la **fraîcheur du rang ajouté** : `canonLabel`
ajoute le rang `taille + 1`, et `SeenValsBounded` place tous les rangs déjà
portés dans `1 … taille` — donc `taille + 1` est frais. Une fois ce point
établi, l'ajout préserve la fidélité du fil, et le filage d'une suite
d'étiquettes la préserve aussi.

Le théorème d'extraction lui-même (`canon l = canon l'` ⇒ il existe un
renommage injectif de `l` vers `l'`) reste le résidu de la tranche.
-/

/-- Un rang porté par le fil est au plus la taille du fil. -/
private theorem snd_mem_le_length {seen : List (Nat × Nat)}
    (hb : SeenValsBounded seen) {v : Nat} (hv : v ∈ seen.map Prod.snd) :
    v ≤ seen.length := by
  obtain ⟨p, hp, hpv⟩ := List.mem_map.mp hv
  rw [← hpv]
  exact (hb p hp).2

/-- Le rang ajouté est frais : `taille + 1` n'est déjà porté par aucune
    étiquette du fil. -/
private theorem fresh_rank_not_mem {seen : List (Nat × Nat)}
    (hb : SeenValsBounded seen) :
    seen.length + 1 ∉ seen.map Prod.snd := by
  intro hv
  have hle := snd_mem_le_length hb hv
  omega

/-- `canonLabel` préserve la fidélité des valeurs : le rang nouveau est frais,
    donc n'entre en collision avec aucun rang déjà porté. -/
private theorem canonLabel_vals_nodup {seen : List (Nat × Nat)} {x : Nat}
    (hn : SeenValsNodup seen) (hb : SeenValsBounded seen) :
    SeenValsNodup (canonLabel seen x).2 := by
  cases hlk : seen.lookup x with
  | some v =>
    simp only [canonLabel, hlk]
    exact hn
  | none =>
    have hlab : (canonLabel seen x).2 = seen ++ [(x, seen.length + 1)] := by
      unfold canonLabel; rw [hlk]
    rw [hlab]
    unfold SeenValsNodup
    rw [List.map_append, List.map_singleton]
    refine List.Nodup.append hn (by simp) ?_
    intro a ha hmem
    simp only [List.mem_singleton] at hmem
    subst hmem
    exact absurd ha (fresh_rank_not_mem hb)

/-- `canonLabel` préserve le bornage des rangs : les rangs déjà portés restent
    dans `1 … taille`, et le rang nouveau vaut la taille du fil enrichi. -/
private theorem canonLabel_vals_bounded {seen : List (Nat × Nat)} {x : Nat}
    (hb : SeenValsBounded seen) :
    SeenValsBounded (canonLabel seen x).2 := by
  cases hlk : seen.lookup x with
  | some v =>
    simp only [canonLabel, hlk]
    exact hb
  | none =>
    have hlab : (canonLabel seen x).2 = seen ++ [(x, seen.length + 1)] := by
      unfold canonLabel; rw [hlk]
    rw [hlab]
    intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨hpos, hle⟩ := hb p hp
      simp only [List.length_append]
      omega
    · simp only [List.mem_singleton] at hp
      rcases hp with rfl
      simp only [List.length_append, List.length_singleton]
      omega

/-- Le filage d'une suite d'étiquettes préserve la fidélité des valeurs
    (induction sur la suite, état initial arbitraire). -/
private theorem canonSlots_vals_nodup {seen : List (Nat × Nat)} {xs : List Nat}
    (hn : SeenValsNodup seen) (hb : SeenValsBounded seen) :
    SeenValsNodup (canonSlots seen xs).2 := by
  induction xs generalizing seen with
  | nil => exact hn
  | cons y ys ih =>
    cases hlk : seen.lookup y with
    | some v =>
      rw [canonSlots_cons_of_some hlk]
      exact ih hn hb
    | none =>
      have hlab : (canonLabel seen y).2 = seen ++ [(y, seen.length + 1)] := by
        unfold canonLabel; rw [hlk]
      have hn' := canonLabel_vals_nodup (seen := seen) (x := y) hn hb
      have hb' := canonLabel_vals_bounded (seen := seen) (x := y) hb
      rw [hlab] at hn' hb'
      rw [canonSlots_cons_of_none hlk]
      exact ih hn' hb'

/-- Le filage d'une suite d'étiquettes préserve le bornage des rangs
    (induction sur la suite, état initial arbitraire). -/
private theorem canonSlots_vals_bounded {seen : List (Nat × Nat)} {xs : List Nat}
    (hb : SeenValsBounded seen) :
    SeenValsBounded (canonSlots seen xs).2 := by
  induction xs generalizing seen with
  | nil => exact hb
  | cons y ys ih =>
    cases hlk : seen.lookup y with
    | some v =>
      rw [canonSlots_cons_of_some hlk]
      exact ih hb
    | none =>
      have hlab : (canonLabel seen y).2 = seen ++ [(y, seen.length + 1)] := by
        unfold canonLabel; rw [hlk]
      have hb' := canonLabel_vals_bounded (seen := seen) (x := y) hb
      rw [hlab] at hb'
      rw [canonSlots_cons_of_none hlk]
      exact ih hb'

/-- **Fil fidèle.** Un fil dont les clés sont distinctes, dont les valeurs
    sont distinctes et bornées : c'est l'état que le filage entre deux
    croisements produit, et c'est la condition que la moitié « extraction »
    consomme. -/
private theorem canonSlots_faithful {seen : List (Nat × Nat)} {xs : List Nat}
    (hk : SeenKeysNodup seen) (hv : SeenValsNodup seen) (hb : SeenValsBounded seen) :
    SeenKeysNodup (canonSlots seen xs).2 ∧
      SeenValsNodup (canonSlots seen xs).2 ∧
      SeenValsBounded (canonSlots seen xs).2 := by
  exact ⟨canonSlots_keys_nodup hk,
    canonSlots_vals_nodup hv hb,
    canonSlots_vals_bounded hb⟩


/-! ## 10. Stabilité du rang (tranche 5)

L'extraction a besoin d'une propriété que les tranches précédentes n'énoncent
pas : **le rang d'une étiquette est le même partout où elle apparaît**. Tant
que le fil est filé d'un croisement à l'autre, une étiquette déjà vue garde son
rang ; c'est ce qui rend le renommage `π` bien défini — l'extraction porte sur
les étiquettes, pas sur les positions.

La clef est que le fil ne fait que **s'agrandir** : `canonLabel` ajoute une
association nouvelle, ou rend l'association existante, sans jamais changer la
valeur portée par une clé déjà présente.

- `ThreadExt` : deux fils compatibles ;
- `lookup_append_ne` / `lookup_append_self` : ce que l'ajout d'une association
  fait aux autres clés, et à la sienne ;
- `canonSlots_ext` : le fil rendu par `canonSlots` étend le fil reçu ;
- `canonSlots_ranks` : **caractérisation** — les numéros produits par
  `canonSlots` sont, pour chaque étiquette, la valeur que le fil final lui
  porte.

Deux détails de Lean core gouvernent la rédaction (mesurés, cf. les sondes) :
`List.lookup` compare la **requête** à la clé stockée (`x == p.1`) et se
déploie en un `match` booléen ; `List.append` est une définition à
récursion bien fondée (`appendTR`), que `simp` ne unfolds pas — la tête
d'une liste appendue s'expose donc par `show` (définitionnelle), pas par `rw`.
Enfin les hypothèses sont réduites par `simp only` : le `simp` complet
réécrit `lookup … = none` en forme d'appartenance, ce qui masquerait la
forme `lookup` attendue par l'hypothèse de récurrence.

Le théorème d'extraction lui-même reste le résidu de la tranche.
-/

/-- Deux fils sont compatibles si toute association portée par le premier est
    encore portée par le second, avec la même valeur. -/
private def ThreadExt (seen seen' : List (Nat × Nat)) : Prop :=
  ∀ x v, seen.lookup x = some v → seen'.lookup x = some v

/-- Le rang canonique d'une étiquette dans un fil : la valeur que le fil lui
    porte, `0` si le fil ne la porte pas. -/
private def threadRank (seen : List (Nat × Nat)) (x : Nat) : Nat :=
  match seen.lookup x with
  | some v => v
  | none => 0

/-- Une clé étrangère à l'ajout ne bouge pas : `lookup` sur la liste étendue
    répond comme sur la liste d'origine. -/
private theorem lookup_append_ne {l : List (Nat × Nat)} {x a : Nat} {v w : Nat}
    (h : l.lookup x = some v) (_hne : x ≠ a) :
    (l ++ [(a, w)]).lookup x = some v := by
  induction l with
  | nil => simp at h
  | cons p t ih =>
    simp only [List.lookup] at h
    by_cases hk : x == p.1
    · simp only [hk] at h
      have hv : p.2 = v := Option.some.inj h
      show List.lookup x (p :: (t ++ [(a, w)])) = some v
      simp only [List.lookup]
      simp only [hk]
      exact congrArg some hv
    · have hk' : (x == p.1) = false := by
        cases hb : x == p.1 with
        | true => exact False.elim (hk hb)
        | false => rfl
      simp only [hk'] at h
      show List.lookup x (p :: (t ++ [(a, w)])) = some v
      simp only [List.lookup]
      simp only [hk']
      exact ih h

/-- Une clé absente du fil est trouvée dans l'ajout qui la porte. -/
private theorem lookup_append_self {l : List (Nat × Nat)} {x : Nat} {w : Nat}
    (h : l.lookup x = none) :
    (l ++ [(x, w)]).lookup x = some w := by
  induction l with
  | nil => simp
  | cons p t ih =>
    simp only [List.lookup] at h
    by_cases hk : x == p.1
    · simp only [hk] at h
      cases h
    · have hk' : (x == p.1) = false := by
        cases hb : x == p.1 with
        | true => exact False.elim (hk hb)
        | false => rfl
      simp only [hk'] at h
      show List.lookup x (p :: (t ++ [(x, w)])) = some w
      simp only [List.lookup]
      simp only [hk']
      exact ih h

/-- Le fil rendu par `canonSlots` étend le fil reçu : aucune association déjà
    portée ne change de valeur. -/
private theorem canonSlots_ext (seen : List (Nat × Nat)) (xs : List Nat) :
    ThreadExt seen (canonSlots seen xs).2 := by
  induction xs generalizing seen with
  | nil =>
    intro x v h
    exact h
  | cons x xs ih =>
    cases hlk : seen.lookup x with
    | some v =>
      rw [canonSlots_cons_of_some hlk]
      intro y w hy
      exact ih seen y w hy
    | none =>
      rw [canonSlots_cons_of_none hlk]
      intro y w hy
      have hne : y ≠ x := by
        intro hyx
        subst hyx
        rw [hlk] at hy
        simp at hy
      have hy' : (seen ++ [(x, seen.length + 1)]).lookup y = some w :=
        lookup_append_ne hy hne
      exact ih (seen ++ [(x, seen.length + 1)]) y w hy'

/-- **Caractérisation des numéros émis.** Les numéros que `canonSlots` produit
    sont, pour chaque étiquette, la valeur que le fil final lui porte : le
    rang d'une étiquette ne dépend donc pas du moment où elle apparaît. -/
private theorem canonSlots_ranks (seen : List (Nat × Nat)) (xs : List Nat) :
    (canonSlots seen xs).1 = xs.map (fun x => threadRank (canonSlots seen xs).2 x) := by
  induction xs generalizing seen with
  | nil => rfl
  | cons x xs ih =>
    cases hlk : seen.lookup x with
    | some v =>
      have hpair : canonSlots seen (x :: xs) =
          (v :: (canonSlots seen xs).1, (canonSlots seen xs).2) :=
        canonSlots_cons_of_some hlk
      have h1 : (canonSlots seen (x :: xs)).1 = v :: (canonSlots seen xs).1 := by
        rw [hpair]
      have h2 : (canonSlots seen (x :: xs)).2 = (canonSlots seen xs).2 := by
        rw [hpair]
      rw [h1, h2]
      rw [List.map_cons]
      rw [ih seen]
      have hext := canonSlots_ext (seen := seen) (xs := xs)
      have hx : (canonSlots seen xs).2.lookup x = some v := hext x v hlk
      have hrank : threadRank (canonSlots seen xs).2 x = v := by
        simp only [threadRank, hx]
      rw [hrank]
    | none =>
      have hpair : canonSlots seen (x :: xs) =
          ((seen.length + 1) :: (canonSlots (seen ++ [(x, seen.length + 1)]) xs).1,
            (canonSlots (seen ++ [(x, seen.length + 1)]) xs).2) :=
        canonSlots_cons_of_none hlk
      have h1 : (canonSlots seen (x :: xs)).1 =
          (seen.length + 1) :: (canonSlots (seen ++ [(x, seen.length + 1)]) xs).1 := by
        rw [hpair]
      have h2 : (canonSlots seen (x :: xs)).2 =
          (canonSlots (seen ++ [(x, seen.length + 1)]) xs).2 := by
        rw [hpair]
      rw [h1, h2]
      rw [List.map_cons]
      rw [ih (seen ++ [(x, seen.length + 1)])]
      have hx' : (seen ++ [(x, seen.length + 1)]).lookup x = some (seen.length + 1) :=
        lookup_append_self hlk
      have hext := canonSlots_ext (seen := seen ++ [(x, seen.length + 1)]) (xs := xs)
      have hx : (canonSlots (seen ++ [(x, seen.length + 1)]) xs).2.lookup x =
          some (seen.length + 1) := hext x (seen.length + 1) hx'
      have hrank : threadRank (canonSlots (seen ++ [(x, seen.length + 1)]) xs).2 x =
          seen.length + 1 := by
        simp only [threadRank, hx]
      rw [hrank]


/-! ## 11. Le fil final d'une liste de croisements (tranche 6)

L'extraction a besoin de deux choses que les tranches précédentes ne donnent
pas encore : le **fil final** d'une liste de croisements (le fil des vues tel
qu'il est rendu après le dernier croisement), et le fait que la rangée
canonique d'un croisement est exactement la liste des **rangs de ses
étiquettes** dans ce fil final.

- `canonThreaded` : les rangées canoniques *et* le fil final ;
- `go_eq_rows` / `canon_eq_rows` : `canon` porte les mêmes rangées que
  `canonThreaded` ;
- `canonThreaded_faithful` : le fil final est fidèle si le fil de départ
  l'était ;
- `canonThreaded_ext` : le fil final **étend** le fil de départ ;
- `canonSlots_lookup_some` : une étiquette filée est portée par le fil
  rendu ;
- `canonThreaded_row_ranks` : **la rangée d'un croisement est la liste des
  rangs de ses quatre étiquettes dans le fil final**.

C'est cette dernière propriété qui fait le lien entre les deux moitiés :
l'égalité `canon l = canon l'` porte alors sur des *rangs*, et non plus sur
des positions.
-/

/-- Deux listes se correspondent point à point. -/
private theorem map_eq_of_pointwise {l : List Nat} {f g : Nat → Nat}
    (h : ∀ x ∈ l, f x = g x) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    have hx := h x (by simp)
    have hxs : ∀ y ∈ xs, f y = g y := by
      intro y hy
      exact h y (by simp [hy])
    rw [hx, ih hxs]

/-- Les rangées canoniques d'une liste de croisements, et le fil des vues tel
    qu'il est rendu après le dernier croisement. -/
private def canonThreaded :
    List PDCrossing → List (Nat × Nat) → List (List Nat) × List (Nat × Nat)
  | [], seen => ([], seen)
  | c :: cs, seen =>
      let (ys, seen') := canonSlots seen [c.e1, c.e2, c.e3, c.e4]
      let (rows, seen'') := canonThreaded cs seen'
      (ys :: rows, seen'')

/-- `canon.go` et `canonThreaded` portent les mêmes rangées. -/
private theorem go_eq_rows (l : List PDCrossing) (seen : List (Nat × Nat)) :
    canon.go l seen = (canonThreaded l seen).1 := by
  induction l generalizing seen with
  | nil => rfl
  | cons c cs ih =>
    have hgo : canon.go (c :: cs) seen =
        (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).1 ::
          canon.go cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2 := rfl
    have hct : (canonThreaded (c :: cs) seen).1 =
        (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).1 ::
          (canonThreaded cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).1 := rfl
    rw [hgo, hct, ih]

/-- `canon` et `canonThreaded` portent les mêmes rangées. -/
private theorem canon_eq_rows (l : List PDCrossing) :
    canon l = (canonThreaded l []).1 := by
  exact go_eq_rows l []

/-- Le fil final est fidèle si le fil de départ l'était. -/
private theorem canonThreaded_faithful {l : List PDCrossing} {seen : List (Nat × Nat)}
    (hk : SeenKeysNodup seen) (hv : SeenValsNodup seen) (hb : SeenValsBounded seen) :
    SeenKeysNodup (canonThreaded l seen).2 ∧
      SeenValsNodup (canonThreaded l seen).2 ∧
      SeenValsBounded (canonThreaded l seen).2 := by
  induction l generalizing seen with
  | nil => exact ⟨hk, hv, hb⟩
  | cons c cs ih =>
    have hcs := canonSlots_faithful (seen := seen) (xs := [c.e1, c.e2, c.e3, c.e4]) hk hv hb
    have hct : (canonThreaded (c :: cs) seen).2 =
        (canonThreaded cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).2 := rfl
    rw [hct]
    exact ih hcs.1 hcs.2.1 hcs.2.2

/-- La compatibilité des fils est transitive. -/
private theorem ThreadExt.trans {a b c : List (Nat × Nat)}
    (hab : ThreadExt a b) (hbc : ThreadExt b c) : ThreadExt a c := by
  intro x v h
  exact hbc x v (hab x v h)

/-- Le fil final **étend** le fil de départ : toute association portée par le
    fil de départ l'est encore par le fil final, avec la même valeur. -/
private theorem canonThreaded_ext :
    ∀ (l : List PDCrossing) (seen : List (Nat × Nat)),
      ∀ x v, seen.lookup x = some v → (canonThreaded l seen).2.lookup x = some v := by
  intro l
  induction l with
  | nil =>
    intro seen x v h
    exact h
  | cons c cs ih =>
    intro seen x v h
    have h1 := canonSlots_ext (seen := seen) (xs := [c.e1, c.e2, c.e3, c.e4]) x v h
    have h2 := ih (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2 x v h1
    have hct : (canonThreaded (c :: cs) seen).2 =
        (canonThreaded cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).2 := rfl
    rw [hct]
    exact h2

/-- Une étiquette filée est portée par le fil rendu. -/
private theorem canonSlots_lookup_some {seen : List (Nat × Nat)} {xs : List Nat} {x : Nat}
    (hx : x ∈ xs) : ∃ v, (canonSlots seen xs).2.lookup x = some v := by
  induction xs generalizing seen with
  | nil => simp at hx
  | cons y ys ih =>
    cases hlk : seen.lookup y with
    | some v =>
      have hpair := congrArg Prod.snd
        (canonSlots_cons_of_some (seen := seen) (x := y) (v := v) (xs := ys) hlk)
      have hext := canonSlots_ext (seen := seen) (xs := ys)
      rw [hpair]
      simp only [List.mem_cons] at hx
      rcases hx with hxy | hx
      · exact ⟨v, hext x v (hxy ▸ hlk)⟩
      · obtain ⟨w, hw⟩ := ih (seen := seen) hx
        exact ⟨w, hw⟩
    | none =>
      have hpair := congrArg Prod.snd
        (canonSlots_cons_of_none (seen := seen) (x := y) (xs := ys) hlk)
      have hy : (seen ++ [(y, seen.length + 1)]).lookup y = some (seen.length + 1) :=
        lookup_append_self hlk
      have hext := canonSlots_ext (seen := seen ++ [(y, seen.length + 1)]) (xs := ys)
      rw [hpair]
      simp only [List.mem_cons] at hx
      rcases hx with hxy | hx
      · exact ⟨seen.length + 1, hxy ▸ hext y (seen.length + 1) hy⟩
      · obtain ⟨w, hw⟩ := ih (seen := seen ++ [(y, seen.length + 1)]) hx
        exact ⟨w, hw⟩

/-- **La rangée d'un croisement est la liste des rangs de ses quatre
    étiquettes dans le fil final.** C'est la propriété qui relie les deux
    moitiés du pont : le nombre canonique d'un slot est le rang de son
    étiquette dans le fil rendu, et non une position. -/
private theorem canonThreaded_row_ranks {c : PDCrossing} {cs : List PDCrossing}
    {seen : List (Nat × Nat)} :
    (canonThreaded (c :: cs) seen).1 =
      [c.e1, c.e2, c.e3, c.e4].map (fun x => threadRank (canonThreaded (c :: cs) seen).2 x) ::
        (canonThreaded cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).1 := by
  have hranks := canonSlots_ranks (seen := seen) (xs := [c.e1, c.e2, c.e3, c.e4])
  have hct : (canonThreaded (c :: cs) seen).1 =
      (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).1 ::
        (canonThreaded cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).1 := rfl
  have hext : ∀ x v,
      (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2.lookup x = some v →
        (canonThreaded (c :: cs) seen).2.lookup x = some v := by
    intro x v h
    have hct2 : (canonThreaded (c :: cs) seen).2 =
        (canonThreaded cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).2 := rfl
    rw [hct2]
    exact canonThreaded_ext cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2 x v h
  have hcarried : ∀ x ∈ [c.e1, c.e2, c.e3, c.e4],
      ∃ v, (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2.lookup x = some v := by
    intro x hx
    exact canonSlots_lookup_some hx
  have hrank : ∀ x ∈ [c.e1, c.e2, c.e3, c.e4],
      threadRank (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2 x =
        threadRank (canonThreaded (c :: cs) seen).2 x := by
    intro x hx
    obtain ⟨v, hv⟩ := hcarried x hx
    have hT : (canonThreaded (c :: cs) seen).2.lookup x = some v := hext x v hv
    simp only [threadRank, hv, hT]
  rw [hct, hranks]
  exact congrArg (fun l => l :: (canonThreaded cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).1)
    (map_eq_of_pointwise (l := [c.e1, c.e2, c.e3, c.e4]) hrank)

/-! ## 12. L'injectivité du rang (tranche 7)

L'extraction a besoin que le renommage `π` soit **bien défini** : une étiquette
ne doit correspondre qu'à un seul rang, et un rang à une seule étiquette. La
première moitié est `SeenKeysNodup` (§8) ; celle-ci est la seconde — un rang
donné n'est porté que par une seule étiquette.

- `mem_of_lookup` : ce que `lookup` retourne est effectivement porté par le fil ;
- `pair_eq_of_mem_of_snd_eq` : dans un fil dont les **valeurs** sont distinctes,
  deux associations de même valeur sont la même association ;
- `threadRank_inj` : **le rang est injectif** sur les étiquettes portées.
-/

/-- Ce que `lookup` retourne est effectivement porté par le fil. -/
private theorem mem_of_lookup {l : List (Nat × Nat)} {x v : Nat}
    (h : l.lookup x = some v) : (x, v) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p t ih =>
    simp only [List.lookup] at h
    by_cases hk : x == p.1
    · simp only [hk] at h
      have hx : x = p.1 := by simpa using hk
      have hv : p.2 = v := Option.some.inj h
      have hp : (x, v) = p := by
        rcases p with ⟨a, b⟩
        simp only at hx hv
        subst hx
        subst hv
        rfl
      rw [hp]
      exact List.mem_cons_self
    · simp only [hk] at h
      exact List.mem_cons_of_mem p (ih h)

/-- Dans un fil dont les valeurs sont distinctes, deux associations de même
    valeur sont la même association. -/
private theorem pair_eq_of_mem_of_snd_eq {l : List (Nat × Nat)}
    (hv : SeenValsNodup l) {x y v : Nat}
    (hx : (x, v) ∈ l) (hy : (y, v) ∈ l) : x = y := by
  unfold SeenValsNodup at hv
  induction l with
  | nil => simp at hx
  | cons p t ih =>
    simp only [List.map_cons, List.nodup_cons] at hv
    obtain ⟨hnotin, hnodup⟩ := hv
    simp only [List.mem_cons] at hx hy
    rcases hx with hxp | hxt
    · rcases hy with hyp | hyt
      · exact congrArg Prod.fst (hxp.trans hyp.symm)
      · exfalso
        have hp2 : p.2 = v := by rw [← hxp]
        have hmem : v ∈ t.map Prod.snd := List.mem_map_of_mem hyt
        rw [← hp2] at hmem
        exact hnotin hmem
    · rcases hy with hyp | hyt
      · exfalso
        have hp2 : p.2 = v := by rw [← hyp]
        have hmem : v ∈ t.map Prod.snd := List.mem_map_of_mem hxt
        rw [← hp2] at hmem
        exact hnotin hmem
      · exact ih hnodup hxt hyt

/-- **Le rang est injectif** sur les étiquettes portées : deux étiquettes
    portées par le fil avec le même rang sont la même étiquette. -/
private theorem threadRank_inj {seen : List (Nat × Nat)} (hv : SeenValsNodup seen)
    {x y vx vy : Nat} (hx : seen.lookup x = some vx) (hy : seen.lookup y = some vy)
    (h : threadRank seen x = threadRank seen y) : x = y := by
  have h2 : vx = vy := by simpa only [threadRank, hx, hy] using h
  have hy' : seen.lookup y = some vx := by rw [h2]; exact hy
  exact pair_eq_of_mem_of_snd_eq hv (mem_of_lookup hx) (mem_of_lookup hy')

/-! ## 13. La suite des rangs portés (tranche 8)

Jusqu'ici le fil était décrit par des **bornes** : ses rangs vivent entre `1` et
la taille du fil (§9). C'est nécessaire, mais insuffisant pour l'extraction :
pour retrouver l'étiquette d'un rang donné, il faut que la suite des rangs
portés soit **exactement** `1, 2, …, n` — sans trou et dans cet ordre.

C'est ce que pose cette section :

- `ThreadRanks` : le fil porte la suite `1 … n` ;
- `canonLabel_threadRanks`, `canonSlots_threadRanks`, `canonThreaded_threadRanks` : le filage
  **préserve** cette suite (un rang nouveau la prolonge d'un cran) ;
- `lookup_eq_some_of_mem` : une entrée du fil est bien celle que `lookup`
  retourne ;
- `rank_covered` : **tout** rang de `1 … n` est porté par une étiquette du
  fil ;
- `rank_unique_label` : **à un rang donné correspond exactement une
  étiquette** (existence par la suite, unicité par l'injectivité du rang, §12).

C'est la seconde moitié de la bonne définition de `π` : `SeenKeysNodup` (§8)
dit qu'une étiquette n'a qu'un rang, `ThreadRanks` dit qu'un rang n'a qu'une
étiquette.
-/

/-- La suite des rangs `1 … n`. -/
private def rankSeq (n : Nat) : List Nat := (List.range n).map (fun k => k + 1)

/-- La suite `1 … n` prolongée de `n+1` est la suite `1 … (n+1)`. -/
private theorem rankSeq_succ (n : Nat) : rankSeq (n + 1) = rankSeq n ++ [n + 1] := by
  unfold rankSeq
  rw [List.range_succ, List.map_append, List.map_singleton]

/-- Le fil porte les rangs `1 … n`, dans cet ordre. -/
private def ThreadRanks (seen : List (Nat × Nat)) : Prop :=
  seen.map Prod.snd = rankSeq seen.length

/-- Le fil vide porte la suite vide. -/
private theorem threadRanks_nil : ThreadRanks [] := by
  simp [ThreadRanks, rankSeq]

/-- `canonLabel` préserve la suite des rangs : un rang déjà porté ne bouge pas,
    un rang nouveau la prolonge d'un cran. -/
private theorem canonLabel_threadRanks {seen : List (Nat × Nat)} {x : Nat}
    (h : ThreadRanks seen) : ThreadRanks (canonLabel seen x).2 := by
  unfold ThreadRanks
  cases hlk : seen.lookup x with
  | some v =>
    have hsame : (canonLabel seen x).2 = seen := by
      unfold canonLabel; rw [hlk]
    rw [hsame]
    exact h
  | none =>
    rw [show (canonLabel seen x).2 = seen ++ [(x, seen.length + 1)] by
      unfold canonLabel; rw [hlk]]
    simp only [List.map_append, List.map_singleton, List.length_append,
      List.length_singleton]
    rw [h, rankSeq_succ]

/-- Le filage d'une suite d'étiquettes préserve la suite des rangs (induction
    sur la suite, état initial arbitraire). -/
private theorem canonSlots_threadRanks {seen : List (Nat × Nat)} {xs : List Nat}
    (h : ThreadRanks seen) : ThreadRanks (canonSlots seen xs).2 := by
  induction xs generalizing seen with
  | nil =>
    simp only [canonSlots]
    exact h
  | cons y ys ih =>
    cases hlk : seen.lookup y with
    | some v =>
      rw [canonSlots_cons_of_some hlk]
      exact ih h
    | none =>
      have hlab : (canonLabel seen y).2 = seen ++ [(y, seen.length + 1)] := by
        unfold canonLabel; rw [hlk]
      have hk' := canonLabel_threadRanks (seen := seen) (x := y) h
      rw [hlab] at hk'
      rw [canonSlots_cons_of_none hlk]
      exact ih hk'

/-- Le fil final d'une liste de croisements porte la suite des rangs. -/
private theorem canonThreaded_threadRanks {l : List PDCrossing} {seen : List (Nat × Nat)}
    (h : ThreadRanks seen) : ThreadRanks (canonThreaded l seen).2 := by
  induction l generalizing seen with
  | nil =>
    simp only [canonThreaded]
    exact h
  | cons c cs ih =>
    have hcs := canonSlots_threadRanks (seen := seen)
      (xs := [c.e1, c.e2, c.e3, c.e4]) h
    have hct : (canonThreaded (c :: cs) seen).2 =
        (canonThreaded cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).2 := rfl
    rw [hct]
    exact ih hcs

/-- Une entrée du fil est bien celle que `lookup` retourne : à clés distinctes,
    la requête qui vise une entrée en retourne la valeur. -/
private theorem lookup_eq_some_of_mem (l : List (Nat × Nat))
    (hk : SeenKeysNodup l) (p : Nat × Nat) (hp : p ∈ l) :
    l.lookup p.1 = some p.2 := by
  induction l with
  | nil => simp at hp
  | cons q t ih =>
    unfold SeenKeysNodup at hk
    simp only [List.map_cons, List.nodup_cons] at hk
    obtain ⟨hnotin, hnodup⟩ := hk
    simp only [List.mem_cons] at hp
    rcases hp with hpq | hpt
    · subst hpq
      simp only [List.lookup, beq_self_eq_true]
    · have hne : (p.1 == q.1) = false := by
        rw [beq_eq_false_iff_ne]
        intro hqc
        apply hnotin
        rw [← hqc]
        exact List.mem_map.mpr ⟨p, hpt, rfl⟩
      simp only [List.lookup, hne]
      exact ih hnodup hpt

/-- **Tout** rang du fil est porté par une étiquette du fil : la suite `1 … n`
    est couverte. -/
private theorem rank_covered {seen : List (Nat × Nat)} (h : ThreadRanks seen)
    (hk : SeenKeysNodup seen) {r : Nat} (hr : 1 ≤ r ∧ r ≤ seen.length) :
    ∃ x, seen.lookup x = some r := by
  have hr1 : r - 1 ∈ List.range seen.length := by
    rw [List.mem_range]
    omega
  have hmem : r ∈ seen.map Prod.snd := by
    rw [ThreadRanks] at h
    unfold rankSeq at h
    rw [h, List.mem_map]
    exact ⟨r - 1, hr1, by omega⟩
  obtain ⟨p, hp, hpv⟩ := List.mem_map.mp hmem
  refine ⟨p.1, ?_⟩
  rw [lookup_eq_some_of_mem seen hk p hp]
  exact congrArg some hpv

/-- **À un rang donné correspond exactement une étiquette** du fil :
    l'existence vient de la suite des rangs, l'unicité de l'injectivité du
    rang (§12). -/
private theorem rank_unique_label {seen : List (Nat × Nat)}
    (hv : SeenValsNodup seen) (hk : SeenKeysNodup seen) (hr : ThreadRanks seen)
    {r : Nat} (hb : 1 ≤ r ∧ r ≤ seen.length) :
    (∃ x, seen.lookup x = some r) ∧
      ∀ x y, seen.lookup x = some r → seen.lookup y = some r → x = y := by
  constructor
  · exact rank_covered hr hk hb
  · intro x y hx hy
    exact threadRank_inj hv hx hy (by simp [threadRank, hx, hy])
/-! ## 14. La correspondance des rangées (tranche 9)

L'égalité `canon l = canon l'` porte sur des **rangées** : à chaque croisement de
`l` correspond un croisement de `l'`, et les **quatre slots** se correspondent
positionnellement. C'est la propriété qui permet de composer le renommage : le
slot `j` d'un croisement de `l` et le slot `j` du croisement correspondant de
`l'` portent le **même rang** dans leurs fils finaux respectifs.

Les rangs sont pris dans le fil final de la **sous-liste courante** : le fil
final d'une liste est celui de sa dernière sous-liste, filée depuis l'état
qu'elle reçoit — d'où la récursion parallèle sur les deux listes.

- `RowsCorrespond` : la correspondance, énoncée comme une récursion parallèle ;
- `four_slots_eq` : deux rangées de quatre slots égales se correspondent
  positionnellement ;
- `rows_correspond` : deux listes qui portent les mêmes rangées canoniques se
  correspondent rang par rang, slot par slot.
-/

/-- Deux listes de quatre slots égales se correspondent positionnellement :
    le slot de rang `j` d'un côté est apparié au slot de rang `j` de l'autre. -/
private theorem four_slots_eq {a b c d a' b' c' d' : Nat} {f g : Nat → Nat}
    (h : [a, b, c, d].map f = [a', b', c', d'].map g) :
    f a = g a' ∧ f b = g b' ∧ f c = g c' ∧ f d = g d' := by
  simp only [List.map] at h
  rcases List.cons.inj h with ⟨h1, h2⟩
  rcases List.cons.inj h2 with ⟨h2', h3⟩
  rcases List.cons.inj h3 with ⟨h3', h4⟩
  rcases List.cons.inj h4 with ⟨h4', _⟩
  exact ⟨h1, h2', h3', h4'⟩

/-- Deux listes de croisements se correspondent si, à chaque croisement
    mutuellement apparié, les quatre slots portent le même rang. Les rangs sont
    pris dans le fil final de la sous-liste courante — le fil final de la liste
    entière étant celui de sa dernière sous-liste, filée depuis l'état qu'elle
    reçoit. -/
private def RowsCorrespond (seen seen' : List (Nat × Nat)) (cs cs' : List PDCrossing) : Prop :=
  match cs, cs' with
  | [], [] => True
  | c :: tl, c' :: tl' =>
      (threadRank (canonThreaded (c :: tl) seen).2 c.e1 =
          threadRank (canonThreaded (c' :: tl') seen').2 c'.e1) ∧
      (threadRank (canonThreaded (c :: tl) seen).2 c.e2 =
          threadRank (canonThreaded (c' :: tl') seen').2 c'.e2) ∧
      (threadRank (canonThreaded (c :: tl) seen).2 c.e3 =
          threadRank (canonThreaded (c' :: tl') seen').2 c'.e3) ∧
      (threadRank (canonThreaded (c :: tl) seen).2 c.e4 =
          threadRank (canonThreaded (c' :: tl') seen').2 c'.e4) ∧
      RowsCorrespond (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2
        (canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).2 tl tl'
  | _, _ => False

/-- **Deux listes qui portent les mêmes rangées canoniques se correspondent
    rang par rang, slot par slot.** C'est le lemme qui relie les deux moitiés du
    pont : l'égalité `canon l = canon l'` associe à chaque croisement de `l` un
    croisement de `l'`, et à chaque slot un slot — par l'égalité des rangs. -/
private theorem rows_correspond :
    ∀ (cs : List PDCrossing) (seen seen' : List (Nat × Nat)) (cs' : List PDCrossing),
      (canonThreaded cs seen).1 = (canonThreaded cs' seen').1 →
      RowsCorrespond seen seen' cs cs' := by
  intro cs
  induction cs with
  | nil =>
      intro seen seen' cs' h
      cases cs' with
      | nil => trivial
      | cons c' tl' =>
          have hne : (canonThreaded (c' :: tl') seen').1 ≠ [] := by
            intro hh
            have hct : (canonThreaded (c' :: tl') seen').1 =
                (canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).1 ::
                  (canonThreaded tl' (canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).2).1 := rfl
            rw [hct] at hh
            exact (List.cons_ne_nil _ _ hh).elim
          exact absurd (h.symm.trans rfl) hne
  | cons c tl ih =>
      intro seen seen' cs' h
      cases cs' with
      | nil =>
          have hne : (canonThreaded (c :: tl) seen).1 ≠ [] := by
            intro hh
            have hct : (canonThreaded (c :: tl) seen).1 =
                (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).1 ::
                  (canonThreaded tl (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).1 := rfl
            rw [hct] at hh
            exact (List.cons_ne_nil _ _ hh).elim
          exact absurd h hne
      | cons c' tl' =>
          have hct1 : (canonThreaded (c :: tl) seen).1 =
              (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).1 ::
                (canonThreaded tl (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).1 := rfl
          have hct2 : (canonThreaded (c' :: tl') seen').1 =
              (canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).1 ::
                (canonThreaded tl' (canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).2).1 := rfl
          rw [hct1, hct2] at h
          rcases List.cons.inj h with ⟨hhead, htail⟩
          have hr1 := canonThreaded_row_ranks (c := c) (cs := tl) (seen := seen)
          have hr2 := canonThreaded_row_ranks (c := c') (cs := tl') (seen := seen')
          have hrow1 : ([c.e1, c.e2, c.e3, c.e4].map
                  (fun x => threadRank (canonThreaded (c :: tl) seen).2 x) ::
                (canonThreaded tl (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).1) =
              ((canonSlots seen [c.e1, c.e2, c.e3, c.e4]).1 ::
                (canonThreaded tl (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).1) :=
            hr1.symm.trans hct1
          rcases List.cons.inj hrow1 with ⟨hmap, _⟩
          have hrow2 : ([c'.e1, c'.e2, c'.e3, c'.e4].map
                  (fun x => threadRank (canonThreaded (c' :: tl') seen').2 x) ::
                (canonThreaded tl' (canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).2).1) =
              ((canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).1 ::
                (canonThreaded tl' (canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).2).1) :=
            hr2.symm.trans hct2
          rcases List.cons.inj hrow2 with ⟨hmap', _⟩
          have hmap'' : ([c.e1, c.e2, c.e3, c.e4].map
                (fun x => threadRank (canonThreaded (c :: tl) seen).2 x)) =
              ([c'.e1, c'.e2, c'.e3, c'.e4].map
                (fun x => threadRank (canonThreaded (c' :: tl') seen').2 x)) :=
            hmap.trans (hhead.trans hmap'.symm)
          rcases four_slots_eq hmap'' with ⟨h1, h2, h3, h4⟩
          refine ⟨h1, h2, h3, h4, ?_⟩
          exact ih (seen := (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2)
              (seen' := (canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).2)
              (cs' := tl') htail

/-! ## 15. L'étiquette d'un rang (tranche 9)

Les tranches précédentes ont établi qu'un rang porté par un fil est porté par
**une** étiquette (§13) et qu'à un rang donné correspond **exactement une**
étiquette (§13). Il manquait l'**opérateur** qui retrouve l'étiquette d'un rang
donné : sans lui, le renommage `π` ne peut pas être écrit.

- `pairOfRank` : la première association du fil qui porte le rang demandé ;
- `pairOfRank_mem` / `pairOfRank_none` : ce qu'elle garantit, et son contraire ;
- `labelOfRank` : l'étiquette qui porte le rang ;
- `labelOfRank_spec` : l'étiquette rendue est bien celle que `lookup` rend ;
- `labelOfRank_exists` : tout rang porté est porté par l'étiquette rendue ;
- `labelOfRank_inj` : deux rangs distincts ne sont jamais portés par la même
  étiquette.
-/

/-- La première association du fil `t` qui porte le rang `r`. -/
private def pairOfRank : List (Nat × Nat) → Nat → Option (Nat × Nat)
  | [], _ => none
  | p :: t, r => if p.2 = r then some p else pairOfRank t r

/-- L'association rendue par `pairOfRank` est bien dans le fil, et porte le
    rang demandé. -/
private theorem pairOfRank_mem {t : List (Nat × Nat)} {r : Nat} {p : Nat × Nat}
    (h : pairOfRank t r = some p) : p ∈ t ∧ p.2 = r := by
  induction t with
  | nil => simp [pairOfRank] at h
  | cons q t ih =>
      by_cases hq : q.2 = r
      · have hq' : pairOfRank (q :: t) r = some q := by simp [pairOfRank, hq]
        rw [hq'] at h
        have hpq : p = q := (Option.some.inj h).symm
        subst hpq
        exact ⟨List.mem_cons_self, hq⟩
      · have hq' : pairOfRank (q :: t) r = pairOfRank t r := by simp [pairOfRank, hq]
        rw [hq'] at h
        obtain ⟨hm, hv⟩ := ih h
        exact ⟨List.mem_cons_of_mem q hm, hv⟩

/-- Aucune association du fil ne porte le rang demandé quand `pairOfRank` ne
    rend rien. -/
private theorem pairOfRank_none {t : List (Nat × Nat)} {r : Nat}
    (h : pairOfRank t r = none) : ∀ p ∈ t, p.2 ≠ r := by
  induction t with
  | nil => intro p hp; simp at hp
  | cons q t ih =>
      intro p hp
      by_cases hq : q.2 = r
      · have hq' : pairOfRank (q :: t) r = some q := by simp [pairOfRank, hq]
        rw [hq'] at h
        simp at h
      · have hq' : pairOfRank (q :: t) r = pairOfRank t r := by simp [pairOfRank, hq]
        rw [hq'] at h
        rcases List.mem_cons.mp hp with hpq | hpt
        · rw [hpq]
          exact hq
        · exact ih h p hpt

/-- L'étiquette qui porte le rang `r` dans le fil `t`. -/
private def labelOfRank (t : List (Nat × Nat)) (r : Nat) : Option Nat :=
  (pairOfRank t r).map Prod.fst

/-- L'étiquette rendue par `labelOfRank` est bien celle que `lookup` rend : à
    clés distinctes, elle porte bien le rang demandé. -/
private theorem labelOfRank_spec {t : List (Nat × Nat)} (hk : SeenKeysNodup t)
    {r y : Nat} (h : labelOfRank t r = some y) : t.lookup y = some r := by
  unfold labelOfRank at h
  cases hp : pairOfRank t r with
  | none => simp [hp] at h
  | some p =>
      have hmem := pairOfRank_mem hp
      have hlookup := lookup_eq_some_of_mem t hk p hmem.1
      have hpy : p.1 = y := by
        simp [hp] at h
        exact h
      calc t.lookup y = t.lookup p.1 := by rw [hpy]
        _ = some p.2 := hlookup
        _ = some r := by rw [hmem.2]

/-- **Tout** rang porté par le fil est porté par l'étiquette que `labelOfRank`
    rend. L'existence vient de la suite des rangs (§13), l'unicité de
    l'injectivité des valeurs (§12). -/
private theorem labelOfRank_exists {t : List (Nat × Nat)} (hv : SeenValsNodup t)
    (hk : SeenKeysNodup t) (hr : ThreadRanks t) {r : Nat} (hb : 1 ≤ r ∧ r ≤ t.length) :
    ∃ y, labelOfRank t r = some y ∧ t.lookup y = some r := by
  obtain ⟨x, hx⟩ := rank_covered hr hk hb
  have hmem := mem_of_lookup hx
  have hnone : pairOfRank t r ≠ none := by
    intro hn
    exact absurd rfl (pairOfRank_none hn (x, r) hmem)
  cases hp : pairOfRank t r with
  | none => exact absurd hp hnone
  | some p =>
      have hpm := pairOfRank_mem hp
      have hpm' : (p.1, r) ∈ t := by rw [← hpm.2]; exact hpm.1
      have hpx : p.1 = x := pair_eq_of_mem_of_snd_eq hv hpm' hmem
      refine ⟨p.1, ?_, ?_⟩
      · simp [labelOfRank, hp]
      · rw [hpx]
        exact hx

/-- Deux rangs distincts ne sont jamais portés par la même étiquette. -/
private theorem labelOfRank_inj {t : List (Nat × Nat)} (hk : SeenKeysNodup t)
    {r s y z : Nat} (hr : labelOfRank t r = some y) (hs : labelOfRank t s = some z)
    (hne : r ≠ s) : y ≠ z := by
  intro h
  subst h
  have h1 := labelOfRank_spec hk hr
  have h2 := labelOfRank_spec hk hs
  rw [h1] at h2
  exact hne (Option.some.inj h2)

end Knots.AnyMoves

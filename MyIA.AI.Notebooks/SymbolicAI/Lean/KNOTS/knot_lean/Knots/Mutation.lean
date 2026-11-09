/-
  Knots.Mutation — Mutation de Conway
  ====================================

  Une mutation de Conway prend un nœud K muni d'une sphère de Conway (rencontre K
  en 4 points), le découpe le long de la sphère, effectue une rotation de 180°,
  puis recolle. La mutation préserve le polynôme d'Alexander et le polynôme de
  Jones — c'est le socle de la paire Conway / Kinoshita-Terasaka (§2-3 du
  monolithe historique, désormais `Knots.ConwayPD`).

  Extrait de `Knots.Conway` (tranche 2 du split #18397, tranche 1 = `Knots.Slice`
  en #18528). Epic #2874.
-/

import Knots.Basic
import Knots.Reidemeister

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

/-! ### Mutation de sphère : rotation du tangle + recollement des points de bord

La fenêtre seule (`mutateWindow`) tourne les positions des étiquettes dans
chaque croisement intérieur — mesure c130 : insuffisante pour relier les
codes census Conway/KT. La mutation de sphère complète ajoute la seconde
moitié du geste géométrique : après le demi-tour du tangle, ses **quatre
points de bord** se recollent aux quatre arcs extérieurs dans un ordre
permuté. Au niveau PD : chaque occurrence intérieure d'une étiquette de
bord est réécrite par une permutation σ des étiquettes de bord (chaque
étiquette de bord ayant exactement une occurrence intérieure et une
extérieure, l'image reste un code PD bi-étiqueté dès que σ est injective
sur son support).
-/


/-- Recollement des points de bord : dans la fenêtre [i, j), chaque
étiquette est réécrite par σ ; hors de la fenêtre, rien ne bouge. -/
def reattachWindow : List PDCrossing → Nat → Nat → (Nat → Nat) → List PDCrossing
  | [], _, _, _ => []
  | c :: cs', 0, 0, _ => c :: cs'
  | c :: cs', 0, j+1, σ => ⟨σ c.e1, σ c.e2, σ c.e3, σ c.e4⟩ :: reattachWindow cs' 0 j σ
  | c :: cs', _+1, 0, _ => c :: cs'
  | c :: cs', i+1, j+1, σ => c :: reattachWindow cs' i j σ

/-- Le recollement préserve le nombre de croisements. -/
theorem reattachWindow_length (cs : List PDCrossing) (i j : Nat) (σ : Nat → Nat) :
    (reattachWindow cs i j σ).length = cs.length := by
  induction cs generalizing i j with
  | nil => rfl
  | cons c cs' ih =>
    match i, j with
    | 0, 0 => rfl
    | 0, _+1 => simp [reattachWindow, ih]
    | _+1, 0 => rfl
    | _+1, _+1 => simp [reattachWindow, ih]

/-- Fenêtre vide : le recollement y est l'identité, pour toute liste. -/
theorem reattachWindow_zero_window (cs : List PDCrossing) (σ : Nat → Nat) :
    reattachWindow cs 0 0 σ = cs := by
  cases cs <;> rfl

/-- Recollement par l'identité : aucune étiquette n'est réécrite. -/
theorem reattachWindow_id (cs : List PDCrossing) (i j : Nat) :
    reattachWindow cs i j id = cs := by
  induction cs generalizing i j with
  | nil => rfl
  | cons c cs' ih =>
    match i, j with
    | 0, 0 => rfl
    | 0, j+1 => simp only [reattachWindow, id_eq, ih 0 j]
    | _+1, 0 => rfl
    | _+1, _+1 => simp only [reattachWindow, ih _ _]

/-- Le recollement est involutif dès que σ l'est (`σ ∘ σ = id` pointwise) :
deux recollements successifs par la même involution redonnent la liste
initiale. C'est le cas d'une vraie mutation — le recollement est un demi-tour
de la sphère à quatre points, donc un élément du groupe de Klein. -/
theorem reattachWindow_involutive (cs : List PDCrossing) (i j : Nat) (σ : Nat → Nat)
    (hσ : ∀ x, σ (σ x) = x) :
    reattachWindow (reattachWindow cs i j σ) i j σ = cs := by
  induction cs generalizing i j with
  | nil => rfl
  | cons c cs' ih =>
    match i, j with
    | 0, 0 => rfl
    | 0, j+1 =>
      simp only [reattachWindow, hσ c.e1, hσ c.e2, hσ c.e3, hσ c.e4, ih 0 j]
    | _+1, 0 => rfl
    | _+1, _+1 => simp only [reattachWindow, ih _ _]

/-- La rotation de Klein après recollement : permuter les positions des
étiquettes puis réécrire leurs valeurs = réécrire les valeurs puis permuter
les positions. -/
theorem KleinRot.apply_reattach (ρ : KleinRot) (σ : Nat → Nat) (c : PDCrossing) :
    ρ.apply ⟨σ c.e1, σ c.e2, σ c.e3, σ c.e4⟩ =
      ⟨σ (ρ.apply c).e1, σ (ρ.apply c).e2, σ (ρ.apply c).e3, σ (ρ.apply c).e4⟩ := by
  cases ρ <;> rfl

/-- La rotation et le recollement d'une même fenêtre **commutent** : ρ permute
les positions des étiquettes, σ en réécrit les valeurs. -/
theorem mutateWindow_reattachWindow_comm (cs : List PDCrossing) (i j : Nat)
    (ρ : KleinRot) (σ : Nat → Nat) :
    mutateWindow (reattachWindow cs i j σ) i j ρ =
      reattachWindow (mutateWindow cs i j ρ) i j σ := by
  induction cs generalizing i j with
  | nil => rfl
  | cons c cs' ih =>
    match i, j with
    | 0, 0 => rfl
    | 0, j+1 =>
      simp only [reattachWindow, mutateWindow, ih 0 j, KleinRot.apply_reattach]
    | _+1, 0 => rfl
    | _+1, _+1 => simp only [reattachWindow, mutateWindow, ih _ _]

/-- **Mutation de sphère de Conway au niveau PD** : rotation de Klein ρ des
croisements de la fenêtre [i, j) (le tangle intérieur), puis recollement
des occurrences intérieures des étiquettes de bord par σ. L'extérieur de
la fenêtre est inchangé. C'est la traduction combinatoire complète du geste
découper / tourner de 180° / recoller. -/
def sphereMutate (cs : List PDCrossing) (i j : Nat) (ρ : KleinRot) (σ : Nat → Nat) :
    List PDCrossing :=
  reattachWindow (mutateWindow cs i j ρ) i j σ

/-- La mutation de sphère préserve le nombre de croisements. -/
theorem sphereMutate_length (cs : List PDCrossing) (i j : Nat) (ρ : KleinRot)
    (σ : Nat → Nat) :
    (sphereMutate cs i j ρ σ).length = cs.length := by
  rw [sphereMutate, reattachWindow_length, mutateWindow_length]

/-- La mutation de sphère est **involutive** dès que σ est involutif : muter
deux fois la même sphère avec la même rotation et le même recollement redonne
le diagramme initial. C'est le geste géométrique — deux demi-tours = identité —
et la raison pour laquelle la relation de mutation est symétrique. -/
theorem sphereMutate_involutive (cs : List PDCrossing) (i j : Nat) (ρ : KleinRot)
    (σ : Nat → Nat) (hσ : ∀ x, σ (σ x) = x) :
    sphereMutate (sphereMutate cs i j ρ σ) i j ρ σ = cs := by
  simp only [sphereMutate]
  rw [mutateWindow_reattachWindow_comm, mutateWindow_involutive]
  exact reattachWindow_involutive cs i j σ hσ

/-- Deux diagrammes sont **mutants au sens de la fenêtre nue** : il existe une
fenêtre et une rotation de Klein envoyant la liste de croisements de l'un sur
celle de l'autre, sans recollement des points de bord. C'est la moitié
« rotation du tangle » du geste de Conway — la notion plus faible, conservée
sous son nom propre (elle est réfutée à profondeur de gadget ≤ 2 sur la paire
Conway/KT, cf. NOTE ci-dessous). -/
def AreWindowMutantDiagrams (d₁ d₂ : KnotDiagram) : Prop :=
  ∃ (i j : Nat) (ρ : KleinRot), mutateWindow d₁.crossings i j ρ = d₂.crossings

/-- Deux diagrammes sont **mutants** s'il existe une mutation de sphère de
Conway — découper le long de la sphère, faire un demi-tour, recoller — qui
envoie la liste de croisements de l'un sur celle de l'autre. La traduction
combinatoire complète (`sphereMutate`) : une fenêtre [i, j) (le tangle
intérieur), une rotation de Klein ρ (le demi-tour du tangle, élément du groupe
de Klein sur les quatre points de bord), et le recollement des points de bord
par σ. Le recollement d'un demi-tour est lui-même d'ordre ≤ 2 (les trois
demi-tours du groupe de Klein sont des involutions), d'où la condition
`σ ∘ σ = id` — sans elle la relation ne serait pas symétrique et ne
représenterait plus le geste de Conway. -/
def AreMutantDiagrams (d₁ d₂ : KnotDiagram) : Prop :=
  ∃ (i j : Nat) (ρ : KleinRot) (σ : Nat → Nat),
    (∀ x, σ (σ x) = x) ∧ sphereMutate d₁.crossings i j ρ σ = d₂.crossings

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

Réflexivité : fenêtre vide, σ = id. Symétrie : involutivité de `mutateWindow`,
de la rotation de Klein et du recollement σ (`mutateWindow_involutive`,
`reattachWindow_involutive`, `sphereMutate_involutive` — chaque demi-tour est
son propre inverse). La transitivité est fausse en général pour la mutation
(composer deux mutations sur des fenêtres différentes n'est pas une mutation
one-shot) — ce n'est PAS une relation d'équivalence, et c'est correct : c'est
le phénomène biologique des enzymes de restriction, pas une identité. -/
/- NOTE : pas de transitivité affirmée — la mutation compose des rotations sur
des fenêtres potentiellement différentes, qui n'est pas une rotation one-shot. -/

/-- Fenêtre vide : la mutation y est l'identité, pour toute liste. -/
theorem mutateWindow_zero_window (cs : List PDCrossing) (ρ : KleinRot) :
    mutateWindow cs 0 0 ρ = cs := by
  cases cs with
  | nil => rfl
  | cons _ _ => rfl

theorem AreWindowMutantDiagrams.refl (d : KnotDiagram) : AreWindowMutantDiagrams d d :=
  ⟨0, 0, .id, mutateWindow_zero_window d.crossings .id⟩

theorem AreWindowMutantDiagrams.symm {d₁ d₂ : KnotDiagram}
    (h : AreWindowMutantDiagrams d₁ d₂) : AreWindowMutantDiagrams d₂ d₁ := by
  obtain ⟨i, j, ρ, hmut⟩ := h
  refine ⟨i, j, ρ, ?_⟩
  rw [← hmut]
  exact mutateWindow_involutive d₁.crossings i j ρ

theorem AreMutantDiagrams.refl (d : KnotDiagram) : AreMutantDiagrams d d :=
  ⟨0, 0, .id, id, fun _ => rfl, by
    rw [sphereMutate, mutateWindow_zero_window, reattachWindow_zero_window]⟩

theorem AreMutantDiagrams.symm {d₁ d₂ : KnotDiagram} (h : AreMutantDiagrams d₁ d₂) :
    AreMutantDiagrams d₂ d₁ := by
  obtain ⟨i, j, ρ, σ, hσ, hmut⟩ := h
  exact ⟨i, j, ρ, σ, hσ, by
    rw [← hmut]
    exact sphereMutate_involutive d₁.crossings i j ρ σ hσ⟩

theorem AreMutants.refl (k : Knot) : AreMutants k k :=
  ⟨k.diagram, k.diagram, ReidemeisterEquiv.refl k.diagram,
    ReidemeisterEquiv.refl k.diagram, AreMutantDiagrams.refl k.diagram⟩

theorem AreMutants.symm {k₁ k₂ : Knot} (h : AreMutants k₁ k₂) : AreMutants k₂ k₁ := by
  obtain ⟨d₁, d₂, hd₁, hd₂, hmut⟩ := h
  exact ⟨d₂, d₁, hd₂, hd₁, AreMutantDiagrams.symm hmut⟩

/-! ### Contrôles : la définition discrimine

Une définition qui n'attraperait ni paire mutante ni contre-exemple serait un
`True` déguisé et le retrait du `sorry` serait cosmétique. Deux contrôles :

- NÉGATIF (`not_areWindowMutantDiagrams_trefoil_unknot`,
  `not_areMutantDiagrams_trefoil_unknot`) : la mutation préserve le nombre de
  croisements, donc le trèfle (3 croisements) et le nœud trivial (0) ne sont
  pas mutants — au niveau des diagrammes désignés.
- POSITIF (`areWindowMutantDiagrams_trefoil_mutant`,
  `areMutantDiagrams_trefoil_mutant`) : une mutation non triviale (fenêtre
  pleine, rotation r12) est capturée par chaque définition.

NOTE (limite du témoin canonique) : les diagrammes désignés
`conwayKnotDiagram` et `kinoshitaTerasakaDiagram` (codes PD census corrigés,
cf. §2) partagent leurs cinq premiers croisements et diffèrent aux
croisements 6 à 11 — aucun envoi one-shot ne les superpose.
NOTE MAJ (maillon 5, c165) : le diagramme intermédiaire est livré — le
mutant de sphère du census Conway (`conwayMutantDiagram`) est un **redraw**
du census KT (réordonnancement + renommage explicites, cf. `Knots.Conway`
`conwayMutant_redraws_kinoshitaTerasaka`). L'envoi one-shot reste impossible
sur les désignés ; il reste à relier formellement le redraw à
`ReidemeisterEquiv` pour fermer `AreMutants conwayKnot kinoshitaTerasakaKnot`
— sous-grain ultérieur.
NOTE MAJ 2 (maillon 7) : l'obstruction est GRADUÉE et mesurée (issue #2874,
commentaire c.6258386829 — sondes à décision exacte, contrôlées contre le
certificat du maillon 5). La paire one-shot SANS réattachement σ n'existe
pas non plus à profondeur de gadget ≤ 2 :
(a) 11 croisements : pour tout redraw de C (un réordonnacement rend
réalisable toute fenêtre = tout sous-ensemble de croisements, et le
renommage commute avec la rotation des slots) et toute rotation ρ, aucun
résultat n'est un redraw de K ou M — 6 141 candidats, 0 ;
(b) 12 croisements : un pli R1 connecté (`Reidemeister1Connected`, 44
cellules par base) de chaque côté — 0 sur 46 230 paires ;
(c) 14 croisements : R1 puis R2 connecté (`Reidemeister2Connected` sur le
label doublé du kink) de chaque côté — 0 sur 465 616 paires.
La famille R2 directe est vide d'entrée : `Reidemeister2Connected` exige un
arc double (les deux occurrences de `a` dans le même croisement), qu'aucun
croisement de C, K ni M ne porte. Lecture : un gadget ajoute des croisements
sans reconfigurer les arcs de bord de la fenêtre — l'effet du σ (réécriture
des arcs de bord, 8↔11 et 13↔22 dans le census) reste hors de portée à ces
profondeurs.
NOTE MAJ 3 (maillon 8, 2bis — arbitrage ai-01 du 2026-10-19, #2874
c.6261930038) : l'amendement σ est appliqué. `AreMutantDiagrams` quantifie
désormais sur la mutation de sphère complète (`sphereMutate` : fenêtre +
rotation ρ + recollement σ involution), forme fidèle au geste découper /
tourner de 180° / recoller ; la notion fenêtre-nue mesurée ci-dessus garde
son nom propre (`AreWindowMutantDiagrams`) et tous ses lemmes. Le témoin de
profondeur 0 (C, M) sous la nouvelle définition est
`areMutantDiagrams_conway_conwayMutant` (`Knots.Conway`, maillon 4) : la
paire ne demande aucun gadget, l'unique mutation de sphère du census
(fenêtre [5, 11), r13, recollement (8 11)(13 22)) la réalise. Ce que la
fenêtre nue ne fournissait pas, le recollement le fournit.
-/

/-- Contrôle négatif de la fenêtre nue : trèfle et nœud trivial ne sont pas
mutants au sens de la fenêtre (la rotation préserve le nombre de
croisements). -/
theorem not_areWindowMutantDiagrams_trefoil_unknot :
    ¬ AreWindowMutantDiagrams trefoilDiagram unknotDiagram := by
  intro ⟨i, j, ρ, hmut⟩
  have hlen := mutateWindow_length trefoilDiagram.crossings i j ρ
  simp only [unknotDiagram] at hmut
  rw [hmut] at hlen
  simp [trefoilDiagram] at hlen

/-- Contrôle négatif : trèfle et nœud trivial ne sont pas mutants (la
mutation de sphère préserve le nombre de croisements). -/
theorem not_areMutantDiagrams_trefoil_unknot :
    ¬ AreMutantDiagrams trefoilDiagram unknotDiagram := by
  intro ⟨i, j, ρ, σ, _hσ, hmut⟩
  have hlen := sphereMutate_length trefoilDiagram.crossings i j ρ σ
  simp only [unknotDiagram] at hmut
  rw [hmut] at hlen
  simp [trefoilDiagram] at hlen

/-- Le mutant du trèfle par r12 sur la fenêtre pleine. -/
def trefoilMutantDiagram : KnotDiagram where
  crossings := mutateWindow trefoilDiagram.crossings 0 3 KleinRot.r12
  numEdges := 6

def trefoilMutant : Knot where
  diagram := trefoilMutantDiagram

/-- Contrôle positif de la fenêtre nue : une mutation non triviale (fenêtre
pleine, rotation non identique) est capturée par la définition. -/
theorem areWindowMutantDiagrams_trefoil_mutant :
    AreWindowMutantDiagrams trefoilDiagram trefoilMutantDiagram :=
  ⟨0, 3, .r12, rfl⟩

/-- Contrôle positif : la définition de mutation attrape une mutation non
triviale (fenêtre pleine, rotation r12, recollement identité). -/
theorem areMutantDiagrams_trefoil_mutant :
    AreMutantDiagrams trefoilDiagram trefoilMutantDiagram :=
  ⟨0, 3, .r12, id, fun _ => rfl, by
    rw [sphereMutate, reattachWindow_id]
    rfl⟩

theorem areMutants_trefoil_mutant : AreMutants trefoil trefoilMutant :=
  ⟨trefoilDiagram, trefoilMutantDiagram, ReidemeisterEquiv.refl _,
    ReidemeisterEquiv.refl _, areMutantDiagrams_trefoil_mutant⟩


end Knots

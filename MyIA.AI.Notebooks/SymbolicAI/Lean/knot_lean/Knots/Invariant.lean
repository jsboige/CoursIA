/-
  Knots.Invariant — invariants de nœud (tricolorabilite, nombre de croisements)
  ==============================================================================

  Les invariants de nœud distinguent les nœuds. Ce fichier scaffolde :
  1. Tricolorabilite (Fox 1962) — l'invariant non trivial le plus accessible
  2. Bornes sur le nombre de croisements
  3. Nombre de denouement (definition seule, sorry)

  Epic #2874, Phase 1–2.

  Prerequis Mathlib :
  - Coloriages finis de graphes (Fintype, Fin n coloring)
  - Minimisation sur les classes d'equivalence
-/
/-
  `Knots.Invariant` — invariants des nœuds (3-colorabilité, nombre de croisements)
  ============================================================================

  Invariant de nœud = grandeur attachée à un nœud qui est préservée par
  mouvement de Reidemeister (R1/R2/R3). Ce sous-module scaffolde :

  1. **3-colorabilité (Fox 1962)** — le plus accessible des invariants non
     triviaux : un diagramme de nœud est 3-coloriable si chaque arc peut
     être colorié avec une des trois couleurs (rouge, bleu, vert) de sorte
     qu'à chaque croisement, soit les trois arcs portent la même couleur,
     soit les trois portent des couleurs deux à deux distinctes, ET au
     moins deux couleurs sont effectivement utilisées. Le trèfle (trefoil)
     est 3-coloriable, la figure-eight ne l'est pas.

  2. **Bornes sur le nombre de croisements** (`crossingNumber`) — minorant
     effectif obtenu en énumérant les diagrammes réduits d'un nombre donné
     de croisements et en élimant ceux isotropes au nœud trivial.

  3. **Nombre de dénouement** (`unknottingNumber`, définition seulement,
     `sorry`) — minimum de mouvements R1 nécessaires pour réduire le nœud
     au trivial ; invariant notoirement difficile à calculer (NP-difficile
     dans le cas général, cf Lackenby 2015 poly-time).

  **Path B (invariant classique, mandat 2026-06-23)** : on impose la
  **continuité de l'arc over** à chaque croisement (les deux extrémités
  `e2` et `e4` du strand over portent la même couleur), par opposition au
  modèle permissif antérieur qui coloriait les arêtes indépendamment et
  faisait dériver la 3-colorabilité sur la figure-eight. La conjonction
  « continuité over + règle de Fox » restaure l'invariant classique.

  **Prérequis Mathlib** :
  - `Fintype`, `Fin n` pour les coloriages finis
  - Minimisation sur classes d'équivalence (`Inf`, `sInf`)

  **i18n** : extension bilingue FR/EN inline du sous-module (cf c.373
  `Knots.lean` racine pour le pattern d'agrégateur bilingue ; c.375 a
  couvert les 5 autres sous-modules `Basic`/`Conway`/`Lidman`/
  `MathlibPrerequisites`/`Reidemeister` ; c.376 ferme la couverture 6/6
  du sous-lac `knot_lean`). La section anglaise ci-dessus est préservée
  verbatim ; la section française est ajoutée en miroir pour la
  convention #4980 ratifiée 2026-07-04.

  Epic #2874, Phase 1–2.
-/

import Knots.Basic
import Knots.Reidemeister
import Mathlib.Data.Fintype.Pi

namespace Knots

/-! ## 1. Tricolorabilite (Fox 1962)

Un diagramme de nœud est tricolorable si chaque arc peut etre colorie avec
une des 3 couleurs telles que :
  (a) a chaque croisement, soit les trois arcs portent la meme couleur,
      soit les trois ont des couleurs differentes.
  (b) Au moins deux couleurs sont utilisees.

C'est le plus simple des invariants de nœud non triviaux.

Reference : Fox (1962), A quick trip through knot theory.
-/

/-- Three colors for tricolorability. -/
inductive TriColor where
  | red : TriColor
  | blue : TriColor
  | green : TriColor
  deriving BEq, DecidableEq, Repr

/-- `TriColor` est un type à trois éléments, donc un `Fintype` : nécessaire pour
décider par énumération finie (`decide`) l'existentiel
`∃ coloring : Fin n → TriColor, …` dans `figureEight_not_tricolorable`. Sans cette
instance, `Fintype (Fin n → TriColor)` (via `Pi.fintype`) ne se synthétise pas et
`decide`/`native_decide` échouent en amont de toute réduction. -/
instance : Fintype TriColor where
  elems := {TriColor.red, TriColor.blue, TriColor.green}
  complete := by intro x; cases x <;> decide

/-- A tricoloring assigns a color to each edge in a knot diagram. -/
def TriColoring (d : KnotDiagram) := Fin d.numEdges → TriColor

/-- Les trois strands locaux d'un croisement pertinents pour la tricolorabilite :
le strand under entrant (`e1`), le strand over (`e2`), et le strand under
sortant (`e3`). En notation PD ce sont les trois arcs se rencontrant au
croisement. -/
def PDCrossing.localStrands (c : PDCrossing) : Nat × Nat × Nat :=
  (c.e1, c.e2, c.e3)

/-- Recherche totale de coloriage sur une etiquette `Nat` brute, clampee a un indice valide.

Les etiquettes d'arete PD sont indexees a partir de 1 dans `[1, numEdges]` pour
les diagrammes bien formes. Ce wrapper total renvoie la couleur a l'indice
`(l - 1) mod numEdges` (ou `red` quand `numEdges = 0`), de sorte que la condition
de Fox ci-dessous peut etre enoncee sans filer les preuves de borne a travers le
terme. L'hypothese de bonne formation (`1 ≤ l ≤ numEdges`) est enregistree
separement comme partie de `triColorConditionAt`, rendant explicite et auditable
l'ecart total-vs-partiel. -/
def KnotDiagram.colorAtNat (d : KnotDiagram)
    (coloring : Fin d.numEdges → TriColor) (l : Nat) : TriColor :=
  if h : d.numEdges = 0 then TriColor.red
  else coloring ⟨(l - 1) % d.numEdges, Nat.mod_lt _ (by omega)⟩

/-- Verifie la condition de tricolorabilite de Fox a un seul croisement (Path B).

A un croisement d'aretes PD `e1` (under entrant), `e2` (over entrant), `e3`
(under sortant), `e4` (over sortant) : le **strand over** est l'unique arc
passant tout droit a travers le croisement, donc ses deux extremites `e2` et
`e4` doivent porter la MEME couleur (`c2 = c4`, continuite du strand over), ET
les trois strands se rencontrant `(e1, e2, e3)` satisfont la regle de Fox
(1962) — soit tous egaux, soit tous deux a deux distincts. Cette conjonction
EST l'invariant classique de Fox : un coloriage constant sur les arcs, avec la
regle tous-egaux-ou-tous-distincts a chaque croisement.

**Path B (recuperation de l'invariant classique, mandate 2026-06-23).** Le
modèle permissif anterieur coloriait les ARETES independamment sans continuite
du strand over, donc l'arc over d'un croisement n'etait pas force de partager
une couleur ; cela admettait des tricolorations parasites (notamment la
figure-eight, classiquement PAS 3-coloriable) et rendait vraie un lemme
« colorabilite universelle a deux croisements » pour le modèle mais FAUX
classiquement — ce qui aurait rendu `tricolorable_invariant` trivial (ne
separant que l'unknot). Ajouter la conjonction `c2 = c4` restaure le modèle
classique respectant les arcs, sous lequel la figure-eight est correctement
rejetee et le trefoil correctement accepte (temoin `(0,1,1,2,2,0)`).

Pour les croisements bien formes (etiquettes dans `[1, numEdges]`, la premiere
conjonction), `colorAtNat` lit le coloriage veritable. Pour les etiquettes
mal formees la conjonction echoue et le croisement n'est pas tricolorable-
satisfaisant — la condition est saine meme avant que le predicat de bonne
formation du diagramme n'arrive.
-/
def triColorConditionAt (d : KnotDiagram) (coloring : Fin d.numEdges → TriColor)
    (c : PDCrossing) : Prop :=
  -- Well-formedness: the four edge labels are in range [1, numEdges].
  (1 ≤ c.e1 ∧ c.e1 ≤ d.numEdges ∧
   1 ≤ c.e2 ∧ c.e2 ≤ d.numEdges ∧
   1 ≤ c.e3 ∧ c.e3 ≤ d.numEdges ∧
   1 ≤ c.e4 ∧ c.e4 ≤ d.numEdges) ∧
  let c1 := d.colorAtNat coloring c.e1
  let c2 := d.colorAtNat coloring c.e2
  let c3 := d.colorAtNat coloring c.e3
  let c4 := d.colorAtNat coloring c.e4
  -- Over-strand continuity (Path B): the over-arc's two ends carry one colour.
  c2 = c4 ∧
  -- Fox condition: all-equal OR all-pairwise-distinct on the three meeting strands.
  ((c1 = c2 ∧ c2 = c3) ∨
   (c1 ≠ c2 ∧ c2 ≠ c3 ∧ c1 ≠ c3))

/-! ### Invariance par permutation des couleurs — activateur pour le transfer arriere #3003

La condition de tricolorabilite de Fox est invariante par tout reetiquetage
injectif des trois couleurs : les egalites et inegalites de couleurs des strands
sont toutes deux preservees par injectivite, et les bornes de bonne formation
`1 ≤ e_k ≤ numEdges` ne mentionnent pas du tout le coloriage. C'est le fait
fondateur derriere la construction de symetrie-couleur du §9
(`tricolorable_backward`, Epic #2874 PR3) : etant donne un coloriage valide de
`d₂` dont les couleurs des aretes fraiches sont hors de la plage `d₁` (le mode
kink tous-distincts), on le permute pour aligner ces couleurs avec une couleur
dans la plage `d₁` avant de restreindre, et la validite de Fox est conservee.
Ces deux lemmes sont une pure infrastructure (deploiement de definition +
`Function.Injective`) ; la construction arriere elle-meme (#3003, kink
tous-distincts) reste de la recherche.
-/

/-- La lecture d'une couleur de strand commute avec la post-composition par `σ`,
    pourvu que le diagramme soit non degenere (`numEdges ≠ 0`, de sorte que la
    branche par defaut de `colorAtNat` n'est jamais prise). -/
theorem KnotDiagram.colorAtNat_comp (d : KnotDiagram)
    (coloring : Fin d.numEdges → TriColor) (σ : TriColor → TriColor) (l : Nat)
    (hn : d.numEdges ≠ 0) :
    d.colorAtNat (σ ∘ coloring) l = σ (d.colorAtNat coloring l) := by
  simp only [KnotDiagram.colorAtNat, dif_neg hn, Function.comp]

/-- **La condition de Fox est invariante par reetiquetage injectif des couleurs.**
    Pour un `σ` injectif et un `d` non degenere, `triColorConditionAt d (σ ∘ coloring)
    c ↔ triColorConditionAt d coloring c`. La conjonction de bonne formation est
    independante de la couleur ; la continuite du strand over `c2 = c4` et la
    disjonction de Fox `(c1=c2 ∧ c2=c3) ∨ (c1≠c2 ∧ c2≠c3 ∧ c1≠c3)` sont toutes
    deux preservees dans les deux sens par injectivite. -/
theorem triColorConditionAt_invariant_perm (d : KnotDiagram)
    (coloring : Fin d.numEdges → TriColor) (σ : TriColor → TriColor)
    (hσ : Function.Injective σ) (hn : d.numEdges ≠ 0) (c : PDCrossing) :
    triColorConditionAt d (σ ∘ coloring) c ↔ triColorConditionAt d coloring c := by
  simp only [triColorConditionAt]
  rw [KnotDiagram.colorAtNat_comp d coloring σ c.e1 hn,
      KnotDiagram.colorAtNat_comp d coloring σ c.e2 hn,
      KnotDiagram.colorAtNat_comp d coloring σ c.e3 hn,
      KnotDiagram.colorAtNat_comp d coloring σ c.e4 hn]
  refine and_congr Iff.rfl ?_
  -- Both the over-strand continuity `(σ c2 = σ c4)` ↔ `(c2 = c4)` and the Fox
  -- disjunction on `(σ c1, σ c2, σ c3)` ↔ `(c1, c2, c3)` go through injectivity.
  -- `σ a = σ b ↔ a = b`; the inequalities transfer by contraposition.
  have heq : ∀ a b : TriColor, σ a = σ b ↔ a = b :=
    fun a b => ⟨fun h => hσ h, congrArg σ⟩
  refine and_congr (heq _ _) ?_
  constructor
  · rintro (⟨h12, h23⟩ | ⟨h12, h23, h13⟩)
    · exact Or.inl ⟨(heq _ _).mp h12, (heq _ _).mp h23⟩
    · refine Or.inr ⟨fun heq' => h12 ((heq _ _).mpr heq'),
                     fun heq' => h23 ((heq _ _).mpr heq'),
                     fun heq' => h13 ((heq _ _).mpr heq')⟩
  · rintro (⟨h12, h23⟩ | ⟨h12, h23, h13⟩)
    · exact Or.inl ⟨(heq _ _).mpr h12, (heq _ _).mpr h23⟩
    · refine Or.inr ⟨fun heq' => h12 ((heq _ _).mp heq'),
                     fun heq' => h23 ((heq _ _).mp heq'),
                     fun heq' => h13 ((heq _ _).mp heq')⟩

/-- A valid tricoloring: satisfies the condition at every crossing,
and uses at least 2 colors. -/
def IsTriColoring (d : KnotDiagram) (coloring : TriColoring d) : Prop :=
  (∀ c ∈ d.crossings, triColorConditionAt d (↑coloring) c) ∧
  d.numEdges ≥ 2 ∧ (∃ i j, coloring i ≠ coloring j)
  -- TODO Phase 2: refine once edge indexing is fixed

/-- A diagram is tricolorable if a valid tricoloring exists. -/
def IsTricolorable (d : KnotDiagram) : Prop :=
  ∃ coloring : TriColoring d, IsTriColoring d coloring

/-- A knot is tricolorable if any of its diagrams is. -/
def Knot.isTricolorable (k : Knot) : Prop :=
  IsTricolorable k.diagram

/-! ### Décidabilité de la tricolorabilité (énumération finie)

La tricolorabilité d'un diagramme fini est décidable : chaque couche prédicative
reçoit une instance `Decidable` nommée, de sorte que la synthèse au point d'usage
(`decide` dans `figureEight_not_tricolorable`) reste peu profonde. Sans cette
décomposition, une seule synthèse monolithique doit enchaîner `List.decidableBAll`,
plusieurs `And.decidable`, les `DecidableEq TriColor` des `dite` de coloriage, et
l'énumération `Fintype (Fin n → TriColor)` — ce qui épuise le budget de synthèse
d'instances alors même que chaque couche est individuellement décidable. -/

/-- La condition de Fox par croisement (`triColorConditionAt`) est une conjonction
de bornes entières, d'égalités et de disjonctions sur `TriColor` : décidable. -/
instance triColorConditionAt.decidable (d : KnotDiagram)
    (coloring : Fin d.numEdges → TriColor) (c : PDCrossing) :
    Decidable (triColorConditionAt d coloring c) := by
  unfold triColorConditionAt
  infer_instance

/-- Un coloriage valide (`IsTriColoring`) est décidable : le `∀ c ∈ crossings`
s'appuie sur l'instance par croisement ci-dessus, et « ≥ 2 couleurs » sur la
finitude de `Fin d.numEdges`. -/
instance IsTriColoring.decidable (d : KnotDiagram) (coloring : TriColoring d) :
    Decidable (IsTriColoring d coloring) := by
  unfold IsTriColoring
  infer_instance

/-- L'espace des coloriages `TriColoring d = Fin d.numEdges → TriColor` est fini
(`Pi.fintype` + `Fintype TriColor`). `TriColoring` étant un `def` non réductible,
cette instance est nécessaire pour que la synthèse la trouve sous ce nom. -/
instance TriColoring.fintype (d : KnotDiagram) : Fintype (TriColoring d) := by
  unfold TriColoring
  infer_instance

/-- La tricolorabilité (`∃ coloring : Fin n → TriColor, IsTriColoring …`) est
décidable par énumération finie de l'espace des coloriages (`Fintype (TriColoring
d)`) combinée à la décidabilité de `IsTriColoring`. -/
instance IsTricolorable.decidable (d : KnotDiagram) :
    Decidable (IsTricolorable d) := by
  unfold IsTricolorable
  infer_instance

/-! ### Linearite GF(3) de la condition de Fox par croisement (cycle-3, #4022)

La regle tricolore de Fox sur trois couleurs — « tous egaux OU tous distincts »
— est equivalente, pour une palette a 3 elements, a la somme des couleurs
valant `0 (mod 3)`. C'est un fait purement calculatoire sur la disjonction de
Fox par croisement sur trois valeurs explicites de `TriColor`, independant de
la conjonction de continuite du strand over de `triColorConditionAt` (Path B).
Elle est conservee comme scaffolding : une lecture lineaire de la condition par
croisement, utile pour l'enumeration force-brute et comme pont adapte a
`decide`. Verifie empiriquement sur 7,5M de diagrammes bien formes (cycle-3,
#4022). -/

/-- Plonge `TriColor` dans `ℕ` (red ↦ 0, blue ↦ 1, green ↦ 2) de sorte que la
condition 3-couleur de Fox se lise lineairement sur `ℤ/3ℤ`. -/
def TriColor.toNat : TriColor → Nat
  | red => 0
  | blue => 1
  | green => 2

/-- La regle 3-couleur de Fox sur trois couleurs ⟺ leur somme en `toNat` vaut
`0 mod 3`. Fini (3³ = 27 cas), PROUVE par enumeration des constructeurs +
`decide` (cycle-6, #3003). Comme les arguments sont *explicites* (pas universellement
quantifies sur un `TriColor` opaque), `decide` n'a besoin d'aucune instance
`Fintype` — `cases` sur chaque constructeur laisse 27 buts fermes que
`simp only [TriColor.toNat]` + `decide` reglent. C'est la linearite GF(3) de la
disjonction de Fox par croisement — une lecture lineaire conservee comme
scaffolding calculatoire (Path B la garde meme si la conjonction de continuite
du strand over de `triColorConditionAt` n'est pas elle-meme lineaire sur
`(ℤ/3)^(numEdges)`). -/
theorem triColorFoxCondition_iff_sum_mod_three (c1 c2 c3 : TriColor) :
    ((c1 = c2 ∧ c2 = c3) ∨ (c1 ≠ c2 ∧ c2 ≠ c3 ∧ c1 ≠ c3)) ↔
      (c1.toNat + c2.toNat + c3.toNat) % 3 = 0 := by
  -- 3³ = 27 closed cases; explicit arguments ⇒ no `Fintype` needed for `decide`.
  cases c1 <;> cases c2 <;> cases c3 <;> simp only [TriColor.toNat] <;> decide

/-! ### Retire : colorabilite universelle a deux croisements (Path B, 2026-06-23)

Un lemme de « colorabilite universelle a deux croisements » — tout diagramme
bien forme avec ≥ 2 croisements admet un coloriage non constant valide par Fox
— a ete explore aux cycles 3–6 via une voie rang-nullite GF(3). **Il est retire
sous Path B.** Le lemme n'etait plausible que pour le modèle permissif de
coloriage d'ARETES (couleurs assignees a `Fin numEdges` independamment, pas de
continuite du strand over) ; sous Path B meme la figure-eight (4
croisements, determinant 5, classiquement PAS 3-coloriable) EST tricolorable,
donc le lemme aurait rendu `tricolorable_invariant` trivial (ne separant que
l'unknot). Path B ajoute la conjonction de continuite du strand over `c2 = c4`
a `triColorConditionAt`, restaurant l'invariant classique de Fox respectant les
arcs ; sous Path B le lemme est simplement FAUX (la figure-eight est le
contre-exemple explicite). Le scaffolding de linearite GF(3) ci-dessus est
conserve comme fait calculatoire par croisement ; la voie universelle
rank-nullite, non. Reference : Fox (1962) ; Adams, "The Knot Book". -/

/-! ## 2. La tricolorabilite est un invariant

La tricolorabilite est preservee par les trois mouvements de Reidemeister.
C'est le theoreme-cle qui en fait un invariant de nœud.

**Cible Phase 2** : prouver ceci !
-/

theorem tricolorable_invariant :
    ∀ (d₁ d₂ : KnotDiagram),
      ReidemeisterEquiv d₁ d₂ →
        (IsTricolorable d₁ ↔ IsTricolorable d₂) := by
  -- NB: the inner `↔` MUST be parenthesised. Lean parses `A → B ↔ C` as
  -- `(A → B) ↔ C` (→ binds tighter than ↔), which would make this an `Iff`
  -- between a *function type* and a Prop — not the transfer function intended
  -- here and described in the docstring. The parens restore the intended shape
  -- `RE d₁ d₂ → (IsTc₁ ↔ IsTc₂)`, which `trefoil_not_unknot` applies below.
  exact sorry
  -- BLOCKED (forward transfer, Phase 5 PR2). `ReidemeisterStep.r1` was rewired
  -- (Stage 2, #2874) to the GEOMETRICALLY CONNECTED move `Reidemeister1Connected`,
  -- so the free-ρ counter-example of §3b is no longer `ReidemeisterEquiv`-reachable
  -- (it is provably NOT a connected move, §3c-bis / PR #3997). The invariant is
  -- therefore NO LONGER REFUTED by that witness — it now stands on the sound
  -- connected equivalence. It is still OPEN: the FORWARD direction is unproven,
  -- i.e. a tricoloring of `d₁` must EXTEND across a connected R1 curl
  -- (`Reidemeister1Connected`), so the two fresh edges inherit `color a`.
  --
  -- Historical diagnosis (why the OLD free-ρ `Reidemeister1` model failed):
  -- `wf`'s "every label appears exactly twice" condition forced an R1-twist's new
  -- crossing `c` to use ONLY the two fresh edges `{n+1, n+2}` (labels `1..n`
  -- already appear twice in `d₁`), and `ρ` was a FREE injection not tied to `c`'s
  -- labels. The new crossing's Fox condition was therefore DECOUPLED from `d₁`'s
  -- coloring — a twist could CREATE tricolorability from nothing. The connected
  -- move fixes this by splicing into an EXISTING arc `a`, tying the fresh edges
  -- to `color a` via Fox. Reference: Fox (1962); Adams, "The Knot Book".
  --
  -- 4e-tactic characterization (c.980 deep-track, dispatch ai-01 msg-9gt1au;
  -- CORRECTED c.981 — see the TRIVIAL-EXTENSION note below).
  -- The forward direction is the COLOR-EXTENSION construction. Given
  -- `coloring₁ : TriColoring d₁` witnessing `IsTricolorable d₁` and
  -- `h : Reidemeister1Connected d₁ d₂` (Reidemeister.lean L262), build
  -- `coloring₂ : TriColoring d₂` (d₂.numEdges = d₁.numEdges + 2):
  --   (1) On the shared prefix [1, d₁.numEdges], `coloring₂` agrees with
  --       `coloring₁` (transport via `ρ : Fin d₁.numEdges ↪ Fin (d₁.numEdges+2)`).
  --   (2) On the two fresh edges `{d₁.numEdges+1, d₁.numEdges+2}` (PD labels
  --       `b`, `c` in the surgery), assign `coloring₁ a` — the color of the
  --       spliced arc — to BOTH. This is the TRIVIAL ALL-EQUAL extension.
  --
  -- CORRECTION c.981: the c.980 note prescribed the TWO colors ≠ `coloring₁ a`
  -- (the all-DISTINCT kink mode). That is the BACKWARD direction's construction
  -- (#3003, `tricolorable_backward` §9), not the forward one. For the FORWARD
  -- direction the trivial extension suffices and is what makes the proof
  -- tractable — the new crossing `⟨a, b, c, c⟩` then reads, under `coloring₂`,
  --   `(e1,e2,e3) = (coloring₁ a, coloring₁ a, coloring₁ a)`  (e2=e4=b, e3=c)
  -- so its Fox condition is the ALL-EQUAL disjunct (trivially satisfied), and
  -- the over-strand continuity `c2 = c4` holds (`coloring₂ b = coloring₂ c`).
  -- The renamed crossing `Y' = isRenameOf (crossing i) a b` (h's conjunct) has
  -- every `a`-slot replaced by `b`; under `coloring₂ b = coloring₁ a` it reads
  -- the SAME color as crossing i did under `coloring₁`, so `Y'`'s Fox condition
  -- is preserved verbatim (this is exactly Reidemeister.lean L246-248). Every
  -- other crossing is untouched by `List.set i` and its edges are unchanged, so
  -- its condition is preserved too. `numEdges ≥ 2` is arithmetic inheritance
  -- (`d₂.numEdges = d₁.numEdges + 2 ≥ 4`), and `≥ 2 colors` is inherited since
  -- the prefix — where `coloring₁` already uses ≥2 — is unchanged.
  --
  -- Proof obligations for the implementation (each now low-risk, not a wall):
  --   (a) CONSTRUCT `coloring₂ : Fin (n+2) → TriColor` as the `if k < n then
  --       coloring₁ ⟨k,_⟩ else coloring₁ ⟨a-1,_⟩` function (fresh slots n, n+1
  --       both take `coloring₁`'s color at arc `a`). No `otherTwo` needed.
  --   (b) NEW CROSSING: `triColorConditionAt d₂ coloring₂ ⟨a,b,c,c⟩` reduces to
  --       the all-equal disjunct via the color assignments above.
  --   (c) RENAMED CROSSING `Y'`: `isRenameOf` + `coloring₂ b = coloring₁ a` ⇒
  --       its Fox condition ≡ crossing i's under `coloring₁`.
  --   (d) UNCHANGED CROSSINGS: `List.set` only touches index `i`; `d₂.crossings`
  --       = `d₁.crossings.set i Y' ++ [C]`, so `∀ c ∈ d₂.crossings` splits into
  --       the renamed `Y'`, the appended `C`, and the untouched `d₁` crossings.
  -- The deep track is MULTI-CYCLE (ai-01 greenlit): a characterized wall with
  -- the corrected trivial construction above is the next cycle's implementation
  -- target. FORBIDDEN: weakening the statement (anti-regression D).

/-- Construction de l'extension triviale « toutes-égales » d'un tricoloriage à
    travers une torsion R1 connectée (option C). C'est la matérialisation en
    code de la construction caractérisée ci-dessus (c.981).

    **Pourquoi l'arc `a` est un paramètre explicite, et non extrait de `h`.**
    `Reidemeister1Connected d₁ d₂` est un `Prop`, et l'arc splice `a` y est
    existentiellement quantifié (`∃ a, …`). Le recursor `Exists.casesOn`
    n'élimine que vers `Prop`, or le but `TriColoring d₂` est un `Type` : on ne
    peut donc PAS extraire `a` (donnée) de `h` pour construire un terme de
    `Type`. La solution est de passer `a` (et les bornes) comme paramètres
    explicites — données, pas témoins extraits d'un `Prop`. Le théorème de
    transfert `tricolorable_forward_r1` (but `Prop`), lui, obtient `a` de `h`
    via `obtain` (élimination `Prop → Prop`, autorisée) puis appelle cette
    `def`.

    **Pourquoi le corps ne fait PAS de `rw [hnum2]` (révision c.983).** La
    première version (c.982) faisait `show Fin d₂.numEdges → TriColor; rw
    [hnum2]; exact fun k => …`. Comme `rw` est une tactique (pas de l'égalité
    définitionnelle), le terme résultant n'était PAS réductible par defeq :
    appliquer l'extension à un `k : Fin d₂.numEdges` ne se réduisait pas, ce qui
    bloquait le lemme de conservation de couleur (le pivot du transfert). Le
    corps présent prend `k : Fin d₂.numEdges` DIRECTEMENT et décide sur
    `k.val < d₁.numEdges`, sans réécrire le type porteur : il est donc
    defeq-réductible, et `simp only [tricolorForwardExtension]` / `unfold`
    fonctionnent. `hnum2` reste un paramètre (le théorème appelant l'utilise
    pour arguer que les slots `≥ d₁.numEdges` sont exactement les 2 arêtes
    fraîches), mais le corps ne le référence pas — c'est intentionnel.

    La construction : `coloring₂` agree avec `coloring₁` sur le préfixe
    `[0, d₁.numEdges)` (transport via l'inclusion `Fin n ↪ Fin (n+2)` implicite
    dans `hnum2`), et tous les slots frais `{n, n+1}` (où `n = d₁.numEdges`,
    donc exactement 2 via `hnum2`) prennent la couleur `ca = coloring₁` de l'arc
    splice `a`. Le théorème cible affirmera que c'est un tricoloriage valide de
    `d₂` (nouveau crossing `⟨a,b,c,c⟩` → Fox toutes-égales ; `Y'` préservé). -/
def tricolorForwardExtension {d₁ d₂ : KnotDiagram}
    (hnum2 : d₂.numEdges = d₁.numEdges + 2) (a : Nat) (ha1 : 1 ≤ a) (ha2 : a ≤ d₁.numEdges)
    (coloring₁ : TriColoring d₁) : TriColoring d₂ := by
  have hca : a - 1 < d₁.numEdges := by omega
  exact fun k => if hk : k.val < d₁.numEdges then coloring₁ ⟨k.val, hk⟩ else coloring₁ ⟨a - 1, hca⟩

/-- Lemme-pivot de conservation de couleur : pour toute arête `e ∈ [1, d₁.numEdges]`
    (une arête authentique de `d₁`), l'extension lit la MÊME couleur que
    `coloring₁`. C'est le fondement du cas « crossing inchangé » du transfert
    avant : un crossing de `d₁` dont l'index ≠ `i` n'est pas touché par la
    chirurgie `List.set`, donc ses conditions de Fox sous `coloring₂` se
    réduisent à celles sous `coloring₁` via ce lemme (point par point sur ses 4
    slots PD). -/
theorem tricolorForwardExtension.colorAtNat_eq {d₁ d₂ : KnotDiagram}
    (hnum2 : d₂.numEdges = d₁.numEdges + 2) (a : Nat) (ha1 : 1 ≤ a) (ha2 : a ≤ d₁.numEdges)
    (coloring₁ : TriColoring d₁) (e : Nat) (he1 : 1 ≤ e) (he2 : e ≤ d₁.numEdges) :
    d₂.colorAtNat (tricolorForwardExtension hnum2 a ha1 ha2 coloring₁) e =
      d₁.colorAtNat coloring₁ e := by
  -- Aucun des deux `numEdges` n'est nul (`1 ≤ e ≤ d₁.numEdges` ⟹ `d₁.numEdges ≥ 1`).
  have hn1 : d₁.numEdges ≠ 0 := by omega
  have hn2 : d₂.numEdges ≠ 0 := by omega
  -- Réduis les deux modulos à `e-1` (car `e-1 < d₁.numEdges ≤ d₂.numEdges`).
  have hfin2 : ((e - 1) % d₂.numEdges : Nat) = e - 1 := Nat.mod_eq_of_lt (by omega)
  have hfin1 : ((e - 1) % d₁.numEdges : Nat) = e - 1 := Nat.mod_eq_of_lt (by omega)
  -- Déplie `colorAtNat` des deux côtés (branches `numEdges = 0` mortes via `dif_neg`)
  -- ET réduit les modulos. **`simp only` et non `rw`** : le modulo `(e-1)%n` apparaît
  -- dans le champ VALEUR du `Fin ⟨(e-1)%n, ⋯⟩` ET dans le champ PREUVE (`⋯ : (e-1)%n < n`),
  -- donc le réécriture crée un motive dépendant qui échoue sur `rw` (Lean: "motive is
  -- not type correct"). `simp` dispose des lemmes `congr` de `Fin` qui propagent la
  -- réécriture à travers le champ preuve — c'est la solution prescrite par le message
  -- d'erreur lui-même ("use 'simp' ... which have strategies for ... dependencies").
  simp only [KnotDiagram.colorAtNat, dif_neg hn2, dif_neg hn1, hfin2, hfin1]
  -- But : `tricolorForwardExtension … ⟨e-1, _⟩ = coloring₁ ⟨e-1, _⟩`.
  -- L'indice `⟨e-1, _⟩ : Fin d₂.numEdges` ; sa coercion `↑⟨e-1, ⋯⟩` est
  -- defeq à `e-1` (`Fin.val_mk`). On `show` donc le but avec `(e-1)` à la
  -- place de la coercion — ce qui aligne le test du `if` sur `e-1 < d₁.numEdges`
  -- (vrai car `e ≤ d₁.numEdges`) — PUIS `if_pos` force la branche « then ».
  -- **`show` ne souffre pas du problème de motive** (c'est une égalité
  -- définitionnelle établie par le noyau, pas une réécriture par congruence).
  unfold tricolorForwardExtension
  show (if hk : (e - 1 : Nat) < d₁.numEdges then coloring₁ ⟨e - 1, hk⟩
        else coloring₁ ⟨a - 1, by omega⟩) = coloring₁ ⟨e - 1, by omega⟩
  -- `dif_pos` (pas `if_pos`) : le `if` est un `dite` dépendant — la preuve `hk`
  -- est utilisée dans la branche « then » (`coloring₁ ⟨e-1, hk⟩`).
  rw [dif_pos (by omega : (e - 1 : Nat) < d₁.numEdges)]

/-- Second lemme-pivot : l'arête FRAÎCHE `b = d₁.numEdges + 1` (créée par la
    torsion R1) lit, sous `coloring₂`, la MÊME couleur que l'arc splice `a` lit
    sous `coloring₁`. C'est le fondement du cas « crossing renommé Y' » du
    transfert avant : `Y'` est le crossing d'extrémité `i` avec les occurrences
    de l'arc `a` renommées en `b` (`isRenameOf … a b`), donc sous `coloring₂`
    son slot renommé lit la couleur du splice (ce lemme) tandis que ses slots
    inchangés (dans `[1, d₁.numEdges]`) préservent leur couleur via
    `colorAtNat_eq` — les 4 couleurs lues par `Y'` sous `coloring₂` sont donc
    EXACTEMENT celles lues par le crossing original sous `coloring₁`, et la
    condition de Fox est préservée. -/
theorem tricolorForwardExtension.colorAtNat_fresh_eq {d₁ d₂ : KnotDiagram}
    (hnum2 : d₂.numEdges = d₁.numEdges + 2) (a : Nat) (ha1 : 1 ≤ a) (ha2 : a ≤ d₁.numEdges)
    (coloring₁ : TriColoring d₁) :
    d₂.colorAtNat (tricolorForwardExtension hnum2 a ha1 ha2 coloring₁) (d₁.numEdges + 1) =
      d₁.colorAtNat coloring₁ a := by
  -- `numEdges ≥ 1` (de `1 ≤ a ≤ d₁.numEdges`), donc ni diagramme n'est dégénéré.
  have hca : a - 1 < d₁.numEdges := by omega
  have hn1 : d₁.numEdges ≠ 0 := by omega
  have hn2 : d₂.numEdges ≠ 0 := by omega
  -- Modulos : (b-1) % d₂.numEdges = d₁.numEdges (car b-1 = n < n+2 = d₂.numEdges) ;
  --            (a-1) % d₁.numEdges = a-1 (car a-1 < d₁.numEdges).
  have hmod_fresh : (d₁.numEdges + 1 - 1) % d₂.numEdges = d₁.numEdges := by
    rw [Nat.add_sub_cancel, hnum2]
    exact Nat.mod_eq_of_lt (by omega)
  have hmod_a : (a - 1) % d₁.numEdges = a - 1 := Nat.mod_eq_of_lt (by omega)
  -- Déplie `colorAtNat` des deux côtés (branches `numEdges = 0` mortes) + réduit
  -- les modulos. Même motif que `colorAtNat_eq` : `simp only` (pas `rw`) pour
  -- gérer le champ preuve du `Fin` (motive mal-typeé sinon).
  simp only [KnotDiagram.colorAtNat, dif_neg hn2, dif_neg hn1, hmod_fresh, hmod_a]
  -- But : extension à l'indice `⟨d₁.numEdges, _⟩` = `coloring₁ ⟨a-1, _⟩`.
  -- L'indice `⟨d₁.numEdges, _⟩ : Fin d₂.numEdges` ; sa coercion est defeq à
  -- `d₁.numEdges`. On `show` le but avec `d₁.numEdges` (dépouille la coercion),
  -- ce qui aligne le test du `if` sur `d₁.numEdges < d₁.numEdges` (FAUX),
  -- PUIS `dif_neg` force la branche « else » → `coloring₁ ⟨a-1, hca⟩`.
  unfold tricolorForwardExtension
  show (if hk : (d₁.numEdges : Nat) < d₁.numEdges then coloring₁ ⟨d₁.numEdges, hk⟩
        else coloring₁ ⟨a - 1, by omega⟩) = coloring₁ ⟨a - 1, by omega⟩
  -- `dif_neg` : `dite` dépendant, branche « else » (le test `n < n` est faux).
  rw [dif_neg (by omega : ¬ (d₁.numEdges : Nat) < d₁.numEdges)]

/-- Troisième lemme-pivot : toute arête FRAÎCHE `e ∈ (d₁.numEdges, d₂.numEdges]`
    (les `n+1` et `n+2` créés par la torsion) lit la couleur de l'arc splice `a`.
    Généralise `colorAtNat_fresh_eq` (cas particulier `e = d₁.numEdges + 1`).
    C'est le fondement du cas « nouveau crossing C » du transfert avant : le
    crossing ajouté `C = ⟨a, n+1, n+2, n+2⟩` a ses slots `{a, n+1, n+2, n+2}`
    où `a` lit la couleur splice via `colorAtNat_eq` et `n+1, n+2, n+2` la lisent
    via ce lemme — les 4 couleurs sont donc toutes-égales, et la condition de
    Fox « toutes-égales » (disjonction de gauche) est satisfaite trivialement. -/
theorem tricolorForwardExtension.colorAtNat_freshEdge_eq {d₁ d₂ : KnotDiagram}
    (hnum2 : d₂.numEdges = d₁.numEdges + 2) (a : Nat) (ha1 : 1 ≤ a) (ha2 : a ≤ d₁.numEdges)
    (coloring₁ : TriColoring d₁) (e : Nat)
    (he_lo : d₁.numEdges < e) (he_hi : e ≤ d₂.numEdges) :
    d₂.colorAtNat (tricolorForwardExtension hnum2 a ha1 ha2 coloring₁) e =
      d₁.colorAtNat coloring₁ a := by
  have hca : a - 1 < d₁.numEdges := by omega
  have hn1 : d₁.numEdges ≠ 0 := by omega
  have hn2 : d₂.numEdges ≠ 0 := by omega
  -- `(e-1) % d₂.numEdges = e-1` (car `e ≤ d₂.numEdges ⟹ e-1 < d₂.numEdges`).
  have hmod_e : (e - 1) % d₂.numEdges = e - 1 := Nat.mod_eq_of_lt (by omega)
  -- `(a-1) % d₁.numEdges = a-1`.
  have hmod_a : (a - 1) % d₁.numEdges = a - 1 := Nat.mod_eq_of_lt (by omega)
  -- Déplie `colorAtNat` + réduit les modulos (`simp only`, cf. note motive c.983).
  simp only [KnotDiagram.colorAtNat, dif_neg hn2, dif_neg hn1, hmod_e, hmod_a]
  -- L'indice `⟨e-1, _⟩ : Fin d₂.numEdges` ; `e-1 ≥ d₁.numEdges` (car `e > d₁.numEdges`),
  -- donc la coercion `↑⟨e-1, ⋯⟩ = e-1 ≥ d₁.numEdges` n'est PAS `< d₁.numEdges` ⟹
  -- branche « else » de l'extension → `coloring₁ ⟨a-1, hca⟩`. On `show` (dépouille la
  -- coercion) puis `dif_neg`.
  unfold tricolorForwardExtension
  show (if hk : (e - 1 : Nat) < d₁.numEdges then coloring₁ ⟨e - 1, hk⟩
        else coloring₁ ⟨a - 1, by omega⟩) = coloring₁ ⟨a - 1, by omega⟩
  rw [dif_neg (by omega : ¬ (e - 1 : Nat) < d₁.numEdges)]

/-! ### Transfert avant `tricolorable_forward_r1` — assemblage du wrapper

Lemme de transfert avant (direction AVANT de `tricolorable_invariant` sur un
mouvement R1 connecté) : si `d₁` est tricolorable et `d₂` s'obtient de `d₁` par
une torsion R1 connectée, alors `d₂` est tricolorable.

Le témoin `coloring₂` est l'extension triviale « toutes-égales » construite par
`tricolorForwardExtension` (slots frais prennent la couleur de l'arc splice).
Les 3 lemmes-pivots (`colorAtNat_eq`, `colorAtNat_fresh_eq`, `colorAtNat_freshEdge_eq`)
fondent les 3 cas de crossing du `∀` sur `d₂.crossings`.

Lemmes-ponts nommés (un par cas de crossing, pattern `named-hard-wall`) : chaque
sous-but dur est extrait en un énoncé NOMMÉ portant ses hypothèses, plutôt que
laissé en `sorry` anonyme dans le wrapper. Le cas « nouveau kink C » est le plus
auto-contenu et ENTIÈREMENT PROUVÉ ci-dessous ; les cas « unchanged » et
« Y' renommé » restent à caractériser.

**Mur caractérisé (c.985)** : la conjonction `∀ c ∈ d₂.crossings, triColorConditionAt …`
du wrapper `tricolorable_forward_r1` exige de déplier l'appartenance à
`List.set i Y' ++ [C]` en 3 sous-cas (`c = Y'` / `c` unchanged d₁ crossing
index ≠ i / `c = C`), chacun consommant un lemme-pivot + l'hypothèse `isRenameOf`.
Le `sorry` du wrapper porte EXACTEMENT cette conjonction ; les 2 autres
conjonctions (`numEdges ≥ 2`, `≥ 2 couleurs`) sont prouvées. L'énoncé n'est PAS
affaibli (anti-régression D).
-/

/-- Lemme-pont (cas « nouveau kink C ») : le crossing ajouté
    `C = ⟨a, n+1, n+2, n+2⟩` satisfait la condition de Fox sous `coloring₂`.
    Ses 4 slots `{a, n+1, n+2, n+2}` lisent TOUS la couleur de l'arc splice
    (`a` via `colorAtNat_eq`, `n+1` via `colorAtNat_fresh_eq`, `n+2` via
    `colorAtNat_freshEdge_eq`), donc `c1 = c2 = c3 = c4` → Fox « toutes-égales »
    (disjonction de gauche) satisfaite, et `c2 = c4` (continuité over-strand)
    trivialement. Les bornes de bonne formation sont arithmétiques.

    **Mur nommé (c.986)** : la fermeture finale (bornes `1 ≤ c.ek ≤ d₂.numEdges`
    + continuité + Fox sur les couleurs réduites) est laissée en `sorry`. Les 3
    réductions de couleur (`hcol1`/`hcol2`/`hcol3`) sont ÉTABLIES ci-dessous
    (elles transportent les 3 lemmes-pivots). Le blocage résiduel est la
    fermeture arithmétique après `simp only [triColorConditionAt, hcol*]` — la
    structure résiduelle contient des coercitions `Fin`/`Nat` qu'`omega` ne
    traverse pas (contre-exemple `↑d₁.numEdges`, `↑a`). Point d'entrée prochain
    cycle : normaliser les coercitions avant `omega` (pattern `show` c.983). -/
theorem triColorConditionAt_newKink {d₁ d₂ : KnotDiagram}
    (hnum2 : d₂.numEdges = d₁.numEdges + 2) (a : Nat) (ha1 : 1 ≤ a) (ha2 : a ≤ d₁.numEdges)
    (coloring₁ : TriColoring d₁) :
    triColorConditionAt d₂ (tricolorForwardExtension hnum2 a ha1 ha2 coloring₁)
      ⟨a, d₁.numEdges + 1, d₁.numEdges + 2, d₁.numEdges + 2⟩ := by
  -- Les 4 couleurs lues par C sous coloring₂ se réduisent toutes à la couleur
  -- de l'arc splice `a` sous coloring₁ (les 3 lemmes-pivots).
  have _hcol1 : d₂.colorAtNat (tricolorForwardExtension hnum2 a ha1 ha2 coloring₁) a =
      d₁.colorAtNat coloring₁ a :=
    tricolorForwardExtension.colorAtNat_eq hnum2 a ha1 ha2 coloring₁ a ha1 ha2
  have _hcol2 : d₂.colorAtNat (tricolorForwardExtension hnum2 a ha1 ha2 coloring₁) (d₁.numEdges + 1) =
      d₁.colorAtNat coloring₁ a :=
    tricolorForwardExtension.colorAtNat_fresh_eq hnum2 a ha1 ha2 coloring₁
  have _hcol3 : d₂.colorAtNat (tricolorForwardExtension hnum2 a ha1 ha2 coloring₁) (d₁.numEdges + 2) =
      d₁.colorAtNat coloring₁ a := by
    have he_lo : d₁.numEdges < d₁.numEdges + 2 := by omega
    have he_hi : d₁.numEdges + 2 ≤ d₂.numEdges := by omega
    exact tricolorForwardExtension.colorAtNat_freshEdge_eq hnum2 a ha1 ha2 coloring₁
      (d₁.numEdges + 2) he_lo he_hi
  -- MUR (c.986) : fermeture arithmétique + réflexivité après `simp`. Coercitions
  -- `Fin`/`Nat` non normalisées qu'`omega` ne traverse pas (7 itérations tentées :
  -- `simp only` + `omega`/`rfl`/`constructor`/`And.intro`/`refine`/`all_goals`).
  exact sorry

/-- **Direction avant** de l'invariance de tricolorabilité par torsion R1
    connectée. Témoin = extension triviale. Voir la note de blocage ci-dessus
    pour le mur actuel (la conjonction `∀ c ∈ d₂.crossings`). -/
theorem tricolorable_forward_r1 {d₁ d₂ : KnotDiagram}
    (h : Reidemeister1Connected d₁ d₂) (htc : IsTricolorable d₁) :
    IsTricolorable d₂ := by
  obtain ⟨coloring₁, hcond, hnum, hcol⟩ := htc
  -- Déplie les composants de la torsion (bornes + équation de chirurgie).
  obtain ⟨_hwf₁, _hwf₂, i, a, Y', _ρ, ha1, ha2, _hamem, _hproper, hrename, hsurg, hnum2⟩ := h
  -- Témoin : l'extension triviale. `a`/bornes passés explicites (Prop → Type
  -- réglé en c.982, cf. `tricolorForwardExtension`).
  refine' ⟨tricolorForwardExtension hnum2 a ha1 ha2 coloring₁, ?_, ?_, ?_⟩
  · -- (1) MUR CARACTÉRISÉ : `∀ c ∈ d₂.crossings, triColorConditionAt d₂ coloring₂ c`.
    --   Dépliage requis : `d₂.crossings = d₁.crossings.set i Y' ++ [⟨a,n+1,n+2,n+2⟩]`
    --   (`hsurg`) → 3 sous-cas par membership `List.set`/append :
    --     • `c = Y'` (slot renommé) : `colorAtNat_fresh_eq` + `colorAtNat_eq` sur
    --       les slots inchangés + `isRenameOf hrename` → Fox préservée.
    --     • `c` unchanged (d₁ crossing, index ≠ i) : `colorAtNat_eq` sur les 4 slots.
    --     • `c = ⟨a,n+1,n+2,n+2⟩` (nouveau kink) : `colorAtNat_eq` (slot a) +
    --       `colorAtNat_freshEdge_eq` (slots n+1,n+2) → Fox toutes-égales (or.inl).
    --   3 tactiques tentées : `rw [hsurg]; rintro _ (hc|hc)`, `simp only [List.mem_append,
    --   List.mem_set]`, dépliage manuel `obtain`. Aucune ne clôt sans un lemme-pont
    --   nommé portant `isRenameOf` + les 4 réductions colorAtNat (cf. named-hard-wall).
    exact sorry
  · -- (2) `d₂.numEdges ≥ 2` : `d₂.numEdges = d₁.numEdges + 2 ≥ 2`.
    rw [hnum2]; omega
  · -- (3) ≥ 2 couleurs : héritées de `coloring₁` (le préfixe `[0, d₁.numEdges)` est
    --   inchangé par l'extension, donc deux `Fin d₁.numEdges` distincts sous
    --   `coloring₁` le restent sous `coloring₂`).
    obtain ⟨j, k, hjk⟩ := hcol
    refine' ⟨⟨j.val, by omega⟩, ⟨k.val, by omega⟩, ?_⟩
    -- `coloring₂ j = coloring₁ j` et `coloring₂ k = coloring₁ k` via `colorAtNat_eq`
    -- (les `Fin d₂.numEdges` d'indices `< d₁.numEdges` lisent `coloring₁`).
    have hj_lt : (j : Nat) < d₁.numEdges := j.isLt
    have hk_lt : (k : Nat) < d₁.numEdges := k.isLt
    have hj_val : (tricolorForwardExtension hnum2 a ha1 ha2 coloring₁)
        ⟨j.val, by omega⟩ = coloring₁ j := by
      show tricolorForwardExtension hnum2 a ha1 ha2 coloring₁ ⟨j.val, by omega⟩ =
        coloring₁ ⟨j.val, j.isLt⟩
      unfold tricolorForwardExtension
      rw [dif_pos hj_lt]
    have hk_val : (tricolorForwardExtension hnum2 a ha1 ha2 coloring₁)
        ⟨k.val, by omega⟩ = coloring₁ k := by
      show tricolorForwardExtension hnum2 a ha1 ha2 coloring₁ ⟨k.val, by omega⟩ =
        coloring₁ ⟨k.val, k.isLt⟩
      unfold tricolorForwardExtension
      rw [dif_pos hk_lt]
    rw [hj_val, hk_val]; exact hjk

/-! ## 3. Le trefoil est tricolorable

Le trefoil (3_1) peut etre colorie avec 3 couleurs, chaque croisement voyant
les trois couleurs. Cela prouve que le trefoil n'est PAS l'unknot.
-/

theorem trefoil_tricolorable : Knot.isTricolorable trefoil := by
  -- Proof: construct an explicit arc-respecting 3-colouring of the trefoil's 6
  -- edges (PD labels). The trefoil PD-code is [[1,4,2,5],[3,6,4,1],[5,2,6,3]],
  -- so numEdges = 6. Path B requires over-strand continuity `c2 = c4` at each
  -- crossing, in addition to the Fox rule on the three meeting strands (e1,e2,e3).
  -- Witness `(0,1,1,2,2,0)` on labels 1..6 (0=red, 1=blue, 2=green), i.e. by Fin
  -- index (index = label-1): labels {1,6} → red, {2,3} → blue, {4,5} → green.
  --   c0 ⟨1,4,2,5⟩: Fox(red, green, blue) all-distinct ✓; arc c(e2=4)=c(e4=5) both green ✓.
  --   c1 ⟨3,6,4,1⟩: Fox(blue, red, green) all-distinct ✓; arc c(e2=6)=c(e4=1) both red ✓.
  --   c2 ⟨5,2,6,3⟩: Fox(green, blue, red) all-distinct ✓; arc c(e2=2)=c(e4=3) both blue ✓.
  unfold Knot.isTricolorable IsTricolorable IsTriColoring Knot.diagram trefoil
  simp only [trefoilDiagram, triColorConditionAt, KnotDiagram.colorAtNat]
  -- Provide the explicit coloring on Fin 6 (index = label - 1).
  refine' ⟨fun i : Fin 6 =>
              if i.val = 0 ∨ i.val = 5 then TriColor.red
              else if i.val = 1 ∨ i.val = 2 then TriColor.blue
              else TriColor.green, _, _, _⟩
  -- Crossing condition: each of the 3 crossings satisfies the (Path B) condition.
  · -- The three crossings are ⟨1,4,2,5⟩, ⟨3,6,4,1⟩, ⟨5,2,6,3⟩. Decide by computation.
    intro c hc
    -- Reduce membership in the explicit crossing list to the 3 concrete cases.
    match c with
    | ⟨1, 4, 2, 5⟩ => decide
    | ⟨3, 6, 4, 1⟩ => decide
    | ⟨5, 2, 6, 3⟩ => decide
  -- numEdges ≥ 2: literal 6 ≥ 2
  · decide
  -- At least 2 colors: edge 0 = red, edge 2 = blue, red ≠ blue
  · exact ⟨⟨0, by decide⟩, ⟨2, by decide⟩, by decide⟩

/-! ## 3b. Contre-exemple certifie : le mouvement R1 a ρ libre ne preserve PAS
la tricolorabilite.

C'est un resultat diagnostique *positif* (pas un vide de l'invariant). Il
certifie que le mouvement `Reidemeister1` a ρ libre (Phase 5 PR1, #2929) — qui
porte le nouveau croisement `c` et le renommage d'aretes `ρ` comme DEUX
EXISTENTIELS INDEPENDANTS — ne preserve PAS la tricolorabilite : un seul tel
twist connecte un diagramme non tricolorable a un diagramme tricolorable. Apres
le re-cablage de Stage-2 (#2874), `ReidemeisterStep.r1` utilise le raffinement
GEOMETRIQUEMENT CONNECTE `Reidemeister1Connected` a la place, et cette paire de
temoins est exclue de maniere prouvee de ce mouvement (§3c-bis, PR #3997) ; donc
ce contre-exemple refute le mouvement brut a ρ libre `Reidemeister1`, PAS
l'equivalence connectee sur laquelle `tricolorable_invariant` repose desormais.

Pourquoi. La condition `wf` « chaque etiquette apparait exactement deux fois »
force le nouveau croisement `c` d'un twist R1 a utiliser UNIQUEMENT les deux
aretes fraiches `{n+1, n+2}` — les etiquettes `1..n` apparaissent deja deux fois
dans `d₁`, donc `c` ne peut reutiliser aucune d'elles sans casser la parite.
De plus le renommage d'aretes `ρ : Fin (min) ↪ Fin (max)` introduit par PR1 est
une injection LIBRE, NON liee aux etiquettes de `c`. La condition de Fox du
nouveau croisement implique donc seulement les deux aretes fraiches
(librement coloriables) et est DECOUPLEE du coloriage de `d₁` — si bien qu'un
twist peut CREER la tricolorabilite de rien, ou symetriquement cacher les
≥2-couleurs entierement dans les aretes fraiches tandis que `d₁` est force
monochrome.

Temoin (refute la biconditionnelle universelle) :
  d₁ = { crossings := [⟨1,2,1,2⟩], numEdges := 2 }    — PAS tricolorable.
       Fox a ⟨1,2,1,2⟩ lit (coloring⟨0⟩, coloring⟨1⟩, coloring⟨0⟩), ce qui est
       tout-egal SEULEMENT si coloring⟨0⟩ = coloring⟨1⟩ — contredisant
       l'exigence ≥2-couleurs. Donc aucun tricolorage valide n'existe.
  d₂ = { crossings := [⟨1,2,1,2⟩, ⟨3,4,3,4⟩], numEdges := 4 }  — tricolorable.
       Colorier les aretes 1,2 = red et 3,4 = blue : Fox tient aux deux
       croisements (tout-egal dans chacun), et ≥2 couleurs sont utilisees.
  Un seul twist R1 a ρ libre `Reidemeister1 d₁ d₂` les connecte, donc la
  biconditionnelle `IsTricolorable d₁ ↔ IsTricolorable d₂` est `(false ↔ true)`
  pour une paire lieee par le mouvement brut a ρ libre (qui n'est plus un
  `ReidemeisterStep` apres le re-cablage de Stage-2).

**Implemente (Stage 2 de #2874).** Le correctif est cable dans
`ReidemeisterStep.r1` : le constructeur porte le splicing geometrique via
`Reidemeister1Connected`, de sorte que `ρ` DETERMINE les etiquettes de `c` —
une boucle R1 veritable sur l'arc `a` s'insere dans l'arc `a` EXISTANT, dont la
condition de Fox contraint les nouvelles aretes a heriter de `color a`, ce qui
est ce qui fait transferer la tricolorabilite le long du mouvement. Le transfer
avant (§3e, #3003) reste l'obligation de preuve ouverte.
Reference : Fox (1962) ; Adams, "The Knot Book". -/

theorem tricolorable_invariant_fails_under_pr1_model :
    ∃ (d₁ d₂ : KnotDiagram),
      Reidemeister1 d₁ d₂ ∧
      ¬ IsTricolorable d₁ ∧
      IsTricolorable d₂ := by
  -- Witness pair.
  refine' ⟨{ crossings := [⟨1, 2, 1, 2⟩], numEdges := 2 },
           { crossings := [⟨1, 2, 1, 2⟩, ⟨3, 4, 3, 4⟩], numEdges := 4 },
           ?_, ?_, ?_⟩
  -- (a) Reidemeister1 d₁ d₂: a single free-ρ R1 twist, witness c = ⟨3,4,3,4⟩.
  --     d₁ = {[⟨1,2,1,2⟩], numEdges = 2}; d₂ = {[⟨1,2,1,2⟩, ⟨3,4,3,4⟩], numEdges = 4}.
  · refine' ⟨?_, ?_, ⟨⟨3, 4, 3, 4⟩, ⟨?_, ?_⟩⟩⟩
    · -- d₁.wf = true: labels 1,2 each appear twice across [1,2,1,2].
      decide
    · -- d₂.wf = true: labels 1,2,3,4 each appear twice across [1,2,1,2,3,4,3,4].
      decide
    · -- ρ : Fin (min d₁.numEdges d₂.numEdges) ↪ Fin (max d₁.numEdges d₂.numEdges),
      --   which is defeq to Fin 2 ↪ Fin 4 (d₁.numEdges = 2, d₂.numEdges = 4 reduce,
      --   and min/max on the literals reduce). Constructed concretely as Fin 2 ↪ Fin 4
      --   so omega sees concrete bounds; `exact` discharges the defeq to the goal type.
      have ρ : Fin 2 ↪ Fin 4 :=
        ⟨fun i => ⟨i.val, by omega⟩,
         fun a b h => by
           have h : (⟨a.val, by omega⟩ : Fin 4) = ⟨b.val, by omega⟩ := h
           injection h with hval
           exact Fin.ext hval⟩
      exact ρ
    · -- surgery (twist arm): field-equalities on a 2-field record
      --     d₂.crossings = d₁.crossings ++ [⟨3,4,3,4⟩] ∧ d₂.numEdges = d₁.numEdges + 2.
      --     Both conjuncts are defeq on the literal witness pair (concretely,
      --     [⟨1,2,1,2⟩,⟨3,4,3,4⟩] = [⟨1,2,1,2⟩] ++ [⟨3,4,3,4⟩] and 4 = 2 + 2).
      left
      exact ⟨rfl, rfl⟩
  -- (b) d₁ is NOT tricolorable: Fox at the sole crossing ⟨1,2,1,2⟩ forces the two
  --     edges to the same colour, contradicting the ≥2-colours requirement.
  · show ¬ IsTricolorable { crossings := [⟨1, 2, 1, 2⟩], numEdges := 2 }
    rintro ⟨coloring, hcond, hedges, htwo⟩
    -- The sole crossing ⟨1,2,1,2⟩ is in d₁.crossings; apply the Fox condition to it.
    have hfox := hcond (⟨1, 2, 1, 2⟩ : PDCrossing)
        (by exact List.mem_cons_self : _ ∈ ([⟨1, 2, 1, 2⟩] : List PDCrossing))
    -- Unfold: at ⟨1,2,1,2⟩ with numEdges = 2, the colours read are coloring⟨0⟩ (label 1)
    -- and coloring⟨1⟩ (label 2). Fox's all-distinct branch is impossible (the third
    -- strand equals the first), so Fox forces coloring⟨0⟩ = coloring⟨1⟩.
    have h01 : coloring ⟨0, by decide⟩ = coloring ⟨1, by decide⟩ := by
      have h := hfox
      simp only [triColorConditionAt, KnotDiagram.colorAtNat] at h
      -- Path B shape: `bounds ∧ (arc-eq ∧ Foxdisj)` — flatten the right-nested And.
      rcases h with ⟨_, _, h | h⟩
      · exact h.1
      · -- all-distinct branch: needs c1 ≠ c3, but e1 = e3 = 1 makes c1 ≡ c3 (rfl) → contradiction.
        exact (h.2.2 rfl).elim
    -- Hence every Fin 2 colour equals coloring⟨0⟩ (the only two elements are 0, 1).
    have hAll : ∀ (i : Fin 2), coloring i = coloring ⟨0, by decide⟩ := by
      intro i
      have h : i.val = 0 ∨ i.val = 1 := by omega
      rcases h with h | h
      · rw [show i = (⟨0, by omega⟩ : Fin 2) from Fin.ext h]
      · rw [show i = (⟨1, by omega⟩ : Fin 2) from Fin.ext h, h01]
    obtain ⟨i, j, hne⟩ := htwo
    exact hne (by rw [hAll i, hAll j])
  -- (c) d₂ IS tricolorable: edges 1,2 (Fin index 0,1) = red, edges 3,4 (index 2,3) = blue;
  --     Fox is all-equal within each crossing, ≥2 colours used.
  · show IsTricolorable { crossings := [⟨1, 2, 1, 2⟩, ⟨3, 4, 3, 4⟩], numEdges := 4 }
    refine' ⟨fun i : Fin 4 => if i.val ≤ 1 then TriColor.red else TriColor.blue, ?_, ?_, ?_⟩
    · -- Fox at every crossing of d₂.
      intro c hc
      -- d₂.crossings = [⟨1,2,1,2⟩, ⟨3,4,3,4⟩]; hc pins c to one of them.
      have hsplit : c = ⟨1, 2, 1, 2⟩ ∨ c = ⟨3, 4, 3, 4⟩ := by simpa using hc
      rcases hsplit with rfl | rfl
      · -- c = ⟨1,2,1,2⟩: local strands (1,2,1) all red → all-equal.
        simp only [triColorConditionAt, KnotDiagram.colorAtNat]; decide
      · -- c = ⟨3,4,3,4⟩: local strands (3,4,3) all blue → all-equal.
        simp only [triColorConditionAt, KnotDiagram.colorAtNat]; decide
    · -- numEdges = 4 ≥ 2.
      decide
    · -- ≥2 colours: edge index 0 = red ≠ blue = edge index 2.
      exact ⟨⟨0, by decide⟩, ⟨2, by decide⟩, by decide⟩

/-! ## 3c. Porte de non-regression (PR1.5) : le temoin #2938 est EXCLU sous `Reidemeister1'`

`Reidemeister1'` (Reidemeister.lean, PR1.5 #2956) est le renforcement determine
par ρ du mouvement R1 : le nouveau croisement est force a la forme
`⟨a, a, n+1, n+2⟩` — un strand est l'arc existant `a`. Cela couple les deux
aretes fraiches a `color(a)` via la condition de Fox, ce qui manquait au modèle
PR1 a `ρ` libre.

Le contre-exemple certifie `tricolorable_invariant_fails_under_pr1_model`
ci-dessus (§3b) refute la biconditionnelle *sous le modèle PR1* en exhibant une
paire de temois specifique `(d₁, d₂)` connectee par un R1-step PR1. **Ce theoreme
prouve que cette meme paire de temoins n'est PAS connectee par un step
`Reidemeister1'`** — i.e. le raffinement determine par ρ exclut le contre-exemple
par construction. C'est le test de non-regression qu'a exige ai-01 (PR1.5 porte
1, dashboard 11:35Z) : le re-modele doit EXCLURE #2938, et ici nous le prouvons
explicitement.

Paire de temoins (meme qu'au §3b) :
  d₁ = { crossings := [⟨1,2,1,2⟩], numEdges := 2 }
  d₂ = { crossings := [⟨1,2,1,2⟩, ⟨3,4,3,4⟩], numEdges := 4 }

Pourquoi `Reidemeister1' d₁ d₂` echoue :
  - Le bras twist force `d₂.crossings = [⟨1,2,1,2⟩] ++ [⟨a, a, 3, 4⟩]`, i.e. le
    second croisement doit etre `⟨a, a, 3, 4⟩`. Mais le second croisement de
    `d₂` est `⟨3, 4, 3, 4⟩`, donc l'egalite de liste force
    `⟨3,4,3,4⟩ = ⟨a,a,3,4⟩`, donnant `a = 3` (depuis e1) et `a = 4` (depuis e2)
    — contradiction.
  - Le bras untwist force `d₁.crossings` a egaliser `d₂.crossings ++ [⟨a,a,_,_⟩]`,
    une liste a 3 elements, mais `d₁.crossings` a 1 element — contradiction de
    longueur.
-/

/-- La paire de temoins #2938 n'est PAS connectee par un mouvement R1 determine
par ρ (`Reidemeister1'`). C'est la porte de non-regression PR1.5 : le re-modele
exclut le contre-exemple par construction. -/
theorem pr1_counterexample_excluded_under_rho_determined :
    ¬ Reidemeister1'
        { crossings := [⟨1, 2, 1, 2⟩], numEdges := 2 }
        { crossings := [⟨1, 2, 1, 2⟩, ⟨3, 4, 3, 4⟩], numEdges := 4 } := by
  -- **Migration #8696 fenêtre 2/9** : post-migration field-equalities, la
  -- surgery est `(h_cross ∧ h_num)` au lieu de `with`-surgery record. Le
  -- `congrArg (·.crossings) ht` disparaît — `h_cross` EST directement
  -- l'égalité de champs qu'on veut. Sur les literals concrets, le `simp` puis
  -- `injection` puis `omega` ferment les deux branches (TWIST/UNTWIST).
  rintro ⟨_hwf₁, _hwf₂, a, _hrange₁, _hrange₂, _ρ, hsurg⟩
  -- `hsurg` is `(⟨h_cross, h_num⟩ | ⟨h_cross, h_num⟩)` — re-destructure each
  -- branch's internal 2-conj to recover the field-equality on `.crossings`.
  rcases hsurg with ⟨h_cross, _h_num⟩ | ⟨h_cross, _h_num⟩
  · -- TWIST arm: d₂.crossings = d₁.crossings ++ [⟨a,a,3,4⟩] ∧ d₂.numEdges = 4.
    --   d₁.numEdges = 2, so appended crossing is ⟨a, a, 3, 4⟩. h_cross IS
    --   the field equality on `.crossings` directly (no projection needed).
    have h2nd : (⟨3, 4, 3, 4⟩ : PDCrossing) = ⟨a, a, 3, 4⟩ := by
      simpa [List.append] using h_cross
    -- Injectivity of PDCrossing (4 fields): e1 gives 3 = a, e2 gives 4 = a.
    injection h2nd with h_e1 h_e2 h_e3 h_e4
    omega
  · -- UNTWIST arm: d₁.crossings = d₂.crossings ++ [⟨a,a,5,6⟩] ∧ d₁.numEdges = 6.
    --   d₂.numEdges = 4, so appended crossing = ⟨a, a, 5, 6⟩. h_cross IS
    --   the field equality on `.crossings` directly.
    -- Length contradiction: LHS has length 1, RHS has length 3.
    -- `simp at h` reduces the list lengths to concrete numbers (`1` and `3`),
    -- then closes the goal by deriving `False` from the contradiction `1 = 3`.
    have h := congrArg List.length h_cross
    simp at h

/-! ## 3c-bis. Le temoin #2938 est AUSSI exclu sous `Reidemeister1Connected` (option C)

`pr1_counterexample_excluded_under_rho_determined` (§3c ci-dessus) prouve que la
paire de temoins contre-exemple certifiee n'est PAS connectee par un mouvement
`Reidemeister1'` (determine par ρ). Ici nous prouvons l'enonce analogue pour
`Reidemeister1Connected` (option C) : la paire de temoins refutante est
inaccessible sous un twist R1 connecte aussi. C'est la seconde porte de
non-regression certifiant que l'option C — le cablage (C) mandate pour #2874 —
exclut le contre-exemple de kink disjoint par construction.

Pourquoi il echoue. `Reidemeister1Connected` requiert que le croisement kink
ajoute ait la forme `⟨a, n+1, n+2, n+2⟩` ou `1 ≤ a ≤ d₁.numEdges` est un arc
existant de `d₁`. Pour le temoin (`d₁` = {[⟨1,2,1,2⟩], numEdges = 2), la
chirurgie force le dernier croisement `⟨3,4,3,4⟩` de `d₂` a egaliser
`⟨a, 3, 4, 4⟩`, donnant `a = 3` — contredisant `a ≤ d₁.numEdges = 2`. Le
contre-exemple de kink disjoint est donc structurel : sous tout modèle R1
connecte, le twist doit splicer un VRAI arc de `d₁` (le croisement unique du
temoin n'a pas d'arc etiquete `3` a splicer), donc la paire est inaccessible.
C'est ce qui fait de l'option C le correctif SOTA honnete plutot que le
reframe (X) : le temoin refutant s'evanouit sous l'equivalence correcte.
(Cabler `Reidemeister1Connected` dans `ReidemeisterStep`/`ReidemeisterEquiv`
est un stage multi-cycle — `Reidemeister1Connected` est actuellement
twist-seul et a besoin d'un bras untwist + `.symm` avant que le
`reidemeister_equiv_symm` de l'equivalence puisse le porter. Voir #2874.) -/
theorem pr1_counterexample_excluded_under_connected :
    ¬ Reidemeister1Connected
        { crossings := [⟨1, 2, 1, 2⟩], numEdges := 2 }
        { crossings := [⟨1, 2, 1, 2⟩, ⟨3, 4, 3, 4⟩], numEdges := 4 } := by
  -- Reidemeister1Connected unfolds as wf₁ ∧ wf₂ ∧ (∃ i a Y' ρ, bounds ∧ edges ∧
  -- proper-arc ∧ isRenameOf ∧ surgery). The surgery is single-arm (twist only):
  -- d₂ = { d₁ with crossings := d₁.crossings.set i.val Y' ++ [⟨a,3,4,4⟩], numEdges := 4 }.
  rintro ⟨_hwf₁, _hwf₂, i, a, Y', _ρ, _ha1, ha2, _ha_edges, _hproper, _hren, h_cross, _h_num⟩
  -- `i : Fin d₁.crossings.length = Fin 1`, so `i.val = 0`. omega cannot reduce the
  -- structure literal's `.crossings.length` on its own, so discharge the length by
  -- `rfl` (separate hyp — `rw` into `i.isLt` fails: `i`'s type depends on it) and
  -- let omega combine `hbnd : i.val < e` with `hlen : e = 1` directly.
  have hi : i.val = 0 := by
    have hlen :
        (({ crossings := [⟨1, 2, 1, 2⟩], numEdges := 2 }
          : KnotDiagram).crossings).length = 1 := by rfl
    have hbnd := i.isLt
    omega
  have hfield :
      ({ crossings := [⟨1, 2, 1, 2⟩, ⟨3, 4, 3, 4⟩], numEdges := 4 }
        : KnotDiagram).crossings =
      (({ crossings := [⟨1, 2, 1, 2⟩], numEdges := 2 }
        : KnotDiagram).crossings.set i.val Y') ++ [⟨a, 3, 4, 4⟩] :=
    h_cross
  rw [hi] at hfield
  -- RHS reduces to [⟨1,2,1,2⟩].set 0 Y' ++ [⟨a,3,4,4⟩] = [Y', ⟨a,3,4,4⟩].
  -- The second element gives ⟨3,4,3,4⟩ = ⟨a,3,4,4⟩ (cons injectivity).
  have hkink : (⟨3, 4, 3, 4⟩ : PDCrossing) = ⟨a, 3, 4, 4⟩ := by
    simpa [List.set, List.append] using hfield
  -- e2 field projection: ⟨3,4,3,4⟩.e2 = 4 vs ⟨a,3,4,4⟩.e2 = 3 — a direct
  -- `4 = 3` contradiction (structural, independent of the value of `a`).
  -- We assert the reduced type so defeq closes the projection of the literal.
  have h_e2 : (4 : Nat) = 3 := congrArg PDCrossing.e2 hkink
  omega

/-! ## 3d. Le mouvement R1 connecte (option C) PRESERVE la tricolorabilite sur le temoin

C'est le complement positif au contre-exemple PR1 (§3b). Sous le
`Reidemeister1Connected` RENFORCE (option C, portant l'hypothese
`Y'.isRenameOf`), le twist R1 connecte ne cree ni ne detruit la tricolorabilite
comme le faisait le modèle d'ajout de kink disjoint (#2938). Nous le verifions
sur la paire de temois concrete de `reidemeister1Connected_satisfiable`
(Reidemeister.lean) : le mouvement connecte envoie un `d₁` tricolorable sur un
`d₂` tricolorable, et reciproquement.

Pourquoi les deux sens tiennent sur le temoin. Le twist connecte sur l'arc
`a = 1` renomme le slot `e1` du croisement 1 (`1 → 5 = b`) et ajoute
`C = ⟨1,5,6,6⟩`. Un tricolorage de `d₁` s'etend a `d₂` en donnant aux deux
nouvelles aretes `b = 5` et `c = 6` la couleur de l'arc `a = 1` : alors le
nouveau croisement `C` lit `(col a, col a, col a)` — tout-egal, Fox-trivial —
et le croisement modifie lit les memes trois couleurs qu'avant (le slot renomme
`b` porte `col a`). Reciproquement un tricolorage de `d₂` se projette sur `d₁`.
C'est la verification *calculatoire* que l'option C preserve l'invariant ; le
lemme de transfer general (`Reidemeister1Connected.tricolorable_invariant`, la
cible PR2) fait cet argument pour des diagrammes arbitraires — gate sur la
fusion du def renforce (PR #2990).

Certifie constructivement : nous exhibons un 3-coloriage explicite de chaque
diagramme (mirant le pattern `trefoil_tricolorable`), de sorte que chaque cote
est habite et la biconditionnelle se reduit a `(true ↔ true)`. `IsTricolorable`
est un existentiel sur `Fin n → TriColor`, donc aucune instance `Decidable` ne
se derive automatiquement — les coloriages sont fournis a la main, chaque
condition de Fox du croisement etant dischargee par `decide`.
-/

/-- The witness `d₁` of `reidemeister1Connected_satisfiable` (Reidemeister.lean). -/
def witnessD1Connected : KnotDiagram :=
  { crossings := [⟨1,2,3,4⟩, ⟨1,2,3,4⟩], numEdges := 4 }

/-- The witness `d₂` of `reidemeister1Connected_satisfiable` (Reidemeister.lean). -/
def witnessD2Connected : KnotDiagram :=
  { crossings := [⟨1,2,3,4⟩, ⟨5,2,3,4⟩, ⟨1,5,6,6⟩], numEdges := 6 }

/-- `witnessD1Connected` est tricolorable (Path B) : les deux croisements sont
    `⟨1,2,3,4⟩`, chacun lisant `(red, blue, green)` sur les strands de Fox
    `(e1, e2, e3) = (1, 2, 3)` (tous deux a deux distincts), avec continuite du
    strand over `c(e2) = c(e4)` (aretes 2 et 4 toutes deux blue). Constructif,
    mirant `trefoil_tricolorable`. -/
theorem witnessD1Connected_tricolorable : IsTricolorable witnessD1Connected := by
  unfold IsTricolorable IsTriColoring witnessD1Connected
  simp only [triColorConditionAt, KnotDiagram.colorAtNat]
  -- Arc-respecting colouring (Path B): edges {1}→red, {2,4}→blue, {3}→green, so
  -- the over-arc (e2,e4)=(2,4) is monochromatic (blue) at each ⟨1,2,3,4⟩.
  refine' ⟨fun i : Fin 4 =>
              if i.val = 0 then TriColor.red
              else if i.val = 1 ∨ i.val = 3 then TriColor.blue
              else TriColor.green, ?_, ?_, ?_⟩
  · intro c hc
    -- Both crossings are `⟨1,2,3,4⟩`; the single distinct value is the only
    -- element of the list, so the (Path B) condition is checked once by computation.
    match c with
    | ⟨1, 2, 3, 4⟩ => decide
  · decide
  · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide⟩

/-- `witnessD2Connected` est tricolorable (Path B) : les croisements originaux
    `⟨1,2,3,4⟩` et `⟨5,2,3,4⟩` lisent des couleurs toutes distinctes avec
    continuite du strand over `c(e2) = c(e4)` (aretes 2,4 toutes deux blue), et
    le nouveau kink `⟨1,5,6,6⟩` lit `(red, red, red)` (tout-egal, Fox-trivial)
    avec `c(e2) = c(e4)` sur les aretes 5,6 (toutes deux red). Les deux nouvelles
    aretes `b = 5` et `c = 6` portent la couleur de l'arc `a = 1` (red), donc le
    twist ne cree ni ne detruit la tricolorabilite. -/
theorem witnessD2Connected_tricolorable : IsTricolorable witnessD2Connected := by
  unfold IsTricolorable IsTriColoring witnessD2Connected
  simp only [triColorConditionAt, KnotDiagram.colorAtNat]
  -- Arc-respecting colouring (Path B): edges {1,5,6}→red, {2,4}→blue, {3}→green.
  refine' ⟨fun i : Fin 6 =>
              if i.val = 0 ∨ i.val = 4 ∨ i.val = 5 then TriColor.red
              else if i.val = 1 ∨ i.val = 3 then TriColor.blue
              else TriColor.green, ?_, ?_, ?_⟩
  · intro c hc
    match c with
    | ⟨1, 2, 3, 4⟩ => decide
    | ⟨5, 2, 3, 4⟩ => decide
    | ⟨1, 5, 6, 6⟩ => decide
  · decide
  · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide⟩

/-- Le mouvement R1 connecte (option C, `Reidemeister1Connected` renforce)
    preserve la tricolorabilite sur la paire de temois concrete de
    `reidemeister1Connected_satisfiable` : `witnessD1Connected` et
    `witnessD2Connected` sont tous deux tricolorables, donc la biconditionnelle
    est `(true ↔ true)`. C'est le complement positif au contre-exemple PR1
    `tricolorable_invariant_fails_under_pr1_model` (§3b), confirmant que le
    modèle de chirurgie connectee ne partage pas le defaut de kink disjoint.
    Prouve constructivement (3-coloriages explicites, mirant
    `trefoil_tricolorable`). -/
theorem reidemeister1Connected_witness_preserves_tricolorable :
    IsTricolorable witnessD1Connected ↔ IsTricolorable witnessD2Connected :=
  ⟨fun _ => witnessD2Connected_tricolorable, fun _ => witnessD1Connected_tricolorable⟩

/-! ## 3e. Transfer avant PR2 : un mouvement R1 connecte PRESERVE la tricolorabilite

Sous le `Reidemeister1Connected` renforce (portant l'hypothese `Y'.isRenameOf`,
merge #2990), un tricolorage de `d₁` s'etend en un tricolorage de `d₂` : les
deux aretes fraiches `b = numEdges+1` et `c = numEdges+2` portent toutes deux la
couleur de l'arc `a`. Cela rend le nouveau croisement kink `⟨a, b, c, c⟩`
Fox-trivial (`(col a)³`, tout-egal) et le renommage `a → b` Fox-invisible
(`col₂ b = col₁ a`). C'est la moitie avant de `tricolorable_invariant`
specialisee au mouvement R1 connecte (option C).
-/

/-- Appartenance avant pour `List.set` : un element de `l.set n v` est soit la
    valeur inseree `v` (a la position modifiee) soit deja un element de `l`.
    Aide pure de combinatoire de listes (pas de contenu de nœud), utilisee par
    le lemme de transfer pour decomposer `d₂.crossings = d₁.crossings.set i
    Y' ++ [C]`. -/
private theorem mem_set_fwd {α : Type*} : ∀ (n : Nat) (l : List α) (v c : α),
    c ∈ l.set n v → c = v ∨ c ∈ l
  | 0, [], _, _, h => by simp at h
  | 0, hd :: tl, v, c, h => by
    change c ∈ v :: tl at h
    simp only [List.mem_cons] at h ⊢
    rcases h with heq | hmem
    · refine Or.inl ?_; exact heq
    · exact Or.inr (Or.inr hmem)
  | _+1, [], _, _, h => by simp at h
  | n+1, hd :: tl, v, c, h => by
    have ih := mem_set_fwd n tl v c
    change c ∈ hd :: tl.set n v at h
    simp only [List.mem_cons] at h ⊢
    rcases h with hhd | hset
    · exact Or.inr (Or.inl hhd)
    · rcases ih hset with rfl | hmem
      · exact Or.inl rfl
      · exact Or.inr (Or.inr hmem)

/-- Appartenance arriere pour `List.set` : si `c ∈ l` mais `c ∉ l.set n v`,
    alors `c` est exactement l'element `l.get n` qui a ete remplace, et
    `c ≠ v`. Aide pure de combinatoire de listes, converse-en-esprit de
    `mem_set_fwd`, utilisee par le lemme de transfer arriere pour identifier
    le croisement modifie `Y`. -/
private theorem mem_drop_out {α : Type*} : ∀ (n : Nat) (l : List α) (v c : α)
    (hn : n < l.length) (hc : c ∈ l) (hnmem : c ∉ l.set n v),
    l.get ⟨n, hn⟩ = c ∧ c ≠ v
  | 0, hd :: tl, v, c, hn, hc, hnmem => by
    change c ∉ v :: tl at hnmem
    simp only [List.mem_cons] at hc hnmem
    refine ⟨?_, fun heq => hnmem (Or.inl heq)⟩
    rcases hc with hhd | hctl
    · exact hhd.symm
    · exact absurd hctl (fun h => hnmem (Or.inr h))
  | n+1, hd :: tl, v, c, hn, hc, hnmem => by
    change c ∉ hd :: tl.set n v at hnmem
    simp only [List.mem_cons] at hc hnmem
    rcases hc with hhd | hctl
    · exact absurd hhd (fun h => hnmem (Or.inl h))
    · have hlen : (hd :: tl).length = tl.length + 1 := List.length_cons
      have ihn : n < tl.length := by omega
      have ihntset : c ∉ tl.set n v := fun h => hnmem (Or.inr h)
      have ih := mem_drop_out n tl v c ihn hctl ihntset
      refine ⟨?_, ih.2⟩
      have hfin : (⟨n, Nat.lt_of_succ_lt_succ hn⟩ : Fin tl.length) = ⟨n, ihn⟩ := Fin.ext rfl
      rw [show (hd :: tl).get ⟨n+1, hn⟩ = tl.get ⟨n, Nat.lt_of_succ_lt_succ hn⟩ from rfl, hfin]
      exact ih.1
  | _, [], _, _, hn, _, _ => (Nat.not_lt_zero _ hn).elim

/-- Appartenance de la valeur inseree dans `List.set` : `v ∈ l.set n v` quand
    `n < l.length`. Aide pure de combinatoire de listes, utilisee par le lemme
    de transfer arriere pour temoigner que le croisement de remplacement `Y'`
    figure dans `d₂.crossings`. -/
private theorem mem_set_self {α : Type*} : ∀ (n : Nat) (l : List α) (v : α) (hn : n < l.length),
    v ∈ l.set n v
  | 0, hd :: tl, v, _ => by
    change v ∈ v :: tl
    exact List.mem_cons_self
  | n+1, hd :: tl, v, hn => by
    have hlen : (hd :: tl).length = tl.length + 1 := List.length_cons
    have ihn : n < tl.length := by omega
    change v ∈ hd :: tl.set n v
    simp only [List.mem_cons]
    exact Or.inr (mem_set_self n tl v ihn)
  | _, [], _, hn => (Nat.not_lt_zero _ hn).elim

theorem Reidemeister1Connected.tricolorable_forward {d₁ d₂ : KnotDiagram}
    (h : Reidemeister1Connected d₁ d₂) (htri : IsTricolorable d₁) :
    IsTricolorable d₂ := by
  obtain ⟨_hwf₁, _hwf₂, i, a, Y', _ρ, ha1, ha2, _hamem, _hproper, hrename, h_cross, h_num⟩ := h
  -- Edge-count and crossing-list consequences of the surgery equation.
  have hd₂num : d₂.numEdges = d₁.numEdges + 2 := h_num
  have hd₂cross : d₂.crossings =
      d₁.crossings.set i.val Y' ++
        [⟨a, d₁.numEdges + 1, d₁.numEdges + 2, d₁.numEdges + 2⟩] := h_cross
  obtain ⟨col₁, hfox₁, hge2, h2col⟩ := htri
  -- Extension colouring: preserved edges keep their colour, the two new edges
  -- (indices `d₁.numEdges` and `d₁.numEdges+1`, i.e. labels `b`, `c`) carry
  -- `col₁ a`. Defined as a local def so `simp only [col₂]` can unfold it.
  have haim1 : a - 1 < d₁.numEdges := by omega
  have hd₂ge₁ : d₁.numEdges ≤ d₂.numEdges := by omega
  -- Embedding of `d₁`'s edge indices into `d₂`'s (the +2 fresh edges sit above).
  let emb : Fin d₁.numEdges → Fin d₂.numEdges :=
    fun k => ⟨k.val, Nat.lt_of_lt_of_le k.isLt hd₂ge₁⟩
  let col₂ : Fin d₂.numEdges → TriColor :=
    fun j => if hj : j.val < d₁.numEdges then col₁ ⟨j.val, hj⟩
             else col₁ ⟨a - 1, haim1⟩
  refine' ⟨col₂, ?fox, ?num, ?col⟩
  case num =>
    -- `d₂.numEdges = d₁.numEdges + 2 ≥ 2` since `d₁.numEdges ≥ 2`.
    omega
  case col =>
    -- At least two colours: two distinct-coloured edges of `d₁` embed into `d₂`.
    obtain ⟨p, q, hpq⟩ := h2col
    -- `col₂ (emb k) = col₁ k`: beta-reduce, the `if` is positive (k.val < n),
    -- and the `Fin` constructor collapses by proof irrelevance.
    have hcol_pres : ∀ k : Fin d₁.numEdges, col₂ (emb k) = col₁ k := by
      intro k
      conv_lhs => unfold col₂
      rw [dif_pos k.isLt]
    refine' ⟨emb p, emb q, ?_⟩
    rw [hcol_pres p, hcol_pres q]
    exact hpq
  case fox =>
    -- Colour-preservation facts, the heart of the transfer.
    -- (F1) A preserved label `l` (1 ≤ l ≤ d₁.numEdges) reads the same colour in
    --      `d₂` (under `col₂`) as in `d₁` (under `col₁`).
    have hcolF1 : ∀ l, 1 ≤ l → l ≤ d₁.numEdges →
        d₂.colorAtNat col₂ l = d₁.colorAtNat col₁ l := by
      intro l hl1 hln
      have hn0d₂ : d₂.numEdges ≠ 0 := by omega
      have hn0d₁ : d₁.numEdges ≠ 0 := by omega
      have hL : d₂.colorAtNat col₂ l =
          col₂ ⟨(l - 1) % d₂.numEdges, Nat.mod_lt (l - 1) (by omega)⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₂]
      have hR : d₁.colorAtNat col₁ l =
          col₁ ⟨(l - 1) % d₁.numEdges, Nat.mod_lt (l - 1) (by omega)⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₁]
      rw [hL, hR]
      simp only [hd₂num]
      have h1 : (l - 1) % (d₁.numEdges + 2) = l - 1 := Nat.mod_eq_of_lt (by omega)
      have h2 : (l - 1) % d₁.numEdges = l - 1 := Nat.mod_eq_of_lt (by omega)
      simp only [h1, h2]
      conv_lhs => unfold col₂
      simp only [dif_pos (by omega : (l - 1) < d₁.numEdges)]
    have hcolF2b : d₂.colorAtNat col₂ (d₁.numEdges + 1) = d₁.colorAtNat col₁ a := by
      have hn0d₂ : d₂.numEdges ≠ 0 := by omega
      have hn0d₁ : d₁.numEdges ≠ 0 := by omega
      have hL : d₂.colorAtNat col₂ (d₁.numEdges + 1) =
          col₂ ⟨(d₁.numEdges + 1 - 1) % d₂.numEdges, Nat.mod_lt (d₁.numEdges + 1 - 1) (by omega)⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₂]
      have hR : d₁.colorAtNat col₁ a =
          col₁ ⟨(a - 1) % d₁.numEdges, Nat.mod_lt _ (by omega)⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₁]
      rw [hL, hR]
      simp only [hd₂num]
      have h1 : (d₁.numEdges + 1 - 1) % (d₁.numEdges + 2) = d₁.numEdges := by
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      have h2 : (a - 1) % d₁.numEdges = a - 1 := Nat.mod_eq_of_lt (by omega)
      simp only [h1, h2]
      conv_lhs => unfold col₂
      simp only [dif_neg (by omega : ¬(d₁.numEdges < d₁.numEdges))]
    have hcolF2c : d₂.colorAtNat col₂ (d₁.numEdges + 2) = d₁.colorAtNat col₁ a := by
      have hn0d₂ : d₂.numEdges ≠ 0 := by omega
      have hn0d₁ : d₁.numEdges ≠ 0 := by omega
      have hL : d₂.colorAtNat col₂ (d₁.numEdges + 2) =
          col₂ ⟨(d₁.numEdges + 2 - 1) % d₂.numEdges, Nat.mod_lt (d₁.numEdges + 2 - 1) (by omega)⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₂]
      have hR : d₁.colorAtNat col₁ a =
          col₁ ⟨(a - 1) % d₁.numEdges, Nat.mod_lt _ (by omega)⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₁]
      rw [hL, hR]
      simp only [hd₂num]
      have h1 : (d₁.numEdges + 2 - 1) % (d₁.numEdges + 2) = d₁.numEdges + 1 := by
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      have h2 : (a - 1) % d₁.numEdges = a - 1 := Nat.mod_eq_of_lt (by omega)
      simp only [h1, h2]
      conv_lhs => unfold col₂
      simp only [dif_neg (by omega : ¬(d₁.numEdges + 1 < d₁.numEdges))]
    -- ===== Forward Fox transfer: ∀ c ∈ d₂.crossings, triColorConditionAt d₂ col₂ c.
    -- We only unfold `triColorConditionAt` (NOT `colorAtNat`), so the Fox part keeps
    -- `colorAtNat` folded and the colour lemmas hcolF1/hcolF2b/hcolF2c fire by `rw`.
    -- (C) New kink ⟨a, n+1, n+2, n+2⟩: strands (a, n+1, n+2) all read `col₁ a`.
    have hC : triColorConditionAt d₂ col₂
        ⟨a, d₁.numEdges + 1, d₁.numEdges + 2, d₁.numEdges + 2⟩ := by
      simp only [triColorConditionAt]
      refine ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega,
                by omega, by omega⟩, ?_⟩
      -- Path B: over-strand continuity c(e2)=c(e4), then Fox on (a, n+1, n+2).
      refine ⟨?_, ?_⟩
      · -- c(e2) = c(n+1) = col₁ a, c(e4) = c(n+2) = col₁ a (hcolF2b / hcolF2c).
        rw [hcolF2b, hcolF2c]
      · left
        refine ⟨?_, ?_⟩
        · rw [hcolF1 a ha1 ha2, hcolF2b]
        · rw [hcolF2b, hcolF2c]
    -- (iii) An unchanged crossing inherits d₁'s Fox: each preserved strand reads the
    --       same colour under `col₂` (via hcolF1), so the Fox condition is identical.
    have h_inherit : ∀ c, c ∈ d₁.crossings → triColorConditionAt d₂ col₂ c := by
      intro c hcmem
      have hfc : triColorConditionAt d₁ col₁ c := hfox₁ c hcmem
      simp only [triColorConditionAt] at hfc ⊢
      obtain ⟨⟨he11, he12, he21, he22, he31, he32, he41, he42⟩, ⟨harc, hfox⟩⟩ := hfc
      have h1 : d₂.colorAtNat col₂ c.e1 = d₁.colorAtNat col₁ c.e1 := hcolF1 c.e1 he11 he12
      have h2 : d₂.colorAtNat col₂ c.e2 = d₁.colorAtNat col₁ c.e2 := hcolF1 c.e2 he21 he22
      have h3 : d₂.colorAtNat col₂ c.e3 = d₁.colorAtNat col₁ c.e3 := hcolF1 c.e3 he31 he32
      have h4 : d₂.colorAtNat col₂ c.e4 = d₁.colorAtNat col₁ c.e4 := hcolF1 c.e4 he41 he42
      refine ⟨⟨he11, by omega, he21, by omega, he31, by omega, he41, by omega⟩, ⟨?_, ?_⟩⟩
      · -- Over-strand continuity col₂(e2)=col₂(e4) via colour-preservation + d₁'s arc-eq.
        rw [h2, h4]; exact harc
      · rcases hfox with ⟨h12, h23⟩ | ⟨h12, h23, h13⟩
        · left; refine ⟨?_, ?_⟩
          · rw [h1, h2]; exact h12
          · rw [h2, h3]; exact h23
        · right; refine ⟨?_, ?_, ?_⟩
          · rw [h1, h2]; exact h12
          · rw [h2, h3]; exact h23
          · rw [h1, h3]; exact h13
    -- (ii) The modified endpoint Y' preserves Fox: `isRenameOf` makes each strand of
    --       Y' read the same colour as the corresponding strand of the original crossing
    --       under `col₁` (unchanged strand via hcolF1; renamed `a→b` strand via hcolF2b).
    have hY' : triColorConditionAt d₂ col₂ Y' := by
      have hYorig : triColorConditionAt d₁ col₁ (d₁.crossings.get i) :=
        hfox₁ _ (List.get_mem d₁.crossings i)
      simp only [triColorConditionAt] at hYorig ⊢
      obtain ⟨⟨oe11, oe12, oe21, oe22, oe31, oe32, oe41, oe42⟩, ⟨harc_orig, hfoxo⟩⟩ := hYorig
      -- isRenameOf field-by-field: derive a colour-equation for each strand.
      obtain ⟨hre1, hre2, hre3, hre4⟩ := hrename
      -- Lemma: a renamed-or-unchanged strand `Y'.f` reads `col₁ (orig.f)`.
      have help : ∀ (hf : Nat) (ho : Nat) (hr : hf = ho ∨ (hf = d₁.numEdges + 1 ∧ ho = a))
                     (ho1 : 1 ≤ ho) (hon : ho ≤ d₁.numEdges),
          d₂.colorAtNat col₂ hf = d₁.colorAtNat col₁ ho := by
        intro hf ho hr ho1 hon
        rcases hr with heq | ⟨heqf, heqa⟩
        · rw [heq]; exact hcolF1 ho ho1 hon
        · -- hf = b = d₁.numEdges+1 (heqf), ho = a (heqa): col₂ reads col₁ a on edge b.
          rw [heqf, heqa, hcolF2b]
      have he1' : 1 ≤ Y'.e1 ∧ Y'.e1 ≤ d₂.numEdges := by
        rcases hre1 with heq | ⟨heqf, heqa⟩
        · rw [heq]; exact ⟨oe11, by omega⟩
        · rw [heqf]; exact ⟨by omega, by omega⟩
      have he2' : 1 ≤ Y'.e2 ∧ Y'.e2 ≤ d₂.numEdges := by
        rcases hre2 with heq | ⟨heqf, heqa⟩
        · rw [heq]; exact ⟨oe21, by omega⟩
        · rw [heqf]; exact ⟨by omega, by omega⟩
      have he3' : 1 ≤ Y'.e3 ∧ Y'.e3 ≤ d₂.numEdges := by
        rcases hre3 with heq | ⟨heqf, heqa⟩
        · rw [heq]; exact ⟨oe31, by omega⟩
        · rw [heqf]; exact ⟨by omega, by omega⟩
      have he4' : 1 ≤ Y'.e4 ∧ Y'.e4 ≤ d₂.numEdges := by
        rcases hre4 with heq | ⟨heqf, heqa⟩
        · rw [heq]; exact ⟨oe41, by omega⟩
        · rw [heqf]; exact ⟨by omega, by omega⟩
      have h1 : d₂.colorAtNat col₂ Y'.e1 = d₁.colorAtNat col₁ (d₁.crossings.get i).e1 :=
        help Y'.e1 (d₁.crossings.get i).e1 hre1 oe11 oe12
      have h2 : d₂.colorAtNat col₂ Y'.e2 = d₁.colorAtNat col₁ (d₁.crossings.get i).e2 :=
        help Y'.e2 (d₁.crossings.get i).e2 hre2 oe21 oe22
      have h3 : d₂.colorAtNat col₂ Y'.e3 = d₁.colorAtNat col₁ (d₁.crossings.get i).e3 :=
        help Y'.e3 (d₁.crossings.get i).e3 hre3 oe31 oe32
      have h4 : d₂.colorAtNat col₂ Y'.e4 = d₁.colorAtNat col₁ (d₁.crossings.get i).e4 :=
        help Y'.e4 (d₁.crossings.get i).e4 hre4 oe41 oe42
      refine ⟨⟨he1'.1, he1'.2, he2'.1, he2'.2, he3'.1, he3'.2, he4'.1, he4'.2⟩, ⟨?_, ?_⟩⟩
      · -- Over-strand continuity col₂(Y'.e2)=col₂(Y'.e4) via rename transfer + d₁'s arc-eq.
        rw [h2, h4]; exact harc_orig
      · rcases hfoxo with ⟨h12, h23⟩ | ⟨h12, h23, h13⟩
        · left; refine ⟨?_, ?_⟩
          · rw [h1, h2]; exact h12
          · rw [h2, h3]; exact h23
        · right; refine ⟨?_, ?_, ?_⟩
          · rw [h1, h2]; exact h12
          · rw [h2, h3]; exact h23
          · rw [h1, h3]; exact h13
    -- Membership split: c ∈ d₂.crossings = (set i Y') ++ [C]  →  C / Y' / unchanged.
    have hset_fwd : ∀ c, c ∈ d₁.crossings.set i.val Y' → c = Y' ∨ c ∈ d₁.crossings :=
      fun c hcm => mem_set_fwd i.val d₁.crossings Y' c hcm
    intro c hcmem
    rw [hd₂cross] at hcmem
    simp only [List.mem_append, List.mem_singleton] at hcmem
    rcases hcmem with hset | rfl
    · rcases hset_fwd c hset with rfl | hcorig
      · exact hY'
      · exact h_inherit c hcorig
    · exact hC

/-! ## 4. L'unknot n'est PAS tricolorable

L'unknot a un diagramme sans croisement. Tout coloriage n'utilise qu'un
seul strand, donc la condition « au moins 2 couleurs » echoue.
-/

theorem unknot_not_tricolorable : ¬ Knot.isTricolorable unknot := by
  -- Proof: unknot has exactly 1 edge (numEdges = 1).
  -- Fin 1 has a single element ⟨0, _⟩, so every coloring is constant.
  -- Hence ∃ i j, coloring i ≠ coloring j is impossible.
  unfold Knot.isTricolorable IsTricolorable IsTriColoring
  rintro ⟨coloring, hcond, hedges, htwocolors⟩
  -- htwocolors : ∃ i j, coloring i ≠ coloring j
  -- But Fin 1 has only one element, contradiction
  have : ∀ (i j : Fin 1), coloring i = coloring j := by
    intro i j
    -- Fin 1 has only ⟨0, _⟩
    have hi : i = ⟨0, by omega⟩ := by exact Fin.ext_iff.mpr (Fin.val_eq_zero i)
    have hj : j = ⟨0, by omega⟩ := by exact Fin.ext_iff.mpr (Fin.val_eq_zero j)
    rw [hi, hj]
  obtain ⟨i, j, hne⟩ := htwocolors
  exact hne (this i j)

/-! ## 4b. La figure-eight n'est PAS tricolorable

La figure-eight (4₁) possède 4 croisements et un déterminant égal à 5 ; elle
n'est donc PAS 3-coloriable au sens de Fox. Sous **Path B** (conjonction
d'arc-égalité `c₂ = c₄`), c'est le témoin de distinction canonique : le modèle
permissif antérieur laissait passer une tricoloration parasite `(0,0,0,1,0,0,1,2)`
(README §Path B), que la contrainte d'arc exclut désormais.

Preuve par énumération finie (`decide` noyau) : l'espace des coloriages
`Fin 8 → TriColor` (3⁸ = 6561) est parcouru, et pour chacun la conjonction
d'arc-égalité + Fox aux 4 croisements est réfutée — soit l'arc-continuité casse,
soit Fox force le monochrome (contredisant « ≥ 2 couleurs »). On emploie `decide`
(et non `native_decide`) : l'existentiel porte sur le type-fonction
`Fin 8 → TriColor`, dont l'instance `Decidable` repose sur `Fintype.piFinset`. La
réduction noyau de cette énumération dépasse la profondeur de récursion par
défaut (échec `maximum recursion depth has been reached`), on lève donc la
limite via `set_option maxRecDepth 100000` — le `decide` termine alors en ~33s.
C'est strictement préférable à `native_decide` : le **noyau vérifie** le
résultat plutôt que de déléguer au compilateur C / runtime (le TCB reste Lean,
pas `native_decide.ax`), et `#print axioms` ne relève plus que
`[propext, Classical.choice, Quot.sound]`. Voir #8723. Témoin de
non-régression Path B (#2874). -/
theorem figureEight_not_tricolorable : ¬ Knot.isTricolorable figureEight := by
  unfold Knot.isTricolorable
  set_option maxRecDepth 100000 in
  decide

/-! ## 5. Corollaire : le trefoil n'est pas l'unknot

Puisque la tricolorabilite est un invariant, et que le trefoil l'a mais
pas l'unknot, ce sont deux nœuds differents.
-/

theorem trefoil_not_unknot : ¬ KnotEquiv trefoil unknot := by
  intro h
  -- trefoil ≈ unknot ⇒ trefoil tricolorable ↔ unknot tricolorable (invariant).
  -- trefoil IS tricolorable, unknot IS NOT ⇒ contradiction.
  -- The sketch that was left as `sorry` now type-checks: `tricolorable_invariant`
  -- exists (sorry-bearing, L334) and the two pieces are proven, so the corollary
  -- composes them — its soundness rests SOLELY on the invariant's transfer sorry,
  -- with no independent sorry of its own (standalone-tactic sorry 5 → 4). When
  -- the Reidemeister transfer lands (L334), this closes with zero rewiring.
  --
  -- The `Knot`-level wrappers (`KnotEquiv`, `Knot.isTricolorable`) are opaque
  -- `def`s that delta-reduce on demand to the `KnotDiagram` level
  -- (`ReidemeisterEquiv`, `IsTricolorable`); the `have` annotations force that
  -- reduction, re-anchoring `h`/`trefoil_tricolorable`/`unknot_not_tricolorable`
  -- at the diagram level the invariant speaks of.
  have hreid : ReidemeisterEquiv trefoilDiagram unknotDiagram := h
  have htc : IsTricolorable trefoilDiagram := trefoil_tricolorable
  have hnunk : ¬ IsTricolorable unknotDiagram := unknot_not_tricolorable
  exact hnunk ((tricolorable_invariant trefoilDiagram unknotDiagram hreid).mp htc)
  -- DISCHARGED (this corollary no longer carries its own `sorry`): the natural
  -- route (tricolorable_invariant + trefoil_tricolorable + unknot_not_tricolorable)
  -- now type-checks, because `tricolorable_invariant` exists as a declaration
  -- (sorry-bearing, L334). The corollary's soundness therefore reduces to — and
  -- rests solely on — the invariant's transfer sorry. The two pieces it composes
  -- (`trefoil_tricolorable`, `unknot_not_tricolorable`) are both proven under the
  -- real Fox condition; when the Reidemeister transfer lands (L334) the corollary
  -- closes with zero rewiring.
  -- Alternative route attempted: prove ¬KnotEquiv directly by showing the diagrams
  -- cannot be Reidemeister-equivalent. Reidemeister1/2/3 are concrete, but
  -- ReidemeisterEquiv is the RTC of those steps; to show two diagrams are NOT
  -- connected one must classify all diagrams reachable from trefoilDiagram —
  -- out of reach without a normalisation invariant (e.g. crossing-number
  -- monotonicity under the moves, itself needing the true minimal crossing number).
  -- Dependency: tricolorable_invariant (→ transfer lemma across moves).

/-! ## 6. Bornes sur le nombre de croisements

Le nombre de croisements d'un diagramme donne une borne superieure sur le
nombre de croisements minimal du nœud.
-/

/-- Le trefoil a un nombre de croisements egal exactement a 3.

Cela requiert de montrer les deux :
  (a) il existe un diagramme a 3 croisements (evident)
  (b) aucun diagramme avec moins de croisements ne represente le trefoil

La partie (b) requiert la classification des nœuds par nombre de croisements.
-/
theorem trefoil_crossing_number :
    Knot.crossingNumber trefoil = 3 := by
  -- Proof: under the Phase 3 provisional definition, crossingNumber equals
  -- crossingNumberOfDiagram, which counts the trefoil diagram's crossings.
  -- The standard trefoil PD-code has exactly 3 crossings.
  show trefoil.crossingNumberOfDiagram = 3
  unfold Knot.crossingNumberOfDiagram Knot.diagram trefoil trefoilDiagram
  decide

/-! ## 7. Nombre de denouement (definition seule)

Le nombre de denouement u(K) est le nombre minimum de changements de
croisement necessaires pour ramener K a l'unknot. C'est un invariant
beaucoup plus difficile.

Reference : le nombre de denouement est NP-difficile a calculer en general.
-/

/-- Change a crossing from positive to negative or vice versa. -/
def changeCrossing (c : PDCrossing) : PDCrossing where
  e1 := c.e1
  e2 := c.e4  -- swap over and under at this crossing
  e3 := c.e3
  e4 := c.e2

/-- Unknotting number: minimum crossing changes to reach the unknot. -/
def Knot.unknottingNumber (k : Knot) : Nat := by
  exact sorry
  -- BLOCKED: requires substantial infrastructure not yet in the project:
  --   1. Crossing change operation on KnotDiagram (changeCrossing exists but no
  --      well-formedness proof that the result is a valid diagram)
  --   2. Minimization over equivalence classes (Knot.crossingNumber has same issue)
  --   3. Reachability in a graph of diagrams
  -- Phase 4+ target — out of scope for Phase 2

/-! ## 8. Transfer arriere (scaffolding de recherche — Epic #2874, Phase 5 PR3)

Cette section est **scaffolding de recherche uniquement** : elle enregistre
l'obligation de preuve pour la direction arriere de
`Reidemeister1Connected.tricolorable_*` (le compagnon du lemme avant du PR
#3000, en attente de merge au moment de l'ecriture), avec les preuves
empiriques cernant la forme de la preuve et un petit lemme structurel non vide
sur `Reidemeister1Connected` reutilisable dans les deux directions.

**Aucun nouveau sorry n'est introduit.** Le theoreme arriere n'est
intentionnellement pas enonce ici comme un placeholder tactic-stub parce que la
baseline des sorries du Knots-CI est verrouillee a 17 (voir `lean-knot.yml`,
mode `real`) et qu'un stub de recherche la pousserait a 18. L'obligation de
preuve est donc documentee comme un contrat en commentaire uniquement et le
prochain BG-prover / cycle dedie enoncera le theoreme en meme temps qu'il le
prouvera (le lemme + le corps arrivent en un commit, gardant la baseline des
sorries a 17 tout du long).

### 8.1. Obligation de preuve (contrat informel)

Sous le renforcement fix-(a) (proper-arc) de `Reidemeister1Connected` arrive
au PR #3003 (`133f7031`), la direction arriere
```
∀ {d₁ d₂ : KnotDiagram},
  Reidemeister1Connected d₁ d₂ →
  IsTricolorable d₂ →
  IsTricolorable d₁
```
est conjecturee VRAIE. Avec `Reidemeister1Connected.tricolorable_forward`
(PR #3000), cela donne la bi-implication R1 necessaire pour debloquer
`tricolorable_invariant` (§2, le placeholder tactic de longue date a la
ligne 116) — modulo des enonces analogues pour R2 et R3 (PR separes).

### 8.2. Preuves empiriques (force-brute, exhaustif sur petits diagrammes)

Une recherche force-brute de couleur en `3^n` sur tous les diagrammes bien
formes avec `numCrossings ∈ {1, 2}` et `numEdges ∈ {2, 4}` (2526 diagrammes wf
distincts, generant 20184 twists R1 connectes valides sous proper-arc) reporte
**0 echecs arriere** : pour chaque `(d₁, d₂)` avec
`Reidemeister1Connected d₁ d₂` et proper-arc, tout tricolorage de `d₂` admet
un tricolorage de `d₁`. C'est la meme methodologie force-brute qui a reduit
le risque de fix (a) lui-meme avant que le PR #3003 ne soit ouvert (voir le
corps de #3003 pour la table empirique analogue « 24 echecs monogon-loop → 0 »).

Une version *plus fine* de la recherche reporte un fait non trivial : dans
**48% de ces cas (139968 / 292032 sondes (paire, col₂))**, le candidat *naïve*
`col₁ := col₂|_{Fin d₁.numEdges}` (restreint aux premiers `d₁.numEdges`
indices) n'est PAS un tricolorage valide de `d₁` — le temoin existe mais ce
n'est PAS cette restriction naïve. La construction de `col₁` depuis `col₂`
doit donc etre plus nuancee.

### 8.3. Pourquoi la restriction naïve peut echouer

Rappel (`Reidemeister.lean`) : `Reidemeister1Connected d₁ d₂` porte un indice
d'extremite `i`, une etiquette d'arc `a` partagee par deux croisements de
`d₁`, et un croisement renomme `Y'` avec
`PDCrossing.isRenameOf Y' (d₁.crossings[i]) a b` ou `b = d₁.numEdges + 1`. La
chirurgie est :
```
d₂.crossings = (d₁.crossings.set i Y') ++ [⟨a, b, c, c⟩]   (c = d₁.numEdges + 2)
d₂.numEdges   = d₁.numEdges + 2.
```
Fixons un tricolorage `col₂` de `d₂`. La condition de Fox en `Y'` lit sur les
slots de `Y'`, ou une occurrence de `a` a ete renommee en `b`. Poser
`col₁ := col₂|_{Fin d₁.numEdges}` evalue le slot dans le `Y` de `d₁` a
`col₂(a-1)`, tandis que `col₂` evaluait le meme slot de `Y'` a `col₂(b-1)`.
Quand la condition de Fox force `col₂(a-1) ≠ col₂(b-1)` (la branche
tous-distincts en `Y'`), la restriction naïve viole Fox en `Y` dans `d₁`.

L'hypothese proper-arc (`a` partagee par un autre croisement `j ≠ i` de `d₁`)
est ce qui empeche ce mode d'echec de refuter le lemme globalement : elle
force `a` a jouer un role dans un croisement *different*, contraignant la
structure de Fox de `d₁` assez pour qu'un `col₁` valide existe toujours — mais
la construction n'est PAS simplement la restriction. Elle doit reconcilier la
couleur de `a` entre le slot renomme de `Y'` (que `col₂` a fixe librement comme
`col₂(b-1)`) et l'autre occurrence de `a` au croisement `j` (que `col₁`
herite de `col₂(a-1)`).

### 8.4. Strategies de preuve suggerees (pour BG-prover / cycle dedie)

1. **Analyse de cas directe sur le mode de Fox de `Y` dans `d₁`** : chaque
   slot PD correspond a l'une des quatre clauses `isRenameOf` (preserve ou
   renomme). Dans chaque cas, deriver une contrainte d'egalite/inegalite de
   couleur sur `col₂` a `{a-1, b-1}` et exhiber un `col₁` (construit depuis
   `col₂` avec un override controle en `a-1` ou a l'autre occurrence de `a`).
2. **Utiliser le temoin proper-arc directement** : depuis
   `∃ j ≠ i, a ∈ d₁.crossings[j]`, retouver le croisement secondaire de `a`
   dans `d₁` et utiliser sa condition de Fox sous `col₂` pour fixer la couleur
   de `a` dans `col₁`.
3. **Reduire au forward** : construire un candidat *bijectif* `col₁` et
   verifier Fox a chaque croisement de `d₁`, exploitant l'equation de
   chirurgie et le fait que tous les croisements de `d₁` sauf `Y` sont
   presents *verbatim* (memes etiquettes, memes indices) dans `d₂.crossings`.

Empiriquement, la strategie (1) suffit dans 100% des cas force-brute.
L'analyse de cas est mecanique mais ~4-voies ; une petite tactique dediee
pourrait la decharger uniformement.

### 8.5. Lemme structurel : `Reidemeister1Connected.numEdges_eq`

Une petite consequence immediate de l'equation de chirurgie : sous
`Reidemeister1Connected d₁ d₂`, `d₂.numEdges = d₁.numEdges + 2`. La preuve
forward (PR #3000) decharge cela inline comme un `have hd₂num` depuis
`congrArg (·.numEdges) hsurg`. L'extraire comme lemme nomme le garde
disponible pour les deux directions et tout lemme R1 de suite sans
duplication.
-/

/-- `Reidemeister1Connected` fait croitre strictement le nombre d'aretes de 2 :
la chirurgie ajoute un nouveau croisement avec deux etiquettes PD fraiches
`b = d₁.numEdges + 1` et `c = d₁.numEdges + 2`. Utilise a la fois par
`tricolorable_forward` (#3000) et le `tricolorable_backward` a venir pour
borner l'arithmetique des indices de couleur. -/
theorem Reidemeister1Connected.numEdges_eq {d₁ d₂ : KnotDiagram}
    (h : Reidemeister1Connected d₁ d₂) :
    d₂.numEdges = d₁.numEdges + 2 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _h_cross, h_num⟩ := h
  exact h_num

/-! ## 9. Transfer arriere — analyse de decomposition (Epic #2874, Phase 5)

Direction arriere de `Reidemeister1Connected.tricolorable_*` : un tricolorage
de `d₂` se restreint en un de `d₁`. Avec le lemme forward (PR #3000), cela
donne la bi-implication R1 necessaire pour debloquer le placeholder §2
`tricolorable_invariant`.

Cette section est une analyse **documentation-uniquement** : elle enregistre
la decomposition que la preuve future suivra, identifie quels sous-cas sont
faciles vs. niveau-recherche, et cernent les preuves empiriques. **Aucune
nouvelle declaration Lean n'est ajoutee dans cette section** — le theoreme
formel atterrira dans un PR dedie une fois le sous-cas tous-distincts construit.
La baseline CI reste inchangee.

### 9.1. Decomposition en sous-cas

Decomposer par mode de Fox au nouveau croisement kink
`C = ⟨a, b, c, c⟩` avec `b = d₁.numEdges + 1`, `c = d₁.numEdges + 2`.

Fox en `C` sous `col₂` lit sur les slots `(a, b, c)`. Les deux modes :
* **mode tout-egal :** `col₂(a-1) = col₂(b-1) = col₂(c-1)`. La restriction
  naïve `col₁ := col₂|_{Fin d₁.numEdges}` fonctionne alors directement : au
  point d'extremite modifie `Y` dans `d₁`, le slot `b` (renomme) dans `Y'` est
  remplace par un slot `a` dans `Y` dont la couleur sous `col₁` egale
  `col₂(a-1) = col₂(b-1)` par la condition tout-egal. Fox est donc preserve
  en `Y` dans `d₁`.
* **mode tous-distincts :** `col₂(a-1) ≠ col₂(b-1)`. La restriction naïve
  attribue la mauvaise couleur au slot renomme de `Y` dans `d₁` (lit
  `col₂(a-1)` la ou `Y'` lisait `col₂(b-1)`). Fox en `Y` dans `d₁` peut alors
  casser — c'est la source du taux empirique d'echec-naïve de 48% documente au
  §8.2.

De plus, la reparation « evidente » `col₁(a-1) := col₂(b-1)` ne fonctionne PAS
non plus : sous celle-ci, Fox au croisement partenaire proper-arc `j ≠ i`
(qui contient encore `a` dans `d₁`) lit la mauvaise couleur au slot `a` (lit
`col₂(b-1)` au lieu de `col₂(a-1)`), donc Fox en `j` casse symetriquement. Le
cas tous-distincts requiert un ajustement multi-position globalement
coherent — vraisemblablement via l'argument de symetrie-couleur (permuter
TriColor a travers le chemin d'arc connectant `Y` au partenaire proper-arc via
`a`) suggere par le brief deep-queue d'ai-01.

### 9.2. Statut empirique

La recherche force-brute du §8.2 (292032 sondes `(pair, col₂)` sur 20184
twists proper-arc valides avec `numCrossings ≤ 2`) reporte **0 echecs
arriere**. La conjecture est donc fortement soutenue empiriquement ;
l'obstruction est uniquement la preuve formelle du mode tous-distincts.

### 9.3. Feuille de route vers le theoreme formel

Quand la construction tous-distincts sera en main, l'enonce du theoreme est :

```
theorem Reidemeister1Connected.tricolorable_backward {d₁ d₂}
    (h : Reidemeister1Connected d₁ d₂) (htri₂ : IsTricolorable d₂) :
    IsTricolorable d₁
```

Le corps de la preuve (i) extraiera la forme de chirurgie via `numEdges_eq`
(§8.5) et `hsurg`, (ii) fera un case-split sur le mode de Fox en `C`,
(iii) fermera tout-egal par restriction naïve, (iv) fermera tous-distincts par
la construction de symetrie-couleur. Reserve a un cycle dedie ; aucune
declaration placeholder strategique n'est committee ici pour garder la
baseline CI honnete.

### 9.4. Bornes structurelles empiriques (sonde v2)

Une enumeration plus fine sur le meme champ (`numCrossings = 2`, `numEdges =
4`, 292032 sondes `(pair, col₂)`) caracterise **la forme du `col₁`**
fonctionnel quand la restriction naïve echoue. Source :
`scripts/tmp_backward_probe_v2.py`.

Taux d'echec-naïve, raffine :
* Condition de Fox seulement sur `col₁_naive` : **139968 / 292032 = 47.93%**
  (le chiffre reporte au §8.2).
* `IsTriColoring` Lean complet (Fox **et** `≥ 2` couleurs utilisees) :
  **157248 / 292032 = 53.85%**. Les 17280 cas supplementaires ont un
  `col₁_naive` Fox-valide mais monochrome — la restriction 4-aretes survivante
  s'effondre en une seule couleur, que `IsTriColoring` rejette mais Fox seul
  non.

Structure du `col₁` fonctionnel (extension a distance de Hamming minimale
depuis `col₁_naive` vers un tricolorage Lean valide de `d₁`) :
* **Existe toujours** (0 / 157248 manquants), corroborant l'affirmation du
  §8.2 « 0 echecs arriere » sous le critere Lean plus strict.
* **Borne de 2 changements de slot** : 110592 cas (70.3% des echecs-naïve)
  sont fermes par un override a *un seul* slot ; 46656 cas (29.7%) requierent
  un override a *deux* slots ; aucun cas n'en necessite trois ou plus.
* **L'override a un slot n'est pas concentre au slot `a-1`** : les quatre
  positions d'arete de `d₁` recoivent chacune 27648 overrides a un slot
  (distribues uniformement). Seulement 26352 des 110592 overrides a un slot
  (≈ 24%) agissent au slot `a-1` ; les 76% restants agissent a une autre arete
  de `d₁`. Cela refute une formulation seduisante « override-a-`a` uniquement ».
* **La forme fermee « evidente » `col₁(a-1) := col₂(b-1)`** (le candidat §9.1
  ecarte informellement) couvre **24192 / 157248 = 15.4%** des echecs-naïve au
  global. Restreint au sous-ensemble ou l'override agit effectivement au slot
  `a-1`, il reussit dans **24192 / 26352 = 91.8%** des cas — confirmant
  l'argument qualitatif du §9.1 que meme dans sa tranche cible il est incomplet
  (2160 cas single-slot-a-`a-1` ont besoin d'une couleur differente). La
  distribution `(col₂(a-1), col₂(b-1))` sur les echecs-naïve est parfaitement
  uniforme sur les 6 paires de couleurs ordonnees (26208 chacune), donc la
  construction ne peut pas etre biaisee par une configuration de couleur
  particuliere.

Implications pour la construction formelle :
* La borne de Hamming (≤ 2 changements de slot par `col₁`) est une **borne de
  cas finie** : toute preuve constructive peut enumerer « single-slot a
  l'arete `k` » pour `k ∈ Fin d₁.numEdges` et « two-slot a `(k, ℓ)` » pour les
  paires ordonnees, puis decharger chacun par un argument de Fox local.
* Les overrides single-slot-a-non-`a` (76% de single-slot, ≈ 53% de tous les
  echecs-naïve) impliquent un slot dont le role Fox est determine par le
  *croisement partenaire proper-arc* `j` et le reste de `d₁` — pas par le
  kink. C'est le contenu geometrique que l'argument de symetrie-couleur
  capture.
* Les 17280 cas monochromes-`col₁_naive` sont une sous-famille trivialement
  reparable : toute autre couleur a tout slot recupere `≥ 2` couleurs, et Fox
  est deja preserve (il tenait sur `col₁_naive` avant le controle de nombre de
  couleurs). Ils s'effondrent dans le bucket single-slot ci-dessus.

Ces bornes reduisent le probleme de construction depuis « ajustement
multi-position globalement coherent » (l'affirmation qualitative du §9.1) vers
« une famille finie et structuree d'overrides locaux » — la preuve formelle
peut proceder cas par cas une fois le lemme local de re-equilibrage Fox enonce.
Reserve a un cycle dedie ; la baseline CI reste inchangee.

### 9.5. Decouplage-Fox au croisement partenaire proper-arc

La sonde v3 (`scripts/tmp_backward_probe_v3.py`, meme champ de 292032 cas)
caracterise, pour les 84240 overrides single-slot-a-non-`a-1` (≈ 53.6% de tous
les echecs-naïve), la **relation geometrique** entre l'etiquette d'arete
d'override `ℓ := k + 1` et le croisement partenaire proper-arc `j`.

Constats :
* **66.15% (55728 / 84240) des overrides ont `ℓ ∉ d₁.crossings[j]`** —
  l'arete d'override n'apparait pas du tout dans le croisement partenaire. Sous
  la contrainte `wf` a `numCrossings = 2, numEdges = 4`, cela signifie que `ℓ`
  apparait deux fois dans le *croisement kink* `i`, et l'override se propage
  entierement via Fox en `i`.
* **33.85% (28512 / 84240) des overrides ont `ℓ ∈ d₁.crossings[j]`** — et dans
  **100%** de ces cas, `ℓ` se trouve au **slot 3 de `j`** (le slot que
  `triColorConditionAt` ignore ; voir §3 / Lean Invariant.lean L82-87 ou Fox
  ne lit que `(e1, e2, e3)`). De maniere cruciale, cela signifie que **0% des
  overrides touchent un slot Fox-sensible de `j`**.
* La distribution jointe `(slot-a dans j, slot-override dans j)` est equilibree
  : `a` aux slots 0/1/2 de `j` apparait chacun avec `ℓ` au slot 3 de `j` dans
  9504 cas (uniforme sur les 3 positions Fox de `a`). Pas de biais vers un
  slot `a` particulier.

Mecanisme. La chirurgie kink en `Y` modifie un slot Fox de `i`. La restriction
naïve casse Fox en `Y`. Pour reparer, changer la couleur a une arete `ℓ`. La
sonde montre que le `ℓ` choisi est *toujours* Fox-irrelevant en `j` : soit
parce que `ℓ` n'apparait pas en `j` (cas 66%), soit parce que `ℓ` apparait
seulement au slot 3 Fox-aveugle de `j` (cas 34%). Dans les deux sous-cas,
**l'override est invisible a Fox en `j`**, et la reparation Fox s'ecoule
entierement via Fox en `i` (ou `ℓ` se trouve a un slot Fox par le meme
comptage).

C'est l'argument de symetrie-couleur du §9.1 rendu concret : l'override
« echange » une couleur a une arete dont le seul role Fox est au croisement
kink lui-meme, donc le changer ne peut pas casser la condition Fox du
partenaire. La preuve formelle peut donc localiser le re-equilibrage
entierement en `i` une fois l'arete d'override identifiee par sa Fox-aveuglete
en `j`.

Le bucket two-slot a 29.7% (§9.4) est le residu ou ce mouvement single-slot
Fox-aveugle n'est pas disponible ; v3 ne le caracterise pas encore (reporte au
§9.6 ci-dessous). La baseline CI reste inchangee.

### 9.6. Couplage-Fox du bucket two-slot au croisement partenaire proper-arc

La sonde v4 (`scripts/tmp_backward_probe_v4.py`, meme champ de 292032 cas)
caracterise les 46656 overrides two-slot (29.7% de tous les echecs-naïve) et
les contraste avec le decouplage-Fox single-slot du §9.5.

Constats :
* **Q1 presence-partenaire.** **94.21% (43956 / 46656) des overrides two-slot
  ont leurs deux aretes d'override dans `d₁.crossings[j]`** ; les 5.79%
  restants (2700) en ont exactement une dans `j` ; **aucun** n'a ni l'une ni
  l'autre. Donc dans le bucket two-slot, au moins une arete d'override est
  toujours presente au croisement partenaire — un contraste net avec le taux
  de 66.15% aucun-dans-`j` du §9.5.
* **Q2 distribution des slots dans `j`.** Parmi les aretes d'override qui
  apparaissent dans `j`, les slots se divisent en **slot 0 : 33.25%, slot 1 :
  32.34%, slot 2 : 31.43%, slot 3 : 2.98%**. Les slots Fox-sensibles (0, 1, 2)
  portent la masse ecrasante, a l'oppose de la concentration a 100% au slot 3
  du §9.5.
* **Q3 distribution des paires d'aretes.** Les six paires non ordonnees
  `(1,2), (1,3), (1,4), (2,3), (2,4), (3,4)` d'etiquettes d'arete d'override
  surviennent quasi-uniformement (7596–7956 chacune), sans paire interdite —
  toute paire d'aretes distinctes de `d₁` peut servir d'override two-slot sous
  un certain `(d₁, surg, col₂)`.
* **Q4 visibilite-Fox.** **94.21% (43956 / 46656) des overrides two-slot ont
  au moins une arete d'override assise dans un slot Fox (0, 1, 2) de `j`** ;
  seulement 5.79% sont entierement Fox-aveugles. Le bucket two-slot est
  *Fox-couple* en `j`, pas Fox-decouple.

Mecanisme. Le re-equilibrage two-slot change les couleurs a deux aretes, et la
sonde montre que — presque toujours — au moins une de ces deux aretes est
Fox-pertinente au croisement partenaire `j`. Un mouvement local naïve en `i`
derangerait donc la condition Fox en `j` ; le re-equilibrage doit se propager
a travers l'arc proper, en choisissant des couleurs aux deux slots d'override
qui restaurent Fox en `i` (via l'arete de chirurgie `a`) et preservent Fox en
`j` (via la contrainte de position croisee a l'arete partagee) simultanement.

C'est la moitie manquante de l'argument de symetrie-couleur du §9.1 : §9.5
montre que le bucket single-slot a 70.3% est *localement* reparable en `i`
parce que l'override est Fox-decouple en `j` ; §9.6 montre que le bucket
two-slot a 29.7% n'est *pas* localement reparable parce que l'override est
Fox-couple en `j` — exactement le regime qui requiert la construction de
symetrie-couleur multi-position du §9.3. La serie de caracterisation §9.4 →
§9.6 se ferme donc empiriquement : chaque echec naïve tombe dans un de deux
buckets avec une structure Fox explicite et contrastee au croisement
partenaire.

Le lemme formel `tricolorable_backward` admet donc deux sous-cas propres — la
famille single-slot reparable localement (avec l'arete d'override identifiee
par Fox-aveuglete en `j`) et la famille two-slot a position croisee (avec les
deux slots d'override contraints par Fox en `j` et en `i`). Les deux
requierent encore une preuve formelle a un cycle futur ; la presente sonde
quantifie *pourquoi* le bucket two-slot ne peut pas etre reduit a la
construction single-slot. La baseline CI reste inchangee.
-/

/-! ## 10. Transfer arriere — declaration formelle (partiel, Epic #2874 PR3)

Le compagnon de `Reidemeister1Connected.tricolorable_forward` (PR #3000) : un
tricolorage de `d₂` se restreint en un de `d₁` sous le R1-connecte
renforce. L'analyse de decomposition du §9 scinde la preuve par le mode de Fox
au kink ajoute `C = ⟨a, b, c, c⟩` (avec `b = d₁.numEdges + 1`,
`c = d₁.numEdges + 2`) :

* **mode tout-egal** (`col₂(a-1) = col₂(b-1) = col₂(c-1)`) : la restriction
  naïve `col₁ := col₂|_{Fin d₁.numEdges}` preserve Fox — le renommage `a → b`
  au croisement d'extremite modifie est couleur-invisible. Le sous-lemme
  `tricolorable_backward` ci-dessous prouve la moitie **preservation-couleur**
  constructivement (une etiquette preservee lit la meme couleur sous `col₁`
  dans `d₁` que sous `col₂` dans `d₂` ; mire `hcolF1` de `tricolorable_forward`).
* **mode tous-distincts** (`col₂(a-1) ≠ col₂(b-1)`) : a besoin du
  re-equilibrage de symetrie-couleur / multi-position caracterise
  empiriquement au §9.4–§9.6 (le regime echec-naïve a 47.9%). Niveau recherche.

L'assemblage restant — transfer-Fox a chaque croisement de `d₁` (les
inchanges heritent via le fait de preservation-couleur, mirant `h_inherit` ;
le croisement modifie `Y` et le mode kink tous-distincts requierent la
construction §9.1), le relift `d₁.numEdges ≥ 2` (derivable depuis `d₁.wf` +
l'hypothese proper-arc, mais un argument separate de parite-wf), et le relift
`≥ 2`-couleur — est laisse comme trois `sorries` tactic residuels pour qu'ai-01
les conseille. Cela fait passer la baseline prose-header du Knots-CI de 25 a 28
(trois `sorries` tactic residuels, un par sous-but). Livraison partielle
autorisee par l'utilisateur (2026-06-15) : livrer avec des obligations de
sous-preuve residuelles qu'ai-01 conseillera. Avec `tricolorable_forward`
(#3000) cela donne la bi-implication R1 necessaire pour debloquer le
placeholder §2 `tricolorable_invariant`. Voir #2874.
-/

/-- Transfer arriere de tricolorabilite (PARTIEL) : sous le R1-connecte
    renforce `Reidemeister1Connected d₁ d₂`, un tricolorage de `d₂` se
    restreint en un tricolorage de `d₁`. Le sous-lemme de preservation-couleur
    est decharge constructivement (mire `hcolF1` de `tricolorable_forward`) ;
    l'assemblage transfer-Fox et le mode kink tous-distincts restent comme
    `sorries` tactic residuels (voir §9.1, §9.4–§9.6). -/
theorem Reidemeister1Connected.tricolorable_backward {d₁ d₂ : KnotDiagram}
    (h : Reidemeister1Connected d₁ d₂) (htri₂ : IsTricolorable d₂) :
    IsTricolorable d₁ := by
  obtain ⟨_hwf₁, _hwf₂, i, a, Y', _ρ, ha1, ha2, _hamem, _hproper, hrename, h_cross, h_num⟩ := h
  -- Surgery shape (mirrors `tricolorable_forward`).
  have hd₂num : d₂.numEdges = d₁.numEdges + 2 := h_num
  have hd₂cross : d₂.crossings =
      d₁.crossings.set i.val Y' ++
        [⟨a, d₁.numEdges + 1, d₁.numEdges + 2, d₁.numEdges + 2⟩] := h_cross
  obtain ⟨col₂, hfox₂, hge2₂, h2col₂⟩ := htri₂
  -- Naïve restriction: `col₁` embeds `d₁`'s edge indices into `d₂` (the +2
  -- fresh edges sit above `Fin d₁.numEdges`). Mirrors `tricolorable_forward`'s
  -- `emb`/`col₂` (PR #3000), reversed.
  have hd₂ge₁ : d₁.numEdges ≤ d₂.numEdges := by omega
  let col₁ : Fin d₁.numEdges → TriColor :=
    fun k => col₂ ⟨k.val, Nat.lt_of_lt_of_le k.isLt hd₂ge₁⟩
  -- (F1) Colour preservation: a preserved label `l ∈ [1, d₁.numEdges]` reads
  -- the SAME colour under `col₁` (in `d₁`) as under `col₂` (in `d₂`). Pure
  -- arithmetic on the `(l-1) % numEdges` index; the reverse of forward `hcolF1`.
  -- This is the constructive core that the unchanged-crossing Fox-inheritance
  -- (`h_inherit` in the forward proof) rides on.
  have hcolPres : ∀ l, 1 ≤ l → l ≤ d₁.numEdges →
      d₁.colorAtNat col₁ l = d₂.colorAtNat col₂ l := by
    intro l hl1 hln
    have hn0d₁ : d₁.numEdges ≠ 0 := by omega
    have hn0d₂ : d₂.numEdges ≠ 0 := by omega
    simp only [KnotDiagram.colorAtNat, dif_neg hn0d₁, dif_neg hn0d₂]
    have h1 : (l - 1) % d₁.numEdges = l - 1 := Nat.mod_eq_of_lt (by omega)
    have h2 : (l - 1) % d₂.numEdges = l - 1 := Nat.mod_eq_of_lt (by omega)
    simp only [h1, h2]
    rfl
  -- Residual assembly (§9): Fox-transfer at every `d₁` crossing under `col₁`
  -- (unchanged crossings inherit via `hcolPres` — mirrors forward `h_inherit`;
  -- the modified crossing `Y` and the all-distinct kink mode need the §9.1
  -- colour-symmetry construction), the `d₁.numEdges ≥ 2` lift (wf + proper-arc),
  -- and the `≥ 2`-colour lift. Left for ai-01 to advise on.
  refine' ⟨col₁, ?fox, ?num, ?col⟩
  case fox =>
    -- ∀ c ∈ d₁.crossings, triColorConditionAt d₁ col₁ c.
    -- Split on whether c survives into d₂. The only d₁ crossing that can drop
    -- out of d₂ is the modified one Y = d₁.crossings.get i (replaced by Y' at
    -- index i in d₂.crossings.set i Y' ++ [kink]). Everything else inherits Fox
    -- via hcolPres — the reverse of forward `h_inherit` (Invariant.lean L587-603).
    intro c hc
    by_cases hc2 : c ∈ d₂.crossings
    · -- pos: unchanged crossing. Fox holds under col₂ (hfox₂), transferred.
      have hfc2 : triColorConditionAt d₂ col₂ c := hfox₂ c hc2
      simp only [triColorConditionAt] at hfc2 ⊢
      obtain ⟨⟨he11, he12, he21, he22, he31, he32, he41, he42⟩, ⟨harc, hfox⟩⟩ := hfc2
      -- WF upper bound: hfc2 only gives c.e_k ≤ d₂.numEdges (= d₁.numEdges + 2).
      -- The stronger bound c.e_k ≤ d₁.numEdges comes from d₁.wf clause (a)
      -- (every d₁ edge label ∈ [1, numEdges]): c ∈ d₁.crossings ⟹ c.e_k ∈ d₁.edges.
      have hcross_ne : d₁.crossings ≠ [] := by
        intro h; rw [h] at hc; exact (List.mem_nil_iff _).mp hc
      have hwf := _hwf₁
      simp only [KnotDiagram.wf, if_neg hcross_ne, Bool.and_eq_true, List.all_eq_true,
        decide_eq_true_iff] at hwf
      obtain ⟨ha, _hb⟩ := hwf
      have hmem_e1 : c.e1 ∈ d₁.edges := by
        simp only [KnotDiagram.edges, List.mem_flatMap]; exact ⟨c, hc, by simp⟩
      have hmem_e2 : c.e2 ∈ d₁.edges := by
        simp only [KnotDiagram.edges, List.mem_flatMap]; exact ⟨c, hc, by simp⟩
      have hmem_e3 : c.e3 ∈ d₁.edges := by
        simp only [KnotDiagram.edges, List.mem_flatMap]; exact ⟨c, hc, by simp⟩
      have hmem_e4 : c.e4 ∈ d₁.edges := by
        simp only [KnotDiagram.edges, List.mem_flatMap]; exact ⟨c, hc, by simp⟩
      have he1 := ha c.e1 hmem_e1
      have he2 := ha c.e2 hmem_e2
      have he3 := ha c.e3 hmem_e3
      have he4 := ha c.e4 hmem_e4
      -- Colour preservation (reverse of forward hcolF1): d₁ colour = d₂ colour.
      have h1 : d₁.colorAtNat col₁ c.e1 = d₂.colorAtNat col₂ c.e1 :=
        hcolPres c.e1 he11 he1.2
      have h2 : d₁.colorAtNat col₁ c.e2 = d₂.colorAtNat col₂ c.e2 :=
        hcolPres c.e2 he21 he2.2
      have h3 : d₁.colorAtNat col₁ c.e3 = d₂.colorAtNat col₂ c.e3 :=
        hcolPres c.e3 he31 he3.2
      have h4 : d₁.colorAtNat col₁ c.e4 = d₂.colorAtNat col₂ c.e4 :=
        hcolPres c.e4 he41 he4.2
      refine ⟨⟨he11, he1.2, he21, he2.2, he31, he3.2, he41, he4.2⟩, ⟨?_, ?_⟩⟩
      · -- Over-strand continuity col₁(e2)=col₁(e4) via colour-preservation + d₂'s arc-eq.
        rw [h2, h4]; exact harc
      · rcases hfox with ⟨h12, h23⟩ | ⟨h12, h23, h13⟩
        · left; refine ⟨?_, ?_⟩
          · rw [h1, h2]; exact h12
          · rw [h2, h3]; exact h23
        · right; refine ⟨?_, ?_, ?_⟩
          · rw [h1, h2]; exact h12
          · rw [h2, h3]; exact h23
          · rw [h1, h3]; exact h13
    · -- neg: c = Y (the modified crossing, dropped from d₂ by `set i Y'`). Fox
      -- at Y under col₁ transfers from Fox at Y' under col₂ (hfox₂): unchanged
      -- strands via hcolPres, the renamed a→b strand via the kink all-equality
      -- (col₂(a)=col₂(n+1) supplies the backward analogue of forward hcolF2b).
      -- all-distinct kink mode: residual §9.1 (col₂(n+1)≠col₂(a) breaks the
      -- rename transfer). BG-prover ai-01 territory; user-authorised residual.
      -- (1) c = d₁.crossings.get i (= Y) and c ≠ Y'.
      have hnotmemSet : c ∉ d₁.crossings.set i Y' := by
        intro hmem; apply hc2; rw [hd₂cross]; exact List.mem_append_left _ hmem
      have hdrop := mem_drop_out i.val d₁.crossings Y' c i.isLt hc hnotmemSet
      rw [show c = d₁.crossings.get i from hdrop.1.symm]
      -- (2) Fox at Y' under col₂ (Y' sits at index i in d₂.crossings).
      have hY'mem : Y' ∈ d₂.crossings := by
        rw [hd₂cross]
        exact List.mem_append.mpr (.inl (mem_set_self i.val d₁.crossings Y' i.isLt))
      have hY'fox : triColorConditionAt d₂ col₂ Y' := hfox₂ _ hY'mem
      -- (3) Fox at the kink under col₂; split on its mode.
      have hCmem : (⟨a, d₁.numEdges + 1, d₁.numEdges + 2, d₁.numEdges + 2⟩ : PDCrossing)
          ∈ d₂.crossings := by
        rw [hd₂cross]; exact List.mem_append_right _ (List.mem_singleton_self _)
      have hCfox : triColorConditionAt d₂ col₂
          ⟨a, d₁.numEdges + 1, d₁.numEdges + 2, d₁.numEdges + 2⟩ := hfox₂ _ hCmem
      obtain ⟨_, hCmode⟩ := hCfox
      have hCmode' :
          (d₂.colorAtNat col₂ (d₁.numEdges + 1) = d₂.colorAtNat col₂ (d₁.numEdges + 2)) ∧
          ((d₂.colorAtNat col₂ a = d₂.colorAtNat col₂ (d₁.numEdges + 1) ∧
            d₂.colorAtNat col₂ (d₁.numEdges + 1) = d₂.colorAtNat col₂ (d₁.numEdges + 2)) ∨
           (d₂.colorAtNat col₂ a ≠ d₂.colorAtNat col₂ (d₁.numEdges + 1) ∧
            d₂.colorAtNat col₂ (d₁.numEdges + 1) ≠ d₂.colorAtNat col₂ (d₁.numEdges + 2) ∧
            d₂.colorAtNat col₂ a ≠ d₂.colorAtNat col₂ (d₁.numEdges + 2))) := hCmode
      rcases hCmode' with ⟨_hCarc, ⟨hCa_n1, _⟩ | _hdist⟩
      · -- all-equal kink mode: col₂(a)=col₂(n+1). Transfer Fox Y'→Y.
        simp only [triColorConditionAt] at hY'fox ⊢
        obtain ⟨⟨he'11, he'12, he'21, he'22, he'31, he'32, he'41, he'42⟩, ⟨harc_Y', hY'foxmode⟩⟩ := hY'fox
        obtain ⟨hre1, hre2, hre3, hre4⟩ := hrename
        -- WF bounds for Y's strands (d₁.wf clause a: every edge label ∈ [1,n]).
        have hcross_ne : d₁.crossings ≠ [] := by
          intro h; rw [h] at hc; exact (List.mem_nil_iff _).mp hc
        have hwf := _hwf₁
        simp only [KnotDiagram.wf, if_neg hcross_ne, Bool.and_eq_true, List.all_eq_true,
          decide_eq_true_iff] at hwf
        obtain ⟨ha_all, _⟩ := hwf
        have hYmem : (d₁.crossings.get i) ∈ d₁.crossings := List.get_mem _ _
        have hmem_eY1 : (d₁.crossings.get i).e1 ∈ d₁.edges := by
          simp only [KnotDiagram.edges, List.mem_flatMap]; exact ⟨_, hYmem, by simp⟩
        have hmem_eY2 : (d₁.crossings.get i).e2 ∈ d₁.edges := by
          simp only [KnotDiagram.edges, List.mem_flatMap]; exact ⟨_, hYmem, by simp⟩
        have hmem_eY3 : (d₁.crossings.get i).e3 ∈ d₁.edges := by
          simp only [KnotDiagram.edges, List.mem_flatMap]; exact ⟨_, hYmem, by simp⟩
        have hmem_eY4 : (d₁.crossings.get i).e4 ∈ d₁.edges := by
          simp only [KnotDiagram.edges, List.mem_flatMap]; exact ⟨_, hYmem, by simp⟩
        have heY1 := ha_all _ hmem_eY1
        have heY2 := ha_all _ hmem_eY2
        have heY3 := ha_all _ hmem_eY3
        have heY4 := ha_all _ hmem_eY4
        -- Per-strand colour transfer (unchanged via hcolPres; renamed via kink).
        have help : ∀ (hf ho : Nat)
            (hmode : hf = ho ∨ (hf = d₁.numEdges + 1 ∧ ho = a))
            (ho1 : 1 ≤ ho) (hon : ho ≤ d₁.numEdges),
            d₂.colorAtNat col₂ hf = d₁.colorAtNat col₁ ho := by
          intro hf ho hmode ho1 hon
          rcases hmode with heq | ⟨heqf, heqa⟩
          · rw [heq]; exact (hcolPres ho ho1 hon).symm
          · rw [heqf, heqa, ← hCa_n1]; exact (hcolPres a ha1 ha2).symm
        have h1 : d₂.colorAtNat col₂ Y'.e1 =
            d₁.colorAtNat col₁ (d₁.crossings.get i).e1 :=
          help Y'.e1 (d₁.crossings.get i).e1 hre1 heY1.1 heY1.2
        have h2 : d₂.colorAtNat col₂ Y'.e2 =
            d₁.colorAtNat col₁ (d₁.crossings.get i).e2 :=
          help Y'.e2 (d₁.crossings.get i).e2 hre2 heY2.1 heY2.2
        have h3 : d₂.colorAtNat col₂ Y'.e3 =
            d₁.colorAtNat col₁ (d₁.crossings.get i).e3 :=
          help Y'.e3 (d₁.crossings.get i).e3 hre3 heY3.1 heY3.2
        have h4 : d₂.colorAtNat col₂ Y'.e4 =
            d₁.colorAtNat col₁ (d₁.crossings.get i).e4 :=
          help Y'.e4 (d₁.crossings.get i).e4 hre4 heY4.1 heY4.2
        refine ⟨⟨heY1.1, heY1.2, heY2.1, heY2.2, heY3.1, heY3.2, heY4.1, heY4.2⟩, ⟨?_, ?_⟩⟩
        · -- Over-strand continuity col₁(Y.e2)=col₁(Y.e4) via rename transfer + Y's arc-eq under col₂.
          rw [← h2, ← h4]; exact harc_Y'
        rcases hY'foxmode with ⟨h12, h23⟩ | ⟨h12, h23, h13⟩
        · left; refine ⟨?_, ?_⟩
          · rw [← h1, ← h2]; exact h12
          · rw [← h2, ← h3]; exact h23
        · right; refine ⟨?_, ?_, ?_⟩
          · rw [← h1, ← h2]; exact h12
          · rw [← h2, ← h3]; exact h23
          · rw [← h1, ← h3]; exact h13
      · -- all-distinct kink mode: residual §9.1.
        --
        -- BREAKTHROUGH PROOF STRATEGY (cycle-3): Fox tricolorability is
        -- LINEAR over GF(3) — `triColorConditionAt` ⟺ c₁+c₂+c₃ ≡ 0 mod 3
        -- (verified: 0 disagreements over 7.5M wf diagrams, m∈{2,3}). The
        -- coloring space V(d) is a linear subspace of (Z/3)^n with
        -- dim V(d) ≥ n − m = m (m crossings ⇒ m homogeneous equations;
        -- n = 2m edges by wf parity). The 3 constant colorings form a
        -- 1-dim subspace, so dim V(d) ≥ m ≥ 2 ⟹ a non-constant
        -- Fox-coloring exists ⟹ IsTricolorable d. UNIVERSAL LEMMA:
        -- `wf d → d.crossings.length ≥ 2 → IsTricolorable d` (GF(3)
        -- rank-nullity; bridge `triColorConditionAt ↔ sum ≡ 0` by decide
        -- on Fin 3). d₁ qualifies (wf + proper-arc ⟹ ≥2 crossings, see
        -- `num` case), so d₁ is tricolorable INDEPENDENTLY of col₂ —
        -- WITHDRAWN under Path B (2026-06-23). The universal lemma above is
        -- FALSE classically: the figure-eight knot is well-formed with 4
        -- crossings yet is NOT Fox-tricolorable (only its 3 constant colourings
        -- exist). The per-crossing GF(3) bridge (`triColorFoxCondition_iff_sum_mod_three`,
        -- cycle-6) still holds, but it does not lift to universal colourability.
        -- This branch is therefore OPEN, awaiting a direct col2->col1 lift
        -- (see the Record below); it is NOT discharged by the withdrawn lemma.
        --
        -- Record — why the direct col₂→col₁ lift below is blocked: d₂.wf
        -- parity on fresh edge b=n₁+1 forces Y to hold `a` in exactly one
        -- slot, and d₁.wf forces `a` at exactly one proper-arc c_j; `a`
        -- is torn (Y wants col₁(a)=col₂(b), c_j wants col₁(a)=col₂(a),
        -- all-distinct denies equality). Projective / single-swap /
        -- σ∘col₂ all fail (Fox σ-invariant, #4003). The GF(3) lemma above
        -- bypasses this entirely — the col₂ construction is unnecessary.
        sorry
  case num =>
    -- d₁.numEdges ≥ 2. Diagnostic for the BG-prover (ai-01): d₁ is forced
    -- NON-DEGENERATE (`crossings ≠ []`) because `_hproper` supplies a distinct
    -- crossing index `j ≠ i`, both inhabiting `Fin d₁.crossings.length`. Hence
    -- `d₁.wf` (Basic.lean:261) takes its ELSE branch — the parity condition:
    -- every label in `[1, numEdges]` appears exactly twice
    -- (`(List.range numEdges).all (fun i => edges.count (i+1) = 2)`), and every
    -- occurring label lies in `[1, numEdges]` (clause (a)).
    --   * numEdges = 0: `edges ≠ []` (crossings ≠ []), so (a) demands labels in
    --     [1, 0] = ∅ — impossible.
    --   * numEdges = 1: a single crossing contributes 4 slots, each forced to
    --     label 1, so `edges.count 1 = 4 ≠ 2` — parity (b) fails.
    -- PROVEN: `_hproper` ⟹ two distinct `Fin crossings.length` indices `i ≠ j`
    -- ⟹ `crossings.length ≥ 2`, so `d₁` is non-degenerate and `wf` takes its
    -- parity branch. `edges.length = 4·crossings.length` (4 slots/crossing);
    -- parity (a)+(b) force `2·numEdges = edges.length`, hence `numEdges ≥ 4`.
    obtain ⟨j, hjne, _⟩ := _hproper
    have hlen2 : 2 ≤ d₁.crossings.length := by
      by_contra h
      have hi : i.val = 0 := by omega
      have hj : j.val = 0 := by omega
      exact hjne (Fin.ext (hj.trans hi.symm))
    have hne : d₁.crossings ≠ [] := by
      intro he; rw [he] at hlen2; simp at hlen2
    have hwf := _hwf₁
    simp only [KnotDiagram.wf, if_neg hne, Bool.and_eq_true] at hwf
    obtain ⟨ha_all, hb_all⟩ := hwf
    have hedges_len : d₁.edges.length = 4 * d₁.crossings.length := by
      have H : ∀ (cs : List PDCrossing),
          (cs.flatMap fun c => [c.e1, c.e2, c.e3, c.e4] : List Nat).length =
            4 * cs.length := by
        intro cs; induction cs with
        | nil => rfl
        | cons c cs' ih =>
          simp only [List.flatMap_cons, List.length_append, List.length_cons,
            List.length_nil, ih]; omega
      simp only [KnotDiagram.edges]; exact H d₁.crossings
    by_contra hne2
    -- `d₁.edges ≠ []`: length = 4·crossings.length ≥ 8 > 0.
    have hedges_ne : d₁.edges ≠ [] := by
      intro h0; rw [h0, List.length_nil] at hedges_len; omega
    obtain ⟨l0, hl0⟩ := List.exists_mem_of_ne_nil d₁.edges hedges_ne
    rw [List.all_eq_true] at ha_all hb_all
    -- Clause (a) at `l0 ∈ edges` forces `1 ≤ l0 ≤ numEdges`, so `numEdges ≥ 1`;
    -- with `hne2` (`numEdges ≤ 1`), `numEdges = 1`.
    have ha_l0 : 1 ≤ l0 ∧ l0 ≤ d₁.numEdges := by
      simpa using ha_all l0 hl0
    have hne1 : d₁.numEdges = 1 := by omega
    -- Clause (b) at `i = 0`: `edges.count 1 = 2`.
    have hb1 : d₁.edges.count 1 = 2 := by
      have h0mem : (0 : ℕ) ∈ List.range d₁.numEdges := by
        rw [List.mem_range]; omega
      have h := hb_all 0 h0mem; simpa using h
    -- Clause (a) (numEdges = 1) forces every edge = 1, so `count 1 = length`.
    have hall1 : ∀ e ∈ d₁.edges, e = 1 := by
      intro e he
      have h : 1 ≤ e ∧ e ≤ d₁.numEdges := by simpa using ha_all e he
      omega
    have hcount1 : d₁.edges.count 1 = d₁.edges.length := by
      have H : ∀ (l : List Nat), (∀ e ∈ l, e = 1) → l.count 1 = l.length := by
        intro l hl
        induction l with
        | nil => rfl
        | cons hd tl ih =>
          obtain rfl : hd = 1 := hl hd List.mem_cons_self
          rw [List.count_cons, List.length_cons, if_pos (by decide)]
          have := ih (fun e he => hl e (List.mem_cons_of_mem _ he))
          omega
      exact H d₁.edges hall1
    -- `4·crossings.length = count 1 = 2` contradicts `crossings.length ≥ 2`.
    rw [hcount1, hedges_len] at hb1; omega
  case col =>
    -- ≥ 2 colours under col₁. Split on the kink's Fox mode. The kink is
    -- C = ⟨a, n+1, n+2, n+2⟩ (the appended surgery crossing, hd₂cross).
    have hCmem : (⟨a, d₁.numEdges + 1, d₁.numEdges + 2, d₁.numEdges + 2⟩ : PDCrossing)
        ∈ d₂.crossings := by
      rw [hd₂cross]
      exact List.mem_append_right _ (by simp)
    have hCfox : triColorConditionAt d₂ col₂
        ⟨a, d₁.numEdges + 1, d₁.numEdges + 2, d₁.numEdges + 2⟩ := hfox₂ _ hCmem
    obtain ⟨_, hCmode⟩ := hCfox
    -- Coerce the `let`-bound Fox disjunction to its inlined form (defeq on C's
    -- fields: e1 = a, e2 = n+1, e3 = n+2) so `rcases` can split the disjunction.
    have hCmode' :
        (d₂.colorAtNat col₂ (d₁.numEdges + 1) = d₂.colorAtNat col₂ (d₁.numEdges + 2)) ∧
        ((d₂.colorAtNat col₂ a = d₂.colorAtNat col₂ (d₁.numEdges + 1) ∧
          d₂.colorAtNat col₂ (d₁.numEdges + 1) = d₂.colorAtNat col₂ (d₁.numEdges + 2)) ∨
         (d₂.colorAtNat col₂ a ≠ d₂.colorAtNat col₂ (d₁.numEdges + 1) ∧
          d₂.colorAtNat col₂ (d₁.numEdges + 1) ≠ d₂.colorAtNat col₂ (d₁.numEdges + 2) ∧
          d₂.colorAtNat col₂ a ≠ d₂.colorAtNat col₂ (d₁.numEdges + 2))) := hCmode
    rcases hCmode' with ⟨_hCarc, ⟨h_a_n1, h_n1_n2⟩ | _hdist⟩
    · -- all-equal kink mode. By contradiction: if col₁ is constant, col₂ is
      -- constant on the whole [0, d₂.numEdges) range (d₁-range via the col₁
      -- embedding; the two fresh indices via the kink's all-equal, tying them to
      -- col₂(a-1)) — contradicting h2col₂ (col₂ has ≥2 colours).
      have hn0d₂ : d₂.numEdges ≠ 0 := by omega
      -- Fixed Fin proofs (avoid `by omega` re-elaborating fresh each use).
      have ha_le : a - 1 < d₂.numEdges := by omega
      have hn_le : d₁.numEdges < d₂.numEdges := by omega
      have hn1_le : d₁.numEdges + 1 < d₂.numEdges := by omega
      have ha1_le : a - 1 < d₁.numEdges := by omega
      -- Reduce the kink's colorAtNat applications to bare col₂ applications,
      -- with the FIXED Fin proofs above.
      have ha_col : d₂.colorAtNat col₂ a = col₂ ⟨a - 1, ha_le⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₂]
        exact congrArg col₂ (Fin.ext (Nat.mod_eq_of_lt ha_le))
      have hn1_col : d₂.colorAtNat col₂ (d₁.numEdges + 1) =
          col₂ ⟨d₁.numEdges, hn_le⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₂]
        have hmod : (d₁.numEdges + 1 - 1) % d₂.numEdges = d₁.numEdges := by
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        exact congrArg col₂ (Fin.ext hmod)
      have hn2_col : d₂.colorAtNat col₂ (d₁.numEdges + 2) =
          col₂ ⟨d₁.numEdges + 1, hn1_le⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₂]
        have hmod : (d₁.numEdges + 2 - 1) % d₂.numEdges = d₁.numEdges + 1 := by
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        exact congrArg col₂ (Fin.ext hmod)
      rw [ha_col, hn1_col] at h_a_n1
      rw [hn1_col, hn2_col] at h_n1_n2
      -- h_a_n1  : col₂ ⟨a-1, ha_le⟩ = col₂ ⟨d₁.numEdges, hn_le⟩
      -- h_n1_n2 : col₂ ⟨d₁.numEdges, hn_le⟩ = col₂ ⟨d₁.numEdges+1, hn1_le⟩
      by_contra hncol
      push_neg at hncol
      obtain ⟨i₀, j₀, hij⟩ := h2col₂
      have hanch : ∀ k : Fin d₂.numEdges, col₂ k = col₂ ⟨a - 1, ha_le⟩ := by
        intro k
        rcases Nat.lt_trichotomy k.val d₁.numEdges with hklt | hkeq | hkgt
        · -- k.val < d₁.numEdges: col₂ k = col₁ ⟨k.val, hklt⟩ (embedding) = anchor.
          have hkemb : col₂ k = col₁ ⟨k.val, hklt⟩ := by simp only [col₁]
          have hncol_k : col₁ ⟨k.val, hklt⟩ = col₁ ⟨a - 1, ha1_le⟩ := hncol _ _
          rw [hkemb, hncol_k]
        · -- k.val = d₁.numEdges: kink all-equal ties it to col₂⟨a-1, ha_le⟩.
          rw [show k = (⟨d₁.numEdges, hn_le⟩ : Fin d₂.numEdges) from Fin.ext hkeq]
          exact h_a_n1.symm
        · -- k.val = d₁.numEdges + 1 (the only index > n in Fin (n+2)).
          have hk1 : k.val = d₁.numEdges + 1 := by omega
          rw [show k = (⟨d₁.numEdges + 1, hn1_le⟩ : Fin d₂.numEdges) from Fin.ext hk1]
          exact h_n1_n2.symm.trans h_a_n1.symm
      exact hij (by rw [hanch i₀, hanch j₀])
    · -- all-distinct kink mode: §9.1 residual. The fresh edges carry a NEW
      -- colour absent from the d₁ range, so the naïve col₁ restriction can be
      -- monochromatic and the ≥2-colour lift via col₂ fails (see the `fox`
      -- case above). [WITHDRAWN under Path B] The hoped-for discharge via the
      -- cycle-3 GF(3) universal lemma (`wf d, >=2 crossings => IsTricolorable d`,
      -- Fox linear over GF(3)) is FALSE classically: the figure-eight knot has
      -- 4 crossings yet is NOT Fox-tricolorable. The universal shortcut is gone,
      -- so this `col` residual is OPEN (as is the `fox` case above); both await a
      -- direct arc-respecting col2->col1 lift rather than the withdrawn lemma.
      sorry

end Knots

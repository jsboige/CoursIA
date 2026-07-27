/-
Knots.Reidemeister — Mouvements de Reidemeister et equivalence des noeuds
=======================================================================

Les trois mouvements de Reidemeister (1927) generent toutes les equivalences
entre diagrammes de noeuds. Deux diagrammes representent le meme noeud si et
seulement si l'on peut transformer l'un en l'autre par une suite finie de
mouvements R1, R2, R3 et d'isotopies planaires.

Epic #2874, Phase 1.

Prerequis Mathlib necessaires :
- Theorie des graphes planaires (pour l'isotopie planaire)
- Suites finies de mouvements (systemes de reecriture combinatoires)
- Le theoreme de Reidemeister lui-meme est un resultat topologique profond
-/

import Knots.Basic
import Mathlib.Logic.Embedding.Basic

/-
  Convention i18n (EPIC #4980, decision user 2026-07-04) : ce fichier est **FR canonique**,
  avec son miroir anglais dans le fichier sibling `Reidemeister_en.lean` (modele sibling pair
  ratifie 2026-07-04, cf `code-style.md` §Lean i18n). Les enonces de theoremes,
  les tactiques Lean, les noms de lemmes et les references Mathlib restent en anglais
  (compat Mathlib 4) ; seules les docstrings de module et ce bloc d'en-tete different
  entre les deux fichiers.
-/

namespace Knots

/-! ## 1. Les trois mouvements de Reidemeister

Chaque mouvement est une transformation locale d'un diagramme de nœud qui
préserve le type de nœud. Ils sont appliqués dans un petit disque, en laissant
le reste inchangé.

**Modèle Phase 5 (constructeurs concrets avec renommage d'arêtes).** Chaque
mouvement est énoncé comme une conjonction existentielle à valeur dans `Prop`
portant :
  (1) l'équation de chirurgie reliant `d₁` et `d₂`,
  (2) la bonne formation `wf` sur les *deux* diagrammes (`KnotDiagram.wf`), et
  (3) un renommage d'arêtes explicite `ρ : Fin d₁.numEdges ↪ Fin d₂.numEdges`
      identifiant comment les arêtes de `d₁` correspondent à celles de `d₂`.

L'hypothèse `wf` des deux côtés est le renforcement clé par rapport au modèle
Phase 3 à existentiel symétrique : elle exclut les témoins mal formés (un
croisement dont les labels PD tombent hors de `[1, numEdges]`) qui réfutaient
`tricolorable_invariant` — voir le diagnostic certifié par contre-exemple de
`tricolorable_invariant` dans `Invariant.lean`. Le renommage d'arêtes `ρ` est
ce que le lemme de transfert (PR2) utilisera pour pousser un coloriage au
travers d'un mouvement.

Les mouvements sont énoncés avec `∃` (et non comme une `structure : Prop`) car
une `structure` à valeur dans `Prop` ne peut pas se projeter sur des champs de
données tels que `ρ : Fin _ ↪ Fin _` ou `c : PDCrossing`. La symétrie
(`*.symm`) vaut pour chaque mouvement : R3 a une preuve purement structurelle
(la disjonction de chirurgie est symétrique) ; la symétrie de R1/R2 est
affirmée ici et déchargée par la machinerie du lemme de transfert en PR2 (le
mouvement inverse existe parce qu'une torsion/pique suivie de son inverse est
l'identité).
-/

/-- R1 (Torsion/Détorsion) : ajout ou suppression d'une boucle dans un brin.

Diagrammatiquement :
  |         /\_    |
  |    ↔   /   \   |
  |        \___/   |

Une boucle crée un croisement supplémentaire et deux arêtes supplémentaires.
Le mouvement est **bipolaire** : la chirurgie est énoncée comme une disjonction
— soit `d₂` est `d₁` avec `c` ajouté en fin (une torsion,
`d₂.numEdges = d₁.numEdges + 2`), soit `d₁` est `d₂` avec `c` ajouté en fin
(une détorsion). Le renommage d'arêtes `ρ` pointe des arêtes du diagramme le
plus petit vers celles du diagramme le plus grand, identifiant les arcs
préservés ; sous un échange de `d₁`/`d₂` cette direction est préservée (le
diagramme le plus petit reste le plus petit), ce qui rend R1 symétrique par
construction.

La bonne formation `wf` sur les deux diagrammes force les quatre labels PD de
`c` à appartenir à `[1, (le plus grand).numEdges]` — excluant les témoins mal
formés du modèle Phase 3 qui réfutaient `tricolorable_invariant`. Le renommage
`ρ` est la donnée le long de laquelle le lemme de transfert (PR2) pousse un
coloriage.
-/
def Reidemeister1 (d₁ d₂ : KnotDiagram) : Prop :=
  d₁.wf = true ∧ d₂.wf = true ∧
  (∃ c : PDCrossing,
     ∃ ρ : Fin (min d₁.numEdges d₂.numEdges) ↪ Fin (max d₁.numEdges d₂.numEdges),
       d₂ = { d₁ with crossings := d₁.crossings ++ [c], numEdges := d₁.numEdges + 2 } ∨
       d₁ = { d₂ with crossings := d₂.crossings ++ [c], numEdges := d₂.numEdges + 2 })

/-- R1 est symétrique : échanger `d₁`/`d₂` permute les deux bras de la
disjonction de chirurgie ; le renommage dirigé par `min`/`max` est invariant
sous l'échange (transporté le long de `Nat.min_comm`/`Nat.max_comm`). -/
theorem Reidemeister1.symm {d₁ d₂ : KnotDiagram} (h : Reidemeister1 d₁ d₂) :
    Reidemeister1 d₂ d₁ := by
  obtain ⟨hwf₁, hwf₂, c, ρ, hsurg | hsurg⟩ := h
  · refine ⟨hwf₂, hwf₁, c, ?_, Or.inr hsurg⟩
    exact (Nat.min_comm d₂.numEdges d₁.numEdges ▸
           Nat.max_comm d₂.numEdges d₁.numEdges ▸ ρ)
  · refine ⟨hwf₂, hwf₁, c, ?_, Or.inl hsurg⟩
    exact (Nat.min_comm d₂.numEdges d₁.numEdges ▸
           Nat.max_comm d₂.numEdges d₁.numEdges ▸ ρ)

/-! ## R1 (raffinement ρ-déterminé) — Phase 5 PR1.5

Le mouvement `Reidemeister1` de la Phase 5 PR1 porte le renommage d'arêtes `ρ`
et le nouveau croisement `c` comme **deux existentiels indépendants** :
`∃ c, ∃ ρ, chirurgie`. Cela laisse `ρ` libre vis-à-vis des labels PD de `c`,
si bien qu'une seule « torsion » R1 peut introduire une boucle dont les deux
arêtes fraîches `{n+1, n+2}` sont complètement déconnectées de l'arc bouclé —
le contre-exemple certifié `tricolorable_invariant_fails_under_pr1_model`
(`Invariant.lean`) exploite exactement cela. Le lemme de transfert (PR2) ne
peut pas valoir sous ce modèle.

`Reidemeister1'` est le **renforcement** : le renommage `ρ` doit
*géométriquement déterminer* les labels du nouveau croisement. Une véritable
boucle R1 sur l'arc `a` introduit un croisement où un brin est l'arc `a`
lui-même et les deux arêtes fraîches sont les deux autres brins de la boucle,
donnant au nouveau croisement la forme `⟨a, a, n+1, n+2⟩`. Ceci relie les
arêtes fraîches à `color(a)` via la condition de Fox, préservant ≥2 couleurs
au travers du mouvement.

Ceci est un **raffinement additif** (ne modifie pas `Reidemeister1`) :
`Reidemeister1'.implies_reidemeister1` prouve l'inclusion conservative.
L'équivalence remodelée et le lemme de transfert (PR2) seront construits sur
`Reidemeister1'` dans une PR ultérieure une fois la construction validée.
-/

/-- **R1 (ρ-déterminé)** : un mouvement R1 où les labels du nouveau croisement
    sont géométriquement déterminés par l'arc bouclé. Dans le bras torsion, le
    nouveau croisement a la forme `⟨a, a, n+1, n+2⟩` : le brin anciennement
    labelisé `a` est le brin bouclé, et `{n+1, n+2}` sont les deux arêtes
    fraîches de la boucle. L'arc `a` vit dans `[1, numEdges]` du diagramme le
    plus petit (labels PD 1-indexés, cohérents avec `KnotDiagram.wf`). -/
def Reidemeister1' (d₁ d₂ : KnotDiagram) : Prop :=
  d₁.wf = true ∧ d₂.wf = true ∧
  (∃ a : Nat,
     1 ≤ a ∧ a ≤ min d₁.numEdges d₂.numEdges ∧
     (∃ ρ : Fin (min d₁.numEdges d₂.numEdges) ↪ Fin (max d₁.numEdges d₂.numEdges),
       (d₂ = { d₁ with crossings := d₁.crossings ++ [⟨a, a, d₁.numEdges + 1, d₁.numEdges + 2⟩],
                            numEdges := d₁.numEdges + 2 } ∨
        d₁ = { d₂ with crossings := d₂.crossings ++ [⟨a, a, d₂.numEdges + 1, d₂.numEdges + 2⟩],
                            numEdges := d₂.numEdges + 2 })))

/-- `Reidemeister1'` est un renforcement de `Reidemeister1` : toute boucle
    ρ-déterminée est, en particulier, un mouvement R1 (libre) avec `wf` des deux
    côtés. Le nouveau croisement `⟨a, a, n+1, n+2⟩` est le témoin de
    l'existentiel indépendant `∃ c` dans `Reidemeister1`. -/
theorem Reidemeister1'.implies_reidemeister1 {d₁ d₂ : KnotDiagram}
    (h : Reidemeister1' d₁ d₂) : Reidemeister1 d₁ d₂ := by
  -- `Reidemeister1'` unfolds as `wf₁ ∧ wf₂ ∧ (∃ a, range ∧ (∃ ρ, surgery|surgery))`.
  obtain ⟨hwf₁, hwf₂, a, _hrange₁, _hrange₂, ρ, hsurg | hsurg⟩ := h
  · exact ⟨hwf₁, hwf₂, ⟨a, a, d₁.numEdges + 1, d₁.numEdges + 2⟩, ρ, Or.inl hsurg⟩
  · exact ⟨hwf₁, hwf₂, ⟨a, a, d₂.numEdges + 1, d₂.numEdges + 2⟩, ρ, Or.inr hsurg⟩

/-! ## R1 (option C, chirurgie connectée) — Phase 5 PR1.5c

`Reidemeister1'` (PR1.5 #2956) est **vide** : sa prémisse `d₂.wf = true` est
insatisfiable pour les torsions non dégénérées, parce que la chirurgie par
ajout seul `d₂ = d₁ ++ [⟨a, a, n+1, n+2⟩]` introduit deux labels singleton
fraîches `n+1`, `n+2` qui violent la condition de parité `wf` (chaque label
doit apparaître exactement deux fois). Un argument de parité montre que TOUTE
chirurgie R1/R2 par ajout seul avec `wf` des deux côtés force le nouveau
croisement à être un **kink disjoint** `⟨n+1, n+1, n+2, n+2⟩` — un composant
nœud non trivial séparé ne partageant aucune arête avec `d₁`. Seul R3 (qui
préserve `numEdges` et renumérote un seul croisement) est véritablement
connecté sous le modèle ajout+`wf`. Voir le contre-exemple certifié
`tricolorable_invariant_fails_under_pr1_model` (`Invariant.lean`) et le
diagnostic structurel posté au coordinateur (2026-06-14).

`Reidemeister1Connected` est le **correctif option C** : une chirurgie NON par
ajout qui vient s'insérer dans un arc existant `a` de `d₁`. Elle modifie un
croisement d'extrémité `Y = d₁.crossings[i]` (renommant une occurrence de `a`
en un label frais `b = d₁.numEdges + 1`) et ajoute un nouveau croisement
`C = ⟨a, b, d₁.numEdges + 2, d₁.numEdges + 2⟩`. La parité est préservée :
- `a` : perd une occurrence (renommée dans `Y`) et en gagne une (dans `C.e1`) → 2× ;
- `b = n+1` : une dans `Y` (slot renommé) + une dans `C.e2` → 2× ;
- `c = n+2` : deux dans `C` (`e3`, `e4`) → 2× ;
- tous les autres labels inchangés.
Ceci est ADDITIF (ne modifie ni `Reidemeister1` ni `Reidemeister1'`) ; c'est
l'artefact concret, satisfiable pour `wf`, réduisant le risque de l'option C
pour la décision de modélisation C/X du coordinateur (Voir #2874). Il ne
remplace PAS les mouvements mergés (#2956) — les deux coexistent si bien que
les résultats antérieurs restent valides.
-/

/-- `Y'` est obtenu à partir de `c` en renommant les occurrences de `a` en `b` :
    chaque champ de `Y'` est soit inchangé par rapport à `c`, soit égal à `b`
    là où `c` avait `a`. C'est la contrainte qui rend le lemme de transfert de
    tricolorabilité (PR2) prouvable : sous une extension de coloriage avec
    `col₂ b = col₁ a` et `col₂ = col₁` sur les arêtes préservées, chaque brin
    de `Y'` lit la même couleur que le brin correspondant de `c` sous `col₁`,
    si bien que la condition de Fox au croisement modifié est préservée.

    Sans cette contrainte (le modèle #2980 mergé), `Y'` est un existentiel
    libre, donc la condition de Fox au croisement modifié est découplée du
    coloriage de `d₁` — le lemme de transfert ne peut pas valoir. Ce
    renforcement (option C, étape « scoped » (a)) est non-cassant : le témoin
    #2980 `⟨5,2,3,4⟩ = rename(⟨1,2,3,4⟩, 1→5)` le satisfait encore (voir
    `reidemeister1Connected_satisfiable`). -/
def PDCrossing.isRenameOf (Y' c : PDCrossing) (a b : Nat) : Prop :=
  (Y'.e1 = c.e1 ∨ (Y'.e1 = b ∧ c.e1 = a)) ∧
  (Y'.e2 = c.e2 ∨ (Y'.e2 = b ∧ c.e2 = a)) ∧
  (Y'.e3 = c.e3 ∨ (Y'.e3 = b ∧ c.e3 = a)) ∧
  (Y'.e4 = c.e4 ∨ (Y'.e4 = b ∧ c.e4 = a))

/-- Un croisement `c` « possède l'arête `a` » si `a` apparaît dans l'un de ses
    quatre slots PD. Sert à énoncer que l'arc `a` recevant une torsion R1
    connectée est un arc PROPRE — un arc partagé entre deux croisements
    distincts de `d₁` (et non une boucle monogone dégénérée confinée à un seul
    croisement). Les champs sont des `Nat` à égalité décidable, donc ce `Prop`
    est décidable et se décharge par `decide` après `unfold`. -/
def PDCrossing.hasEdge (c : PDCrossing) (a : Nat) : Prop :=
  c.e1 = a ∨ c.e2 = a ∨ c.e3 = a ∨ c.e4 = a

/-- **Reidemeister1Connected (option C)** : une torsion R1 CONNECTÉE sur l'arc
    `a`. La chirurgie modifie le croisement d'extrémité
    `Y = d₁.crossings[i]` (un slot `a` renommé en `b = d₁.numEdges + 1`,
    matérialisé comme le `Y'` fourni) et ajoute `⟨a, b, c, c⟩` avec
    `c = d₁.numEdges + 2`. Contrairement à `Reidemeister1'`, la prémisse
    `d₂.wf = true` est **satisfiable** — voir
    `reidemeister1Connected_satisfiable`. L'hypothèse `a ∈ d₁.edges` force le
    mouvement à être véritablement connecté (l'arc `a` est une vraie arête de
    `d₁`), si bien que le nouveau croisement partage une arête avec `d₁` plutôt
    que d'être un kink disjoint.

    L'hypothèse `Y'.isRenameOf (d₁.crossings.get i) a (d₁.numEdges + 1)`
    (renforcée à l'étape « scoped » (a)) relie `Y'` au croisement d'extrémité
    qu'il remplace — c'est ce croisement avec les occurrences de `a` renommées
    en `b`, rien d'autre. C'est ce dont le lemme de transfert PR2 a besoin pour
    pousser une tricoloration au travers du mouvement (la condition de Fox du
    croisement modifié est préservée sous `col₂ b = col₁ a`).

    **Hypothèse d'arc propre (cette PR, correctif du défaut de transfert
    arrière certifié par la recherche exhaustive derrière #3002) :** l'arc `a`
    est partagé avec un autre croisement `j ≠ i` de `d₁`. Sans cela, la def
    admet une torsion sur un arc monogone dégénéré (`a` apparaissant deux fois
    au seul croisement d'extrémité `i`), sous laquelle le transfert ARRIÈRE de
    tricolorabilité est FAUX — un kink connecté peut CRÉER de la
    tricolorabilité à partir d'un double-monogone `d₁` non tricolorable.
    Exiger que `a` soit un arc propre (joignant deux croisements distincts)
    élimine tous ces contre-exemples (validé par recherche exhaustive
    « brute-force » sur 2526 diagrammes bien formés, 20184 torsions valides :
    24 échecs arrière, tous des monogones, tous exclus par cette hypothèse). La
    direction AVANT (#3000) n'est pas affectée — elle est inconditionnelle. -/
def Reidemeister1Connected (d₁ d₂ : KnotDiagram) : Prop :=
  d₁.wf = true ∧ d₂.wf = true ∧
  (∃ (i : Fin d₁.crossings.length) (a : Nat) (Y' : PDCrossing)
     (ρ : Fin d₁.numEdges ↪ Fin (d₁.numEdges + 2)),
     1 ≤ a ∧ a ≤ d₁.numEdges ∧
     a ∈ d₁.edges ∧
     (∃ (j : Fin d₁.crossings.length), j ≠ i ∧ (d₁.crossings.get j).hasEdge a) ∧
     Y'.isRenameOf (d₁.crossings.get i) a (d₁.numEdges + 1) ∧
     d₂ = { d₁ with crossings := d₁.crossings.set i.val Y' ++
                       [⟨a, d₁.numEdges + 1, d₁.numEdges + 2, d₁.numEdges + 2⟩],
                    numEdges := d₁.numEdges + 2 })

/-- `Reidemeister1Connected` n'est PAS vide (contrairement à
    `Reidemeister1'`) : une torsion connectée concrète `d₁ → d₂` avec
    `wf = true` des deux côtés.

    Témoin : `d₁ = {[⟨1,2,3,4⟩, ⟨1,2,3,4⟩], 4}` (l'arc `a = 1` apparaît en
    `e1` des deux croisements). La torsion modifie le croisement 1
    (`⟨1,2,3,4⟩ → ⟨5,2,3,4⟩`, slot `e1` : `1 → 5 = b`) et ajoute
    `C = ⟨1,5,6,6⟩`. Le résultat
    `d₂ = {[⟨1,2,3,4⟩, ⟨5,2,3,4⟩, ⟨1,5,6,6⟩], 6}` est bien formé
    (`wf = true`, vérifié empiriquement par `#eval` lors de la réduction de
    risque et ici par `decide`). C'est la propriété phare distinguant
    l'option C du modèle vide PR1.5. -/
theorem reidemeister1Connected_satisfiable :
    Reidemeister1Connected
      { crossings := [⟨1,2,3,4⟩, ⟨1,2,3,4⟩], numEdges := 4, hwell := by trivial }
      { crossings := [⟨1,2,3,4⟩, ⟨5,2,3,4⟩, ⟨1,5,6,6⟩], numEdges := 6, hwell := by trivial } := by
  refine ⟨by decide, by decide, ⟨1, by decide⟩, 1, ⟨5,2,3,4⟩, ?_, ?_⟩
  · -- ρ : Fin 4 ↪ Fin 6 (trivial embedding, first 4 → first 4 of 6).
    exact { toFun := fun j => ⟨j.val, by omega⟩,
            inj' := fun x y h => by injection h with hv; exact Fin.ext hv }
  · -- body: 1 ≤ a, a ≤ numEdges, a ∈ d₁.edges, proper-arc (arc 1 shared with
    --   crossing j=0: ⟨1,2,3,4⟩.e1 = 1), Y' isRenameOf (rename 1→5 at e1), and
    --   the surgery equation. `decide` (kernel reduction) handles the struct
    --   projections / flatMap that `omega` cannot see; `rfl` closes the
    --   definitional surgery equation. The isRenameOf holds: e1 renamed (1→5),
    --   e2=e3=e4 unchanged. isRenameOf must be unfolded first — as a raw `def`
    --   it has no `Decidable` instance, but the unfolded `∧∨=` on `Nat` does.
    --   The proper-arc conjunct: arc a=1 appears at crossing j=⟨0⟩ (e1=1) with
    --   j=0 ≠ i=1, witnessed explicitly; `hasEdge` unfolded + `decide`.
    exact ⟨by decide, by decide, by decide,
           ⟨⟨0, by decide⟩, by decide, by unfold PDCrossing.hasEdge; decide⟩,
           by unfold PDCrossing.isRenameOf; decide, rfl⟩

/-! ### Lemmes d'API pour `Reidemeister1Connected` (infrastructure option C pour PR2)

Ces lemmes de projection exposent la forme combinatoire de la chirurgie, que le
lemme de transfert (PR2) consomme lorsqu'il pousse une tricoloration au travers
d'une torsion R1 connectée : le nombre d'arêtes croît d'exactement 2 (même
amplitude que le modèle de kink disjoint par ajout, mais atteinte par une
insertion connectée), et le nombre de croisements croît d'exactement 1. Ils
mitent le style d'API de projection `trefoil_wf` / `unknot_wf` de `Basic.lean`.
-/

/-- Une torsion R1 connectée ajoute exactement deux arêtes (le monogone kink
    `c` et l'extrémité d'arc renommée `b`), même amplitude que le modèle de kink
    disjoint mais via une insertion connectée. -/
theorem Reidemeister1Connected.numEdges_succ {d₁ d₂ : KnotDiagram}
    (h : Reidemeister1Connected d₁ d₂) : d₂.numEdges = d₁.numEdges + 2 := by
  obtain ⟨_hwf₁, _hwf₂, _i, _a, _Y', _ρ, _hr1, _hr2, _hmem, _hproper, _hrename, hsurg⟩ := h
  have hne := congrArg (·.numEdges) hsurg
  simpa using hne

/-- Une torsion R1 connectée ajoute exactement un croisement (la boucle `C`) ;
    le croisement d'extrémité existant `Y` est renuméroté sur place (`List.set`
    préserve la longueur), non dupliqué. -/
theorem Reidemeister1Connected.numCrossings_succ {d₁ d₂ : KnotDiagram}
    (h : Reidemeister1Connected d₁ d₂) : d₂.crossings.length = d₁.crossings.length + 1 := by
  obtain ⟨_hwf₁, _hwf₂, _i, _a, _Y', _ρ, _hr1, _hr2, _hmem, _hproper, _hrename, hsurg⟩ := h
  have hcl := congrArg (fun d => d.crossings.length) hsurg
  simpa [List.length_set, List.length_append] using hcl

/-- L'arc `a` recevant la torsion est une arête authentique de `d₁` (hypothèse
    de connectivité) : le nouveau croisement `C = ⟨a, b, c, c⟩` partage l'arête
    `a` avec `d₁`, ce qui distingue une torsion connectée d'un kink disjoint
    `⟨n+1,n+1,n+2,n+2⟩` (qui ne partage aucune arête avec `d₁`). -/
theorem Reidemeister1Connected.shares_edge {d₁ d₂ : KnotDiagram}
    (h : Reidemeister1Connected d₁ d₂) : ∃ a : Nat, a ∈ d₁.edges ∧ 1 ≤ a ∧ a ≤ d₁.numEdges := by
  obtain ⟨_hwf₁, _hwf₂, _i, a, _Y', _ρ, hr1, hr2, hmem, _hproper, _hrename, _hsurg⟩ := h
  exact ⟨a, hmem, hr1, hr2⟩

/-- L'équation de chirurgie sur les croisements sous forme directement
    utilisable : `d₂.crossings` est `d₁.crossings` avec le croisement
    d'extrémité à l'index `i` réécrit en `Y'` (via `List.set`), puis le kink
    monogone `⟨a, d₁.numEdges + 1, d₁.numEdges + 2, d₁.numEdges + 2⟩` ajouté en
    fin. Le lemme de transfert PR2 réécrit avec cette équation pour analyser la
    condition de Fox exactement aux deux croisements touchés par le mouvement
    (le `Y'` renuméroté à l'index `i`, et le kink ajouté `C` dont la
    auto-boucle `e3 = e4 = c` signifie que l'arc `c` est un brin fermé). -/
theorem Reidemeister1Connected.crossings_eq {d₁ d₂ : KnotDiagram}
    (h : Reidemeister1Connected d₁ d₂) :
    ∃ (i : ℕ) (Y' : PDCrossing) (a : Nat),
      i < d₁.crossings.length ∧
      d₂.crossings = d₁.crossings.set i Y' ++
        [⟨a, d₁.numEdges + 1, d₁.numEdges + 2, d₁.numEdges + 2⟩] := by
  obtain ⟨_hwf₁, _hwf₂, i, a, Y', _ρ, _hr1, _hr2, _hmem, _hproper, _hrename, hsurg⟩ := h
  refine ⟨i.val, Y', a, i.isLt, ?_⟩
  simpa using congrArg (·.crossings) hsurg

/-- R2 (Pique/Dépiqué) : ajout ou suppression de deux croisements consécutifs
de signe opposé.

Deux brins parallèles peuvent se traverser l'un l'autre :
  |   |        /\    |   |
  |   |   ↔   /  \   |   |
  |   |      /    \  |   |
  |   |      \    /  |   |
  |   |       \  /   |   |
  |   |        \/    |   |

Bipolaire comme R1 : un diagramme a quatre arêtes de plus que l'autre. Le
renommage `ρ : Fin (min) ↪ Fin (max)` pointe du diagramme le plus petit vers le
plus grand.
-/
def Reidemeister2 (d₁ d₂ : KnotDiagram) : Prop :=
  d₁.wf = true ∧ d₂.wf = true ∧
  (∃ c₁ c₂ : PDCrossing,
     ∃ ρ : Fin (min d₁.numEdges d₂.numEdges) ↪ Fin (max d₁.numEdges d₂.numEdges),
       d₂ = { d₁ with crossings := d₁.crossings ++ [c₁, c₂], numEdges := d₁.numEdges + 4 } ∨
       d₁ = { d₂ with crossings := d₂.crossings ++ [c₁, c₂], numEdges := d₂.numEdges + 4 })

/-- R2 est symétrique : même construction que R1 (transport le long de
`Nat.min_comm`/`Nat.max_comm`). -/
theorem Reidemeister2.symm {d₁ d₂ : KnotDiagram} (h : Reidemeister2 d₁ d₂) :
    Reidemeister2 d₂ d₁ := by
  obtain ⟨hwf₁, hwf₂, c₁, c₂, ρ, hsurg | hsurg⟩ := h
  · refine ⟨hwf₂, hwf₁, c₁, c₂, ?_, Or.inr hsurg⟩
    exact (Nat.min_comm d₂.numEdges d₁.numEdges ▸
           Nat.max_comm d₂.numEdges d₁.numEdges ▸ ρ)
  · refine ⟨hwf₂, hwf₁, c₁, c₂, ?_, Or.inl hsurg⟩
    exact (Nat.min_comm d₂.numEdges d₁.numEdges ▸
           Nat.max_comm d₂.numEdges d₁.numEdges ▸ ρ)

/-- R3 (Glissement) : déplacer un brin par-dessus un croisement.

Un brin peut glisser par-delà un croisement sans changer le nœud :
  \  |  /      \  |  /
   \ | /        \ | /
    \|/    ↔    / | \
     |          /  |  \
     |         /   |   \

R3 préserve le nombre de croisements et d'arêtes ; il ne fait que renuméroter
les arêtes à un croisement. Le renommage `ρ` est donc une bijection, exprimée
ici comme une injection `Fin d₁.numEdges ↪ Fin d₂.numEdges` (avec dimensions
égales).
-/
def Reidemeister3 (d₁ d₂ : KnotDiagram) : Prop :=
  d₁.crossings.length = d₂.crossings.length ∧ d₁.numEdges = d₂.numEdges ∧
  ∃ i c, ∃ ρ : Fin d₁.numEdges ↪ Fin d₂.numEdges,
    (d₂ = { d₁ with crossings := d₁.crossings.set i c } ∨
     d₁ = { d₂ with crossings := d₂.crossings.set i c }) ∧
    d₁.wf = true ∧ d₂.wf = true

/-- R3 est symétrique par construction : la disjonction de chirurgie est
symétrique, les hypothèses de bonne formation s'échangent, et puisque R3
préserve le nombre d'arêtes (`d₁.numEdges = d₂.numEdges`) le renommage
d'arêtes est transportable dans les deux sens. -/
theorem Reidemeister3.symm {d₁ d₂ : KnotDiagram} (h : Reidemeister3 d₁ d₂) :
    Reidemeister3 d₂ d₁ := by
  obtain ⟨hl, he, i, c, ρ, h | h, hwf₁, hwf₂⟩ := h
  · refine ⟨hl.symm, he.symm, i, c, ?_, ?_, hwf₂, hwf₁⟩
    · -- Inverse renaming: transport ρ across the equal edge counts.
      exact he ▸ ρ
    · exact Or.inr h
  · refine ⟨hl.symm, he.symm, i, c, ?_, ?_, hwf₂, hwf₁⟩
    · exact he ▸ ρ
    · exact Or.inl h

/-! ## R3 (raffinement slot-déterminé) — Phase 5 PR1.5d

`Reidemeister3` (Phase 5 PR1) porte le croisement renuméroté `c` comme un
existentiel LIBRE (`∃ i c, ∃ ρ, chirurgie`). Cela laisse `c` non contraint :
le seul croisement renuméroté peut prendre des labels PD arbitraires.
Contrairement aux modèles R1'/R2 par ajout seul (qui sont vides sous `wf`), la
chirurgie de R3 préservant `numEdges` maintient `d₂.wf` satisfiable — mais le
`c` libre est trop lâche pour que le lemme de transfert (PR2) pousse une
tricoloration au travers du mouvement : la condition de Fox au croisement
renuméroté est découplée du coloriage de `d₁`.

`Reidemeister3Determined` est le **renforcement** : le croisement renuméroté
`c` est contraint à être une **permutation de slots** du croisement qu'il
remplace (`c.isSlotPermOf (d₁.crossings.get i)`) — ses quatre labels PD sont
une permutation des quatre labels du croisement d'origine. Ceci préserve le
multi-ensemble global d'arêtes (donc `wf` des deux côtés est automatique à
partir de `d₁.wf`), et relie la structure de brins du croisement renuméroté à
celle de l'original : les quatre brins se rencontrant au croisement `i` sont
les quatre mêmes brins, assignés aux slots dans un ordre possiblement
différent (l'essence combinatoire d'un glissement R3, qui réarrange les brins
par-delà un croisement sans changer quels brins s'y rencontrent).

Ceci est un **raffinement additif** (ne modifie pas `Reidemeister3`) :
`Reidemeister3Determined.implies_reidemeister3` prouve l'inclusion
conservative. Le lemme de transfert (PR2) et la question de savoir quelles
permutations de slots correspondent à de véritables glissements R3 (vs des
renumérotations arbitraires) sont explicitement un travail futur — ceci est
l'échafaudage de réduction de risque établissant un modèle non vide,
satisfiable pour `wf`, à renforcement fort, parallèle à
`Reidemeister1Connected` pour R1 (Voir #2874).
-/

/-- `c` « est une permutation de slots de `Y` » ssi les quatre labels PD de `c`
    sont une permutation des quatre labels de `Y` (le même multi-ensemble de
    quatre brins, assignés possiblement à des slots différents). Les champs
    sont des `Nat` à égalité décidable, donc ce `Prop` est décidable
    (`List.Perm` sur `List Nat`) et se décharge par `decide`. -/
def PDCrossing.isSlotPermOf (c Y : PDCrossing) : Prop :=
  List.Perm [c.e1, c.e2, c.e3, c.e4] [Y.e1, Y.e2, Y.e3, Y.e4]

/-- **Reidemeister3Determined** : un glissement R3 où le croisement renuméroté
    `c` est une permutation de slots du croisement d'origine à l'index `i`
    (mêmes quatre brins, possiblement réordonnés). `numEdges` et le nombre de
    croisements sont préservés (comme dans `Reidemeister3`) ; `wf` vaut des deux
    côtés. Le renommage d'arêtes `ρ` est porté pour correspondre à la forme de
    `Reidemeister3` (le raffinement le fournit directement). Non vide — voir
    `reidemeister3Determined_satisfiable`. -/
def Reidemeister3Determined (d₁ d₂ : KnotDiagram) : Prop :=
  d₁.crossings.length = d₂.crossings.length ∧ d₁.numEdges = d₂.numEdges ∧
  (∃ (i : Fin d₁.crossings.length) (c : PDCrossing)
     (ρ : Fin d₁.numEdges ↪ Fin d₂.numEdges),
     c.isSlotPermOf (d₁.crossings.get i) ∧
     (d₂ = { d₁ with crossings := d₁.crossings.set i.val c } ∨
      d₁ = { d₂ with crossings := d₂.crossings.set i.val c }) ∧
     d₁.wf = true ∧ d₂.wf = true)

/-- `Reidemeister3Determined` est un renforcement de `Reidemeister3` : un
    glissement slot-déterminé est, en particulier, un mouvement R3 (à `c`
    libre). Le croisement témoin `c` et le renommage `ρ` sont fournis
    directement ; l'équation de chirurgie est inchangée (`set i.val c` avec
    `i.val` le `Nat` sous-jacent). -/
theorem Reidemeister3Determined.implies_reidemeister3 {d₁ d₂ : KnotDiagram}
    (h : Reidemeister3Determined d₁ d₂) : Reidemeister3 d₁ d₂ := by
  obtain ⟨hl, he, i, c, ρ, _hperm, hsurg | hsurg, hwf₁, hwf₂⟩ := h
  · exact ⟨hl, he, i.val, c, ρ, Or.inl hsurg, hwf₁, hwf₂⟩
  · exact ⟨hl, he, i.val, c, ρ, Or.inr hsurg, hwf₁, hwf₂⟩

/-- `Reidemeister3Determined` n'est PAS vide : un glissement slot-déterminé
    concret `d₁ → d₂` avec `wf = true` des deux côtés. Témoin : `d₁` a deux
    croisements identiques `⟨1,2,3,4⟩` ; `d₂` renumérote le croisement 0 en
    `⟨1,3,2,4⟩` (slots e2/e3 échangés — une permutation de slots de
    `⟨1,2,3,4⟩`). Le multi-ensemble global de labels `{1,2,3,4}` est inchangé,
    donc `wf` vaut des deux côtés. -/
theorem reidemeister3Determined_satisfiable :
    Reidemeister3Determined
      { crossings := [⟨1,2,3,4⟩, ⟨1,2,3,4⟩], numEdges := 4, hwell := by trivial }
      { crossings := [⟨1,3,2,4⟩, ⟨1,2,3,4⟩], numEdges := 4, hwell := by trivial } := by
  refine ⟨by decide, by decide, ?_⟩
  refine ⟨⟨0, by decide⟩, ⟨1,3,2,4⟩, ?_, ?_, ?_, ?_, ?_⟩
  · -- ρ : Fin 4 ↪ Fin 4 (identity; numEdges equal on both sides)
    exact Function.Embedding.refl (Fin 4)
  · -- c.isSlotPermOf (d₁.crossings.get ⟨0⟩): [1,3,2,4] ~ [1,2,3,4] (swap middle pair).
    -- `isSlotPermOf` is a raw `def` (no Decidable instance), so unfold it first to
    -- the underlying `List.Perm` on `List Nat`, which IS decidable.
    exact by unfold PDCrossing.isSlotPermOf; decide
  · -- surgery, left arm: d₂ = {d₁ with crossings := d₁.crossings.set 0 ⟨1,3,2,4⟩}
    exact Or.inl rfl
  · -- d₁.wf = true (each of {1,2,3,4} appears exactly twice)
    exact by decide
  · -- d₂.wf = true (multiset unchanged by the slot swap)
    exact by decide

/-! ## 2. Pas de Reidemeister unique

Un pas unique est n'importe lequel de R1, R2 ou R3.
-/

inductive ReidemeisterStep (d : KnotDiagram) : KnotDiagram → Prop where
  | r1 {d'} :
      (Reidemeister1Connected d d' ∨ Reidemeister1Connected d' d) →
      ReidemeisterStep d d'
  | r2 {d'} : Reidemeister2 d d' → ReidemeisterStep d d'
  | r3 {d'} : Reidemeister3 d d' → ReidemeisterStep d d'

/-! ## 3. Équivalence de Reidemeister (fermeture réflexive transitive)

Deux diagrammes sont équivalents au sens de Reidemeister s'ils sont reliés par
une suite finie de mouvements (dans les deux sens).
-/

/-- Fermeture réflexive transitive des pas de Reidemeister. -/
inductive ReidemeisterEquiv : KnotDiagram → KnotDiagram → Prop where
  | refl (d : KnotDiagram) : ReidemeisterEquiv d d
  | step {d₁ d₂ : KnotDiagram} :
      ReidemeisterStep d₁ d₂ → ReidemeisterEquiv d₁ d₂
  | trans {d₁ d₂ d₃ : KnotDiagram} :
      ReidemeisterEquiv d₁ d₂ → ReidemeisterEquiv d₂ d₃ → ReidemeisterEquiv d₁ d₃

/-- Symétrie : si d₁ →* d₂ alors d₂ →* d₁ (chaque mouvement a un inverse).

Preuve : récurrence sur la RTC. Chaque mouvement de base (R1/R2/R3) est
symétrique par les lemmes `*.symm` explicites ci-dessus ; la réflexivité est
triviale ; la transitivité inverse les deux moitiés et les compose.
-/
theorem reidemeister_equiv_symm {d₁ d₂ : KnotDiagram}
    (h : ReidemeisterEquiv d₁ d₂) : ReidemeisterEquiv d₂ d₁ := by
  induction h with
  | refl d => exact ReidemeisterEquiv.refl d
  | step hstep => exact ReidemeisterEquiv.step (by
      cases hstep with
      | r1 h => exact ReidemeisterStep.r1 h.symm
      | r2 h => exact ReidemeisterStep.r2 h.symm
      | r3 h => exact ReidemeisterStep.r3 h.symm)
  | trans _ _ ih₁ ih₂ => exact ReidemeisterEquiv.trans ih₂ ih₁

/-- Relation d'équivalence. -/
theorem reidemeister_equiv_equivalence : Equivalence (@ReidemeisterEquiv) where
  refl := ReidemeisterEquiv.refl
  symm := reidemeister_equiv_symm
  trans := ReidemeisterEquiv.trans

/-! ## 4. Équivalence des nœuds

Deux nœuds sont équivalents si leurs diagrammes sont équivalents au sens de
Reidemeister.
-/

def KnotEquiv (k₁ k₂ : Knot) : Prop :=
  ReidemeisterEquiv k₁.diagram k₂.diagram

/-! ## 5. Théorème de Reidemeister (énoncé seul)

Ceci est le théorème fondamental de la théorie des nœuds : l'isotopie ambiante
des nœuds correspond exactement aux mouvements de Reidemeister sur les
diagrammes.

**Ceci est un théorème très profond** dont la preuve requiert :
- La topologie linéaire par morceaux (PL) des variétés de dimension 3
- Des arguments de position générale pour les courbes dans l'espace à 3
  dimensions
- Le théorème d'Alexander (tout nœud a un diagramme)
- Référence : Reidemeister (1927), Alexander (1928)
- Preuve moderne : Kauffman (cf. « Knots and Physics »)
-/
theorem reidemeister_theorem :
    ∀ (k₁ k₂ : Knot),
      -- Ambient isotopy of the embeddings S¹ → S³
      sorry -- ambient_isotopic k₁ k₂
      ↔
      -- Reidemeister equivalence of diagrams
      KnotEquiv k₁ k₂ := by
  exact sorry
  -- Reference: Reidemeister (1927)
  -- Mathlib prerequisites:
  --   1. PL manifolds (not in Mathlib)
  --   2. Embeddings S¹ → S³ (not in Mathlib)
  --   3. Ambient isotopy (not in Mathlib)
  --   4. General position / transversality (not in Mathlib)
  -- See Kyle Miller's talk (UCSC 2024): long-term project to build these

end Knots

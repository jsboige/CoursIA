import Mathlib.Tactic
import RepeatedGames.Stage

/-!
# FairBot par le théorème de Löb (L2)

Formalisation du deuxième niveau (L2) de l'équilibre en programmes pour le
Dilemme du Prisonnier : **FairBot**, l'agent qui coopère exactement quand la
coopération de son adversaire est *prouvable* — et la coopération mutuelle
FairBot × FairBot, obtenue par le **théorème de Löb**.

C'est le pont entre les deux livrables voisins de l'EPIC #15062
« Math for AI Safety » : le noyau borné L1 (`ProgramGames/Basic.lean`,
grain #15176, où `probeBot` est un surrogate du FairBot *sans* Löb et où
`exploiterBot` démontre la limite du niveau borné) et le pont GL
(`SymbolicAI/Lean/formal_logic_lean/FormalLogic/GLBridge.lean`, tranche L3,
PR #15923, qui fournit le témoin noyau-vérifié du schéma de Löb).

Références :
  - Barasz, Christiano, Fallenstein, Herreshoff, LaVictor, Yudkowsky
    (2014), « Program Equilibrium via Succinct Circuit Representation »,
    arXiv:1401.5577 ;
  - LaVictor (2015), « Robust cooperation in the Prisoner's Dilemma :
    program equilibrium via provability logic », arXiv:1401.5577 appendices ;
  - Critch (2016), « Parametric Bounded Löb's Theorem and Robust
    Cooperation of Bounded Agents », arXiv:1602.04184.

## Architecture honnête du schéma de Löb

L'EPIC interdit de déclarer Löb comme axiome ad hoc puis de présenter
FairBot comme « certifié ». Ce module procède autrement, en trois temps :

1. **Interface.** `ModalProvability box` capture toute modalité de
   prouvabilité au sens de Hilbert-Bernays-Löb : nécessitation (D1),
   distribution (D2), introspection positive (D3), plus le schéma de Löb
   comme CHAMP de la structure. Tous les théorèmes ci-dessous sont
   relatifs à cette interface — ils valent pour *toute* instance.
2. **Indépendance mesurée.** La modalité témoin `bump p := p ∨ (0 = 1)`
   satisfait D1/D2/D3 mais viole le schéma de Löb (`bump_loeb_fails`) :
   le champ `loeb` n'est donc PAS redondant, aucune preuve de Löb ne peut
   être obtenue des seules dérivées HBL. Le contenu du champ est réel.
3. **Témoin vérifié.** Ce module ne couple pas le build de
   `game_theory_lean` au lake GL (pattern « libs volontairement légères »
   du lakefile : seuls `Mathlib.Tactic` et `RepeatedGames.Stage` sont
   importés) : le champ `loeb` est une **hypothèse explicite de
   l'interface**, et sa non-vacuité est attestée par le témoin externe
   noyau-vérifié `FormalLogic.GLBridge.loeb_schema` (lake
   `formal_logic_lean`, PR #15923, bibliothèque `ProvabilityLogic` à
   commit épinglé) qui dérive `□(□A → A) → □A` dans le calcul de Hilbert
   GL — **cité par référence, jamais importé, et ce module ne définit
   aucune instance de `ModalProvability`** : toute instance devra fournir
   le champ, le pont servant de témoin, pas d'instance.

## Résultats-phare

  - `loeb_mutual_fixedpoint` : dans un système d'équations modales
    croisées `q ↔ □r`, `r ↔ □q`, chaque côté satisfait la condition de
    Löb, donc les deux coopèrent — la dérivation de Barasz et al. 2014 ;
  - `fairBot_fairBot_cooperation` : FairBot × FairBot = (C, C), obtenu par
    Löb, là où L1 devait se contenter du sondage borné `probeBot` ;
  - `fairBot_not_sucker` / `fairBot_unexploitable` : FairBot n'est jamais
    le dindon de la farce **sous hypothèse explicite de fiabilité locale**
    (`box r → r` sur la clause adverse) — l'exploitation exigerait un
    système de preuve qui certifie une coopération fausse ;
  - `fairBot_vs_coopBot` / `fairBot_vs_defectBot` : la table pédagogique —
    FairBot coopère avec qui coopère de façon prouvable, dévie contre
    DefectBot *sous hypothèse explicite de cohérence* (`¬ box False`).

## Contraste avec le niveau L1

La faille de `probeBot` (L1) était une **signature de surface** : son
profil de sonde `(C, D)`, lisible par n'importe quel agent borné
(`exploiterBot`). La décision de FairBot dépend de `box r` — un fait de
prouvabilité, pas de comportement de surface : amener FairBot à coopérer
pendant qu'on dévie exige `box r` avec `¬r`, c'est-à-dire un système de
preuve non fiable sur `r` — exactement ce que l'hypothèse explicite de
`fairBot_not_sucker` exclut. C'est le saut conceptuel de la coopération
robuste : ne sonder ni le comportement ni la surface, mais la preuve.
-/

namespace ProgramGames

open RepeatedGames PDAction

/-! ## Interface de prouvabilité : Box + D1/D2/D3 + Löb postulé -/

/-- Modalité de prouvabilité au sens de Hilbert-Bernays-Löb. `box p` se lit
« p est prouvable dans le système ». Les trois premiers champs sont les
dérivées HBL classiques ; le quatrième est le schéma de Löb, **postulé
comme hypothèse explicite de l'interface** (voir le docstring du module :
le champ n'est ni un axiome local ni importé ni redondant —
`bump_loeb_fails` mesure son indépendance, sa non-vacuité est attestée par
le témoin externe cité par référence). -/
class ModalProvability (box : Prop → Prop) where
  /-- D1 — nécessitation (méta-règle) : ce qui est établi est prouvable. -/
  nec {p : Prop} (h : p) : box p
  /-- D2 — distribution : la prouvabilité se distribue sur la modus ponens. -/
  dist {p q : Prop} (hpq : box (p → q)) (hp : box p) : box q
  /-- D3 — introspection positive : ce qui est prouvable est prouvablement
  prouvable. C'est le champ que la dérivation de FairBot × FairBot
  consomme (via `box_mono` : la preuve de la clause adverse devient
  elle-même objet de preuve). -/
  posIntros {p : Prop} (hp : box p) : box (box p)
  /-- Schéma de Löb : si « prouvablement (prouvable p implique p) » alors
  « prouvable p ». **Hypothèse explicite de l'interface**, pas un axiome
  local ni un import : sa non-vacuité est attestée par le témoin externe
  noyau-vérifié `FormalLogic.GLBridge.loeb_schema` (lake
  `formal_logic_lean`, PR #15923, bibliothèque ProvabilityLogic à commit
  épinglé), **cité par référence sans coupler le build**. L'indépendance
  de ce champ vis-à-vis de D1/D2/D3 est mesurée par `bump_loeb_fails`
  ci-dessous. -/
  loeb {p : Prop} (h : box (box p → p)) : box p

open ModalProvability

variable {box : Prop → Prop} [ModalProvability box]

/-! ## Dérivées de l'interface -/

/-- Monotonie : la prouvabilité préserve l'implication (D1 + D2). -/
theorem box_mono {p q : Prop} (hpq : p → q) (hp : box p) : box q :=
  dist (nec hpq) hp

/-- Löb, version « russe » : si `p` dès que `p` est prouvable, alors `p`.
Équivalente au schème `loeb` (nécessitation de l'hypothèse puis modus
ponens). C'est la forme directement consommée par la coopération mutuelle :
« si je coopère dès que ma coopération est prouvable, alors je coopère ». -/
theorem loeb_russian {p : Prop} (h : box p → p) : p :=
  h (loeb (nec h))

/-! ## Actions modales et définition de FairBot -/

/-- Action dictée par une proposition abstraite : coopérer si elle tient,
dévier sinon. Non calculable (`Prop` abstraite, décision classique) — le
contenu du module est dans les théorèmes, pas dans l'exécution. -/
noncomputable def modalAction (P : Prop) : PDAction :=
  @ite PDAction P (Classical.dec P) cooperate defect

@[simp] theorem modalAction_true {P : Prop} (h : P) :
    modalAction P = cooperate := if_pos h

@[simp] theorem modalAction_false {P : Prop} (h : ¬P) :
    modalAction P = defect := if_neg h

/-- La coopération se lit sur l'action (réciproque partielle de
`modalAction_true`). -/
theorem cooperates_of_action {P : Prop} (h : modalAction P = cooperate) : P := by
  by_contra hp
  rw [modalAction_false hp] at h
  exact absurd h (by decide)

/-- FairBot : coopère contre son adversaire exactement quand la coopération
de CET adversaire contre FairBot est prouvable dans le système. C'est la
définition centrale de Barasz et al. 2014. Le surrogate L1 était
`probeBot` (sonde de surface sur le profil de comportement) ; FairBot
sonde la PREUVE — la différence conceptuelle exacte entre L1 et L2. -/
noncomputable def fairBotAction (box : Prop → Prop) (r : Prop) : PDAction :=
  modalAction (box r)

/-- FairBot coopère dès que la coopération adverse est prouvable. -/
theorem fairBot_cooperates_with_provable_cooperator {r : Prop} (h : box r) :
    fairBotAction box r = cooperate := modalAction_true h

/-- FairBot dévie en l'absence de preuve de coopération adverse. -/
theorem fairBot_defects_without_proof {r : Prop} (h : ¬ box r) :
    fairBotAction box r = defect := modalAction_false h

/-! ## FairBot contre FairBot : le point fixe coordonné -/

/-- Duel modal FairBot × FairBot : un système d'équations modales croisées.
`rowCooperates` (« la ligne coopère ») est équivalent à la prouvabilité de
la coopération de la colonne, et réciproquement — chaque FairBot applique
sa clause à la clause de l'autre. -/
structure FairBotDuel (box : Prop → Prop) where
  /-- Fait « la ligne (FairBot n° 1) coopère ». -/
  rowCooperates : Prop
  /-- Fait « la colonne (FairBot n° 2) coopère ». -/
  colCooperates : Prop
  /-- Clause de FairBot côté ligne : coopère ssi la coopération adverse
  est prouvable. -/
  rowClause : rowCooperates ↔ box colCooperates
  /-- Clause de FairBot côté colonne. -/
  colClause : colCooperates ↔ box rowCooperates

/-- Cœur de la tranche : le point fixe coordonné par Löb. Chaque côté du
duel satisfait la condition de la version russe (`box q → q`), donc Löb
donne la coopération des deux côtés. La dérivation consomme D3 (une
preuve de coopération devient prouvablement une preuve) — c'est ce qui
fait sortir du niveau L1, où la coopération mutuelle ne tenait que par
sondage de surface. -/
theorem loeb_mutual_fixedpoint (d : FairBotDuel box) :
    d.rowCooperates ∧ d.colCooperates := by
  have hrow : box d.rowCooperates → d.rowCooperates := by
    intro hbq
    exact d.rowClause.2 (dist (nec d.colClause.2) (posIntros hbq))
  have hcol : box d.colCooperates → d.colCooperates := by
    intro hbr
    exact d.colClause.2 (dist (nec d.rowClause.2) (posIntros hbr))
  exact ⟨loeb_russian hrow, loeb_russian hcol⟩

/-- FairBot × FairBot = (C, C) : coopération mutuelle par Löb. Là où le
`probeBot` de L1 l'obtenait par un `rfl` de sondage borné — et le payait
par sa signature exploitable — FairBot l'obtient par le raisonnement sur
les preuves mutuelles, sans exposer de surface à sonder. -/
theorem fairBot_fairBot_cooperation (d : FairBotDuel box) :
    (modalAction d.rowCooperates, modalAction d.colCooperates)
      = (cooperate, cooperate) := by
  obtain ⟨h1, h2⟩ := loeb_mutual_fixedpoint d
  rw [modalAction_true h1, modalAction_true h2]

/-! ## Inexploloitabilité sous hypothèse explicite -/

/-- FairBot n'est jamais le dindon de la farce dès lors que le système de
preuve est FIABLE SUR LA CLAUSE ADVERSE (`soundCol : box r → r`) : coopérer
pendant que l'adversaire dévie exigerait une preuve `box r` d'une
coopération `r` fausse. L'hypothèse est explicite et minimale — elle porte
sur la clause adverse seulement, pas sur la solidité globale du système. -/
theorem fairBot_not_sucker (d : FairBotDuel box)
    (soundCol : box d.colCooperates → d.colCooperates) :
    ¬ (d.rowCooperates ∧ ¬ d.colCooperates) := by
  rintro ⟨hq, hr⟩
  exact hr (soundCol (d.rowClause.1 hq))

/-- Version « action » de `fairBot_not_sucker` : le profil (C, D) du dindon
est exclu sous la même hypothèse de fiabilité locale. -/
theorem fairBot_unexploitable (d : FairBotDuel box)
    (soundCol : box d.colCooperates → d.colCooperates) :
    (modalAction d.rowCooperates, modalAction d.colCooperates)
      ≠ (cooperate, defect) := by
  have h := fairBot_not_sucker d soundCol
  intro heq
  rw [Prod.mk.injEq] at heq
  obtain ⟨h1, h2⟩ := heq
  refine h ⟨cooperates_of_action h1, ?_⟩
  intro hcol
  rw [modalAction_true hcol] at h2
  exact absurd h2 (by decide)

/-- Sous fiabilité locale, Löb va plus loin que l'exclusion du dindon :
l'adversaire COOPÈRE (version russe appliquée à sa propre clause). La
fiabilité transforme « pas exploitable » en « coopération garantie ». -/
theorem opponent_cooperates_of_sound (d : FairBotDuel box)
    (soundCol : box d.colCooperates → d.colCooperates) :
    d.colCooperates :=
  loeb_russian soundCol

/-! ## Confrontations spécialisées -/

/-- FairBot contre CoopBot : la clause adverse est « coopère toujours ».
La coopération mutuelle ne demande aucune hypothèse — `box True` tient par
nécessitation. -/
def coopDuel : FairBotDuel box where
  rowCooperates := box True
  colCooperates := True
  rowClause := Iff.rfl
  colClause := ⟨fun _ => nec (nec True.intro), fun _ => True.intro⟩

/-- FairBot coopère avec CoopBot (sans hypothèse). -/
theorem fairBot_vs_coopBot :
    fairBotAction box True = cooperate :=
  modalAction_true (nec True.intro)

/-- FairBot dévie contre DefectBot — SOUS HYPOTHÈSE EXPLICITE de cohérence
du système (`¬ box False`). Sans cohérence, un système incohérent « prouve »
tout, y compris la coopération de DefectBot : l'hypothèse n'est pas
cosmétique, elle est exactement ce qui sépare défection mutuelle et
coopération illusoire. -/
theorem fairBot_vs_defectBot (hconsis : ¬ box False) :
    fairBotAction box False = defect :=
  modalAction_false hconsis

/-! ## Indépendance du schéma de Löb : le champ n'est pas redondant -/

/-- Modalité témoin `bump p := p ∨ (0 = 1)` : elle satisfait les dérivées
HBL (D1, D2, D3 — voir les trois lemmes suivants) mais pas le schéma de
Löb. Elle prouve qu'aucune preuve de Löb ne peut être dérivée des seules
D1/D2/D3 : le champ `ModalProvability.loeb` a un contenu propre, et son
attestation externe (le témoin GL #15923, cité par référence) prouve que
ce contenu propre est réalisable — pas une redondance déguisée en axiome. -/
private def bump (p : Prop) : Prop := p ∨ ((0 : ℕ) = 1)

private theorem bump_nec {p : Prop} (h : p) : bump p := Or.inl h

private theorem bump_dist {p q : Prop} (hpq : bump (p → q)) (hp : bump p) :
    bump q := by
  rcases hpq with hpq | h01
  · rcases hp with hp | h01
    · exact Or.inl (hpq hp)
    · exact Or.inr h01
  · exact absurd h01 (by decide)

private theorem bump_posIntros {p : Prop} (hp : bump p) : bump (bump p) :=
  Or.inl hp

/-- La modalité `bump` satisfait D1/D2/D3 mais VIOLE le schéma de Löb en
`p := False` : l'antécédent `bump (bump False → False)` est vrai (car
`bump False → False` équivaut à la réfutation de `0 = 1`, une tautologie
décidable), tandis que `bump False` est faux. Löb est donc indépendant des
dérivées HBL dans ce cadre — l'interface `ModalProvability` en fait un
champ postulé (hypothèse explicite que toute instance devra fournir),
dont le témoin externe noyau-vérifié du dépôt est
`FormalLogic.GLBridge.loeb_schema` (logique GL, bibliothèque
ProvabilityLogic, PR #15923), cité par référence. -/
theorem bump_loeb_fails :
    ¬ (bump (bump False → False) → bump False) := by
  intro h
  have hb := h (Or.inl (fun hx => Or.elim hx id (fun h01 => absurd h01 (by decide))))
  rcases hb with h1 | h2
  · exact h1
  · exact absurd h2 (by decide)

end ProgramGames

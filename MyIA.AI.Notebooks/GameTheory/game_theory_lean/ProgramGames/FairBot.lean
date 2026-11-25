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
FairBot comme « certifié ». Ce module procède autrement, en quatre temps :

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
4. **Non-instanciation mesurée (T4, #26945).** Instancier l'interface par
   une prouvabilité réelle (PA, l'organe GL du dépôt) ÉCHOUE — pas faute
   de Löb, mais à cause du champ `nec` : écrit `(h : p) : box p`, il dit
   « vrai ⇒ prouvable » (**réflexion**) et non « dérivé ⇒ prouvable » (la
   méta-règle D1 des systèmes de Hilbert, `Provability.D1` dans l'organe
   FFL). Réflexion + Löb effondrent toute instance
   (`every_instance_boxes_false`, puis `every_instance_boxes_everything`)
   : une prouvabilité réelle satisfait D2/D3/Löb mais refuse la réflexion
   (premier théorème d'incomplétude — la phrase de Gödel est vraie et non
   prouvable). L'instanciation qui existe vit un niveau plus haut, sur
   les PHRASES : `FormalLogic.FairBotLoeb` (L3, #17537), coopération
   mutuelle de FairBots arbitraires sous les hypothèses nommées
   `Diagonalization T₀` (lemme diagonal) et `𝔅.HBL`.

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
    DefectBot *sous hypothèse explicite de cohérence* (`¬ box False`) ;
  - `every_instance_boxes_false` / `every_instance_boxes_everything`
    (T4 #26945) : toute instance boote `False`, puis toute proposition —
    le champ `nec` est la réflexion, pas la nécessitation ; aucune
    prouvabilité réelle n'instancie l'interface (premier théorème
    d'incomplétude), et la version instanciable vit en L3
    (`FormalLogic.FairBotLoeb`, #17537) sous lemme diagonal + HBL ;
  - `cupodAction` / `CupodDuel` : le zoo s'étend au dual CUPOD (coopère sauf
    preuve de défection, Critch) — self-play (D, D) sous hypothèses nommées
    **en lecture de vraie prouvabilité** (dans l'interface, la dégénérescence
    T4 le rend inconditionnel : `cupod_cupod_mutual_defect_degenerate`),
    asymétrie DUPOC/CUPOD citée (2ᵉ incomplétude — vacuité T4 mesurée),
    théorème borné cité (organ-first : ColombanD/TorchLean le démontrent) ;
  - `PrudentBotDuel` : le PrudentBot payorien `P ↔ □(□P → Q) ∧ □(□¬P → ¬Q)`,
    pont direct vers le lemme de Payor du carnet `Dynamics-04c` (série
    Dynamics, issue #26985 tranche T-2).

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
  /-- D1 — nécessitation (méta-règle) : ce qui est établi est prouvable.
  « Établi » y est lu au sens de VRAI (`h : p` est une preuve Lean de la
  vérité de `p`) : le champ est donc la **réflexion** « vrai ⇒ prouvable »,
  plus forte que la méta-règle de Hilbert `T ⊢ φ → T ⊢ □φ` (qui va de la
  DÉRIVATION à la prouvabilité, `Provability.D1` dans l'organe FFL) —
  l'écart est mesuré par `every_instance_boxes_false` (T4 #26945). -/
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

/-! ## T4 (#26945) : dégénerescence de l'interface — aucune prouvabilité
réelle ne l'instancie

La tranche T4 de #26945 demandait d'instancier l'interface par l'organe
natif GL. La réponse tient en quatre lignes : le champ `nec` n'est pas la
nécessitation des systèmes de Hilbert (une méta-règle, de la DÉRIVATION de
`p` vers `T ⊢ □p`) mais le principe de RÉFLEXION (« vrai ⇒ prouvable »).
Réflexion + Löb = effondrement : toute instance boote `False`, donc tout —
l'interface ne distingue aucune proposition. Une prouvabilité réelle (PA,
vérifiée par l'organe `FormalLogic.FairBotLoeb` du lake GL) satisfait D2,
D3 et Löb — mais pas la réflexion (premier théorème d'incomplétude) :
l'instanciation échoue exactement sur le champ `nec`, et la coopération
mutuelle reste vraie un niveau plus haut (L3) sous les hypothèses nommées
: lemme diagonal (`Diagonalization T₀`) + HBL (`𝔅.HBL`). Les résultats
POSITIFS de ce module restent vrais — mais la dégénerescence mesure leur
limite : dans l'interface, FairBot coopère TOUJOURS (`box r` pour tout
`r`), alors que la coopération d'un vrai FairBot est conditionnelle (L3
la prouve pour FairBot × FairBot, la réfute contre DefectBot). -/

/-- **T4 (#26945) — l'effondrement réflexion + Löb.** Toute instance de
`ModalProvability` satisfait `box False`. La preuve : si `box False`, c'est
fini ; sinon la cohérence `¬ box False` est une vérité, donc `nec` la
boote, et `loeb` en `p := False` transforme `box (box False → False)` en
`box False`. Le champ `nec` n'est pas la méta-règle de nécessitation des
systèmes de Hilbert (`T ⊢ φ → T ⊢ □φ`, de la DÉRIVATION à la prouvabilité
— c'est `Provability.D1` dans l'organe natif FFL) mais le principe de
RÉFLEXION (« vrai ⇒ prouvable »), et réflexion + Löb sont incompatibles
avec la cohérence : c'est le schéma du second théorème d'incomplétude. -/
theorem every_instance_boxes_false : box False := by
  by_cases h : box False
  · exact h
  · exact loeb (p := False) (nec h)

/-- **Corollaire : dégénerescence maximale.** Toute instance boote TOUTE
proposition — ex falso boxée : `box False` puis `dist` sur `False → p`.
L'interface ne distingue donc aucune proposition ; ses hypothèses
négatives (`¬ box r`, `¬ box False`) sont insatisfaisables (voir
`consistency_hypothesis_unsat` et `no_unprovable_proposition`). Les
résultats POSITIFS du module (coopération mutuelle par Löb) restent
intacts : ils ne consomment jamais une négation de box. -/
theorem every_instance_boxes_everything {p : Prop} : box p :=
  dist (nec (fun h => h.elim)) every_instance_boxes_false

/-- L'hypothèse de cohérence `¬ box False` de `fairBot_vs_defectBot` est
INSATISFIABLE dans l'interface : ce théorème est vrai de vacuité. T4
(#26945) le mesure au lieu de le laisser implicite — la version
instanciable de la cohérence vit un niveau plus haut, sur les phrases :
c'est `Consistent T` dans l'organe `FormalLogic.FairBotLoeb` (L3). -/
theorem consistency_hypothesis_unsat : ¬ (¬ box False) :=
  fun h => h every_instance_boxes_false

/-- Symétrique pour `fairBot_defects_without_proof` : dans l'interface,
rien n'est non-prouvable — son hypothèse `¬ box r` est insatisfaisable
pour tout `r`. Une prouvabilité réelle sépare les propositions (la phrase
de Gödel est vraie et non prouvable) ; l'interface axiomatique, elle, ne
peut pas. -/
theorem no_unprovable_proposition {r : Prop} : ¬ (¬ box r) :=
  fun h => h every_instance_boxes_everything

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

/-- FairBot dévie en l'absence de preuve de coopération adverse.
**Mesure T4 (#26945)** : l'hypothèse `¬ box r` est insatisfaisable dans
l'interface (`no_unprovable_proposition`) — le théorème est vrai de
vacuité ; voir la section T4. -/
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
est exclu sous la même hypothèse de fiabilité locale.
Preuve alternative déclarée (formulation différente) :
`formal_logic_lean/FormalLogic/FairBotLoeb.lean` déclare un théorème du même
nom en lecture syntaxique — `T₀ ⊢ p 🡘 𝔅 q` et `T ⊢ p` donnent `T ⊢ q` sous
`[𝔅.Kreisel]`. Maison canonique de l'agent FairBot : ce lac
`game_theory_lean`, où vit le duel opérationnel ; la version
`formal_logic_lean` en est la généralisation Löb. Comparaison : ici
l'hypothèse est la fiabilité locale `box r → r` portant sur la clause adverse
d'un duel concret, et la conclusion exclut un profil d'actions ; là,
l'hypothèse de Kreisel gouverne toute théorie `T` et la conclusion est une
prouvabilité — cadres non transportables terme à terme, chaque preuve est
canonique dans le sien. Axiomes atteints : propext, Classical.choice, Quot.sound. -/
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
coopération illusoire. **Mesure T4 (#26945)** : dans l'interface, cette
hypothèse est INSATISFIABLE (`consistency_hypothesis_unsat`) — le théorème
est vrai de vacuité ; la cohérence instanciable vit en L3 (`Consistent T`
dans l'organe `FormalLogic.FairBotLoeb`).
Preuve alternative déclarée (formulation différente) :
`formal_logic_lean/FormalLogic/FairBotLoeb.lean` déclare un théorème du même
nom sous `[Consistent T] [𝔅.Kreisel]` et conclut `T ⊬ p` : la coopération
n'est pas prouvable. Maison canonique de l'agent FairBot : ce lac
`game_theory_lean` ; la version `formal_logic_lean` en est la lecture
syntaxique. Comparaison : ici la conclusion est une égalité d'action
(`fairBotAction box False = defect`) — le comportement du duel est déterminé ;
là, une non-prouvabilité — l'information épistémique qui manque à ce côté.
Deux forces distinctes, aucune ne contient l'autre. Axiomes atteints :
propext, Classical.choice, Quot.sound. -/
theorem fairBot_vs_defectBot (hconsis : ¬ box False) :
    fairBotAction box False = defect :=
  modalAction_false hconsis

/-! ## Le zoo s'étend : CUPOD, le dual de FairBot (Critch) -/

/-- CUPOD (Cooperate Unless Proof Of Defection) coopère sauf s'il peut
prouver que son adversaire dévie. La proposition `r` lit l'adversaire :
`r` vraie signifie « l'adversaire dévie » — attention, la même `r` qui
lisible chez FairBot disait « l'adversaire coopère ». Dual exact de
`fairBotAction` (rebaptisé DUPOC par Critch : Defect Unless Proof Of
Cooperation). Source : A. Critch, « Open-Source Game Theory », AI-Safety
for Mathematicians, 2026, archivé au gisement : « CUPOD cooperates unless
it can prove its opponent defects, and DUPOC defects unless it can prove
its opponent cooperates. » -/
noncomputable def cupodAction (box : Prop → Prop) (r : Prop) : PDAction :=
  modalAction (¬ box r)

/-- CUPOD coopère quand il ne trouve pas de preuve de défection adverse. -/
theorem cupod_cooperates_without_proof {r : Prop} (h : ¬ box r) :
    cupodAction box r = cooperate :=
  modalAction_true h

/-- CUPOD dévie quand il trouve une preuve de défection adverse. -/
theorem cupod_defects_with_proof {r : Prop} (h : box r) :
    cupodAction box r = defect :=
  modalAction_false (fun hnr => hnr h)

/-- Rencontre de deux CUPOD : chacun dévie si et seulement s'il peut prouver
la défection de l'autre. Structure duale de `FairBotDuel` — les clauses
suivent les *défections* au lieu des coopérations. -/
structure CupodDuel (box : Prop → Prop) where
  rowDefects : Prop
  colDefects : Prop
  rowClause : rowDefects ↔ box colDefects
  colClause : colDefects ↔ box rowDefects

/-- Dans un duel CUPOD-CUPOD, toute défection est elle-même prouvable :
`A → □B → □□B → □A`. NOTE T4 (#26945) : ce théorème ne témoigne PAS
d'une non-dérivabilité — dans cette interface dégénérée, sa réciproque
`□A → A` est AUSSI dérivable (tout l'est : voir
`cupod_row_defects_unconditional` et `every_instance_boxes_everything`).
L'asymétrie DUPOC/CUPOD — qui tient dans la direction de la réflexion —
est une observation sur la VRAIE prouvabilité (Critch), à instancier en
L3 (`FormalLogic.FairBotLoeb`). -/
theorem cupod_defect_provable (d : CupodDuel box) :
    d.rowDefects → box d.rowDefects :=
  fun hA => box_mono d.rowClause.2 (posIntros (d.rowClause.1 hA))

/-- Sans preuve de défection adverse, pas de défection : la clause de
CUPOD, dite aussi sa « bienveillance ». NOTE T4 : l'hypothèse
`¬ box d.colDefects` est insatisfaisable dans l'interface
(`no_unprovable_proposition`) — l'énoncé y est vrai de vacuité. -/
theorem cupod_cooperates_of_no_proof (d : CupodDuel box)
    (h : ¬ box d.colDefects) : ¬ d.rowDefects :=
  fun hA => h (d.rowClause.1 hA)

/-- **Témoin T4 — dégénérescence du zoo.** Dans l'interface, la défection
du camp ligne est dérivable SANS hypothèse : `rowClause.2` consomme
`every_instance_boxes_everything`. Toutes les lectures « sous hypothèses »
de cette section y sont donc triviairement inconditionnelles — l'interface
ne discrimine pas le zoo, seule la vraie prouvabilité (L3) le peut. -/
theorem cupod_row_defects_unconditional (d : CupodDuel box) :
    d.rowDefects :=
  d.rowClause.2 every_instance_boxes_everything

/-- Self-play CUPOD × CUPOD = (D, D) **sous les hypothèses nommées** que
chaque recherche aboutit : `hrow`, la recherche du camp ligne trouve une
preuve de la défection adverse ; `hcol`, celle du camp colonne. L'action
du camp ligne est `cupodAction box d.colDefects` — elle lit l'adversaire.

NOTE T4 (#26945) : dans cette interface dégénérée, les deux hypothèses
sont fournies GRATUITEMENT par `every_instance_boxes_everything` — le
corollaire `cupod_cupod_mutual_defect_degenerate` ci-dessous établit le
(D, D) sans aucune hypothèse. La lecture « sous hypothèses nommées »
décrit la VRAIE prouvabilité : là, un système cohérent ne prouve pas
l'absence de preuve (second théorème de Gödel), et c'est la contre-intuition
que signale Critch : « CUPOD seems the nicer robot, yet it defects
against itself. »

Le théorème **borné** (Critch, « Cooperative and uncooperative institution
designs », 2022) établit `outcome(CUPOD(k), CUPOD(k)) = (D, D)` pour tout
k assez grand, sans hypothèse — en vraie prouvabilité. Il est **cité, pas
prouvé** ici : organ-first, sa démonstration paramétrique appartient au
corpus ColombanD/TorchLean (week-08) que cette série cite sans le porter. -/
theorem cupod_cupod_mutual_defect (d : CupodDuel box)
    (hrow : box d.colDefects) (hcol : box d.rowDefects) :
    (cupodAction box d.colDefects, cupodAction box d.rowDefects)
      = (defect, defect) := by
  rw [cupod_defects_with_proof hrow, cupod_defects_with_proof hcol]

/-- **Corollaire T4** : dans l'interface, le self-play CUPOD × CUPOD est
INCONDITIONNEL — les hypothèses `hrow`/`hcol` de la version ci-dessus
sont des instances de `every_instance_boxes_everything`. Ce corollaire
réconcilie le zoo avec la dégénérescence mesurée par #26945 : ce que
l'interface prouve « sous hypothèses » y est toujours gratuit ; le zoo
discriminant (celui de Critch) vit en L3. -/
theorem cupod_cupod_mutual_defect_degenerate (d : CupodDuel box) :
    (cupodAction box d.colDefects, cupodAction box d.rowDefects)
      = (defect, defect) :=
  cupod_cupod_mutual_defect d every_instance_boxes_everything
      every_instance_boxes_everything

/-- Asymétrie DUPOC × CUPOD (Critch, ibid.) : si le DUPOC ne trouve pas de
preuve que le CUPOD coopère, il dévie ; si le CUPOD ne trouve pas de
preuve que le DUPOD dévie, il coopère. Issue : (D, C). Chez Critch, ces
hypothèses ne sont pas décoratives — impossible de prouver *dans le
système* que CUPOD coopère (il faudrait prouver l'absence d'une preuve de
défection), donc DUPOC dévie ; symétriquement CUPOD coopère. NOTE T4
(#26945) : dans CETTE interface, les deux hypothèses négatives sont
insatisfaisables (`no_unprovable_proposition`) — l'énoncé y est vrai de
vacuité, mesuré par `dupoc_cupod_asymmetry_vacuous` ; l'observation de
Critch décrit la vraie prouvabilité (L3). -/
theorem dupoc_cupod_asymmetry {coopCol defCol : Prop}
    (hnoCoop : ¬ box coopCol) (hnoDef : ¬ box defCol) :
    (fairBotAction box coopCol, cupodAction box defCol)
      = (defect, cooperate) := by
  rw [fairBot_defects_without_proof hnoCoop,
      cupod_cooperates_without_proof hnoDef]

/-- **Témoin T4 — vacuité de l'asymétrie dans l'interface.** Les
hypothèses négatives de `dupoc_cupod_asymmetry` ne peuvent pas être
satisfaites : rien n'est non-prouvable ici
(`no_unprovable_proposition`). L'issue (D, C) de Critch n'est donc pas
mécanisable à ce niveau — elle vit en L3. -/
theorem dupoc_cupod_asymmetry_vacuous {coopCol defCol : Prop} :
    ¬ (¬ box coopCol ∧ ¬ box defCol) :=
  fun h => h.1 every_instance_boxes_everything

/-! ## PrudentBot payorien : deux simulations au lieu d'une -/

/-- Le PrudentBot **payorien** : coopérer ssi (1) une preuve que « si ma
coopération était prouvable, l'adversaire coopérerait » **et** (2) une
preuve que « si ma défection était prouvable, l'adversaire dévierait » :
`P ↔ □(□P → Q) ∧ □(□¬P → ¬Q)`. Source : commentaire de
`transhumanist_atom_understander` au billet *Payorian cooperation is easy
with Kripke frames* (Alignment Forum, 2026-03) — le même fil qui fonde le
carnet `Dynamics-04c` de la série Dynamics. Le PrudentBot **löbien**
d'origine, `PB(X) ↔ □(X(PB) ∧ (¬□⊥ → ¬X(DB)))` (rappelé par Payor dans le
même fil ; Barasz, Christiano, Fallenstein, Herreshoff, LaVictoire,
Yudkowsky, *Robust Cooperation in the Prisoner's Dilemma*, LORI-V 2014)
teste l'adversaire contre DefectBot sous un niveau de stabilité : il est
**cité**, non mécanisé ici. L'auto-jeu PrudentBot × PrudentBot n'est pas
traité ici — la source le laisse « non-obvious », et cette section ne
prétend pas trancher. NOTE T4 : dans l'interface dégénérée, la question y
serait de toute façon triviale (les deux clauses de chaque camp sont des
box, donc bootées gratuitement) ; c'est en vraie prouvabilité — L3 —
qu'elle se pose. -/
structure PrudentBotDuel (box : Prop → Prop) where
  rowCooperates : Prop
  colCooperates : Prop
  rowClause : rowCooperates ↔ (box (box rowCooperates → colCooperates) ∧
      box (box (¬ rowCooperates) → ¬ colCooperates))
  colClause : colCooperates ↔ (box (box colCooperates → rowCooperates) ∧
      box (box (¬ colCooperates) → ¬ rowCooperates))

/-- Un PrudentBot payorien n'est jamais le dindon de la farce dès lors que
la boîte est fiable sur la clause adverse (`soundCol`) : sa première
clause exige une preuve `box (box P → Q)`, et sa propre coopération `P`
la nourrit par nécessitation — miroir exact de `fairBot_not_sucker`. -/
theorem prudent_not_sucker (d : PrudentBotDuel box)
    (soundCol : box d.colCooperates → d.colCooperates) :
    ¬ (d.rowCooperates ∧ ¬ d.colCooperates) := by
  rintro ⟨hRow, hNotCol⟩
  exact hNotCol (soundCol (dist (d.rowClause.1 hRow).1 (posIntros (nec hRow))))

/-- La première clause du PrudentBot payorien **est** la clause du FairBot
payorien `P ↔ □(□P → Q)` — le lemme de Payor que le carnet `Dynamics-04c`
réfute sur cadres de Kripke. Ce pont relie L2 au carnet Python : coopérer
en PrudentBot, c'est coopérer en FairBot payorien **plus** le test de
prudence. -/
theorem prudent_implies_payorian (d : PrudentBotDuel box)
    (hRow : d.rowCooperates) :
    box (box d.rowCooperates → d.colCooperates) :=
  (d.rowClause.1 hRow).1

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

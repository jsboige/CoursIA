import Foundation.FirstOrder.Incompleteness.Löb
import Foundation.FirstOrder.Incompleteness.Definability

/-!
# FairBot par le théorème de Löb *prouvé* (L3, EPIC #15062)

Troisième niveau de l'équilibre en programmes pour le Dilemme du Prisonnier.
Le niveau L2 (`game_theory_lean/ProgramGames/FairBot.lean`) raisonne sur une
interface `ModalProvability box` dont le schéma de Löb est un **champ postulé** :
ses quatre champs sont `nec` (D1), `dist` (D2), `posIntros` (D3) et `loeb`. La
modalité témoin `bump` de L2 montre que ce champ n'est pas redondant : D1, D2 et
D3 seules ne donnent pas Löb.

Ce module consomme directement la bibliothèque *Formalized Formal Logic* (FFL,
paquet `Foundation` épinglé par le lakefile), où le théorème de Löb n'est plus
un champ mais un **théorème** : `ProvabilityAbstraction.löb_theorem`, démontré
par le point fixe de Kreisel. Correspondance champ par champ avec L2 :

| L2 (`ModalProvability`) | L3 (FFL) | Statut dans ce module |
|---|---|---|
| `nec` (D1) | `Provability.bew_def` / `Provability.D1` | champ de la structure `Provability` |
| `dist` (D2) | classe `Provability.HBL2` | hypothèse de classe |
| `posIntros` (D3) | classe `Provability.HBL3` | hypothèse de classe |
| `loeb` | `ProvabilityAbstraction.löb_theorem` | **théorème**, aucun champ |

L'ingrédient qui manque à L2 n'est donc pas une quatrième condition de
dérivabilité : c'est le **lemme diagonal** (classe `Diagonalization T₀`), qui
fournit les phrases autoréférentielles. La modalité `bump` de L2 n'en possède
pas, et c'est exactement pour cela que Löb y échoue.

## Contenu

* **Section abstraite**, pour toute théorie `T` munie d'un prédicat de
  prouvabilité `𝔅` satisfaisant les conditions de Hilbert–Bernays–Löb
  relativement à une théorie de base diagonalisante `T₀` :
  - `fairBot_self_cooperation` : FairBot contre sa propre copie coopère ;
  - `fairBot_mutual_cooperation` : deux FairBots **quelconques**, décrits par
    des équations croisées `p ↔ 𝔅 q` et `q ↔ 𝔅 p`, coopèrent — aucune identité
    syntaxique n'est requise ;
  - `fairBot_unexploitable` : sous la condition de Kreisel, la coopération
    prouvée de FairBot entraîne celle de l'adversaire ;
  - `fairBot_vs_cooperateBot`, `fairBot_vs_defectBot` et
    `fairBot_vs_defectBot_defection_unprovable` : la défection contre
    DefectBot est vraie mais **indémontrable dans `T`**, lecture ludique du
    second théorème d'incomplétude ;
  - `contrarianBot_independent` : contrôle négatif — même diagonale, signe
    inversé, destin opposé (phrase de Gödel, indépendante).
* **Section arithmétique**, instanciée sur la prouvabilité standard de FFL
  (`Theory.standardProvability`, base `𝗜𝚺₁`) :
  - `pa_fairBot_self_cooperation` : `𝗣𝗔` prouve la coopération de FairBot avec
    lui-même, sans aucune hypothèse restante ;
  - `fairBotA` / `fairBotB` : une paire de FairBots de **codes distincts**
    (`fairBotA_ne_fairBotB`), obtenue par `exclusiveMultifixedpoint`, dont
    `pa_fairBot_pair_cooperation` établit la coopération mutuelle ;
  - `pa_fairBot_vs_defectBot` et `pa_fairBot_defects_in_standard_model` : contre
    DefectBot, `𝗣𝗔` ne prouve ni la coopération ni la défection de FairBot,
    alors que la défection est vraie dans `ℕ`.

Références :
  - Barasz, Christiano, Fallenstein, Herreshoff, LaVictor, Yudkowsky (2014),
    « Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via
    Provability Logic », arXiv:1401.5577 ;
  - Critch (2016), « Parametric Bounded Löb's Theorem and Robust Cooperation
    of Bounded Agents », arXiv:1602.04184 ;
  - pont GL du même lake : `FormalLogic.GLBridge` (#15923), niveau L2 :
    `ProgramGames.FairBot` (#16414).
-/

open FFL FFL.Entailment FFL.FirstOrder

namespace FormalLogic.FairBotLoeb

/-! ## Section abstraite : toute prouvabilité de Hilbert–Bernays–Löb -/

section Abstract

open ProvabilityAbstraction Diagonalization Provability

variable {L : Language} [L.ReferenceableBy L] [L.DecidableEq]
  {T₀ T : Theory L} [Diagonalization T₀] [T₀ ⪯ T]

/-- FairBot face à sa propre copie : la phrase `F` telle que `F ↔ 𝔅 F`
(« je coopère ssi ma coopération est prouvable »). C'est la phrase de Henkin,
obtenue par le lemme diagonal de la théorie de base `T₀`. -/
def fairBotSelf (𝔅 : Provability T₀ T) : Sentence L :=
  fixedpoint T₀ “x. !𝔅.prov x”

variable {𝔅 : Provability T₀ T}

omit [L.DecidableEq] [T₀ ⪯ T] in
/-- Clause de FairBot face à lui-même, prouvée dans la théorie de base. -/
lemma fairBotSelf_spec : T₀ ⊢ fairBotSelf 𝔅 🡘 𝔅 (fairBotSelf 𝔅) := by
  simpa [fairBotSelf, Provability.pr] using diag (T := T₀) “x. !𝔅.prov x”

/-- FairBot × FairBot (même code) : la coopération est prouvable dans `T`.
Une seule application de Löb suffit, sur la moitié `𝔅 F 🡒 F` de la clause. -/
theorem fairBot_self_cooperation [𝔅.HBL] : T ⊢ fairBotSelf 𝔅 :=
  ProvabilityAbstraction.löb_theorem (WeakerThan.pbl (K_right fairBotSelf_spec))

/-- Coopération mutuelle de deux FairBots arbitraires, dérivation de
Barasz et al. (2014). Les phrases `p` et `q` ne sont soumises qu'aux clauses
croisées `p ↔ 𝔅 q` et `q ↔ 𝔅 p` : deux programmes syntaxiquement distincts
mais prouvablement équivalents à FairBot coopèrent. Löb s'applique à la
conjonction `p ⋏ q`, en distribuant `𝔅` sur la conjonction (D2). -/
theorem fairBot_mutual_cooperation [𝔅.HBL] {p q : Sentence L}
    (hp : T₀ ⊢ p 🡘 𝔅 q) (hq : T₀ ⊢ q 🡘 𝔅 p) : T ⊢ p ⋏ q := by
  apply ProvabilityAbstraction.löb_theorem (𝔅 := 𝔅)
  have hd : T₀ ⊢ 𝔅 (p ⋏ q) 🡒 𝔅 p ⋏ 𝔅 q := bew_distribute_and
  have h : T₀ ⊢ 𝔅 (p ⋏ q) 🡒 p ⋏ q := by cl_prover [hd, hp, hq]
  exact WeakerThan.pbl h

omit [L.DecidableEq] [Diagonalization T₀] in
/-- Inexploitabilité : si `T` prouve que FairBot coopère, `T` prouve que
l'adversaire coopère. L'hypothèse de Kreisel (`T ⊢ 𝔅 σ → T ⊢ σ`) est la
contrepartie syntaxique de la fiabilité locale `box r → r` de L2 ; pour la
prouvabilité standard, elle découle de la correction de `T` sur les énoncés
𝚺₁. -/
theorem fairBot_unexploitable [𝔅.Kreisel] {p q : Sentence L}
    (hp : T₀ ⊢ p 🡘 𝔅 q) (h : T ⊢ p) : T ⊢ q :=
  𝔅.KR ((WeakerThan.pbl (K_left hp)) ⨀ h)

omit [L.DecidableEq] [Diagonalization T₀] in
/-- FairBot contre CooperateBot (la phrase `⊤`) : coopération sans hypothèse,
par nécessitation (D1) appliquée à `⊤`. -/
theorem fairBot_vs_cooperateBot {p : Sentence L} (hp : T₀ ⊢ p 🡘 𝔅 ⊤) : T ⊢ p :=
  WeakerThan.pbl ((K_right hp) ⨀ (D1 (by simp)))

omit [L.DecidableEq] [Diagonalization T₀] in
/-- FairBot contre DefectBot (la phrase `⊥`) : si `T` est cohérente et
satisfait Kreisel, `T` ne prouve pas que FairBot coopère. -/
theorem fairBot_vs_defectBot [Consistent T] [𝔅.Kreisel] {p : Sentence L}
    (hp : T₀ ⊢ p 🡘 𝔅 ⊥) : T ⊬ p := by
  intro h
  have hbot : T ⊢ ⊥ := fairBot_unexploitable hp h
  have : ¬Consistent T :=
    not_consistent_iff_inconsistent.mpr <| inconsistent_iff_provable_bot.mpr hbot
  contradiction

/-- … mais `T` ne prouve pas non plus que FairBot **dévie** : la défection
équivaut à `∼𝔅 ⊥`, c'est-à-dire à la cohérence `𝔅.con`, que `T` ne prouve pas
(second théorème d'incomplétude, `con_unprovable`). Pour `𝗣𝗔`, la défection
est pourtant l'issue réelle : voir `pa_fairBot_defects_in_standard_model`. -/
theorem fairBot_vs_defectBot_defection_unprovable [Consistent T] [𝔅.HBL]
    {p : Sentence L} (hp : T₀ ⊢ p 🡘 𝔅 ⊥) : T ⊬ ∼p := by
  intro h
  have hp' : T ⊢ p 🡘 𝔅 ⊥ := WeakerThan.pbl hp
  have hcon : T ⊢ ∼𝔅 ⊥ := by cl_prover [h, hp']
  exact con_unprovable (𝔅 := 𝔅) hcon

/-- Contrôle négatif : le « bot contrariant », qui coopère ssi sa coopération
n'est **pas** prouvable, est exactement la phrase de Gödel `gödel 𝔅`
(`G ↔ ∼𝔅 G`). Même lemme diagonal que `fairBotSelf`, signe inversé : là où
FairBot coopère prouvablement, le contrariant est indépendant de `T`. -/
theorem contrarianBot_independent [Consistent T] [𝔅.Kreisel] :
    Independent T (gödel 𝔅) :=
  gödel_independent

end Abstract

/-! ## Section arithmétique : prouvabilité standard de FFL -/

section Arithmetic

open Arithmetic ProvabilityAbstraction

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]

/-- FairBot contre lui-même pour la prouvabilité standard de `T`, base `𝗜𝚺₁`. -/
theorem standard_fairBot_self_cooperation :
    T ⊢ fairBotSelf T.standardProvability :=
  fairBot_self_cooperation

/-- Corollaire sans hypothèse restante : `𝗣𝗔` prouve la coopération de
FairBot avec sa propre copie. -/
theorem pa_fairBot_self_cooperation :
    𝗣𝗔 ⊢ fairBotSelf 𝗣𝗔.standardProvability :=
  standard_fairBot_self_cooperation 𝗣𝗔

/-- Corps des deux FairBots de la paire : le bot `0` coopère ssi la
coopération du bot `1` est prouvable (`#1`), et réciproquement (`#0`). -/
noncomputable def fairBotPairBody : Fin 2 → ArithmeticSemisentence 2 :=
  ![T.standardProvability.prov/[#1], T.standardProvability.prov/[#0]]

/-- Premier FairBot de la paire, point fixe multiple exclusif d'indice `0`. -/
noncomputable def fairBotA : ArithmeticSentence :=
  exclusiveMultifixedpoint (fairBotPairBody T) 0

/-- Second FairBot de la paire, point fixe multiple exclusif d'indice `1`. -/
noncomputable def fairBotB : ArithmeticSentence :=
  exclusiveMultifixedpoint (fairBotPairBody T) 1

omit [𝗜𝚺₁ ⪯ T] in
/-- Les deux FairBots ont des codes distincts : la coopération mutuelle
ci-dessous ne repose sur aucune identité syntaxique entre les programmes. -/
theorem fairBotA_ne_fairBotB : fairBotA T ≠ fairBotB T := by
  simp [fairBotA, fairBotB]

omit [𝗜𝚺₁ ⪯ T] in
/-- Clause du premier FairBot : il coopère ssi le second coopère
prouvablement. -/
lemma fairBotA_spec :
    𝗜𝚺₁ ⊢ fairBotA T 🡘 T.standardProvability (fairBotB T) := by
  simpa [fairBotA, fairBotB, fairBotPairBody, Provability.pr,
    Rew.subst_comp_subst, ← TransitiveRewriting.comp_app,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton] using!
    exclusiveMultidiagonal (T := 𝗜𝚺₁) (fairBotPairBody T) (i := 0)

omit [𝗜𝚺₁ ⪯ T] in
/-- Clause du second FairBot, symétrique. -/
lemma fairBotB_spec :
    𝗜𝚺₁ ⊢ fairBotB T 🡘 T.standardProvability (fairBotA T) := by
  simpa [fairBotA, fairBotB, fairBotPairBody, Provability.pr,
    Rew.subst_comp_subst, ← TransitiveRewriting.comp_app,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton] using!
    exclusiveMultidiagonal (T := 𝗜𝚺₁) (fairBotPairBody T) (i := 1)

/-- Coopération mutuelle de la paire de codes distincts. -/
theorem standard_fairBot_pair_cooperation :
    T ⊢ fairBotA T ⋏ fairBotB T :=
  fairBot_mutual_cooperation (fairBotA_spec T) (fairBotB_spec T)

/-- Corollaire sans hypothèse restante sur `𝗣𝗔`. -/
theorem pa_fairBot_pair_cooperation :
    𝗣𝗔 ⊢ fairBotA 𝗣𝗔 ⋏ fairBotB 𝗣𝗔 :=
  standard_fairBot_pair_cooperation 𝗣𝗔

/-- FairBot contre DefectBot dans `𝗣𝗔` : sa clause de coopération est `□⊥`.
`𝗣𝗔` ne prouve ni que FairBot coopère, ni qu'il dévie. -/
theorem pa_fairBot_vs_defectBot :
    𝗣𝗔 ⊬ 𝗣𝗔.standardProvability ⊥ ∧ 𝗣𝗔 ⊬ ∼𝗣𝗔.standardProvability ⊥ :=
  ⟨fairBot_vs_defectBot (𝔅 := 𝗣𝗔.standardProvability) (by cl_prover),
    fairBot_vs_defectBot_defection_unprovable (𝔅 := 𝗣𝗔.standardProvability)
      (by cl_prover)⟩

/-- … et pourtant FairBot dévie **réellement** contre DefectBot : sa clause
`□⊥` est fausse dans le modèle standard `ℕ`, par correction de la prouvabilité
standard (`Provability.SoundOn ℕ`) et cohérence de `𝗣𝗔`. L'issue (D, D) est
vraie dans `ℕ` sans être un théorème de `𝗣𝗔`. -/
theorem pa_fairBot_defects_in_standard_model :
    ¬ (ℕ↓[ℒₒᵣ] ⊧ 𝗣𝗔.standardProvability ⊥) := by
  intro h
  have hbot : 𝗣𝗔 ⊢ ⊥ :=
    Provability.SoundOn.sound_on (𝔅 := 𝗣𝗔.standardProvability) h
  exact not_consistent_iff_inconsistent.mpr
    (inconsistent_iff_provable_bot.mpr hbot) inferInstance

end Arithmetic

end FormalLogic.FairBotLoeb

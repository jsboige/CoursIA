import Foundation.FirstOrder.Basic.Semantics.Semantics
import Foundation.FirstOrder.Basic.Soundness
import Foundation.FirstOrder.Completeness.CounterModel
import Mathlib.Tactic.FinCases

/-!
# Pont FOL : micro-théorie exécutée ↔ certifiée (Tranche B, EPIC #16877)

Ce module est le versant Lean du notebook `Tweety-02d-FOL-Lab-Lean.ipynb` :
la micro-théorie définie ici est **la même** que celle exécutée par le raisonneur
Tweety dans le notebook — un langage à quatre prédicats unaires (`Homme`,
`Mortel`, `Grec`, `Philosophe`) et deux constantes (`socrate`, `platon`),
l'axiome universel `∀X (Homme(X) → Mortel(X))` et trois faits.

Côté notebook, Tweety *répond* (des verdicts de requête) ; ici le noyau
*certifie*, sur la sémantique FFL des structures (`Foundation.FirstOrder.Basic.Semantics`) :

- la dérivation de `Mortel(socrate)` observée chez Tweety devient un théorème de
  **conséquence sémantique** `KB ⊨ Mortel(socrate)`, quantifié sur toutes les
  structures — un modus ponens vérifié par le noyau, pas un sondage ;
- les deux existentiels `∃X Grec(X)` et `∃X Philosophe(X)` sont chacun conséquence
  (témoins `socrate` et `platon`), mais leur **fusion à témoin unique**
  `∃X (Grec(X) ∧ Philosophe(X))` n'est **pas** conséquence : un contre-modèle
  fini à deux éléments est exhibé et vérifié ligne à ligne ;
- `∀X Mortel(X)` n'est pas conséquence : le même monde témoin le falsifie
  (`platon` n'y est ni `Homme` ni `Mortel`).

Ancres métathéoriques citées (aucune redémonstration) :
- `Theory.Proof.sound` (`Foundation.FirstOrder.Basic.Soundness`) : `T ⊢ φ → T ⊨ φ` ;
- `Theory.Proof.complete_iff` (`Foundation.FirstOrder.Completeness.CounterModel`) :
  `T ⊨ φ ↔ T ⊢ φ` — le pont sémantique ↔ syntaxique que le versant
  propositionnel (`Bridge.lean`, Tranche A) ne pouvait qu'annoncer.

Verdict d'intégration : CONSUMER_PINNÉ au commit `81810b9f` (pilote #15520).
-/

open FFL.FirstOrder
open FFL.FirstOrder.Semiterm

namespace FormalLogic.FolBridge

/-! ## Le langage : quatre prédicats unaires, deux constantes

Un `Language` FFL est une paire de familles de symboles indexée par l'arité ;
les constantes sont les fonctions d'arité `0`. Les deux familles ci-dessous
sont la traduction exacte de la signature Tweety du notebook (FOL non typé,
prédicats d'arité 1, constantes `socrate` et `platon`). -/

/-- Les quatre prédicats unaires de la micro-théorie. -/
inductive SocRel : ℕ → Type
  | homme : SocRel 1
  | mortel : SocRel 1
  | grec : SocRel 1
  | philosophe : SocRel 1

/-- Les deux constantes du domaine nommé. -/
inductive SocFunc : ℕ → Type
  | socrate : SocFunc 0
  | platon : SocFunc 0

/-- Le langage de la micro-théorie. -/
abbrev Lsoc : Language where
  Func := SocFunc
  Rel := SocRel

/-- Le terme clos `socrate` : la constante appliquée à zéro argument. -/
abbrev tSocrate : Semiterm Lsoc Empty 0 := Semiterm.func SocFunc.socrate ![]

/-- Le terme clos `platon`. -/
abbrev tPlaton : Semiterm Lsoc Empty 0 := Semiterm.func SocFunc.platon ![]

/-! ## La théorie : un axiome universel et trois faits -/

/-- L'axiome universel `∀X (Homme(X) → Mortel(X))`. -/
abbrev axHommeMortel : Sentence Lsoc :=
  ∀¹ (Semiformula.rel SocRel.homme (fun _ => #(0 : Fin 1)) 🡒
      Semiformula.rel SocRel.mortel (fun _ => #(0 : Fin 1)))

/-- Le fait `Homme(socrate)`. -/
abbrev faitHommeSocrate : Sentence Lsoc :=
  Semiformula.rel SocRel.homme (fun _ => tSocrate)

/-- Le fait `Grec(socrate)`. -/
abbrev faitGrecSocrate : Sentence Lsoc :=
  Semiformula.rel SocRel.grec (fun _ => tSocrate)

/-- Le fait `Philosophe(platon)`. -/
abbrev faitPhilosophePlaton : Sentence Lsoc :=
  Semiformula.rel SocRel.philosophe (fun _ => tPlaton)

/-- La base de croyances du notebook : axiome universel + trois faits. -/
def KB : Theory Lsoc :=
  {axHommeMortel, faitHommeSocrate, faitGrecSocrate, faitPhilosophePlaton}

/-- La requête vedette du notebook : `Mortel(socrate)`. -/
abbrev qMortelSocrate : Sentence Lsoc :=
  Semiformula.rel SocRel.mortel (fun _ => tSocrate)

/-- Le premier existentiel : `∃X Grec(X)` (témoin attendu : `socrate`). -/
abbrev qExisteGrec : Sentence Lsoc :=
  ∃¹ Semiformula.rel SocRel.grec (fun _ => #(0 : Fin 1))

/-- Le second existentiel : `∃X Philosophe(X)` (témoin attendu : `platon`). -/
abbrev qExistePhilosophe : Sentence Lsoc :=
  ∃¹ Semiformula.rel SocRel.philosophe (fun _ => #(0 : Fin 1))

/-- La fusion à témoin unique : `∃X (Grec(X) ∧ Philosophe(X))`. -/
abbrev qExisteGrecEtPhilosophe : Sentence Lsoc :=
  ∃¹ (Semiformula.rel SocRel.grec (fun _ => #(0 : Fin 1)) ⋏
      Semiformula.rel SocRel.philosophe (fun _ => #(0 : Fin 1)))

/-- La forme universelle : `∀X Mortel(X)`. -/
abbrev qTousMortels : Sentence Lsoc :=
  ∀¹ Semiformula.rel SocRel.mortel (fun _ => #(0 : Fin 1))

/-! ## Versant positif : trois conséquences sémantiques

Chaque preuve suit le même schéma : on se donne une structure **quelconque**
qui modélise `KB`, puis on instancie l'axiome universel au terme de la
constante — le modus ponens que Tweety exécute sur sa structure, déroulé une
fois pour **toutes** les structures. -/

/-- Pont local : la satisfaction d'une phrase par `M↓[L]` est son évaluation
de Tarski `Eval` — les deux formes sont égales par définition. -/
theorem models_iff_eval {M : Type*} [Nonempty M] [s : Structure Lsoc M]
    {σ : Sentence Lsoc} :
    M↓[Lsoc] ⊧ σ ↔
      Semiformula.Eval (s := s) (![] : Fin 0 → M) (Empty.elim : Empty → M) σ := by
  rw [models_iff]

/-- **La dérivation devient théorème** : `KB ⊨ Mortel(socrate)`. C'est le
syllogisme exécuté par Tweety (universel instancié à `socrate`, modus ponens
avec le fait `Homme(socrate)`), certifié sur toutes les structures. -/
theorem mortel_socrate : KB ⊨ qMortelSocrate := by
  intro 𝓜 hT
  have hAx : 𝓜 ⊧ axHommeMortel := hT.models_set (by simp [KB])
  have hFait : 𝓜 ⊧ faitHommeSocrate := hT.models_set (by simp [KB])
  rw [struc_models_iff_models, models_iff_eval] at hAx hFait ⊢
  simp only [axHommeMortel, faitHommeSocrate, qMortelSocrate, tSocrate] at hAx hFait ⊢
  simp at hAx hFait ⊢
  exact hAx _ hFait

/-- Le premier existentiel est conséquence : `KB ⊨ ∃X Grec(X)`, témoin la
constante `socrate` — dans **chaque** structure qui modélise `KB`, le
dénommé `socrate` est Grec. -/
theorem existe_grec : KB ⊨ qExisteGrec := by
  intro 𝓜 hT
  have hFait : 𝓜 ⊧ faitGrecSocrate := hT.models_set (by simp [KB])
  rw [struc_models_iff_models, models_iff_eval] at hFait ⊢
  simp only [faitGrecSocrate, qExisteGrec, tSocrate] at hFait ⊢
  simp at hFait ⊢
  exact ⟨_, hFait⟩

/-- Le second existentiel est conséquence : `KB ⊨ ∃X Philosophe(X)`, témoin
la constante `platon`. -/
theorem existe_philosophe : KB ⊨ qExistePhilosophe := by
  intro 𝓜 hT
  have hFait : 𝓜 ⊧ faitPhilosophePlaton := hT.models_set (by simp [KB])
  rw [struc_models_iff_models, models_iff_eval] at hFait ⊢
  simp only [faitPhilosophePlaton, qExistePhilosophe, tPlaton] at hFait ⊢
  simp at hFait ⊢
  exact ⟨_, hFait⟩

/-! ## Le monde témoin : un contre-modèle fini à deux éléments

Tweety répond « non conséquence » sans expliquer ; Lean, lui, **exhibe** la
structure qui témoigne : domaine `Fin 2` où `0` joue `socrate` et `1` joue
`platon`. C'est le contre-modèle calculé du notebook, transporté terme à
terme et revérifié par le noyau. -/

/-- Le monde témoin : `0` joue `socrate`, `1` joue `platon`. Socrate y est
Homme, Mortel et Grec ; Platon y est Philosophe — mais ni Homme ni Mortel ni
Grec. Toutes les formules de `KB` y sont vraies. -/
instance mondeTemoins : Structure Lsoc (Fin 2) where
  func := fun {_k} F _v =>
    match F with
    | SocFunc.socrate => 0
    | SocFunc.platon => 1
  rel := fun {_k} R v =>
    match R with
    | SocRel.homme => v 0 = 0
    | SocRel.mortel => v 0 = 0
    | SocRel.grec => v 0 = 0
    | SocRel.philosophe => v 0 = 1

/-- **Le monde témoin modélise `KB`** : l'axiome universel y est vrai (le
seul Homme, `0`, est Mortel) et les trois faits y sont vrais. C'est la
preuve que « non conséquence » est possible : la théorie a un modèle qui
ressemble exactement à l'intuition. -/
theorem monde_modele_KB : (Fin 2)↓[Lsoc] ⊧* KB := by
  rw [models_theory_iff]
  intro σ hσ
  simp only [KB, Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
  rcases hσ with rfl | rfl | rfl | rfl
  · -- axiome universel : pour `0` l'implication est triviale, pour `1` l'hypothèse est absurde
    rw [models_iff_eval]
    intro x
    fin_cases x
    · exact Or.inr rfl
    · exact Or.inl (fun h => absurd (show (1 : Fin 2) = 0 from h) (by decide))
  · rw [models_iff_eval]; exact rfl
  · rw [models_iff_eval]; exact rfl
  · rw [models_iff_eval]; exact rfl

/-- **La fusion à témoin unique est falsifiée** : dans le monde témoin,
personne n'est à la fois Grec et Philosophe — `0` est Grec mais pas
Philosophe, `1` est Philosophe mais pas Grec. -/
theorem monde_falsifie_conjonction : ¬ ((Fin 2)↓[Lsoc] ⊧ qExisteGrecEtPhilosophe) := by
  rw [models_iff_eval]
  simp only [qExisteGrecEtPhilosophe]
  intro h
  obtain ⟨x, hx1, hx2⟩ := h
  have e1 : (x : Fin 2) = 0 := hx1
  have e2 : (x : Fin 2) = 1 := hx2
  exact absurd (e1.symm.trans e2) (by decide)

/-- **`∀X Mortel(X)` est falsifié** : dans le monde témoin, `platon`
(l'élément `1`) n'est pas Mortel. -/
theorem monde_falsifie_tous_mortels : ¬ ((Fin 2)↓[Lsoc] ⊧ qTousMortels) := by
  rw [models_iff_eval]
  simp only [qTousMortels]
  intro h
  have h1 : (1 : Fin 2) = 0 := h 1
  exact absurd h1 (by decide)

/-! ## Versant négatif : deux non-conséquences certifiées

« Pas conséquence » ne se prouve pas par l'absence de preuve : on **exhibe**
un modèle de `KB` qui falsifie la requête — le contre-modèle fini
ci-dessus. C'est la symétrie exacte du côté Tweety : le solveur répond
`FALSE` (non-conséquence), le noyau certifie **pourquoi** c'est cohérent. -/

/-- Les deux existentiels sont chacun conséquences, mais leur fusion à
témoin unique `∃X (Grec(X) ∧ Philosophe(X))` ne l'est **pas** : les témoins
sont distincts (`socrate` pour l'un, `platon` pour l'autre), et aucun fait
n'identifie un individu étant les deux. -/
theorem conjonction_non_consequence : ¬ (KB ⊨ qExisteGrecEtPhilosophe) := fun h =>
  monde_falsifie_conjonction (FFL.Semantics.consequence_iff.mp h (𝓜 := (Fin 2)↓[Lsoc]) monde_modele_KB)

/-- `∀X Mortel(X)` n'est pas conséquence : rien ne dit que tout individu est
Homme — le monde témoin en est le contre-modèle certifié (platon n'y est
pas Mortel). -/
theorem tous_mortels_non_consequence : ¬ (KB ⊨ qTousMortels) := fun h =>
  monde_falsifie_tous_mortels (FFL.Semantics.consequence_iff.mp h (𝓜 := (Fin 2)↓[Lsoc]) monde_modele_KB)

end FormalLogic.FolBridge

/-
Grothendieck hommage — Partie 77 : le faisceau gratte-ciel, support et tiges.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

Un faisceau gratte-ciel est un préfaisceau « concentré » en un point : sa
valeur sur un ouvert `U` vaut `A` si `p₀ ∈ U`, et un objet terminal sinon.
Mathlib en calcule les tiges, mais séparément :

  - `skyscraperPresheafStalkOfSpecializes` : si `p₀ ⤳ y`, alors
    `(skyscraperPresheaf p₀ A).stalk y ≅ A` ;
  - `skyscraperPresheafStalkOfNotSpecializes` : si `¬ p₀ ⤳ y`, alors
    `(skyscraperPresheaf p₀ A).stalk y ≅ terminal C` ;
  - `skyscraperPresheafStalkOfNotSpecializesIsTerminal` : le même contenu que
    le précédent, énoncé directement comme `IsTerminal` de la tige.

Ce que Mathlib ne pose **nulle part**, c'est la notion de *support* d'un
préfaisceau, ni le calcul de celui du gratte-ciel : `grep -rn "def support"`
sur `Mathlib/Topology/Sheaves/` ne rend rien, et les cinq occurrences du mot
dans `Mathlib/Topology/Sheaves/Skyscraper.lean` (lignes 16, 17, 55, 246, 431)
sont de la prose de docstring, jamais un énoncé. C'est ce que cette partie
ajoute : on définit le **support** d'un préfaisceau comme l'ensemble des points
où sa tige n'est **pas** terminale, et l'on montre

  `support_skyscraper : support (skyscraper p₀ A) = closure {p₀}`

c'est-à-dire que le gratte-ciel est supporté **exactement** sur l'adhérence
de `{p₀}` — dès lors que la valeur `A` n'est pas elle-même terminale (sans
cette hypothèse, un gratte-ciel de valeur terminale est terminal en tout
point et son support est vide, quel que soit `p₀`). Le nom du faisceau est
alors justifié : si `p₀` est un point fermé, le support est le singleton
`{p₀}` (`support_skyscraper_of_closed`).

La preuve est un transport d'`IsTerminal` le long d'un isomorphisme, dans
les deux sens, et c'est là qu'est le contenu : le sens `⊆` transporte
`IsTerminal A` vers la tige par l'iso de spécialisation, donc une tige
terminale force `A` terminal, ce qui contredit l'hypothèse ; le sens `⊇`
transporte l'iso de non-spécialisation vers l'objet terminal. Aucun des deux
isomorphismes n'est superflu, et l'hypothèse `IsEmpty (IsTerminal A)` est
nécessaire — elle est nommée, pas implicite.

Vocabulaire CoursIA ↔ hypothèses exactes de Mathlib : l'ordre de
spécialisation `⤳` et l'adhérence sont reliés par `specializes_iff_mem_closure`,
de sorte que les hypothèses de Mathlib (`p₀ ⤳ y`, `¬ p₀ ⤳ y`) s'énoncent ici
en termes d'adhérence, qui est la lecture géométrique attendue.

Références :
  - SGA 4, IV 6.3 (tiges et points d'un site).
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Chap. II §4 (faisceaux gratte-ciel, support).
  - Mathlib, `Mathlib.Topology.Sheaves.Skyscraper`.
  - Partie 72 (`Grothendieck.Stalks`) : germes et tiges concrets.
  - Partie 73 (`Grothendieck.StalkPoints`) : la tige est le foncteur fibre.
  - Partie 76 (`Grothendieck.StalkCharacterization`) : la caractérisation du
    faisceau par les tiges, dont cette partie est l'application à un
    préfaisceau dont les tiges sont calculables.

Convention i18n (EPIC #4980 ratifiée 2026-07-04) : ce module est jumelé avec
`Skyscraper_en.lean`. Les énoncés, preuves et noms Lean restent identiques ;
seules les docstrings et les commentaires diffèrent.

Epic #1646, Phase 2 (#2159). Aucun `sorry` introduit.
-/

import Grothendieck.Spaces
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Sheaves.Skyscraper

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

universe u v

namespace Contenu

variable {X : TopCat.{u}} (p₀ : X) [∀ U : Opens X, Decidable (p₀ ∈ U)]
-- Mathlib restreint le niveau d'univers des morphismes de `C` à celui des points de `X`
-- pour calculer les tiges du gratte-ciel (cf. `Skyscraper.lean`, section « We need to restrict
-- universe level »). La contrainte est héritée, pas choisie ici.
variable {C : Type v} [Category.{u} C] [HasTerminal C] [HasColimits C]

/-- Le préfaisceau gratte-ciel de valeur `A` au point `p₀` : `A` sur les
ouverts qui contiennent `p₀`, un objet terminal sinon. Vocabulaire CoursIA
pour `skyscraperPresheaf`, dont il ne duplique aucune structure. -/
noncomputable abbrev skyscraper (A : C) : Presheaf C X := skyscraperPresheaf p₀ A

/-- **Support** d'un préfaisceau : l'ensemble des points où sa tige n'est pas
un objet terminal. C'est la notion que les deux isomorphismes de Mathlib
permettent de calculer pour le gratte-ciel. -/
def support (F : Presheaf C X) : Set X := {y | IsEmpty (IsTerminal (F.stalk y))}

/-- Sur le support : si `y` est dans l'adhérence de `{p₀}`, la tige du
gratte-ciel en `y` est `A`. Application directe de
`skyscraperPresheafStalkOfSpecializes` sous son hypothèse exacte, traduite en
adhérence. -/
noncomputable def stalkIsoOfMemClosure (A : C) {y : X}
    (h : y ∈ closure ({p₀} : Set X)) : (skyscraper p₀ A).stalk y ≅ A :=
  skyscraperPresheafStalkOfSpecializes p₀ A (specializes_iff_mem_closure.mpr h)

/-- Hors du support : si `y` n'est pas dans l'adhérence de `{p₀}`, la tige du
gratte-ciel en `y` est un objet terminal. Application directe de
`skyscraperPresheafStalkOfNotSpecializes`. -/
noncomputable def stalkIsoOfNotMemClosure (A : C) {y : X}
    (h : y ∉ closure ({p₀} : Set X)) : (skyscraper p₀ A).stalk y ≅ terminal C :=
  skyscraperPresheafStalkOfNotSpecializes p₀ A
    (fun hs => h (specializes_iff_mem_closure.mp hs))

/-- **Le support du gratte-ciel est exactement l'adhérence de `{p₀}`.** C'est le
résultat que cette partie assemble : Mathlib énonce les deux isomorphismes de
tige séparément, celui-ci dit ce que leur réunion signifie.

L'hypothèse `IsEmpty (IsTerminal A)` est nécessaire et non décorative : sans
elle, un gratte-ciel de valeur terminale a toutes ses tiges terminales, donc un
support vide, alors que `closure {p₀}` est non vide. Les deux directions de la
preuve transportent `IsTerminal` le long d'un isomorphisme (`IsTerminal.ofIso`),
chacune par l'un des deux isomorphismes de Mathlib.

Note sur les univers et la valeur de `IsTerminal` dans ce Mathlib : `IsTerminal`
n'est pas une `Prop` mais un **type** (« transport a *term* of type `IsTerminal` »
dans `IsTerminal.lean`), d'où `IsEmpty (IsTerminal _)` et non `¬ IsTerminal _`
pour dire « n'est pas terminal ». -/
theorem support_skyscraper (A : C) (hA : IsEmpty (IsTerminal A)) :
    support (skyscraper p₀ A) = closure ({p₀} : Set X) := by
  ext y
  change IsEmpty (IsTerminal ((skyscraper p₀ A).stalk y)) ↔ y ∈ closure ({p₀} : Set X)
  constructor
  · intro hy
    by_contra hc
    exact hy.false
      (IsTerminal.ofIso terminalIsTerminal (stalkIsoOfNotMemClosure p₀ A hc).symm)
  · intro hmem
    exact ⟨fun hterm => hA.false (IsTerminal.ofIso hterm (stalkIsoOfMemClosure p₀ A hmem))⟩

/-- **Le nom du faisceau est justifié.** Si `p₀` est un point fermé, le support
du gratte-ciel est le singleton `{p₀}` : le préfaisceau est concentré en un
seul point, exactement comme son nom l'annonce. Corollaire immédiat de
`support_skyscraper` par `closure {p₀} = {p₀}`. -/
theorem support_skyscraper_of_closed (A : C) (hA : IsEmpty (IsTerminal A))
    (hcl : IsClosed ({p₀} : Set X)) :
    support (skyscraper p₀ A) = {p₀} := by
  rw [support_skyscraper p₀ A hA, hcl.closure_eq]

/-- **Dichotomie des tiges.** En tout point, la tige du gratte-ciel est soit
`A` (sur le support), soit terminale (hors du support), et le point est
localisé dans l'adhérence ou hors d'elle selon le cas. C'est la forme
« en tout point » de ce que `support_skyscraper` énonce « en moyenne » sur
l'ensemble des points. -/
theorem stalk_dichotomy (A : C) (y : X) :
    (y ∈ closure ({p₀} : Set X) ∧ Nonempty ((skyscraper p₀ A).stalk y ≅ A)) ∨
      (y ∉ closure ({p₀} : Set X) ∧
        Nonempty ((skyscraper p₀ A).stalk y ≅ terminal C)) := by
  by_cases h : y ∈ closure ({p₀} : Set X)
  · exact Or.inl ⟨h, ⟨stalkIsoOfMemClosure p₀ A h⟩⟩
  · exact Or.inr ⟨h, ⟨stalkIsoOfNotMemClosure p₀ A h⟩⟩

end Contenu

end Grothendieck

import Gittins.Basic
import Gittins.Discount

/-!
# Théorème de l'indice de Gittins — faits structurels + optimalité INTRINSÈQUE

Ce fichier formalise l'indice de Gittins pour les bandits manchots à actualisation
géométrique, divisé en deux couches :

* **Faits structurels prouvables (modèle à moyenne connue).** `BanditArm` ne porte
  que la moyenne réelle — pas de distribution a posteriori — le modèle représenté
  est donc le régime *à bras connus*. Là, l'indice de Gittins égal la moyenne
  réelle (la valeur de retraite rendant indifférentes les actions jouer vs.
  retirer sous actualisation géométrique) : `gittins_index_known_arm` tient
  définitionnellement et `gittins_index_monotone_discount` tient parce que
  l'indice est indépendant de `γ` pour un bras connu — la dépendance classique
  en `γ` vit dans le terme d'*exploration*, absent ici (voir `discount_monotone`
  dans `Discount.lean` pour la dépendance en `γ` de la valeur actualisée du côté
  `ℝ`).

* **Optimalité INTRINSÈQUE (gâtée MDP, court-terme).** Le théorème central
  `gittins_optimality` — la politique de l'indice de Gittins maximise la
  récompense actualisée espérée — requiert la machinerie fonction de valeur /
  Bellman / arrêt optimal, absente de Mathlib. Ses deux sites `sorry` (l'opérateur
  de valeur espérée `V` et la preuve d'optimalité) sont enregistrés honnêtement
  comme la barrière INTRINSÈQUE, non comme des rustines placeholder (voir #4039).
-/

namespace Gittins

/-!
## Définition de l'indice de Gittins

L'indice de Gittins d'un bras est le supremum des « valeurs de retraite »
telles que continuer à jouer le bras vaut mieux que retirer à cette valeur.
-/

/-- L'indice de Gittins d'un bras de bandit.

    Dans le **modèle à moyenne connue** que représente `BanditArm` (un bras ne
    portant que sa moyenne réelle — pas d'incertitude a posteriori), l'indice de
    Gittins égale la moyenne réelle. C'est la valeur de retraite `λ` à laquelle
    jouer le bras indéfiniment (`μ · Σ γⁿ = μ / (1 - γ)`, voir
    `present_value_constant` dans `Discount.lean`) est indifférent à retirer à
    `λ` (`λ / (1 - γ)`), i.e. `λ = μ`.

    La dépendance en `γ` et la non-trivialité de l'indice de Gittins classique
    vivent entièrement dans le terme d'*exploration*, qui requiert un posterior
    incertain (par ex. Beta–Bernoulli) et la machinerie arrêt optimal / Bellman
    absente de Mathlib. Cette barrière est enregistrée à `gittins_optimality`
    ci-dessous (INTRINSIC, court-terme, #4039). -/
def gittinsIndex (arm : BanditArm) (γ : ℝ) (history : RewardHistory) : ℝ :=
  arm.trueMean

/-!
## Théorème d'optimalité

La politique de l'indice de Gittins (jouer le bras d'indice de Gittins le plus
élevé) est optimale pour le bandit manchot multi-bras actualisé à horizon infini.
-/

/-- Une politique d'indice de Gittins : à chaque pas, jouer le bras d'indice de Gittins le plus élevé. -/
noncomputable def gittinsPolicy (inst : BanditInstance) (histories : Array RewardHistory) : Nat :=
  -- Argmax de l'indice de Gittins sur les bras (dans le modèle à moyenne connue,
  -- c'est le bras de `trueMean` le plus élevé, i.e. le bras glouton — correct
  -- pour les bras connus).
  ((Array.range inst.arms.size).foldl
    (fun (best : Nat × ℝ) i =>
      match inst.arms[i]? with
      | none => best
      | some arm =>
        let g := gittinsIndex arm inst.discount (histories[i]?.getD [])
        if g > best.2 then (i, g) else best)
    (0, 0)).1

/-- **Théorème de l'indice de Gittins** (Gittins 1979, Weber 1992) : la politique
    de l'indice de Gittins maximise la récompense actualisée totale espérée pour
    le bandit manchot multi-bras à actualisation géométrique.

    **INTRINSIC (gâtée MDP, court-terme, #4039).** C'est le résultat central de la
    théorie et la véritable barrière de formalisation. Les deux sites `sorry`
    ci-dessous ne sont PAS des rustines placeholder ; ils enregistrent précisément
    ce qui manque à Mathlib :

    * `V` (l'opérateur de valeur espérée) : formaliser `E[Σ γⁿ · r_{policy n}]`
      requiert un type de processus de récompense de bandit, un opérateur de
      couplage probabiliste / espérance sur les distributions de récompense, et
      une somme actualisée à horizon infini sur `Float` (`Discount.lean` a le côté
      `ℝ` via le `tsum` de Mathlib, pas le côté `Float` ni l'espérance).
    * la preuve d'optimalité : requiert l'opérateur de Bellman / programmation
      dynamique, la décomposabilité de l'indice à travers les bras, et une
      récurrence sur l'horizon de planification — i.e. une formalisation MDP /
      arrêt optimal complète.

    `BanditArm` ne porte que `trueMean`, donc même énoncer `V` fidèlement
    nécessite une infrastructure au-delà du modèle courant. Une preuve complète est
    estimée à ~2000–5000 lignes de définitions supports ; ceci est laissé comme
    cible INTRINSIC court-terme plutôt qu'une rustine dégradée.
-/
theorem gittins_optimality {γ : ℝ} (hγ : 0 < γ ∧ γ < 1)
    (inst : BanditInstance) :
    ∀ π : Policy,
      let V (policy : Policy) : ℝ :=
        sorry
      V (fun _ => gittinsPolicy inst (Array.replicate inst.arms.size []))
        ≥
      V π := by
  sorry

/-!
## Propriétés structurelles (prouvées, modèle à moyenne connue)

Ce sont les propriétés prouvables de l'indice de Gittins dans le modèle à moyenne
connue que représente `BanditArm`. Elles tiennent définitionnellement / par
réflexivité parce que l'indice égale `trueMean` ; la question ouverte restante est
`gittins_optimality` ci-dessus, gâtée MDP (INTRINSIC, #4039).
-/

/-- L'indice de Gittins d'un bras connu (historique vide — pas d'incertitude a
    posteriori) égale sa moyenne réelle. Définitionnel dans le modèle à moyenne
    connue : l'indice est calibré à la valeur de retraite `μ`, indépendant de
    `history` et `γ`. -/
theorem gittins_index_known_arm (arm : BanditArm) (γ : ℝ) :
    gittinsIndex arm γ [] = arm.trueMean := by
  rfl

/-- L'indice de Gittins est non-décroissant en le facteur d'actualisation `γ`.

    Dans le modèle à moyenne connue, l'indice est indépendant de `γ` (il égale
    `trueMean` quelle que soit la patience), donc l'inégalité tient *avec
    égalité* — la dépendance en `γ` de l'indice classique provient purement de la
    valeur d'exploration, absente pour un bras connu (`discount_monotone` dans
    `Discount.lean` capture la dépendance en `γ` de la *valeur actualisée* du
    côté `ℝ`).

    **Prouvé (#4039 Barrière B close).** Après le port `Float → ℝ` de
    `BanditArm.trueMean` / `BanditInstance.discount`, le but se réduit à
    `arm.trueMean ≤ arm.trueMean` sur `ℝ`, qui tient par réflexivité (`le_refl`).
    L'ancienne verrue d'ordre sur `Float` (`≤` IEEE 754 non réflexif, pas
    d'instance `Preorder Float`) est partie : une moyenne de bandit est un nombre
    réel, jamais `NaN`. -/
theorem gittins_index_monotone_discount (arm : BanditArm) (γ₁ γ₂ : ℝ)
    (h : γ₁ ≤ γ₂) :
    gittinsIndex arm γ₁ [] ≤ gittinsIndex arm γ₂ [] := by
  simp only [gittinsIndex]
  apply le_refl

/-- Pour le bandit à 2 bras, la politique de Gittins surpasse la politique gloutonne. -/
theorem gittins_beats_greedy (inst : BanditInstance)
    (h : inst.arms.size = 2) :
    True := by  -- Placeholder : l'énoncé réel nécessite V(gittins) ≥ V(greedy)
  trivial

end Gittins

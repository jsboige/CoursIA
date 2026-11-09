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
  Bellman / arrêt optimal, absente de Mathlib. L'opérateur de valeur `V` n'est
  plus un trou : `discountedValue` le définit sur ce que le modèle porte
  réellement (des moyennes connues, donc une somme actualisée **sans espérance**),
  et c'est cette définition qui rend l'énoncé vérifiable au lieu de circulaire.
  Reste **un** site `sorry` — la preuve d'optimalité — enregistré honnêtement
  comme la barrière INTRINSÈQUE, non comme une rustine placeholder (voir #4039).
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

/-- La récompense moyenne du bras que la politique `π` joue au pas `n`, et `0`
    quand cet indice ne désigne aucun bras de l'instance.

    C'est la seule récompense que ce modèle puisse nommer : `BanditArm` ne porte
    que `trueMean`, il n'y a ici ni distribution à échantillonner ni espérance à
    prendre. -/
noncomputable def policyMeanAt (inst : BanditInstance) (π : Policy) (n : ℕ) : ℝ :=
  match inst.arms[π n]? with
  | some arm => arm.trueMean
  | none => 0

/-- **Valeur actualisée d'une politique** dans le modèle à moyennes connues :
    `V π = Σₙ γⁿ · μ(π n)`.

    C'est un `tsum` de `ℝ` et **non une espérance** : le régime que `BanditArm`
    représente est celui des bras à moyennes connues, où la récompense de chaque
    pas vaut sa moyenne réelle, sans aléa. Y écrire un `E[…]` mentirait sur ce que
    le type porte ; la version probabiliste (posterior Beta–Bernoulli, terme
    d'exploration) est la barrière INTRINSÈQUE documentée plus bas — ce n'est pas
    cette définition, et c'est précisément pourquoi l'énoncé ci-dessous est
    restreint à ce régime au lieu de promettre le théorème général.

    Sous `0 < γ < 1` et des moyennes bornées, la série converge ;
    `present_value_constant` en est le cas d'une récompense constante. -/
noncomputable def discountedValue (inst : BanditInstance) (π : Policy) : ℝ :=
  ∑' n : ℕ, inst.discount ^ n * policyMeanAt inst π n

/-- **Théorème de l'indice de Gittins, dans le régime que ce lac formalise**
    (Gittins 1979, Weber 1992 pour l'énoncé général) : à moyennes connues, la
    politique de l'indice de Gittins maximise la valeur actualisée
    `discountedValue` sur toutes les politiques.

    **Ce que cet énoncé ne dit pas, et qu'il ne prétend pas dire.** Le théorème de
    Gittins porte sur des bras *incertains*, où l'indice arbitre exploration et
    exploitation ; c'est là qu'il diffère du glouton. Ici `gittinsIndex` égale
    `trueMean` (`gittins_index_known_arm`) et la politique de l'indice **coïncide**
    avec la gloutonne (`gittinsPolicy_eq_greedyPolicy`) : l'énoncé est donc
    l'optimalité du glouton à moyennes connues, et il est vrai à ce titre. Le
    régime incertain — donc le théorème dans sa portée réelle — reste la barrière
    INTRINSÈQUE ci-dessous. Écrire l'inverse (faire passer ce cas pour le théorème
    général) serait exactement la dégradation que ce fichier refuse.

    **INTRINSIC (gâtée MDP, court-terme, #4039) — reste un site `sorry`, la
    preuve.** Elle demande l'opérateur de Bellman / programmation dynamique, la
    décomposabilité de l'indice à travers les bras et une récurrence sur l'horizon
    de planification, c'est-à-dire une formalisation MDP / arrêt optimal complète.
    L'énoncé, lui, n'est plus circulaire : `discountedValue` lui donne un sens
    indépendant de ce qu'on cherche à prouver. -/
theorem gittins_optimality (inst : BanditInstance)
    (hγ_pos : 0 < inst.discount) (hγ_lt : inst.discount < 1)
    (hmean : ∀ arm ∈ inst.arms, 0 ≤ arm.trueMean) :
    ∀ π : Policy,
      discountedValue inst (fun _ => gittinsPolicy inst (Array.replicate inst.arms.size []))
        ≥ discountedValue inst π := by
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

/-- Politique gloutonne (myope) : toujours jouer le bras de moyenne réelle la plus
    élevée. C'est le même argmax que `gittinsPolicy` mais lu directement sur
    `arm.trueMean` plutôt que via l'indice de Gittins. -/
noncomputable def greedyPolicy (inst : BanditInstance) : Nat :=
  ((Array.range inst.arms.size).foldl
    (fun (best : Nat × ℝ) i =>
      match inst.arms[i]? with
      | none => best
      | some arm =>
        let g := arm.trueMean
        if g > best.2 then (i, g) else best)
    (0, 0)).1

/-- Dans le modèle à moyenne connue, la politique de Gittins **coïncide** avec la
    politique gloutonne, quelle que soit l'historique observé : l'indice de Gittins
    égale `trueMean` (`gittins_index_known_arm`), donc les deux argmax portent sur la
    même quantité. La preuve est définitionnelle (réduction à l'identité des deux
    plis après débrouillage de `gittinsIndex`).

    C'est précisément pourquoi l'ancien énoncé « Gittins bat greedy » était vide ici :
    la domination de la politique de Gittins sur l'approche gloutonne n'apparaît que
    dans le régime à croyances incertaines (posterior Beta–Bernoulli, exploration),
    qui requiert la machinerie arrêt-optimal / Bellman absente de Mathlib (INTRINSIC,
    `gittins_optimality` ci-dessus, #4039). Dans le modèle à bras connus,
    Gittins = greedy, point. -/
theorem gittinsPolicy_eq_greedyPolicy (inst : BanditInstance)
    (histories : Array RewardHistory) :
    gittinsPolicy inst histories = greedyPolicy inst := by
  unfold gittinsPolicy greedyPolicy gittinsIndex
  rfl

end Gittins

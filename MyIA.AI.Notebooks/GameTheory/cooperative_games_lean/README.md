# Cooperative Games Lean

Formalisation en Lean 4 de la théorie des jeux coopératifs (valeur de Shapley, cœur).

## Statut

- **Toolchain** : v4.30.0-rc2
- **Compte de sorry** : **0** — le théorème de Bondareva-Shapley est prouvé dans les deux directions
- **Build** : `lake build CooperativeGames` — SUCCESS
- **Dépendances** : Mathlib4

## Modules

| Fichier | sorry | Description |
|---------|-------|-------------|
| `CooperativeGames/Shapley.lean` | 0 | Valeur de Shapley (définition + unicité), joueurs nul/dummy, indice de pouvoir de Banzhaf |
| `CooperativeGames/Basic.lean` | 0 | Jeu coopératif / fonction caractéristique / Cœur / théorème de Bondareva-Shapley |
| `CooperativeGames/ConeKernel.lean` | 0 | Noyau Farkas / séparation de cône (machinerie prouvant la direction backward) |

## Résultats clés

- **Unicité de la valeur de Shapley** : prouvé que la valeur de Shapley est l'unique valeur satisfaisant les axiomes d'efficacité, symétrie, joueur nul et additivité (Shapley.lean, 0 sorry)
- **Définitions du Cœur** : jeu coopératif, fonction caractéristique, ensemble des joueurs, Cœur (Basic.lean)
- **Direction `←` de Bondareva-Shapley** (balanced ⇒ Cœur non vide) : **entièrement prouvée** via la machinerie de séparation de cône du module `ConeKernel.lean` (`ProperCone.hyperplane_separation_point` de Mathlib)
- **Indice de pouvoir de Banzhaf** : cadre défini (`Critical G i S`, `BanzhafRaw G i` — nombre de coalitions pour lesquelles `i` est critique) avec le théorème `dummy_banzhaf_raw_zero` : un joueur dummy (qui ne change jamais la valeur de coalition) a un indice de Banzhaf brut nul (Shapley.lean, 0 sorry, PR #4011)

## Indice de pouvoir de Banzhaf

La valeur de Shapley n'est pas le seul indice de pouvoir pertinent en théorie des jeux
coopératifs. L'**indice de Banzhaf** mesure le pouvoir d'un joueur comme son nombre de
*swings* (coalitions pivots) : combinaisons où son passage de hors-coalition à
dans-coalition fait basculer la valeur de la coalition. Contrairement à la valeur de
Shapley (qui pondère chaque coalition par un facteur factoriel), l'indice de Banzhaf brut
traite toutes les coalitions de manière égale.

Le module formalise ce cadre sur les jeux à valeur pondérée (`WeightedVotingGame`) :

- **Joueur critique** — `Critical G i S` est vraie lorsque `i ∈ S`, la coalition `S` gagne
  (`G.v S = 1`) mais la coalition privée de `i` perd (`G.v (S.erase i) = 0`). Un joueur est
  critique pour `S` si son retrait fait perdre une coalition gagnante.
- **Indice de Banzhaf brut** — `BanzhafRaw G i` est le nombre de coalitions pour lesquelles
  `i` est critique, i.e. `(Finset.univ.filter fun S => Critical G i S).card`.

Deux théorèmes de nullité sont prouvés (les deux à 0 `sorry`) :

- `dummy_shapley_zero` : un joueur dummy reçoit une valeur de Shapley nulle.
- `dummy_banzhaf_raw_zero` (PR #4011) : un joueur dummy a un indice de Banzhaf brut nul.

Un joueur dummy (`DummyPlayer`) ne change jamais la valeur d'une coalition, il n'est donc
jamais critique : son indice de Banzhaf brut est bien nul. C'est l'analogue, pour l'indice
de Banzhaf, du théorème de joueur nul pour la valeur de Shapley.

**Prouvé** (PR #4037, merged `ba3b169e`) : le théorème de symétrie `banzhaf_raw_symmetric`
(`Shapley.lean:1106`) — deux joueurs interchangeables (`SymmetricPlayers`) ont des indices
de Banzhaf brut égaux, l'analogue Banzhaf de `shapley_symmetric`. La preuve construit une
involution `banzhafSwap` échangeant `i` et `j` dans chaque coalition (quatre cas : contient
les deux, aucun, ou exactement un des deux), montre qu'elle préserve la valeur du jeu (par
`SymmetricPlayers`, après division en cas sur `S ∩ {i, j}`) et qu'elle transporte
bijectivement les coalitions critiques de `i` sur celles de `j` ; les deux filtres de
coalitions critiques sont donc en bijection, d'où l'égalité de leurs cardinaux — les indices
de Banzhaf bruts. Cette lignée power-index (`dummy_banzhaf_raw_zero` #4011 →
`banzhaf_raw_symmetric` #4037) parallèle la caractérisation Shapley.

## Notes

- Le théorème de Bondareva-Shapley est clos dans les deux directions (`forward` + `backward`), **0 sorry**. La direction `←` extrayait une allocation du Cœur par un argument de Farkas / séparation d'hyperplan sur un cône ; cet argument, longtemps tagué **INTRACTABLE**, est désormais construit et prouvé dans `CooperativeGames/ConeKernel.lean` (cône augmenté `augCone`, lemme dual `augCone_dual_iff`, séparateur `separatingFunctional_none_neg`, décodage du témoin `exists_preimputation_strict_core`)
- Arc de preuve : PR #3933 (noyau ConeKernel, TUGame-free) → #3941 (pont `balancedUnit`) → #3945 (cœur du décodage) → #3951 (câblage du pipeline) → #3954 (sorry 1→0). `hb_witness` est désormais un `have` certifié (`Basic.lean:348`)
- Lié à `stable_marriage_lean/` (théorie des appariements comme jeu coopératif)

## Conclusion

Ce projet formalise la théorie des jeux coopératifs en Lean 4 — la **valeur de Shapley**
(close, 0 `sorry`) et le **Cœur** avec le **théorème de Bondareva-Shapley** (0 `sorry`,
prouvé dans les deux directions). Il compile avec `lake build CooperativeGames` sur
Mathlib4 (toolchain `v4.30.0-rc2`).

### Ce qui est prouvé

- **Unicité de la valeur de Shapley** (`Shapley.lean`, 0 `sorry`) : la valeur de Shapley
  est l'allocation *unique* satisfaisant efficacité, symétrie, joueur nul et additivité —
  la caractérisation axiomatique de Shapley (1953).
- **Indices de pouvoir et joueurs dummy** (`Shapley.lean`, 0 `sorry`) : en plus de la
  caractérisation de la valeur de Shapley, le module formalise la notion de joueur nul/dummy
  (`NullPlayer`, `DummyPlayer`) avec les deux théorèmes de nullité `dummy_shapley_zero`
  (un joueur dummy reçoit une valeur de Shapley nulle) et `dummy_banzhaf_raw_zero`
  (un joueur dummy a un indice de Banzhaf brut nul). Le cadre Banzhaf repose sur la
  définition `Critical G i S` (le joueur `i` est critique pour la coalition `S` lorsque
  `i ∈ S`, `G.v S = 1` mais `G.v (S.erase i) = 0`) et sur l'indice brut
  `BanzhafRaw G i` qui compte les coalitions critiques via un filtre sur `Finset.univ`
  (PR #4011). L'**indice de Banzhaf normalisé** `BanzhafIndex G i = BanzhafRaw G i / 2^(n-1)`
  (probabilité que `i` soit pivot dans une coalition contenant `i` tirée uniformément) hérite
  des deux propriétés clés : `banzhaf_index_symmetric` (joueurs interchangeables ⟹ indices
  normalisés égaux, analogue de `shapley_symmetric`) et `banzhaf_index_dummy_zero` (joueur
  dummy ⟹ indice normalisé nul).
- **Cœur + théorème de Bondareva-Shapley** (`Basic.lean` + `ConeKernel.lean`) : jeu
  coopératif, fonction caractéristique, le Cœur et la condition de jeu équilibré (balanced),
  avec la direction `←` (balanced ⇒ Cœur non vide) **entièrement prouvée** par séparation de
  cône.

### Comment la direction backward a été prouvée

L'étape jadis taggée **INTRACTABLE** — extraire de la condition équilibrée une allocation
`x ∈ Core` avec `∑ xᵢ ≤ v(N)`, un argument de Farkas / séparation d'hyperplan sur un cône —
est désormais close. La machinerie vit dans `CooperativeGames/ConeKernel.lean` : le cône
augmenté `augCone` encode les violations de poids équilibrés, et
`ProperCone.hyperplane_separation_point` (Mathlib `Analysis.Convex.Cone.Dual`) fournit un
séparateur `f` ; les lemmes de dualité (`augCone_dual_iff`), de séparateur non-négatif
(`separatingFunctional_none_neg`) et de décodage du témoin (`exists_preimputation_strict_core`)
convertissent ce séparateur en une imputation du Cœur. `hb_witness` est désormais un `have`
certifié (`Basic.lean:348`). Arc : #3933 → #3941 → #3945 → #3951 → #3954 (sorry 1→0). Le
plan d'origine reste documenté dans
[`docs/BONDAREVA_FARKAS_PLAN.md`](docs/BONDAREVA_FARKAS_PLAN.md).

### Où aller ensuite

- **Théorie** : Bondareva (1963) / Shapley (1967), les caractérisations du Cœur ;
  Shapley (1953), *A Value for n-Person Games*.
- **Plan actif** : [`docs/BONDAREVA_FARKAS_PLAN.md`](docs/BONDAREVA_FARKAS_PLAN.md)
  et [`FORMAL_STATUS.md`](FORMAL_STATUS.md).
- **Lié** : [`stable_marriage_lean/`](../stable_marriage_lean/) (appariement Gale-Shapley)
  et [`social_choice_lean/`](../social_choice_lean/) (Arrow / Sen).

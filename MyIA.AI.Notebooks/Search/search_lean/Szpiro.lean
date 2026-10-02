import Mathlib

/-!
# Szpiro — ancrage Mathlib des bornes de Pasten 2026 (hommage à Serre)

Sibling Lean du carnet
[`App-32-Szpiro-Pasten-2026.ipynb`](../Applications/Search/App-32-Szpiro-Pasten-2026.ipynb)
(issue #16549, option A) : Pasten 2026, *Improved Bounds for Szpiro's Conjecture*,
arXiv 2609.17390 (preprint, 261 Ko, archivé `Bibliographie IA\NumberTheory`).

## Ce que ce module fait — et ne fait pas

La hauteur de Faltings `h(E)` n'existe pas dans Mathlib : les énoncés de Pasten
ne sont donc **pas formellement prouvés ici** (aucun `sorry`, aucun axiome
ajouté — le présent fichier ne déclare que des objets et des faits vérifiés
mécaniquement). Les théorèmes du papier, cités en prose fidèle :

> **Théorème 1.1 (résultat principal).** Pour une courbe elliptique `E` sur ℚ,
> soit `N = DM` une factorisation **admissible** et `ℓ` un premier ne divisant
> pas `N`. Alors `h(E) ≪ M·φ(D)·log ℓ`, à constante absolue effective.
>
> **Corollaire 1.2.** Pour toute courbe elliptique `E` sur ℚ :
> `h(E) ≪ N·log log N` — inconditionnel (auparavant connu sous GRH, 2013 :
> `h(E) ≪ N·log N`).
>
> **Corollaire 1.3.** Pour `E` semistable hors d'un ensemble fini `S` de
> premiers : `h(E) ≪_S N`.

Le contexte conjectural (Szpiro `log Δ ≪ log N`, forme renforcée de Frey
`h(E) ≪ log N`, et `log Δ ≪ max{1, h(E)}`) est déroulé dans le carnet §1 ; la
démonstration passe par Jacquet–Langlands et les formes modulaires
quaternioniques — la tradition Serre (modularité, ℓ-adique) dont ce fichier
veut être une entrée d'hommage.

Ce que le module ancre dans Mathlib, en miroir du carnet :

- la **factorisation admissible** `N = DM` (définition du papier : `gcd(D,M) = 1`,
  `D` sans facteur carré, nombre **pair** de facteurs premiers — la parité vient
  du signe de l'espace de formes quaternioniques), vérifiée sur les exemples
  `N = 30` du carnet §2 (dont le contre-exemple de parité `D = 2`) ;
- l'**identité `M·φ(D) ≤ N`** (carnet §2, `borne_11`) : la quantité du
  théorème 1.1 ne dépasse jamais `N` — conséquence directe de `φ(D) ≤ D` ;
- le **discriminant de Weierstrass** de la courbe témoin `E : y² = x³ + x + 1`
  (carnet §3, première ligne du tableau) : `Δ = -496`, et `E` est non singulière.

Conventions numériques : `WeierstrassCurve.Δ` est le discriminant classique
complet (pour `y² = x³ + ax + b` de caractéristique ≠ 2, 3 :
`Δ = -16·(4a³ + 27b²)`, même convention que `delta_modele` du carnet).
-/

namespace Szpiro

/-- Factorisation admissible `N = D * M` au sens de Pasten 2026 (définition qui
précède le théorème 1.1) : `D` et `M` premiers entre eux, `D` sans facteur
carré, et `D` comptant un nombre **pair** de facteurs premiers. -/
def AdmissibleFactorization (D M : ℕ) : Prop :=
  D.gcd M = 1 ∧ Squarefree D ∧ Even D.primeFactorsList.length

/-- `N = 30 = 2·3·5` : la factorisation triviale (`D = 1`, zéro facteur premier
— zéro est pair) est admissible. Première ligne du tableau du carnet §2. -/
theorem admissible_trente_triviale : AdmissibleFactorization 1 30 := by decide

/-- `N = 30` : `D = 15 = 3·5` (deux facteurs premiers, pair) est admissible. -/
theorem admissible_trente_quinze : AdmissibleFactorization 15 2 := by decide

/-- Contre-exemple de parité du carnet §2 : `D = 2` a exactement **un** facteur
premier (impair), donc `30 = 2·15` n'est PAS admissible — bien que
`gcd(2, 15) = 1` et que `2` soit sans facteur carré. La contrainte de parité
porte seule l'exclusion. -/
theorem non_admissible_trente_deux : ¬AdmissibleFactorization 2 15 := by decide

/-- φ(15) = 8 : la valeur utilisée par le carnet §2 (`borne_11`) pour la
meilleure factorisation admissible de `N = 30`. -/
theorem phi_quinze : Nat.totient 15 = 8 := by decide

/-- Identité du carnet §2 : la quantité `M·φ(D)` du théorème 1.1 ne dépasse
jamais `N = D·M`, puisque `φ(D) ≤ D`. À constante absolue près, la borne
`h(E) ≪ M·φ(D)·log ℓ` est donc toujours au moins aussi fine que
`h(E) ≪ N·log ℓ`. -/
theorem borne_shape_le_N {D M N : ℕ} (h : N = D * M) :
    M * Nat.totient D ≤ N := by
  rw [h]
  calc M * Nat.totient D ≤ M * D :=
        Nat.mul_le_mul (Nat.le_refl M) (Nat.totient_le D)
    _ = D * M := Nat.mul_comm M D

section Courbe

/-- La courbe témoin du carnet §3 (première ligne du tableau) :
`E : y² = x³ + x + 1` sur ℚ, en coefficients de Weierstrass généraux
(`a₁ = a₂ = a₃ = 0`, `a₄ = a₆ = 1`). -/
def E : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 1
  a₆ := 1

/-- Le discriminant du modèle vaut `Δ = -496 = -16·(4·1³ + 27·1²)` : la valeur
imprimée par `delta_modele(1, 1)` dans le carnet §3 (même convention :
discriminant classique complet). -/
theorem delta_E : E.Δ = -496 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, E]
  norm_num

/-- `Δ ≠ 0`, donc la courbe `E` est non singulière — elliptique au sens de
`WeierstrassCurve.IsElliptic`. -/
theorem E_est_elliptique : E.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by rw [delta_E]; norm_num)⟩

end Courbe

end Szpiro

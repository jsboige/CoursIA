import Mathlib.Tactic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Sign

/-!
# Tables de caractères calculées par le noyau : l'orthogonalité de Schur vérifiée

Pendant kernel du notebook `05-table-de-caracteres.ipynb` (série *Serre 100*,
EPIC #16334 — voie de graduation « pendants kernel »). Le notebook *mesure* en
Python les tables de caractères de S₃ et S₄ (règle de Murnaghan–Nakayama) et
vérifie les deux familles d'orthogonalité de Schur ; ce module fait vérifier
les mêmes tables par le noyau Lean, et démontre les témoins indépendants du
notebook directement sur `Equiv.Perm`.

Plan, en miroir du notebook (§1 et §2) :

1. **Définitions** (`tableS3`, `taillesClassesS3`, `tableS4`,
   `taillesClassesS4`, `indiceClasseS3`, `indiceClasseS4`) — les tables sont
   les données du notebook, ligne par ligne ; l'indice de colonne d'une
   permutation se lit sur ses points fixes et sur `σ²`.
2. **Témoins sur `Equiv.Perm`** : la ligne signature de chaque table EST la
   signature de chaque permutation (égalité dans `ℤˣ`), et le caractère
   standard vaut points fixes − 1 — les « coincidences exactes » du notebook,
   prouvées sur tout le groupe et non plus observées sur les classes.
3. **Orthogonalité** : lignes (`∑ |C| χᵢ χⱼ = |G| δ`) et colonnes
   (`∑ χᵢ(C) χᵢ(C') = (|G|/|C|) δ`) pour S₃ et S₄, par le noyau.
4. **Degrés** : le lemme général `sommeCarresDegres` dérive `∑ d² = |G|` de
   l'orthogonalité des colonnes, puis s'instancia sur les deux tables ; les
   degrés de 2T (§3 du notebook, sept irréductibles) vérifient `∑ d² = 24`.

Hors périmètre (documenté) : la table de 2T vit sur ℚ(√−3) — ses valeurs non
rationnelles demandent un anneau de coefficients (`AdjoinRoot`, corps
cyclotomique) et attendent un pendant dédié ; la récurrence de
Murnaghan–Nakayama, elle, reste du côté Python du notebook.
-/

set_option autoImplicit false

namespace Serre100

/-! ## Définitions — les tables du notebook, comme données

Lignes = partitions (caractères), colonnes = classes de conjugaison.
S₃ : lignes `(3)`, `(2,1)`, `(1³)` sur les classes `1³` (taille 1), `2·1`
(taille 3), `3` (taille 2). S₄ : lignes `(4)`, `(3,1)`, `(2,2)`, `(2,1,1)`,
`(1⁴)` sur les classes de tailles 1, 6, 3, 8, 6.
-/

/-- Table de caractères de S₃ (notebook, cellule « table de S₃ ») :
lignes `(3)`, `(2,1)`, `(1³)` ; colonnes `1³`, `2·1`, `3`. -/
def tableS3 : Fin 3 → Fin 3 → ℤ :=
  ![![1, 1, 1], ![2, 0, -1], ![1, -1, 1]]

/-- Tailles des classes de conjugaison de S₃ : 1, 3, 2. -/
def taillesClassesS3 : Fin 3 → ℤ := ![1, 3, 2]

/-- Table de caractères de S₄ (notebook, cellule « table de S₄ ») :
lignes `(4)`, `(3,1)`, `(2,2)`, `(2,1,1)`, `(1⁴)` ; colonnes `1⁴`, `2·1²`,
`2²`, `3·1`, `4`. -/
def tableS4 : Fin 5 → Fin 5 → ℤ :=
  ![![1, 1, 1, 1, 1],
    ![3, 1, -1, 0, -1],
    ![2, 0, 2, -1, 0],
    ![3, -1, -1, 0, 1],
    ![1, -1, 1, 1, -1]]

/-- Tailles des classes de conjugaison de S₄ : 1, 6, 3, 8, 6. -/
def taillesClassesS4 : Fin 5 → ℤ := ![1, 6, 3, 8, 6]

/-- Nombre de points fixes d'une permutation de `Fin n` : les points fixes
sont les `x` tels que `σ x = x` (notebook, `points_fixes`). -/
def pointsFixes {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (fun x => σ x = x)).card

/-- Indice de la colonne de `σ` dans la table de S₃, lu sur ses points
fixes : 3 points fixes (identité), 1 (transposition), 0 (3-cycle). -/
def indiceClasseS3 (σ : Equiv.Perm (Fin 3)) : Fin 3 :=
  if pointsFixes σ = 3 then 0
  else if pointsFixes σ = 1 then 1
  else 2

/-- Indice de la colonne de `σ` dans la table de S₄, lu sur ses points fixes
et sur `σ²` : 4 points fixes (`1⁴`), 2 (`2·1²`), 1 (`3·1`) ; sans point fixe,
`σ² = 1` distingue le type `2²` du type `4`. -/
def indiceClasseS4 (σ : Equiv.Perm (Fin 4)) : Fin 5 :=
  if pointsFixes σ = 4 then 0
  else if pointsFixes σ = 2 then 1
  else if pointsFixes σ = 1 then 3
  else if σ * σ = 1 then 2
  else 4

/-! ## Témoins du notebook, démontrés sur `Equiv.Perm`

Le notebook vérifie ses tables contre des témoins indépendants (cellules
« Standard attendu (pf − 1) » et « Signe attendu (−1)^(n−cyc) ») ; le noyau
les prouve ici pour **chaque permutation**, la table étant lue à travers
`indiceClasse`. L'égalité de signature vit dans `ℤˣ` — le groupe d'arrivée
de `Equiv.Perm.sign` — sans coercison vers `ℤ`.
-/

/-- Ligne signature de S₃, comme valeurs dans `ℤˣ` (la ligne `(1³)` de la
table, relue dans le groupe d'arrivée de la signature). -/
def tableSigneS3 : Fin 3 → ℤˣ := ![1, -1, 1]

/-- Ligne signature de S₄, comme valeurs dans `ℤˣ` (la ligne `(1⁴)` de la
table). -/
def tableSigneS4 : Fin 5 → ℤˣ := ![1, -1, 1, 1, -1]

/-- Témoin signature de S₃ : la ligne `(1³)` de la table est la signature de
chaque permutation (6 éléments couverts par le noyau). -/
theorem temoinSigneS3 : ∀ σ : Equiv.Perm (Fin 3),
    Equiv.Perm.sign σ = tableSigneS3 (indiceClasseS3 σ) := by decide

/-- Témoin standard de S₃ : le caractère de la représentation standard
(ligne `(2,1)`) vaut points fixes − 1 sur chaque permutation. -/
theorem temoinStandardS3 : ∀ σ : Equiv.Perm (Fin 3),
    (pointsFixes σ : ℤ) - 1 = tableS3 1 (indiceClasseS3 σ) := by decide

/-- Témoin signature de S₄ : la ligne `(1⁴)` de la table est la signature de
chaque permutation (24 éléments couverts par le noyau). -/
theorem temoinSigneS4 : ∀ σ : Equiv.Perm (Fin 4),
    Equiv.Perm.sign σ = tableSigneS4 (indiceClasseS4 σ) := by decide

/-- Témoin standard de S₄ : la ligne `(3,1)` vaut points fixes − 1. -/
theorem temoinStandardS4 : ∀ σ : Equiv.Perm (Fin 4),
    (pointsFixes σ : ℤ) - 1 = tableS4 1 (indiceClasseS4 σ) := by decide

/-- Témoin twist de S₄ : la ligne `(2,1,1)` est le produit du caractère
standard par la ligne signature — l'exercice 3 du notebook, avant l'heure
(les deux facteurs sont relus dans la même table ; le second est la ligne
`(1⁴)`, égale à la signature par `temoinSigneS4`). -/
theorem temoinStandardSigneS4 : ∀ σ : Equiv.Perm (Fin 4),
    tableS4 3 (indiceClasseS4 σ)
      = ((pointsFixes σ : ℤ) - 1) * tableS4 4 (indiceClasseS4 σ) := by decide

/-! ## Orthogonalité de Schur — les deux familles, par le noyau

Lignes (notebook, cellule 8) : `∑_C |C| χᵢ(C) χⱼ(C) = |G| δᵢⱼ` — la table
est une famille orthonormée pour la forme pondérée par les tailles.
Colonnes : `∑ᵢ χᵢ(C) χᵢ(C') = (|G|/|C|) δ_CC'`.
-/

/-- Orthogonalité des lignes pour S₃ (6 paires couvertes, poids = tailles
de classes). -/
theorem orthogonaliteLignesS3 : ∀ i j : Fin 3,
    ∑ k, taillesClassesS3 k * tableS3 i k * tableS3 j k
      = if i = j then 6 else 0 := by decide

/-- Orthogonalité des colonnes pour S₃ (9 couples couverts). -/
theorem orthogonaliteColonnesS3 : ∀ j k : Fin 3,
    ∑ i, tableS3 i j * tableS3 i k
      = if j = k then 6 / taillesClassesS3 k else 0 := by decide

/-- Orthogonalité des lignes pour S₄ (15 paires du triangle supérieur et
de la diagonale, étendues à toutes les paires ordonnées). -/
theorem orthogonaliteLignesS4 : ∀ i j : Fin 5,
    ∑ k, taillesClassesS4 k * tableS4 i k * tableS4 j k
      = if i = j then 24 else 0 := by decide

/-- Orthogonalité des colonnes pour S₄ (25 couples couverts). -/
theorem orthogonaliteColonnesS4 : ∀ j k : Fin 5,
    ∑ i, tableS4 i j * tableS4 i k
      = if j = k then 24 / taillesClassesS4 k else 0 := by decide

/-! ## Degrés — une conséquence de l'orthogonalité des colonnes

Le notebook lit `∑ d² = |G|` comme un contrôle ; c'est en fait l'orthogonalité
des colonnes évaluée sur la classe du neutre (centralisateur 1). Le lemme
général ci-dessous le dérive une fois pour toute table, puis s'instancia.
-/

/-- Depuis l'orthogonalité des colonnes, la somme des carrés des degrés
(première colonne = classe du neutre, taille 1) vaut l'ordre du groupe. -/
theorem sommeCarresDegres {n : ℕ} [NeZero n] (T : Fin n → Fin n → ℤ) (G : ℤ) (c : Fin n → ℤ)
    (hcol : ∀ j k : Fin n, ∑ i, T i j * T i k = if j = k then G / c k else 0)
    (hc1 : c 0 = 1) : ∑ i, T i 0 * T i 0 = G := by
  simpa [hc1] using hcol 0 0

/-- Degrés de S₃ : `1 + 4 + 1 = 6 = |S₃|` — le contrôle de taille du
notebook, dérivé de l'orthogonalité. -/
example : ∑ i, tableS3 i 0 * tableS3 i 0 = 6 :=
  sommeCarresDegres tableS3 6 taillesClassesS3 orthogonaliteColonnesS3 rfl

/-- Degrés de S₄ : `1 + 9 + 4 + 9 + 1 = 24 = |S₄|` — le
`sum d^2 = 24` de la cellule 8 du notebook, dérivé et non plus observé. -/
example : ∑ i, tableS4 i 0 * tableS4 i 0 = 24 :=
  sommeCarresDegres tableS4 24 taillesClassesS4 orthogonaliteColonnesS4 rfl

/-- La colonne des transpositions : somme des carrés `4 = 24/6 = |G|/|C|` —
le dernier contrôle chiffré de la cellule 8 du notebook. -/
theorem carresTranspositionsS4 :
    ∑ i, tableS4 i 1 * tableS4 i 1 = 4 := by
  simpa [taillesClassesS4] using orthogonaliteColonnesS4 1 1

/-! ## Les degrés de 2T — sept irréductibles, sans la table

Le notebook (§3, cellule « la table complète 7×7 de 2T sur ℚ(√−3) ») obtient
les degrés de 2T (le groupe binaire tétraédrique, 24 éléments) : trois
linéaires (facteurs par C₃), trois twists du caractère naturel, et une
3-dim SO(3) — soit `1, 1, 1, 2, 2, 2, 3`. La table elle-même vit sur ℚ(√−3)
et attend un pendant dédié (cf. en-tête du module) ; la somme des carrés,
elle, est déjà un énoncé entier. -/

/-- Degrés des sept représentations irréductibles de 2T (notebook §3). -/
def degres2T : Fin 7 → ℤ := ![1, 1, 1, 2, 2, 2, 3]

/-- `1 + 1 + 1 + 4 + 4 + 4 + 9 = 24 = |2T|` : le contrôle de taille du
notebook, par le noyau. -/
example : ∑ i, degres2T i ^ 2 = 24 := by decide

end Serre100

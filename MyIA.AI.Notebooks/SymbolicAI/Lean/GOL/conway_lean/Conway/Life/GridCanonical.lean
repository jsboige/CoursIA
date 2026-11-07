/-
# Formes canoniques de grille — la spécification `sortDedup` (Conway)

Copyright (c) 2026 CoursIA. Tous droits réservés.
Distribué sous licence Apache 2.0 comme décrit dans le fichier LICENSE.
Version française mirrorée depuis l'anglais — voir les notes d'accessibilité
plus bas pour le rationale i18n.

## Formes canoniques de grille — la spécification `sortDedup`

Toute grille manipulée par le moteur Life est l'image d'un `sortDedup` :
`step`, `evolve (n+1)`, `shift` et `MacroCell.toGrid` se composent tous
à droite avec `sortDedup`, et `restrictGridTo` est un `filter` d'une telle
image. Ce module prouve que les sorties de `sortDedup` sont **canoniques**
— triées lexicographiquement et sans doublons — et que les listes
canoniques sont **rigides** : déterminées par leur seul prédicat
d'appartenance (`Canonical.ext`).

C'est le **pont** qui transforme les objectifs d'égalité de listes des
théorèmes de correction Hashlife (P4/P5, `HashlifeCorrectness.lean`) en
objectifs d'appartenance point par point, où la combinatoire réelle de la
règle B3/S23 et la récursion macrocell peuvent être argumentées cellule
par cellule.

La théorie de l'ordre est élémentaire : `lexLe` (la clôture réflexive de
`lexLt`) est totale, transitive et antisymétrique sur `Int × Int`, le tout
par `omega` après dépliage en arithmétique linéaire entière.

Ce module est **entièrement prouvé** (aucun `sorry`).

## Note d'accessibilité Epic #1452/#1453

Ce module héberge **13 theorem + 1 def** sur 4 sections, dédiées à la
canonicité structurelle de la grille (sans aucune sémantique runtime
Hashlife). Les tactiques mobilisées sont **arithmétiques et structurelles**
(`omega`, `unfold`, `simp only [...]`, `rw [mem_sortDedup]`, `split_ifs`,
`exact ⟨_, _⟩`) avec deux appels à `List.Pairwise.sublist` / `List.Nodup.sublist`
pour préserver la canonicité sous `filter`. C'est précisément la calibration
cible pour l'Epic #1453 : cible SOTA-OK où le harnais prouveur résout
proprement des lemmes de canonicité structurelle entre représentations de
listes équivalentes.

**Densité 2.371 thm/KB** (13 / 5483) — la plus élevée du sous-domaine
`conway_lein/Life/*` : densité record car la substance est *purement
canonique* (1 axiome par ~10 lignes de preuve structurée), avec une
définition de prédicat `Canonical` réutilisée par 6 theorem. C'est la
signature attendue d'un module de **canonicité structurelle** : un seul
concept (canonicité de liste) instancié sur les opérations fondamentales
du moteur Life (`step`, `evolve`, `shift`, `filter`).

**Satellite de N2 redesign arc EPIC #3846.** Ce module n'est pas sur le
chemin W3/W4 du cycle-break N2 lui-même (c'est `ConeGeometry` qui en est
W3, et `LightCone` qui en est le pont), mais il est **consommé** par
`HashlifeCorrectness.lean` pour transformer les objectifs d'égalité de
listes P4/P5 en objectifs d'appartenance cellulaire. La fermeture de
`hashlife_correct` (4 sorries à fermer dans `HashlifeCorrectness.lean`,
cf issue #5726) débloque l'éligibilité du Jeu de la Vie comme substrat
de stratification ICT (issue #5726, partie de l'EPIC #4588).

## Substance réelle — canonicité structurelle, 13 theorem + 1 def sur 4 sections

`GridCanonical.lean` héberge **13 theorem + 1 def** sur la **canonicité
de la grille** (lex-sortie + sans-doublons) maintenue par les opérations
fondamentales du moteur Life :

- `lexLt_iff` : **lexLt en arithmétique linéaire** — `lexLt a b = true ↔
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)` (par dépliage `lexLt` + `split_ifs`
  + `simp` + `omega`). Fait de base pour relier la définition opérationnelle
  `lexLt` à l'arithmétique linéaire des paires d'entiers.
- `lexLe_iff` : **lexLe en arithmétique linéaire** — `lexLe a b = true ↔
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)` (par `simp only [lexLe, Bool.or_eq_true,
  lexLt_iff, beq_iff_eq, Prod.ext_iff]` + `omega`). Fait jumeau du
  précédent, pour la clôture réflexive.
- `lexLe_total` : **lexLe total** — `(lexLe a b || lexLe b a) = true` (par
  `simp only [Bool.or_eq_true, lexLe_iff]` + `omega`). C'est l'hypothèse
  que `List.pairwise_insertionSort` exige sur son argument comparateur.
- `lexLe_trans` : **lexLe transitif** — `lexLe a c = true` depuis
  `lexLe a b = true` + `lexLe b c = true` (par `simp only [lexLe_iff] at *`
  + `omega`).
- `lexLe_antisymm` : **lexLe antisymétrique** — `lexLe a b = true` +
  `lexLe b a = true` ⇒ `a = b` (par `simp only [lexLe_iff] at *` + `rw
  [Prod.ext_iff]` + `omega`). Fait clef qui rend les listes lex-triées
  *rigides* : une permutation entre deux listes triées est l'identité.
- `Canonical` *(def)* : **prédicat de canonicité** sur `Grid` —
  `g.Pairwise (fun a b => lexLe a b = true) ∧ g.Nodup`. Définition
  *composite* (sortedness + no-duplicates) qui capture la rigidité.
- `canonical_sortDedup` : **`sortDedup` produit une grid canonique** —
  `Canonical (sortDedup l)` pour toute liste `l` (par dépliage `sortDedup`
  + `List.Pairwise.sublist (List.dedup_sublist _)` (depuis
  `pairwise_insertionSort` via instances locales `lexLe_trans` +
  `lexLe_total`) +
  `List.nodup_dedup _`). Le fait central : toute image `sortDedup` est
  canonique.
- `Canonical.filter` : **filter préserve la canonicité** — `Canonical
  (g.filter q)` depuis `Canonical g` (par `List.Pairwise.sublist
  List.filter_sublist` + `List.Nodup.sublist List.filter_sublist`). Fait
  technique pour les opérations de restriction (`restrictGridTo`).
- `Canonical.ext` : **rigidité des grilles canoniques** — deux grilles
  canoniques avec les mêmes membres sont **égales comme listes**
  (`g₁ = g₂`). La preuve : la même-appartenance donne une permutation
  (`List.perm_ext_iff_of_nodup` qui demande la no-dups), puis une
  permutation entre deux listes lex-triées est l'identité par
  antisymétrie (`List.Perm.eq_of_pairwise` utilisant `lexLe_antisymm`).
  C'est le fait **central** de ce module : la canonicité identifie
  listes et ensembles.
- `sortDedup_eq_sortDedup_iff` : **égalité iff ensembles égaux** — pour
  deux listes `l₁`, `l₂`, `sortDedup l₁ = sortDedup l₂ ↔ ∀ p, p ∈ l₁ ↔
  p ∈ l₂` (par `constructor` + `rw [← mem_sortDedup, h, mem_sortDedup]`
  pour forward + `Canonical.ext` pour backward). Le **workhorse** utilisé
  par P4/P5 de `HashlifeCorrectness.lean`.
- `canonical_step` : **`step` produit des grilles canoniques** — `Canonical
  (step g)` (par `canonical_sortDedup _`). Fait de préservation directe
  puisque `step g = sortDedup (candidates g.filter (aliveNext g))`.
- `canonical_evolve_of_pos` : **`evolve n` canonique pour `n ≥ 1`** —
  `Canonical (evolve n g)` (par `obtain ⟨m, rfl⟩ : ∃ m, n = m + 1` + `rw
  [evolve_succ]` + `canonical_step _`). Pour `n = 0`, `evolve 0 g = g`,
  qui n'a pas besoin d'être canonique.
- `canonical_shift` : **`shift` produit des grilles canoniques** —
  `Canonical (shift v g)` (par `canonical_sortDedup _`). Translation
  préserve la canonicité.
- `mem_step_iff` : **appartenance dans `step g` dépliée** — `p ∈ step g ↔
  p ∈ candidates g ∧ aliveNext g p = true` (par `unfold step` + `rw
  [mem_sortDedup, List.mem_filter]`). Fait de **désucrage** qui permet
  aux théorèmes P4/P5 de raisonner sur la règle B3/S23 elle-même
  plutôt que sur la machinerie `sortDedup`.

Le **fait central formalisé** dans ce module est donc la **canonicité
structurelle des grilles du moteur Life** : toute grille construite par
`sortDedup` est canonique (lex-sortie + sans-doublons), et les listes
canoniques sont **rigides** — déterminées par leur seul prédicat
d'appartenance. Cette rigidité est exactement ce qui permet aux
théorèmes P4/P5 de `HashlifeCorrectness.lean` de transformer leurs
objectifs d'égalité de listes en objectifs d'appartenance cellulaire
(où la combinatoire B3/S23 peut être argumentée cellule par cellule).

## Pont Mathlib + accessibilité Epic #1452

L'import est `Conway.Life` (le module parent qui agrège tous les
sous-modules Life). Sans `import Mathlib` direct — Mathlib est ré-importé
transitivement via la chaîne de lakes. Toutes les tactiques utilisées
(`omega`, `unfold`, `simp only [...]`, `rw [...]`, `split_ifs`,
`exact ⟨_, _⟩`, `List.Pairwise.sublist`, `List.Nodup.sublist`,
`List.perm_ext_iff_of_nodup`, `List.Perm.eq_of_pairwise`) sont des
**champs de structure canoniques Mathlib 4** sur `List` et `Int × Int`.
C'est la calibration SOTA-OK visée par l'Epic #1453 : cibles où le
harnais prouveur résout proprement des lemmes de canonicité structurelle
entre représentations de listes équivalentes.

Suit : hommage MathOverflow + Mathlib i18n convention #4980 ratifiée
2026-07-04 (option A pragmatique : deux blocs `/` top-level distincts,
sans séparateur `---` interne).
-/

/-
## Convention i18n (EPIC #4980, Option A)

Convention ratifiée par user 2026-07-04 (cf `code-style.md` §Lean i18n) :
fichier **FR canonique** + sibling **EN** dans `GridCanonical_en.lean`.
Seules les **docstrings `/-- ... -/`** et les **commentaires `-- ...`**
diffèrent entre les deux fichiers. **Préservation byte-identity** sur
le reste (signatures, preuves, tactiques) — vérifiable par diff.
Pas de bloc bilingue inline dans un même fichier (Option B rejeté).
-/

import Conway.Life

namespace Conway
namespace Life

/-! ## Le comparateur lexicographique : axiomes d'ordre -/

/-- `lexLt` en termes d'arithmétique linéaire sur les entiers. -/
theorem lexLt_iff {a b : Int × Int} :
    lexLt a b = true ↔ a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2) := by
  unfold lexLt
  split_ifs <;> simp <;> omega

/-- `lexLe` en termes d'arithmétique linéaire sur les entiers. -/
theorem lexLe_iff {a b : Int × Int} :
    lexLe a b = true ↔ a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2) := by
  simp only [lexLe, Bool.or_eq_true, lexLt_iff, beq_iff_eq, Prod.ext_iff]
  omega

/-- `lexLe` est total — l'hypothèse qu'exige `List.pairwise_insertionSort`. -/
theorem lexLe_total (a b : Int × Int) : (lexLe a b || lexLe b a) = true := by
  simp only [Bool.or_eq_true, lexLe_iff]
  omega

/-- `lexLe` est transitif. -/
theorem lexLe_trans (a b c : Int × Int)
    (hab : lexLe a b = true) (hbc : lexLe b c = true) : lexLe a c = true := by
  simp only [lexLe_iff] at *
  omega

/-- `lexLe` est antisymétrique — ce qui rend les listes triées Nodup rigides. -/
theorem lexLe_antisymm (a b : Int × Int)
    (hab : lexLe a b = true) (hba : lexLe b a = true) : a = b := by
  simp only [lexLe_iff] at hab hba
  rw [Prod.ext_iff]
  omega

/-- Instances de typeclass pour `lexLe`, pour que `List.pairwise_insertionSort`
    (qui exige `[Std.Total r] [IsTrans α r]`) synthétise automatiquement. -/
instance lexLe.isTrans : IsTrans (Int × Int) fun a b => lexLe a b = true :=
  ⟨fun _ _ _ hab hbc => lexLe_trans _ _ _ hab hbc⟩

instance lexLe.isTotal : Std.Total fun a b : Int × Int => lexLe a b = true :=
  ⟨fun a b => by
    have h : (lexLe a b || lexLe b a) = true := lexLe_total a b
    rw [Bool.or_eq_true_eq_eq_true_or_eq_true] at h
    exact h⟩

/-! ## Grilles canoniques -/

/-- Une grille sous forme canonique : triée lexicographiquement et sans
    doublon. Invariant de toute image de `sortDedup`, préservé par `filter`. -/
def Canonical (g : Grid) : Prop :=
  g.Pairwise (fun a b => lexLe a b = true) ∧ g.Nodup

/-- `sortDedup` produit toujours une grille canonique : le tri vient de
    `pairwise_insertionSort` (utilisant la totalité et la transitivité de
    `lexLe`) et survit à `dedup` car `dedup` produit une sous-liste ; l'absence
    de doublons est `nodup_dedup`.

    `insertionSort` (et non `mergeSort`) est utilisé dans `sortDedup` car le
    réducteur du noyau peut évaluer `List.insertionSort` sous `decide` alors que
    `List.mergeSort` reste bloqué (mesuré po-2026 c.786). Le lemme Mathlib
    `List.pairwise_insertionSort` est basé sur des typeclasses
    (`[Std.Total r]` `[IsTrans α r]`) ; nous déchargeons ces instances
    localement à partir de `lexLe_total` et `lexLe_trans`. -/
theorem canonical_sortDedup (l : List (Int × Int)) : Canonical (sortDedup l) := by
  unfold sortDedup
  have hsort : List.Pairwise (fun a b => lexLe a b = true)
      (List.insertionSort (fun a b => lexLe a b = true) l) :=
    List.pairwise_insertionSort _ l
  exact ⟨hsort.sublist (List.dedup_sublist _), List.nodup_dedup _⟩

/-- Le filtrage préserve la forme canonique (`filter` produit une sous-liste). -/
theorem Canonical.filter {g : Grid} (h : Canonical g) (q : (Int × Int) → Bool) :
    Canonical (g.filter q) :=
  ⟨List.Pairwise.sublist List.filter_sublist h.1,
   List.Nodup.sublist List.filter_sublist h.2⟩

/-- **Rigidité des grilles canoniques** : deux grilles canoniques avec les
    mêmes membres sont égales comme listes. La même-appartenance donne une
    permutation (`perm_ext_iff_of_nodup`), et une permutation entre deux listes
    lex-triées est l'identité par antisymétrie (`Perm.eq_of_pairwise`). -/
theorem Canonical.ext {g₁ g₂ : Grid} (h₁ : Canonical g₁) (h₂ : Canonical g₂)
    (h : ∀ p, p ∈ g₁ ↔ p ∈ g₂) : g₁ = g₂ :=
  List.Perm.eq_of_pairwise (fun a b _ _ hab hba => lexLe_antisymm a b hab hba)
    h₁.1 h₂.1 ((List.perm_ext_iff_of_nodup h₁.2 h₂.2).mpr h)

/-- Le corollaire workhorse : deux images `sortDedup` sont égales **ssi** leurs
    listes d'entrée ont les mêmes membres. L'égalité de listes des grilles
    canoniques est exactement l'égalité ensembliste. -/
theorem sortDedup_eq_sortDedup_iff {l₁ l₂ : List (Int × Int)} :
    sortDedup l₁ = sortDedup l₂ ↔ ∀ p, p ∈ l₁ ↔ p ∈ l₂ := by
  constructor
  · intro h p
    rw [← mem_sortDedup (l := l₁), h, mem_sortDedup]
  · intro h
    exact Canonical.ext (canonical_sortDedup _) (canonical_sortDedup _)
      (fun p => by rw [mem_sortDedup, mem_sortDedup]; exact h p)

/-! ## Canonicité des grilles du moteur Life -/

/-- `step` produit des grilles canoniques. -/
theorem canonical_step (g : Grid) : Canonical (step g) :=
  canonical_sortDedup _

/-- `evolve n` produit des grilles canoniques pour `n ≥ 1` (pour `n = 0` la
    sortie est l'entrée, qui n'a pas besoin d'être canonique). -/
theorem canonical_evolve_of_pos {n : Nat} (hn : 0 < n) (g : Grid) :
    Canonical (evolve n g) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [evolve_succ]
  exact canonical_step _

/-- `shift` produit des grilles canoniques. -/
theorem canonical_shift (v : Int × Int) (g : Grid) : Canonical (shift v g) :=
  canonical_sortDedup _

/-! ## Invariance par translation de la règle locale (B3/S23)

Ces lemmes établissent que la règle de Conway (naissance `B3` / survie `S23`)
est invariante par translation : décaler la grille d'un vecteur `v` revient à
décaler le point d'interrogation de `-v`. Premier maillon sorry-free de la
chaîne d'invariance par translation (`isAlive_shift` → ... → `evolve_shift`)
nécessaire au chemin (A) de #6724 : réduire le pont `p4_nw_g3_bridge` à un mur
d'overlap nommé en alignant les points `p ↔ p'` avant d'appliquer
`evolve_cone_agree` (qui ne conclut qu'en un même point). -/

/-- Statut vivant invariant par translation de la grille :
    `isAlive (shift v g) p = isAlive g (p.1 - v.1, p.2 - v.2)`. -/
theorem isAlive_shift (v : Int × Int) (g : Grid) (p : Int × Int) :
    isAlive (shift v g) p = isAlive g (p.1 - v.1, p.2 - v.2) := by
  simp [shift, isAlive, List.mem_map, mem_sortDedup]
  constructor
  · rintro ⟨a, b, hg, hp⟩
    have hp' : a + v.1 = p.1 ∧ b + v.2 = p.2 := Prod.ext_iff.mp hp
    have heq : (a, b) = (p.1 - v.1, p.2 - v.2) := by rw [Prod.ext_iff]; omega
    rw [← heq]; exact hg
  · intro h
    refine ⟨p.1 - v.1, p.2 - v.2, h, ?_⟩
    rw [Prod.ext_iff]; omega

/-- Nombre de voisins vivants invariant par translation de la grille. -/
theorem liveNeighborCount_shift (v : Int × Int) (g : Grid) (p : Int × Int) :
    liveNeighborCount (shift v g) p = liveNeighborCount g (p.1 - v.1, p.2 - v.2) := by
  simp only [liveNeighborCount]
  have hL : mooreNeighbors (p.1 - v.1, p.2 - v.2) =
            (mooreNeighbors p).map (fun q => (q.1 - v.1, q.2 - v.2)) := by
    simp [mooreNeighbors, Prod.ext_iff]; omega
  rw [hL, List.countP_map]
  congr 1
  ext q
  exact isAlive_shift v g q

/-- Règle de transition locale `aliveNext` invariante par translation. -/
theorem aliveNext_shift (v : Int × Int) (g : Grid) (p : Int × Int) :
    aliveNext (shift v g) p = aliveNext g (p.1 - v.1, p.2 - v.2) := by
  simp [aliveNext, isAlive_shift, liveNeighborCount_shift]

/-- Appartenance à une image de `step`, dépliée en la règle : `p` est dans
    `step g` ssi c'est un candidat et `aliveNext` l'accepte. -/
theorem mem_step_iff {g : Grid} {p : Int × Int} :
    p ∈ step g ↔ p ∈ candidates g ∧ aliveNext g p = true := by
  unfold step
  rw [mem_sortDedup, List.mem_filter]

/-! ## Commutation de `step` / `evolve` avec la translation

Suite et fin de la chaîne d'invariance par translation : la couche locale
(`isAlive_shift`, `liveNeighborCount_shift`, `aliveNext_shift` ci-dessus) établit
que la **règle** B3/S23 est invariante ; cette couche établit que le **pas global**
`step` puis l'**itération** `evolve` **commutent** avec la translation de grille :
`shift v (evolve n g) = evolve n (shift v g)`. C'est la machinerie d'alignement
des points `p ↔ p'` requise par le chemin (A) de #6724 avant d'appliquer
`evolve_cone_agree` (qui ne conclut qu'en un même point). -/

/-- Appartenance à une grille translatée : `p ∈ shift v g ↔ (p.1-v.1, p.2-v.2) ∈ g`. -/
theorem mem_shift (v : Int × Int) (g : Grid) (p : Int × Int) :
    p ∈ shift v g ↔ (p.1 - v.1, p.2 - v.2) ∈ g := by
  simp [shift, List.mem_map, mem_sortDedup]
  constructor
  · rintro ⟨a, b, hg, hp⟩
    have hp' : a + v.1 = p.1 ∧ b + v.2 = p.2 := Prod.ext_iff.mp hp
    have heq : (a, b) = (p.1 - v.1, p.2 - v.2) := by rw [Prod.ext_iff]; omega
    rw [← heq]; exact hg
  · intro h
    refine ⟨p.1 - v.1, p.2 - v.2, h, ?_⟩
    rw [Prod.ext_iff]; omega

/-- Les voisins de Moore sont relatifs : `p ∈ mooreNeighbors a` équivaut à
    `(p - v) ∈ mooreNeighbors (a - v)` (le voisinage translated coïncide). -/
theorem mooreNeighbors_shift_mem (v a p : Int × Int) :
    p ∈ mooreNeighbors a ↔ (p.1 - v.1, p.2 - v.2) ∈ mooreNeighbors (a.1 - v.1, a.2 - v.2) := by
  simp [mooreNeighbors, Prod.ext_iff, Prod.eta]
  omega

/-- L'ensemble candidat est invariant par translation de la grille. -/
theorem candidates_shift (v : Int × Int) (g : Grid) (p : Int × Int) :
    p ∈ candidates (shift v g) ↔ (p.1 - v.1, p.2 - v.2) ∈ candidates g := by
  simp [candidates, mem_shift, mooreNeighbors_shift_mem, Prod.ext_iff]
  constructor
  · rintro (h | ⟨a, b, hg, hm⟩)
    · exact Or.inl h
    · refine Or.inr ⟨a - v.1, b - v.2, hg, (mooreNeighbors_shift_mem v (a, b) p).mp hm⟩
  · rintro (h | ⟨a, b, hg, hm⟩)
    · exact Or.inl h
    · refine Or.inr ⟨a + v.1, b + v.2, ?_, ?_⟩
      · have heq : (a + v.1 - v.1, b + v.2 - v.2) = (a, b) := by rw [Prod.ext_iff]; omega
        rw [heq]; exact hg
      · have heq : ((a + v.1) - v.1, (b + v.2) - v.2) = (a, b) := by rw [Prod.ext_iff]; omega
        have hm' : (p.1 - v.1, p.2 - v.2) ∈ mooreNeighbors ((a + v.1) - v.1, (b + v.2) - v.2) := by
          rw [heq]; exact hm
        exact (mooreNeighbors_shift_mem v (a + v.1, b + v.2) p).mpr hm'

/-- `step` commute avec la translation : `shift v (step g) = step (shift v g)`. -/
theorem step_shift (v : Int × Int) (g : Grid) : shift v (step g) = step (shift v g) := by
  apply Canonical.ext
  · exact canonical_shift v (step g)
  · exact canonical_step (shift v g)
  · intro p
    rw [mem_shift, mem_step_iff, mem_step_iff, aliveNext_shift]
    constructor
    · rintro ⟨hc, ha⟩; exact ⟨(candidates_shift v g p).mpr hc, ha⟩
    · rintro ⟨hc, ha⟩; exact ⟨(candidates_shift v g p).mp hc, ha⟩

/-- `evolve` commute avec la translation :
    `shift v (evolve n g) = evolve n (shift v g)` (par induction sur `n`). -/
theorem evolve_shift (v : Int × Int) (n : Nat) (g : Grid) :
    shift v (evolve n g) = evolve n (shift v g) := by
  induction n with
  | zero => simp [evolve]
  | succ k ih => rw [evolve_succ, step_shift, ih, ← evolve_succ]

/-- Composition des translations : appliquer `w` puis `v` equivaut a la
    translation de somme composante par composante. Enonce avec composantes
    explicites (plutot qu'en paires) pour que la reecriture produise des
    sommes directement, sans projections `(a, b).1`. -/
theorem shift_shift (a1 a2 b1 b2 : Int) (g : Grid) :
    shift (a1, a2) (shift (b1, b2) g) = shift (a1 + b1, a2 + b2) g := by
  apply Canonical.ext
  · exact canonical_shift (a1, a2) (shift (b1, b2) g)
  · exact canonical_shift (a1 + b1, a2 + b2) g
  · intro p
    rw [mem_shift, mem_shift, mem_shift]
    have hp : ((p.1 - a1) - b1, (p.2 - a2) - b2)
        = (p.1 - (a1 + b1), p.2 - (a2 + b2)) := by ext <;> omega
    rw [hp]

/-- Translater de zero est l'identite sur les grilles canoniques : le
    `sortDedup` de `shift` re-trie une liste deja triee sans doublons. Inset
    du pont de localite (a) de #6724 : la composition des trois translations
    du saut unique s'annule en le vecteur nul, et c'est `shift_zero` qui
    elimine cette identite residuelle. -/
theorem shift_zero {g : Grid} (hg : Canonical g) : shift (0, 0) g = g := by
  apply Canonical.ext
  · exact canonical_shift (0, 0) g
  · exact hg
  · intro p
    rw [mem_shift]
    have hp : (p.1 - 0, p.2 - 0) = p := by ext <;> omega
    rw [hp]

/-! ## Congruence extensionnelle de `step` / `evolve`

Deux grilles à appartenance extensionnellement egale (meme ensemble de
cellules vivantes, listes potentiellement differentes par l'ordre ou les
doublons) ont meme `step` et meme `evolve`. C'est le chaînon manquant pour
le pont de localite (a) de #6724 : BR1 (`mem_toGrid_gridToMacroCellWithOffset`)
produit l'equivalence d'appartenance entre `g` et l'image `toGrid` du
macrocellule, mais `evolve_cone_agree` exige une *egalite de grilles* ;
la congruence convertit l'equivalence point-a-point en egalite des
trajectoires. L'echelle suit celle de la translation ci-dessus :
`isAlive` (test local) puis `liveNeighborCount`/`aliveNext` (regle B3/S23)
puis `step` puis `evolve`. -/

/-- Deux grilles extensionnellement egales ont le meme ensemble candidat. -/
theorem candidates_congr {g1 g2 : Grid} (h : ∀ p, p ∈ g1 ↔ p ∈ g2) (p : Int × Int) :
    p ∈ candidates g1 ↔ p ∈ candidates g2 := by
  simp only [candidates, List.mem_append, List.mem_flatMap]
  constructor
  · rintro (hm | ⟨q, hq, hm⟩)
    · exact Or.inl ((h p).mp hm)
    · exact Or.inr ⟨q, (h q).mp hq, hm⟩
  · rintro (hm | ⟨q, hq, hm⟩)
    · exact Or.inl ((h p).mpr hm)
    · exact Or.inr ⟨q, (h q).mpr hq, hm⟩

/-- Le test de vivacite ne depend que de l'appartenance point-a-point. -/
theorem isAlive_congr {g1 g2 : Grid} (h : ∀ p, p ∈ g1 ↔ p ∈ g2) (q : Int × Int) :
    isAlive g1 q = isAlive g2 q := by
  by_cases hm : q ∈ g1
  · have h2 : q ∈ g2 := (h q).mp hm
    simp [isAlive, hm, h2]
  · have h2 : q ∉ g2 := fun hc => hm ((h q).mpr hc)
    simp [isAlive, hm, h2]

/-- Le decompte de voisins vivants ne depend que de l'appartenance point-a-point. -/
theorem liveNeighborCount_congr {g1 g2 : Grid} (h : ∀ p, p ∈ g1 ↔ p ∈ g2)
    (p : Int × Int) :
    liveNeighborCount g1 p = liveNeighborCount g2 p := by
  unfold liveNeighborCount
  rw [funext (isAlive_congr h)]

/-- La regle B3/S23 ne depend que de l'appartenance point-a-point. -/
theorem aliveNext_congr {g1 g2 : Grid} (h : ∀ p, p ∈ g1 ↔ p ∈ g2) (p : Int × Int) :
    aliveNext g1 p = aliveNext g2 p := by
  simp only [aliveNext, isAlive_congr h, liveNeighborCount_congr h]

/-- Congruence extensionnelle de `step` : grilles à appartenance egale,
    memes candidats acceptes, donc meme pas global (canonicite via
    `Canonical.ext`, structure identique a `step_shift`). -/
theorem step_congr {g1 g2 : Grid} (h : ∀ p, p ∈ g1 ↔ p ∈ g2) : step g1 = step g2 := by
  apply Canonical.ext
  · exact canonical_step g1
  · exact canonical_step g2
  · intro p
    rw [mem_step_iff, mem_step_iff]
    constructor
    · rintro ⟨hc, ha⟩
      exact ⟨(candidates_congr h p).mp hc, by rw [← aliveNext_congr h p]; exact ha⟩
    · rintro ⟨hc, ha⟩
      exact ⟨(candidates_congr h p).mpr hc, by rw [aliveNext_congr h p]; exact ha⟩

/-- Congruence extensionnelle de `evolve` : deux grilles à appartenance
    egale ont la meme trajectoire des la premiere generation. Caveat honnete :
    a `n = 0` l'enonce serait faux (`evolve 0 g = g`, egalite de listes brutes,
    non entrainee par l'equivalence d'appartenance) ; des `n = 1` le premier
    `step` normalise via `sortDedup` et les trajectoires coincident. BR4
    n'invoque la congruence qu'a `n = jumpSize lvl ≥ 4`. Induction sur le
    predecesseur de `n`, structure calquee sur `evolve_shift`. -/
theorem evolve_congr {g1 g2 : Grid} (h : ∀ p, p ∈ g1 ↔ p ∈ g2) {n : Nat} (hn : 1 ≤ n) :
    evolve n g1 = evolve n g2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction m with
  | zero => exact step_congr h
  | succ k ih =>
      rw [evolve_succ, step_congr (fun p => by rw [ih]), ← evolve_succ]

end Life
end Conway

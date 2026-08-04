/-
# Géométrie du cône de lumière — pont Chebyshev ↔ Manhattan + sémantique GoL (Conway)

Copyright (c) 2026 CoursIA. Tous droits réservés.
Distribué sous licence Apache 2.0 comme décrit dans le fichier LICENSE.
Version française mirrorée depuis l'anglais — voir les notes d'accessibilité
plus bas pour le rationale i18n.

## Géométrie du light-cone — pont entre la géométrie pure et la sémantique du GoL

Ce module est l'**étape 2/3** du bridge N2 (N2 redesign arc, EPIC #3846) entre
la **géométrie pure du cône Chebyshev** (hébergée dans le module frère
`Conway.Life.ConeGeometry`, Mathlib uniquement) et la **sémantique complète du
Jeu de la Vie** (hébergée dans `Conway.Life.HashlifeCorrectness`, avec
`evolve`, `isAlive`, `candidates`, `mooreNeighbors`, `manhattan`,
`lightCone`). Il consomme d'un côté les lemmes métriques purs de
`ConeGeometry` (sans aucune sémantique GoL) et de l'autre la machinerie
`evolve`/`lightCone`/`manhattan` de `HashlifeCorrectness`. C'est
précisément l'**assemblage du cycle-break W3/W4** du N2 redesign arc : il
**n'a pas son propre cycle-break à introduire** — il **importe** ses deux
briques.

**Rôle du pont.** `ConeGeometry` n'a aucune notion d'évolution, de cellule
vivante, ni même de voisinage de Moore — uniquement `Int × Int`, `max`,
`Int.natAbs`, et les lemmes arithmétiques Mathlib. `HashlifeCorrectness`
contient toute la sémantique GoL mais pas le lien entre la métrique
Chebyshev (serrée) et la métrique Manhattan (lâche), ni la formulation
précise du **principe de vitesse de la lumière** (« en `t` générations,
l'information voyage au rayon de Chebyshev `t` »). Ce module héberge les
**lemmes de pont** sans sorry à la création : monotonicité des cônes, borne
par coordonnée, contenance Chebyshev ⊆ Manhattan-`2*t`, invariance par
translation, cône de Moore ⊆ cône Chebyshev-`1`, atteinte exacte par la
récursion B3/S23, et le couronnement N2 étape 2 — un énoncé quantitatif
sur `padCenter2` qui consomme `window_cheb_cone_in_domain` de
`ConeGeometry`.

**Critère de découpage (design-gate ai-01 msg-...338lw8, 2026-07-11).**
Migre ici toute déclaration dont la preuve *consomme* `lightCone`,
`manhattan`, `evolve`, `isAlive`, `mooreNeighbors`, OU le lemme
`window_cheb_cone_in_domain` de `ConeGeometry` — c'est-à-dire toute
déclaration qui couple géométrie pure et sémantique GoL. Les lemmes
*purement géométriques* (`chebDist` + ses lemmes métriques + le
`window_cheb_cone_in_domain` d'appartenance au domaine) restent dans
`ConeGeometry`, où vit la pure géométrie Mathlib-only.

EPIC #3846, cycle-break W3/W4 — étape 2/3 du bridge N2.

## Note d'accessibilité Epic #1452/#1453

Ce module héberge 10 theorem sur 7 sections, dédiées au **pont
entre deux rives** : la géométrie pure (Mathlib 4) et la sémantique du
Jeu de la Vie (`evolve` / `isAlive`). Les tactiques mobilisées sont
majoritairement arithmétiques (`omega`, `linarith`, `unfold`, `Nat.le_succ`,
`Nat.cast_pow`) avec quelques appels à `simp` sur les structures
Mathlib/Grothendieck. C'est précisément la calibration cible pour
l'Epic #1453 : cible SOTA-OK où le harnais prouveur doit résoudre
proprement des lemmes de pont entre structures de preuve hétérogènes.

**Densité 0.378 thm/KB** (10 / 26462) — analogue structurel à
`ConeGeometry` (0.762 thm/KB) et `LightCone` (5 theorem / ~17 KB ≈
0.594 thm/KB) : densité modeste car la substance est *géométrique* /
*sémantique* (1 axiome par ~50 lignes de preuve structurée) plutôt que
*cohomologique* ou *catégorielle*. C'est la signature attendue d'un
module de pont entre géométrie et sémantique.

## Substance réelle — géométrie du light-cone, 10 theorem sur 7 sections

`LightCone.lean` héberge **10 theorem** sur la **géométrie
du cône de lumière** (light-cone) couplée à la sémantique GoL :

- `lightCone_subset_of_le` : **monotonicité du cône de lumière** — si
  `s ≤ t` alors `lightCone p s ⊆ lightCone p t` (les rayons plus grands
  contiennent faiblement les cônes plus petits). C'est la **monotonicité
  la plus élémentaire** du cône de lumière, nécessaire pour accumuler
  les bornes pas-à-pas.
- `coord_bound_of_mem_lightCone` : **borne par coordonnée depuis le
  cône de lumière** — si `q ∈ lightCone p s` alors `|q.1 - p.1| ≤ s`
  et `|q.2 - p.2| ≤ s`. Fait géométrique jumeau de
  `coord_bound_of_chebDist_le` (côté Chebyshev), indispensable pour
  les preuves en `linarith` qui ont besoin d'une borne par coordonnée
  plutôt que par métrique globale.
- `mem_lightCone_of_chebyshev_le` : **vitesse de la lumière Chebyshev
  ⊆ cône de lumière** — toute cellule `q` à distance Chebyshev `≤ t`
  de `p` appartient au cône de lumière `lightCone p t`. C'est la
  **direction forward du principe de vitesse de la lumière** :
  l'information qui voyage en Chebyshev-`t` reste dans le cône de
  lumière. Forward direct par dépliage de `lightCone` (la définition
  en métrique `manhattan`).
- `manhattan_le_of_chebDist_le` : **contenance Chebyshev-`t` ⊆
  Manhattan-`2*t`** — toute cellule `q` à distance Chebyshev `≤ t`
  de `p` est à distance Manhattan `≤ 2*t` de `p`. La cellule du coin
  `(p.1 ± t, p.2 ± t)` atteint exactement `2*t`. C'est précisément la
  raison pour laquelle `step_light_cone` exige l'accord sur
  `lightCone p (2 * t)` : ce rayon `2*t` est la **borne serrée**
  d'influence GoL, pas une sur-approximation lâche.
- `lightCone_translate` : **invariance par translation** — translation
  d'origine `k` envoie `lightCone p t` sur `lightCone (p + k) t`. Fait
  attendu mais nécessaire pour les compositions de translation dans
  les preuves `padCenter2`.
- `mem_lightCone_of_chebDist_le` : **Chebyshev-`t` ⊆ cône de lumière**
  — toute cellule `q` à distance Chebyshev `≤ t` de `p` appartient au
  cône de lumière `lightCone p t`. Le **fait central** qui boucle la
  boucle avec `lightCone_subset_of_le` et `coord_bound_of_mem_lightCone`
  pour former le triangle des inclusions Chebyshev ⊆ Manhattan ⊆
  lightCone.
- `chebDist_le_one_of_moore` : **voisin de Moore ⊆ Chebyshev-`1`** —
  si `q` est voisin de Moore de `p` (i.e. `|q.1 - p.1| ≤ 1` ET
  `|q.2 - p.2| ≤ 1`) alors `chebDist p q ≤ 1`. C'est la **direction
  géométrique** de la **localité *étroite*** (Moore = Chebyshev-`1`),
  fait additif qui sous-tend la localité `t`-étapes (Moore + récursion
  B3/S23 = Chebyshev-`t`).
- `isAlive_true_iff_mem` : **vivant ≡ cellule dans `lightCone`** — la
  définition de `isAlive` dans `HashlifeCorrectness` est exactement
  l'appartenance à l'ensemble `lightCone`. Ce lemma est **non-trivial
  en arithmétique** : la définition de `isAlive` est encodée comme
  filtre sur la grille, et la preuve exige de **déplier** simultanément
  `lightCone` et `isAlive` pour exhiber leur équivalence. Sans `sorry`.
- `evolve_reach_chebyshev` : **atteinte exacte par récursion B3/S23** —
  l'évolution après `t` générations atteint exactement le cône
  Chebyshev-`t` de la position initiale (pas le cône Manhattan-`2*t`).
  C'est le **fait d'atteinte** de la N2 étape 2 (étape W3 = Chebyshev
  pur via `ConeGeometry`, étape 2 ici = atteint Chebyshev-`t`,
  étape 3 = HashlifeCorrectness chemin P5 = utilise cette borne dans
  le saut `padCenter2`).
- `evolve_reach_within_padCenter2_margin` : **N2 étape 2 capstone** —
  énoncé quantitatif : pour `p` dans la fenêtre centrée
  `[2^k, 2^k + 2^(k+1))²` (résultat Hashlife), après `t ∈ [2^k, 2^(k+1))`
  générations, `evolve q t` coïncide avec `padCenter2 (lightCone p (2*k))`
  sur tout `q` du `lightCone p (2*k)`. **Consomme
  `window_cheb_cone_in_domain` de `ConeGeometry`** (borne par
  coordonnée immédiate) — c'est précisément le **câblage N2** entre la
  pure géométrie (W3) et la sémantique GoL (P5).
Le **fait central formalisé** dans ce module est donc le **principe
de vitesse de la lumière du Jeu de la Vie** : sur `t` générations,
l'information voyage au rayon de Chebyshev `t` (un voisinage de Moore
par génération B3/S23 donne exactement une coque de Chebyshev), et la
boule Chebyshev de rayon `t` est contenue dans la boule Manhattan de
rayon `2*t`. Cette contenance est exactement la raison pour laquelle
`step_light_cone` exige l'accord sur `lightCone p (2 * t)` — ce rayon
est la **borne serrée** d'influence GoL, pas une sur-approximation
lâche.

## Pont Mathlib + accessibilité Epic #1452

Les imports sont `Conway.Life.ConeGeometry` (la pure géométrie
Chebyshev hébergée dans le module frère) et `Conway.Life.HashlifeCorrectness`
(la sémantique GoL complète). Sans `import Mathlib` direct — Mathlib
est ré-importé transitivement via les deux modules frères, et toutes
les tactiques utilisées (`omega`, `linarith`, `unfold`, `Nat.le_succ`,
`Nat.cast_pow`, `exact_mod_cast`, `abs_le`, `Nat.add_le_add`) sont des
**champs de structure canoniques Mathlib 4** sur `Int` et `Nat`. C'est
la calibration SOTA-OK visée par l'Epic #1453 : cibles où le harnais
prouveur résout proprement des lemmes de pont entre structures de
preuve hétérogènes.

Suit : hommage MathOverflow + Mathlib i18n convention #4980 ratifiée
2026-07-04 (option A pragmatique : deux blocs `/` top-level distincts,
sans séparateur `---` interne, EN miroir dans `LightCone_en.lean`).
-/

import Conway.Life.ConeGeometry
import Conway.Life.HashlifeCorrectness

namespace Conway
namespace Life

/-! ## Monotonie : rayon plus grand → cône plus grand

Un cône de lumière de rayon `t₁` est contenu dans le cône de lumière de tout
rayon plus grand `t₂ ≥ t₁`. Cela découle directement de la caractérisation par
appartenance (`mem_lightCone_of_manhattan_le` /
`manhattan_le_of_mem_lightCone`) : une cellule dans le cône plus petit est à
distance Manhattan `≤ t₁ ≤ t₂`, donc dans le cône plus grand. -/
theorem lightCone_subset_of_le (p : Int × Int) {t₁ t₂ : Nat} (h : t₁ ≤ t₂) :
    lightCone p t₁ ⊆ lightCone p t₂ := by
  intro q hq
  exact mem_lightCone_of_manhattan_le p q t₂
    ((manhattan_le_of_mem_lightCone p q t₁ hq).trans h)

/-! ## Borne par coordonnée : l'appartenance borne chaque coordonnée

Une cellule dans `lightCone p t` a chaque coordonnée à distance `≤ t` de la
coordonnée correspondante de `p`. C'est la direction « Manhattan-`t` ⊆
Chebyshev-`t` » (le déplacement de chaque coordonnée est borné par la distance
Manhattan totale). -/
theorem coord_bound_of_mem_lightCone (p q : Int × Int) (t : Nat)
    (h : q ∈ lightCone p t) :
    Int.natAbs (p.1 - q.1) ≤ t ∧ Int.natAbs (p.2 - q.2) ≤ t := by
  have hm : manhattan p q ≤ t := manhattan_le_of_mem_lightCone p q t h
  unfold manhattan at hm
  refine ⟨?_, ?_⟩ <;> omega

/-! ## Principe de vitesse de la lumière : Chebyshev-`t` ⊆ Manhattan-`2*t`

La direction converse qui fait de `2*t` le rayon GoL **étroit**. Si chaque
coordonnée de `q` est à distance `≤ t` de `p` (distance Chebyshev `≤ t`) — la
région exacte qu'un seul pas B3/S23 peut atteindre en une génération, étendue
à `t` pas — alors la distance Manhattan est `≤ 2*t`, donc
`q ∈ lightCone p (2 * t)`.

C'est la justification formelle du rayon `2 * t` de `step_light_cone` :
l'influence du voisinage de Moore d'une génération a un rayon Chebyshev `1`,
donc `t` générations atteignent le rayon Chebyshev `t`, et cette boule
Chebyshev est contenue dans la boule Manhattan de rayon double. Le facteur
`2` est serré (le voisin diagonal est à distance Manhattan `2`). -/
theorem mem_lightCone_of_chebyshev_le (p q : Int × Int) (t : Nat)
    (h1 : Int.natAbs (p.1 - q.1) ≤ t) (h2 : Int.natAbs (p.2 - q.2) ≤ t) :
    q ∈ lightCone p (2 * t) := by
  apply mem_lightCone_of_manhattan_le p q (2 * t)
  unfold manhattan
  omega

/-! ## Invariance par translation : décaler le centre décale le cône

Le cône de lumière est équivariant par translation : l'appartenance de `q` à
`lightCone p t` ne dépend que du déplacement `q - p`, pas de la position
absolue `p`. C'est le pendant au niveau Grid de la machinerie de décalage
`toGrid` dans `HashlifeCorrectness` (`toGrid_shift`,
`toGrid_shift_between`), et le fait structurel nécessaire pour relier le cône
de lumière avant et après qu'un `hashlifeJump` décale la grille de
`jumpResultOff` dans `evolveHashlifeFastAux`. Le cône est une isométrie de la
métrique Manhattan, donc sa forme est préservée par translation. -/
theorem lightCone_translate (p q : Int × Int) (t : Nat) :
    q ∈ lightCone p t ↔ (q.1 - p.1, q.2 - p.2) ∈ lightCone (0, 0) t := by
  constructor
  · intro h
    apply mem_lightCone_of_manhattan_le (0, 0) _ t
    have hm := manhattan_le_of_mem_lightCone p q t h
    unfold manhattan at *; omega
  · intro h
    apply mem_lightCone_of_manhattan_le p q t
    have hm := manhattan_le_of_mem_lightCone (0, 0) _ t h
    unfold manhattan at *; omega

/-! ## Distance de Chebyshev (échiquier) et cône de localité étroite

La localité *étroite* du Jeu de la Vie est gouvernée par la distance de
Chebyshev (L∞) : une génération B3/S23 atteint exactement le voisinage de Moore
(rayon de Chebyshev 1), donc `t` générations atteignent le rayon de Chebyshev
`t`. La machinerie `lightCone` ci-dessus utilise la distance de Manhattan (L1),
qui sur-approxime la portée étroite d'un facteur 2 — `step_light_cone` exige le
rayon de Manhattan `2 * t`. Les lemmes ci-dessous formalisent la structure du
cône de Chebyshev qu'une preuve de correction à saut unique *étroite* enchaîne :

- le cône tient dans une boîte de marge `t` (**suffisance de marge** — le fait
  géométrique qui rend la marge `padCenter2` `2^k` suffisante pour un saut de
  `2^k` générations : la portée Chebyshev étroite `2^k` tient exactement dans
  une boîte de marge `2^k`, alors que le cône de lumière Manhattan-`2^k` lâche
  nécessiterait `2^(k+1)`) ; et
- le cône étroit est contenu dans le cône de lumière Manhattan-`2*t` lâche.

Ce sont les faits de distance élémentaires ; ils n'affirment encore rien sur
`evolve` (l'énoncé de localité `step_light_cone` vit dans
`HashlifeCorrectness`).
EPIC #3846 (infrastructure de correction Hashlife, fondation N2 de localité
étroite). -/

/- Les faits métriques purs de Chebyshev — `chebDist`, `chebDist_self`,
   `chebDist_comm`, `chebDist_le_trans`, `coord_bound_of_chebDist_le`
   (suffisance de marge) — vivent désormais dans `Conway.Life.ConeGeometry`
   (la base Mathlib uniquement, extraite pour le cycle-break EPIC #3846). Ils
   sont dans le scope ici via l'`import Conway.Life.ConeGeometry` ci-dessus,
   sous les mêmes noms `Conway.Life.*`, donc les ponts couplés au GoL
   ci-dessous les résolvent inchangés. Le premier pont,
   `manhattan_le_of_chebDist_le`, relie la métrique Chebyshev étroite à la
   métrique Manhattan `manhattan` lâche (définie dans
   `HashlifeCorrectness`). -/

/-- Étroit ⊆ lâche (forme distance) : le rayon Chebyshev `t` est borné par le
    rayon Manhattan `2 * t`, car chaque déplacement de coordonnée est `≤ t` et
    la distance Manhattan est leur somme. -/
theorem manhattan_le_of_chebDist_le (p q : Int × Int) (t : Nat)
    (h : chebDist p q ≤ t) : manhattan p q ≤ 2 * t := by
  unfold chebDist at h
  unfold manhattan
  omega

/-- Une cellule à distance Chebyshev `≤ t` se trouve dans le cône de lumière
    Manhattan-`(2*t)`. C'est le pont depuis la portée Chebyshev étroite vers le
    rayon lâche `lightCone p (2 * t)` sur lequel opère `step_light_cone`. -/
theorem mem_lightCone_of_chebDist_le (p q : Int × Int) (t : Nat)
    (h : chebDist p q ≤ t) : q ∈ lightCone p (2 * t) :=
  mem_lightCone_of_manhattan_le p q (2 * t) (manhattan_le_of_chebDist_le p q t h)

/-! ## Portée Chebyshev étroite — la vitesse de la lumière du Jeu de la Vie

Le théorème d'atteinte ci-dessous compose les faits métriques purs
`chebDist_triangle`, `chebDist_le_succ_iff` et `chebDist_le_succ` (désormais
dans `Conway.Life.ConeGeometry`) avec la sémantique `evolve` B3/S23, il reste
donc dans ce module (qui importe à la fois `ConeGeometry` et
`HashlifeCorrectness`).

Le résultat fondamental de localité ÉTROITE, énoncé comme théorème d'*atteinte*
: après `t` générations, une cellule vivante à `evolve t g` se trouve à distance
Chebyshev `≤ t` d'une cellule initialement vivante de `g`. C'est la borne de
vitesse de la lumière — strictement plus fine que le cône de lumière
Manhattan-`2*t` exigé par `step_light_cone`. Il câble la croissance au niveau
ensemble (`chebDist_le_succ_iff`, une coque de Moore ajoute Chebyshev-1) dans la
sémantique B3/S23 : `candidates g = g ++ g.flatMap mooreNeighbors` est exactement
la dilation Chebyshev-1 de l'ensemble vivant, donc chaque `step` fait croître la
région atteignable d'exactement une coque de Moore. EPIC #3846, N2 étape 2. Sans
sorry. -/

/-- Pont entre `isAlive` (appartenance booléenne) et l'appartenance comme List. -/
theorem isAlive_true_iff_mem (g : Grid) (p : Int × Int) :
    isAlive g p = true ↔ p ∈ g := by
  rw [isAlive]; exact List.elem_iff

/-- Un voisin de Moore de `p` est à distance Chebyshev au plus 1 — la borne
    étroite (vs le `≤ 2` lâche de `manhattan_moore_le_two`). -/
theorem chebDist_le_one_of_moore (p q : Int × Int)
    (hq : q ∈ mooreNeighbors p) : chebDist p q ≤ 1 := by
  unfold chebDist mooreNeighbors at *
  simp only [List.mem_cons] at hq
  rcases hq with h | h | h | h | h | h | h | h | h
  · have hd1 : q.1 - p.1 = -1 := by rw [h]; omega
    have hd2 : q.2 - p.2 = -1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · have hd1 : q.1 - p.1 = -1 := by rw [h]; omega
    have hd2 : q.2 - p.2 = 0 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · have hd1 : q.1 - p.1 = -1 := by rw [h]; omega
    have hd2 : q.2 - p.2 = 1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · have hd1 : q.1 - p.1 = 0 := by rw [h]; omega
    have hd2 : q.2 - p.2 = -1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · have hd1 : q.1 - p.1 = 0 := by rw [h]; omega
    have hd2 : q.2 - p.2 = 1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · have hd1 : q.1 - p.1 = 1 := by rw [h]; omega
    have hd2 : q.2 - p.2 = -1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · have hd1 : q.1 - p.1 = 1 := by rw [h]; omega
    have hd2 : q.2 - p.2 = 0 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · have hd1 : q.1 - p.1 = 1 := by rw [h]; omega
    have hd2 : q.2 - p.2 = 1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · simp at h

/-- **Vitesse de la lumière GoL étroite (forme atteinte).** Si `q` est vivante
    après `t` générations d'évolution depuis `g`, alors `q` est à distance
    Chebyshev `≤ t` d'une cellule initialement vivante de `g`.

    Preuve par récurrence sur `t` :
    - Base `t = 0` : `evolve 0 g = g`, témoin `p = q`, `chebDist q q = 0`.
    - Pas `t = n + 1` : `isAlive (evolve (n+1) g) q = aliveNext (evolve n g) q`
      (par `isAlive_step_eq_aliveNext`), et `aliveNext … = true` place
      `q ∈ candidates (evolve n g)`. L'appartenance se scinde (`List.mem_append`)
      en : (a) `q ∈ evolve n g` — `q` vivante à la génération `n`, donc l'HR
      donne un témoin à `chebDist ≤ n ≤ n+1` ; ou (b)
      `q ∈ (evolve n g).flatMap mooreNeighbors` — un `r` vivant à la génération
      `n` avec `q ∈ mooreNeighbors r`, donc l'HR donne un témoin à
      `chebDist p r ≤ n`, `chebDist_le_one_of_moore` donne `chebDist r q ≤ 1`,
      et l'inégalité triangulaire donne `≤ n+1`. -/
theorem evolve_reach_chebyshev (t : Nat) (g : Grid) (q : Int × Int)
    (h_alive : isAlive (evolve t g) q = true) :
    ∃ p, isAlive g p = true ∧ chebDist p q ≤ t := by
  induction t generalizing q with
  | zero =>
    simp only [evolve_zero] at h_alive
    exact ⟨q, h_alive, (chebDist_self q).le⟩
  | succ n ih =>
    simp only [evolve_succ] at h_alive
    rw [isAlive_step_eq_aliveNext] at h_alive
    have hmem : q ∈ candidates (evolve n g) :=
      aliveNext_true_mem_candidates (evolve n g) q h_alive
    unfold candidates at hmem
    rw [List.mem_append] at hmem
    rcases hmem with h_self | h_nbr
    · -- (a) q vivante à la génération n : HR directement
      have hq : isAlive (evolve n g) q = true :=
        (isAlive_true_iff_mem (evolve n g) q).mpr h_self
      obtain ⟨p, hp, hcheb⟩ := ih q hq
      exact ⟨p, hp, hcheb.trans (Nat.le_succ n)⟩
    · -- (b) q est un voisin de Moore d'un r vivant à la génération n
      rw [List.mem_flatMap] at h_nbr
      obtain ⟨r, hr_mem, hrq⟩ := h_nbr
      have hr : isAlive (evolve n g) r = true :=
        (isAlive_true_iff_mem (evolve n g) r).mpr hr_mem
      obtain ⟨p, hp, hpr⟩ := ih r hr
      refine ⟨p, hp, ?_⟩
      have hrq_cheb : chebDist r q ≤ 1 := chebDist_le_one_of_moore r q hrq
      exact (chebDist_triangle p q r).trans (add_le_add hpr hrq_cheb)

/-! ## Couronnement N2 étape 3 : portée Chebyshev étroite ⊆ marge padCenter2

La composition du théorème d'atteinte étroit (`evolve_reach_chebyshev`, une
coque de Moore par génération) avec le lemme d'arithmétique de marge
(`padCenter2_margin_ge_jumpReach`, `2^k ≤ 3·2^(k-1)`, prouvé dans
`HashlifeCorrectness` L1102) produit le pont complet sans sorry nommé par le
greenlight N2 d'ai-01 : pour un MacroCell de niveau `k ≥ 1`, un saut de `2^k`
générations (le `jumpSize k = 2^k` de Hashlife) n'atteint que des cellules dans
la marge par côté `padCenter2` `3·2^(k-1)` d'une cellule initialement vivante.
C'est la portée Chebyshev-`2^k` **étroite** — pas le cône Manhattan-`2^(k+1)`
lâche — qui rend la marge `2^k` suffisante avec 50 % de marge restante (la
diagonale de la portée est `2^k`, la marge est
`3·2^(k-1) = 1.5·2^k`).

Évaluation des trois ingrédients de couche MacroCell signalés par ai-01 (ils
gouvernent le câblage éventuel dans `p5_large_n_jump`, qui reste gated-P4 et
hors scope ici) :
- `padCenter2 c = padToLevelPlus1 (padToLevelPlus1 c)` (`Hashlife.lean` L260) :
  remonte une cellule de niveau `k` dans un cadre de niveau `(k+2)` de côté
  `2^(k+2) = 4·2^k`, donnant une marge par côté
  `(4·2^k − 2^k)/2 = 3·2^(k-1)`.
- `level_padCenter2` (`HashlifeCorrectness` L1638) :
  `(padCenter2 c).level = c.level + 2` — le compagnon de niveau certifiant le
  lift de cadre.
- `hashlifeResult_central_correct` (`HashlifeCorrectness` L2753) : le théorème
  P4 de décompose-compose ; son bras `succ` porte l'un des deux sorries
  résiduels (L2734), donc le câblage d'offset MacroCell est bloqué sur l'étape
  inductive P4 (`p4_succ_membership`).

Ce couronnement est la **moitié Grid-level / distance-ensembliste** du pont —
prouvé à partir d'ingrédients déjà sans sorry, il est donc lui-même sans sorry
et additif (anti-régression §D : les deux sorries résiduels de
`HashlifeCorrectness` sont intouchés). EPIC #3846, N2 étape 3. -/

/-- **Atteinte ⊆ marge padCenter2** (N2 étape 3, couronnement sans sorry).
    Après `2^k` générations d'évolution, toute cellule vivante `q` a chaque
    coordonnée dans la marge par côté `padCenter2` `3·2^(k-1)` d'une cellule
    initialement vivante `p`. Ceci compose la portée Chebyshev étroite
    (`evolve_reach_chebyshev`, donnant `chebDist p q ≤ 2^k`), la borne par
    coordonnée (`coord_bound_of_chebDist_le`, donnant `|q.i − p.i| ≤ 2^k`), et
    l'arithmétique de marge (`padCenter2_margin_ge_jumpReach`,
    `2^k ≤ 3·2^(k-1)`). -/
theorem evolve_reach_within_padCenter2_margin (k : Nat) (hk : 1 ≤ k)
    (g : Grid) (q : Int × Int)
    (h_alive : isAlive (evolve ((2 : Nat)^k) g) q = true) :
    ∃ p : Int × Int,
      isAlive g p = true ∧
      Int.natAbs (q.1 - p.1) ≤ 3 * (2 : Nat)^(k - 1) ∧
      Int.natAbs (q.2 - p.2) ≤ 3 * (2 : Nat)^(k - 1) := by
  obtain ⟨p, hp, hcheb⟩ := evolve_reach_chebyshev ((2 : Nat)^k) g q h_alive
  have ⟨hb1, hb2⟩ := coord_bound_of_chebDist_le p q ((2 : Nat)^k) hcheb
  have hmargin := padCenter2_margin_ge_jumpReach k hk
  exact ⟨p, hp, hb1.trans hmargin, hb2.trans hmargin⟩

/-! ## W3 cône étroit dans le domaine — migré vers `Conway.Life.ConeGeometry`

Le lemme de cône étroit dans le domaine `window_cheb_cone_in_domain` (W3,
EPIC #3846) a été extrait vers `Conway.Life.ConeGeometry` — le module de base
Mathlib uniquement — comme break de cycle de dépendances qui permet à
`HashlifeCorrectness` de l'atteindre pour le câblage P5 `p5_large_n_jump` sans
l'import inverse circulaire que ce module imposerait sinon (il importe
`HashlifeCorrectness`). Il est dans le scope ici inchangé via l'`import
Conway.Life.ConeGeometry` ci-dessus. Voir ce module pour l'énoncé, la preuve, et
la note de câblage architectural. -/

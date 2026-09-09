/-
Copyright (c) 2026 CoursIA. Tous droits réservés.
Distribué sous licence Apache 2.0 comme décrit dans le fichier LICENSE.

## Livrable B (#9568) — le fragment « fenêtre à marge » (premier cran Spartan logic)

Module compagnon de `Conway.Life.HashlifeCorrectness` (l'infrastructure de correction
`hashlife_correct` / `centralCorrect` / `centralCorrect_mem`, c.153) et du bestiaire
`Conway.Life.AdversarialBattery` (#9589). Il formalise le **premier cran de relativisation
géométrique** du cadrage user (2026-08-06, issue #9568) : prouver que Hashlife « marche
bien en Spartan logic » — une correction **relative/bornée**, connue pour être bien plus
facile que l'universelle et **suffisante pour les corollaires réels visés**.

### Le fragment

Le fragment des configurations dont le **support tient dans la fenêtre centrale avec une
marge de garde égale à l'horizon `2^k`** : chaque cellule vivante est à au moins `2^k`
cellules de la frontière du domaine MacroCell, donc sur les `2^k` générations de
l'horizon, **rien ne peut jamais saigner hors de la fenêtre** — le cône de lumière
Chebyshev de rayon `2^k` reste strictement à l'intérieur de la marge.

Prédicat candidat :
  `supportInMargin c k := BoxAssezGrandN (c.toGrid (0, 0)) (2^k)`

On utilise la variante **n-aware** `BoxAssezGrandN` (padding `max 2 n`, satisfiable pour
tout `n`) plutôt que la fixed-frame `BoxAssezGrand` (plafonnée à `n ≤ 2` par
`boxAssezGrand_nonempty_le_two`) : c'est ce qui rend le fragment **satisfiable pour tout
horizon `2^k`** et valide l'argument de suffisance « choisir `k` par horizon » ci-dessous.
Le sanity-check `cexBlock1_supportInMargin_k2` exhibe `2^2 = 4` sur le bloc 2×2 —
impossible avec la fixed-frame, possible ici.

### L'énoncé-cadre `hashlife_correct_margin` (sorry documenté, verdict INTRINSIC)

Sous le fragment `supportInMargin c k` et l'hypothèse de correction centrale
`centralCorrect c k` (le whnf-wall bypass de c.153), l'égalité de grille globale
`evolveHashlifeFast (2^k) (c.toGrid (0,0)) = evolve (2^k) (c.toGrid (0,0))` tient sur tout
l'horizon `2^k`. La preuve requiert l'**assemblage borné P4/P5** — comment `centralCorrect`
(correction MacroCell-level au niveau `k`) se relève en égalité de grille globale via la
récursion Hashlife, avec la marge contenant le cône de lumière à chaque saut. Cet
assemblage est le contenu des PR #9745/#9760 d'ai-01 (c.92–c.94, `p4_nw_overlap_wall`
sorry 10→9) et reste le cœur de recherche ouvert. L'énoncé est livré comme **cadre**
(acceptance B : sorry documenté acceptable au premier commit), pas comme une preuve
manquée — verdict INTRINSIC sur la partie non prouvée, avec la raison.

### Pourquoi ce fragment GÉOMÉTRIQUE suffit pour les corollaires réels

La « Spartan logic » au sens strict (still lifes + gliders, vocabulaire Goucher) est un
raffinement ultérieur ; ce fragment géométrique la précède et suffit déjà :

1. **Machine de Turing finie (T pas)** : toute computation de MT pour `T` pas s'embed dans
   le fragment en choisissant `k` tel que `2^k ≥ T` (horizon) avec la marge de garde. L'aspect
   non-borné en temps se traite par **ré-invocation à `k` croissant** (le wrapper Hashlife
   standard « expand puis récurse ») — chaque horizon instancié vit dans le fragment.
2. **Tuile OTCA / réplication Gemini** : ces patterns ont un support borné connu ; on
   choisit `k` par la taille du pattern + horizon de réplication, et la marge contient le
   cône de lumière de la phase de réplication.
3. **GOL-dans-GOL** : l'émulation d'un GOL fini dans un GOL plus grand s'embed avec marge
   par construction (le GOL hôte fournit la fenêtre centrale, l'invité le support).

### Contraintes

FR canonique + sibling `_en` (gate #4980 : refus merge FR-only). Le `sorry` documenté est
accepté explicitement au titre de l'acceptance B. Sanity-checks réels (décidables au
kernel) sur le bestiaire ci-dessous. EPIC #3846 / #6724 / #9568.
-/

/-
  Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier est **FR
  canonique**, avec son miroir anglais dans le fichier sibling
  `HashlifeMarginFragment_en.lean`. Les énoncés de théorèmes, les tactiques Lean, les noms
  de lemmes et les références Mathlib restent en anglais (compat Mathlib 4) ; seules les
  docstrings et ce bloc d'en-tête diffèrent entre les deux fichiers.
-/

import Conway.Life.AdversarialBattery
import Conway.Life.HashlifeCorrectness
import Conway.Life.LightCone

namespace Conway
namespace Life

/-! ## Le prédicat de fragment `supportInMargin` -/

/-- **Le fragment « fenêtre à marge » (Livrable B, #9568).** Le support de la cellule
    `c` (rendu en grille à l'origine) tient dans la fenêtre centrale avec une marge de
    garde égale à l'horizon `2^k` : chaque cellule vivante est à au moins `2^k` de la
    frontière du domaine MacroCell. Sur les `2^k` générations de l'horizon, le cône de
    lumière Chebyshev (rayon `2^k`) reste strictement à l'intérieur de la marge, donc
    **rien ne saigne hors de la fenêtre**.

    On utilise la variante **n-aware** `BoxAssezGrandN` (padding `max 2 n`, satisfiable
    pour tout `n`) plutôt que la fixed-frame `BoxAssezGrand` (plafonnée à `n ≤ 2` par
    `boxAssezGrand_nonempty_le_two`) : c'est ce qui rend le fragment satisfiable pour tout
    horizon `2^k` et valide l'argument de suffisance « choisir `k` par horizon ». -/
def supportInMargin (c : MacroCell) (k : Nat) : Prop :=
  BoxAssezGrandN (c.toGrid (0, 0)) (2^k)

/-- **Décidabilité du fragment** (compagnon de l'instance `Decidable (BoxAssezGrandN)`,
    HashlifeCorrectness L227). `supportInMargin` est une `def ... : Prop` séparée, donc
    l'instance `Decidable (BoxAssezGrandN g n)` ne se propage pas automatiquement à travers
    elle (Lean ne réduit pas une `def` non-`@[reducible]` lors de la synthèse d'instance).
    On déclare l'instance compagnon, exactement comme `BoxAssezGrandN` déclare la sienne
    au-dessus de l'instance `Decidable` native — pattern canonique du codebase. -/
instance (c : MacroCell) (k : Nat) : Decidable (supportInMargin c k) :=
  inferInstanceAs (Decidable (BoxAssezGrandN (c.toGrid (0, 0)) (2^k)))

/-- **Trivialité du fragment** (relocalisé c.8206, #9568). `supportInMargin`
    contient TOUTE MacroCell à TOUT horizon `k` — c'est une **tautologie**,
    prouvé sur place depuis `boxAssezGrandN_trivial` (à côté de
    `BoxAssezGrandN` dans `Foundation`, c.8206). L'hypothèse
    `h_margin : supportInMargin c k` de `hashlife_correct_margin` ne restreint
    donc rien ; voir la note *inconditionnel-en-attente* dans la docstring
    de ce théorème. -/
theorem supportInMargin_trivial (c : MacroCell) (k : Nat) :
    supportInMargin c k :=
  boxAssezGrandN_trivial _ _

/-! ## L'énoncé-cadre `hashlife_correct_margin` (sorry documenté, INTRINSIC)

Sous le fragment + `centralCorrect c k`, l'égalité de grille globale
`evolveHashlifeFast (2^k) (c.toGrid (0,0)) = evolve (2^k) (c.toGrid (0,0))` tient sur
l'horizon `2^k`. Le `sorry` est l'assemblage borné P4/P5 (ai-01, #9745/#9760) : comment
`centralCorrect` (correction MacroCell-level) se relève en égalité globale via la récursion
Hashlife, la marge contenant le cône de lumière à chaque saut. Énoncé-cadre (acceptance B),
pas une preuve manquée. -/

/-- **Correction Hashlife relative au fragment « fenêtre à marge » (Livrable B, #9568).**
    Si le support de `c` tient dans la fenêtre centrale avec marge de garde `2^k`
    (`supportInMargin`), et si la correction centrale `centralCorrect c k` tient au
    niveau `k`, alors `evolveHashlifeFast` coïncide avec l'évolution de référence `evolve`
    sur tout l'horizon `2^k` — la marge garantit qu'aucun cône de lumière ne saigne hors de
    la fenêtre pendant la récursion Hashlife.

    **Suffisance pour les corollaires réels** (le cœur pédagogique de ce Livrable B) :
    toute computation bornée s'embed dans le fragment en choisissant `k` par horizon.
    (1) **MT finie (T pas)** : choisir `2^k ≥ T` + marge ; l'aspect non-borné en temps se
    traite par ré-invocation à `k` croissant (wrapper « expand puis récurse »). (2) **Tuile
    OTCA / réplication Gemini** : support borné connu, `k` par taille + horizon de
    réplication. (3) **GOL-dans-GOL** : l'émulation d'un GOL fini dans un GOL plus grand
    s'embed avec marge par construction. La Spartan logic stricte (still lifes + gliders,
    vocabulaire Goucher) est un raffinement ultérieur de ce fragment géométrique.

    **Verdict sur la preuve : INTRINSIC.** Le pont de `centralCorrect` (correction
    MacroCell-level) vers l'égalité de grille globale requiert l'assemblage borné P4/P5 —
    `p4_nw_overlap_wall` et sa chaîne helper 4-stage (PR #9745/#9760, ai-01 c.92–c.94,
    sorry 10→9). C'est le cœur de recherche ouvert ; cet énoncé en est le cadre honnête
    (acceptance B : sorry documenté acceptable au premier commit).

    **Note de cadrage (c.212, 2026-08-11) — *inconditionnel-en-attente*.** Le prédicat
    `supportInMargin` est une **tautologie** (prouvé par `supportInMargin_trivial`,
    JumpCapture.lean:120) : `gridFrameN n g` pad par `max 2 n ≥ n` et `cellMargin` côté
    proche est non strict, donc `BoxAssezGrandN g n` est vraie pour **toute** grille et
    **tout** `n`. L'hypothèse `h_margin : supportInMargin c k` ne restreint donc rien —
    l'énoncé effectif est l'inconditionnel complet, sous un habillage géométrique qui ne
    relativise pas. La vraie relativisation est ailleurs (prédicat `jumpCaptured`,
    JumpCapture.lean §3, avec témoin `jumpCaptured_not_trivial`). Ce `sorry` reste donc
    le **cœur de recherche ouvert**, indépendamment de la fragilité de son habillage —
    verdict INTRINSIC préservé, contenu scientifique non-affaibli par ce constat. -/
theorem hashlife_correct_margin (c : MacroCell) (k : Nat)
    (h_margin : supportInMargin c k) (h_central : centralCorrect c k) :
    evolveHashlifeFast (2^k) (c.toGrid (0, 0)) = evolve (2^k) (c.toGrid (0, 0)) := by
  -- INTRINSIC: bounded P4/P5 assembly (ai-01, #9745/#9760). The margin `supportInMargin`
  -- contains the Chebyshev light-cone (radius 2^k) of the jump, so the hashlife recursion
  -- never reads outside the central window; `centralCorrect` (c.153 whnf-wall bypass) then
  -- lifts to the global grid equality over the horizon. The inductive lift through the
  -- MacroCell recursion (`p4_nw_overlap_wall` and the offset-matching assembly) is the
  -- open P4/P5 heart — sorry documenté (acceptance B).
  sorry

/-! ## Assemblage P4.4 — réduction sorry-stable (tranche 2, #13483)

Diagnostic du 2026-09-04 (c.5539811910) : toutes les briques préliminaires sont prouvées
(`p5_large_n_jumpN` b3', P4 complet, les 4 murs bornés sans sorry) — le sorry de
`hashlife_correct_margin` est l'assemblage lui-même. Décomposition :

- **L1** — l'hypothèse `h_margin` est gratuite : `supportInMargin` est tautologique
  (`supportInMargin_trivial`), l'énoncé effectif est l'inconditionnel sous `centralCorrect`.
- **L2** — le but se réduit à l'hypothèse de la machine N : `hashlife_correctN` (prouvé,
  HashlifeCorrectness) donne l'égalité globale dès `hcap : ∀ t ≤ 2^k, jumpCaptured …`.
  C'est le lemme ci-dessous, sorry-free.
- **L3 (cœur ouvert)** — relever `centralCorrect c k` (égalité de grille RESTREINTE à la
  fenêtre finale) en `hcap` (confinement de la TRAJECTOIRE entière). C'est l'assemblage
  borné P4/P5 proprement dit : un argument de structure de la récursion Hashlife (la marge
  contient le cône de lumière à chaque saut), PAS un argument de réversibilité — le GoL
  n'est pas réversible, le cône rétrograde ne contraint pas les états intermédiaires.
- **L4** — la jambe d'égalité : `centralCorrect` est une égalité restreinte, le but est
  global ; la fermeture exige que les deux grilles portent leur support dans la fenêtre
  (`jumpCaptured` du final + borne forward du support de `evolve`).

`hashlife_correct_margin c k h_margin h_central` se déchargerait par
`hashlife_correct_margin_of_hcap c k h_central (L3 c k h_central)` : L3/L4 sont les seuls
maillons ouverts. -/

/-- **P4.4 L2 — copie locale byte-identical de `jumpCaptured`** (pattern
    d'inlining du lake, cf HashlifeCorrectness L6436 : le `jumpCaptured` que
    consomme `hashlife_correctN` y est `private` — inline de
    `Conway.Life.JumpCapture.jumpCaptured` pour casser le cycle d'import
    A↔B, `JumpCapture.lean` important CE module). Ce module ne peut donc ni
    voir le private ni importer `JumpCapture` (cycle) : même remède, copie
    byte-identical. La defeq des corps identiques (delta-unfolding des deux
    `def` semi-reducibles) fait passer l'appel à `hashlife_correctN` ci-dessous. -/
private def jumpCapturedF (c : MacroCell) : Bool :=
  (evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0))).all fun p =>
    decide ((2 ^ c.level : Int) ≤ p.1) &&
    decide (p.1 < (2 ^ c.level : Int) + ((2 ^ (c.level + 1) : Nat) : Int)) &&
    decide ((2 ^ c.level : Int) ≤ p.2) &&
    decide (p.2 < (2 ^ c.level : Int) + ((2 ^ (c.level + 1) : Nat) : Int))

/-- **Interface (c) tranche 3, étape 1 — dépliage propositionnel de `jumpCapturedF`.**
    Même preuve que `jumpCaptured_iff` (JumpCapture L264), répliquée localement :
    ce module ne peut pas importer `JumpCapture` (cycle d'import, cf docstring de
    `jumpCapturedF` ci-dessus). C'est la porte d'entrée du corridor (LightCone,
    langage `isAlive`) dans le prédicat Bool que `hcap` exige. -/
theorem jumpCapturedF_iff (c : MacroCell) :
    jumpCapturedF c = true ↔
      ∀ p ∈ evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0)),
        (2 ^ c.level : Int) ≤ p.1 ∧
          p.1 < (2 ^ c.level : Int) + ((2 ^ (c.level + 1) : Nat) : Int) ∧
          (2 ^ c.level : Int) ≤ p.2 ∧
          p.2 < (2 ^ c.level : Int) + ((2 ^ (c.level + 1) : Nat) : Int) := by
  unfold jumpCapturedF
  rw [List.all_eq_true]
  constructor
  · intro h p hp
    have hb := h p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    tauto
  · intro h p hp
    have hb := h p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    tauto

/-- **Interface (c) tranche 3, étape 2 — le corridor forward ferme le saut dès
    que la fenêtre absorbe la dérive.** Pont entre le langage du corridor
    (`evolve_support_dilation_from`, brique (a-b) de la tranche 3, LightCone :
    confinement `isAlive` de la trajectoire) et le prédicat Bool `jumpCapturedF` :
    si le support de la grille paddée tient dans la boîte `[a, b)` (`h₀`) et que
    la boîte dilatée de `2^c.level` — la dérive forward maximale du saut — reste
    dans la fenêtre du test `[2^lvl, 2^lvl + 2^(lvl+1))²` (`hwin1..4`), alors le
    saut est capturé. La preuve ne fait aucune hypothèse de réversibilité (le GoL
    n'est pas réversible) : le relais forward borne la dérive depuis `t₀ = 0`,
    l'inclusion de fenêtres est linéaire. Les hypothèses `h₀`/`hwin` sont ce que
    la partie géométrique de L3 (caractériser le niveau de la reconstruction le
    long de la trajectoire) doit établir — ce lemme en est la cloison nette :
    confinement forward [prouvé par le corridor] séparé de géométrie de fenêtre
    [ouverte]. Les bornes de `hwin` portent le cast nat explicite
    `((2 ^ c.level : Nat) : Int)` — même atome que celle du corridor (sinon la
    puissance est forcée dans Int et omega la voit déconnectée). -/
theorem jumpCapturedF_of_dilation (c : MacroCell) (a b : Int × Int)
    (h₀ : ∀ p, isAlive ((padCenter2 c).toGrid (0, 0)) p = true →
      a.1 ≤ p.1 ∧ p.1 < b.1 ∧ a.2 ≤ p.2 ∧ p.2 < b.2)
    (hwin1 : ((2 ^ c.level : Nat) : Int) ≤ a.1 - ((2 ^ c.level : Nat) : Int))
    (hwin2 : b.1 + ((2 ^ c.level : Nat) : Int) ≤
      ((2 ^ c.level : Nat) : Int) + ((2 ^ (c.level + 1) : Nat) : Int))
    (hwin3 : ((2 ^ c.level : Nat) : Int) ≤ a.2 - ((2 ^ c.level : Nat) : Int))
    (hwin4 : b.2 + ((2 ^ c.level : Nat) : Int) ≤
      ((2 ^ c.level : Nat) : Int) + ((2 ^ (c.level + 1) : Nat) : Int)) :
    jumpCapturedF c = true := by
  rw [jumpCapturedF_iff]
  intro p hp
  have hq : isAlive (evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0))) p = true := by
    rw [isAlive]
    exact List.elem_iff.mpr hp
  obtain ⟨c1, c2, c3, c4⟩ :=
    evolve_support_dilation_from 0 (2 ^ c.level) ((padCenter2 c).toGrid (0, 0)) a b
      (Nat.zero_le _) h₀ p hq
  simp only [Nat.sub_zero] at c1 c2 c3 c4
  -- le but (issu de la définition) parle en `(2 ^ lvl : Int)` (pow dans Int) :
  -- la relation avec le cast nat du corridor est fournie explicitement, puis
  -- tout est linéaire.
  have hpow : (2 ^ c.level : Int) = ((2 ^ c.level : Nat) : Int) := by
    exact (Nat.cast_pow 2 c.level).symm
  omega

/-- **Une période se répète** (copie locale byte-identical de
    `evolve_mul_of_period`, JumpCapture L518 — ce module ne peut pas
    l'importer, cycle A↔B, cf docstring de `jumpCapturedF`) : si `g` est de
    période `T` (au sens faible `evolve T g = g`), alors tout multiple
    `m·T` d'étapes la ramène à elle-même. Par induction sur `m` via
    `evolve_add`. -/
theorem evolve_mulF_of_period {T : Nat} (g : Grid)
    (hper : evolve T g = g) (m : Nat) :
    evolve (m * T) g = g := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : (m + 1) * T = m * T + T := by ring
    rw [hsplit, evolve_add, hper, ih]

/-- **Borne de domaine d'une cellule bien formée** (copie locale
    byte-identical de `cellWf_toGrid_bounds`, JumpCapture L475 — cycle
    d'import A↔B, cf ci-dessus) : toute cellule vivante du `toGrid` d'une
    `MacroCell` bien formée (au sens `cellWf`) de niveau `n` vit dans le
    carré `[r0, r0 + 2^n) × [c0, c0 + 2^n)`. Induction sur `cellWf` :
    chaque feuille émet au plus son coin, chaque nœud distribue ses quatre
    enfants de niveau `n` sur les quadrants d'offset `0` ou `2^n`, donc le
    nœud de niveau `n+1` couvre `[·, · + 2^(n+1))`. -/
theorem cellWfF_toGrid_bounds {c : MacroCell} (hc : cellWf c) (r0 c0 : Int)
    {p : Int × Int} (hp : p ∈ c.toGrid (r0, c0)) :
    r0 ≤ p.1 ∧ p.1 < r0 + (2 ^ c.level : Int) ∧
      c0 ≤ p.2 ∧ p.2 < c0 + (2 ^ c.level : Int) := by
  induction hc generalizing r0 c0 with
  | leaf b =>
    rw [mem_toGrid] at hp
    cases b with
    | true =>
      simp only [MacroCell.toCellsAux, Prod.fst, Prod.snd, List.mem_singleton] at hp
      obtain ⟨hrr, hcc⟩ : p.1 = r0 ∧ p.2 = c0 := Prod.ext_iff.mp hp
      subst hrr hcc
      simp only [MacroCell.level, pow_zero]
      omega
    | false => simp [MacroCell.toCellsAux] at hp
  | node hnw hne hsw hse hne_lvl hsw_lvl hse_lvl inw ine isw ise =>
    rename_i nw ne sw se
    simp only [mem_toGrid, MacroCell.toCellsAux, List.mem_append, or_assoc] at hp
    push_cast at hp
    have hlvl : MacroCell.level (MacroCell.node nw ne sw se) = nw.level + 1 := by
      simp only [MacroCell.level]; omega
    have hpos : (0 : Int) ≤ 2 ^ nw.level := by positivity
    rcases hp with hp | hp | hp | hp
    · have hb := inw r0 c0 (mem_toGrid.mpr hp)
      rw [hlvl, pow_succ]
      omega
    · have hb := ine r0 (c0 + (2 ^ nw.level : Int)) (mem_toGrid.mpr hp)
      simp only [← hne_lvl, ← hsw_lvl, ← hse_lvl] at hb
      rw [hlvl, pow_succ]
      omega
    · have hb := isw (r0 + (2 ^ nw.level : Int)) c0 (mem_toGrid.mpr hp)
      simp only [← hne_lvl, ← hsw_lvl, ← hse_lvl] at hb
      rw [hlvl, pow_succ]
      omega
    · have hb := ise (r0 + (2 ^ nw.level : Int)) (c0 + (2 ^ nw.level : Int))
        (mem_toGrid.mpr hp)
      simp only [← hne_lvl, ← hsw_lvl, ← hse_lvl] at hb
      rw [hlvl, pow_succ]
      omega

/-- **Interface (c) tranche 3, étape 3 — la classe périodique `T ∣ 2^k` est
    capturée.** Version `jumpCapturedF` du critère 3
    (`jumpCaptured_of_period_divides`, JumpCapture L533) : tout motif de
    période `T ≥ 1` divisant l'horizon du jump `2^c.level`, porté par une
    cellule bien formée de niveau `k ≥ 1`, satisfait le prédicat de capture.
    La génération finale du jump est le motif lui-même (période répétée),
    inchangé dans son cadrage `padCenter2` — donc dans la fenêtre centrale
    par la géométrie `[3·2^(k-1), 5·2^(k-1)) ⊂ [2^k, 3·2^k)`.

    **Complément orthogonal du corridor** (étape 2,
    `jumpCapturedF_of_dilation`) : le corridor exige une fenêtre qui absorbe
    la dérive forward `2^lvl` — arithmétiquement fermée au niveau plein pour
    tout contenu non vide (les `hwin` forcent une boîte de largeur nulle).
    La classe périodique, elle, ne dérive pas du tout : l'invariance
    temporelle exacte `evolve T g = g` remplace la sur-approximation du
    corridor. C'est la classe hcap-atteignable identifiée par le scoping
    tranche 3 (c.5551593604) : natures mortes (`T = 1`) et oscillateurs à
    période dyadique (`T ∣ 2^k`), les témoins du langage multi-cycles. -/
theorem jumpCapturedF_of_period_divides (c : MacroCell) (hwf : c.wf = true)
    (hlvl : 1 ≤ c.level) {T : Nat} (_hT : 0 < T)
    (hper : evolve T (c.toGrid (0, 0)) = c.toGrid (0, 0))
    (hdiv : T ∣ 2 ^ c.level) :
    jumpCapturedF c = true := by
  have hcw : cellWf c := cellWf_of_wf c hwf
  obtain ⟨m, hm⟩ := hdiv
  have hself : evolve (2 ^ c.level) (c.toGrid (0, 0)) = c.toGrid (0, 0) := by
    rw [hm, Nat.mul_comm]
    exact evolve_mulF_of_period _ hper m
  have hfinal : evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0))
      = shift ((3 * 2 ^ (c.level - 1) : Int), (3 * 2 ^ (c.level - 1) : Int))
          (c.toGrid (0, 0)) := by
    rw [padCenter2_toGrid_shift c hlvl, ← evolve_shift, hself]
  rw [jumpCapturedF_iff]
  intro p hp
  rw [hfinal, mem_shift] at hp
  -- Bornes du contenu dans son propre cadrage `[0, 2^c.level)²`…
  obtain ⟨hb1, hb2, hb3, hb4⟩ := cellWfF_toGrid_bounds hcw 0 0 hp
  dsimp only at hb1 hb2 hb3 hb4
  -- …et relations linéaires entre les trois atomes `2^(c.level-1)`,
  -- `2^c.level`, `2^(c.level+1)` — le reste est `omega`.
  have hpow : (2 ^ c.level : Int) = 2 * (2 ^ (c.level - 1) : Int) := by
    have hsplit : c.level = (c.level - 1) + 1 := by omega
    conv_lhs => rw [hsplit]
    rw [pow_succ]
    ring
  have hnext : ((2 ^ (c.level + 1) : Nat) : Int)
      = (2 ^ c.level : Int) + (2 ^ c.level : Int) := by
    rw [Nat.cast_pow, pow_succ]
    ring
  have hy : (0 : Int) ≤ 2 ^ (c.level - 1) := by positivity
  omega

/-- **Corollaire still-life** (`T = 1`) : toute nature morte — motif avec
    `evolve 1 g = g`, au sens fort un point fixe de `step` — est capturée
    à tout niveau `k ≥ 1`. C'est la forme consommable de la classe pour
    les objets Life usuels (bloc, ruche, pain, baril…) : le premier maillon
    de L3 pour la classe `T = 1` — quel que soit `t ≤ 2^k`, `evolve t g = g`
    et la reconstruction de la trajectoire est la cellule elle-même. -/
theorem jumpCapturedF_of_still_life (c : MacroCell) (hwf : c.wf = true)
    (hlvl : 1 ≤ c.level)
    (hfix : evolve 1 (c.toGrid (0, 0)) = c.toGrid (0, 0)) :
    jumpCapturedF c = true :=
  jumpCapturedF_of_period_divides c hwf hlvl (T := 1) (by omega) hfix (by omega)

/-- **P4.4 L2 (réduction sorry-stable).** L'égalité globale du cadre se réduit à
    l'hypothèse de capture de trajectoire de la machine N : `hashlife_correctN` (prouvé)
    clôt le but dès `hcap`. Les maillons ouverts sont L3 (relever `centralCorrect c k`
    en `hcap`) et L4 (égalité restreinte → globale). -/
theorem hashlife_correct_margin_of_hcap (c : MacroCell) (k : Nat)
    (h_central : centralCorrect c k)
    (hcap : ∀ t ≤ 2^k, jumpCapturedF
      (gridToMacroCellWithOffset (evolve t (c.toGrid (0, 0)))).2 = true) :
    evolveHashlifeFast (2^k) (c.toGrid (0, 0)) = evolve (2^k) (c.toGrid (0, 0)) :=
  hashlife_correctN (2^k) (c.toGrid (0, 0)) hcap

/-! ## L3 classe `T = 1` — hcap des natures mortes (tranche 3, étape 4)

Premier maillon L3 **entièrement clos** : pour la classe des natures mortes
(`evolve 1 g = g`, point fixe de `step`), l'hypothèse `hcap` de la réduction L2
est établie de bout en bout — la trajectoire est constante, la reconstruction
est constante, et le saut est capturé par `jumpCapturedF_of_still_life`. Le
chaînage : round-trip ÉGALITÉ de la reconstruction pour grilles canoniques
(`Canonical.ext`, rigidité des listes triées-dédupliquées) → transport du point
fixe à l'origine via `toGrid_shift_grid`/`evolve_shift` → capture. -/

/-- **Round-trip ÉGALITÉ de la reconstruction (grilles canoniques).**
    La forme générale du docstring de `gridToMacroCellWithOffset` — jusqu'ici
    établie seulement au niveau des membres
    (`mem_toGrid_gridToMacroCellWithOffset`, MacroCell L857) — se renforce en
    **égalité de listes** dès que `g` est canonique : les deux grilles sont
    canoniques (`toGrid` est une image `sortDedup`, `g` l'est par hypothèse)
    et ont les mêmes membres, donc sont égales par rigidité
    (`Canonical.ext`). C'est le pont members→égalité qui manquait pour
    transporter des équivalences de point fixe (des `Prop` d'égalité) à
    travers la reconstruction. -/
theorem toGrid_gridToMacroCellWithOffset_eq (g : Grid) (hg : Canonical g) :
    (gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1 = g :=
  Canonical.ext (canonical_sortDedup _) hg (fun p => mem_toGrid_gridToMacroCellWithOffset g p)

/-- **Transport du point fixe à la reconstruction (rendue à l'origine).**
    Si `g` est une nature morte canonique, alors la MacroCell reconstruite
    rendue à l'origine `(gridToMacroCellWithOffset g).2.toGrid (0, 0)` est
    elle-même un point fixe de `evolve 1` : la navette `toGrid_shift_grid`
    ramène l'origine à un shift de la grille cadrée, `evolve_shift` fait
    commuter le shift avec `evolve`, `evolve_congr` transporte l'évolution au
    cadre de `g` (même membres), et le round-trip ÉGALITÉ referme la boucle.
    C'est l'hypothèse `hfix` exacte qu'exige `jumpCapturedF_of_still_life`
    sur la reconstruction — désormais disponible pour la classe `T = 1`. -/
theorem still_life_fix_toGrid_zero (g : Grid) (hg : Canonical g)
    (hfix : evolve 1 g = g) :
    evolve 1 ((gridToMacroCellWithOffset g).2.toGrid (0, 0))
      = (gridToMacroCellWithOffset g).2.toGrid (0, 0) := by
  have hrt : (gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1
      = g := toGrid_gridToMacroCellWithOffset_eq g hg
  have hshift : (gridToMacroCellWithOffset g).2.toGrid (0, 0)
      = shift (0 - (gridToMacroCellWithOffset g).1.1,
               0 - (gridToMacroCellWithOffset g).1.2)
          ((gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1) :=
    toGrid_shift_grid _ 0 0 _ _
  rw [hshift, ← evolve_shift, hrt, hfix]

/-- **hcap de la classe `T = 1` (natures mortes) — la capture de la
    reconstruction.** Pour toute nature morte `g` (canonique ou vide), la
    MacroCell reconstruite satisfait le prédicat de saut : c'est l'hypothèse
    de capture que la réduction L2 consomme, établie pour la classe entière.
    Cas non vide : `jumpCapturedF_of_still_life` consomme les trois hypothèses
    désormais disponibles — wf (`buildFromGrid_wf`), niveau (la borne
    n-aware : `2 < 2^lvl` dès `g ≠ []`, donc `1 ≤ lvl`) et point fixe
    (`still_life_fix_toGrid_zero`). Cas vide : la reconstruction est une
    feuille morte de niveau 0, la grille paddée est vide, et `List.all` sur
    `[]` est trivialement vrai — décidé par le noyau. -/
theorem jumpCapturedF_reconstruction_of_still_life (g : Grid) (hg : Canonical g)
    (hfix : evolve 1 g = g) :
    jumpCapturedF (gridToMacroCellWithOffset g).2 = true := by
  by_cases hne : g = []
  · subst hne
    decide
  · apply jumpCapturedF_of_still_life _ ?_ ?_ ?_
    · unfold gridToMacroCellWithOffset
      exact buildFromGrid_wf g _ _ _
    · have hN := gridToMacroCellWithOffsetN_level_gt_n 2 g hne
      rw [gridToMacroCellWithOffsetN_le_two_eq 2 g (by omega)] at hN
      cases hL : (gridToMacroCellWithOffset g).2.level with
      | zero => rw [hL] at hN; exact absurd hN (by decide)
      | succ m => omega
    · exact still_life_fix_toGrid_zero g hg hfix

/-- **hcap des natures mortes, trajectoire complète.** Pour toute nature
    morte `g`, **tout** instant `t` (a fortiori tout `t ≤ 2^k`) : la
    trajectoire est constante (`evolve t g = g`, période 1 répétée via
    `evolve_mulF_of_period`), donc la reconstruction le long de la trajectoire
    est l'objet constant `gridToMacroCellWithOffset g`, dont le saut est
    capturé. Avec le corollaire d'assemblage ci-dessous, c'est le **premier
    maillon L3 entièrement prouvé** de la décomposition P4.4 : relever une
    classe de motifs en l'hypothèse `hcap` de la machine N, sans aucun sorry. -/
theorem hcap_of_still_life (g : Grid) (hg : Canonical g)
    (hfix : evolve 1 g = g) (t : Nat) :
    jumpCapturedF (gridToMacroCellWithOffset (evolve t g)).2 = true := by
  have hself : evolve t g = g := by
    have hmul := evolve_mulF_of_period g hfix t
    rwa [Nat.mul_one] at hmul
  rw [hself]
  exact jumpCapturedF_reconstruction_of_still_life g hg hfix

/-- **L3 clos pour la classe `T = 1` : correction Hashlife des natures
    mortes.** Corollaire d'assemblage — le premier cas de la décomposition
    P4.4 où le maillon L3 (relever une classe de motifs en `hcap`) est
    **entièrement prouvé** : pour toute MacroCell dont la grille rendue à
    l'origine est une nature morte, l'égalité globale `hashlife_correctN`
    s'applique à tout horizon `2^k` sous `centralCorrect`. Il ne reste que
    L4 (l'égalité restreinte `centralCorrect` elle-même), qui vit dans
    l'hypothèse — exactement la cloison annoncée par la réduction L2. -/
theorem hashlife_correct_margin_of_still_life (c : MacroCell) (k : Nat)
    (h_central : centralCorrect c k)
    (hfix : evolve 1 (c.toGrid (0, 0)) = c.toGrid (0, 0)) :
    evolveHashlifeFast (2^k) (c.toGrid (0, 0)) = evolve (2^k) (c.toGrid (0, 0)) :=
  hashlife_correct_margin_of_hcap c k h_central
    (fun t _ => hcap_of_still_life _ (canonical_sortDedup _) hfix t)

/-! ## L3 géométrie — bornes de la boîte et niveau de la reconstruction (tranche 3, étape 5)

Le scoping 3-(c) (c.5551298160) identifie la jambe « géométrie » de L3 : au niveau
adaptatif, la fenêtre `[2^lvl, 3·2^lvl)` doit absorber la boîte du corridor. Deux
briques se posent : (i) les **bornes de la boîte englobante** d'une grille dont le
support est contraint — `gridRowMin` est minorée, `gridRowMax` est majorée (et
colonnes) ; (ii) la **borne de niveau** de la reconstruction
`gridToMacroCellWithOffset g` en fonction de la boîte. Ce sont les prémisses
géométriques pour la capture au niveau adaptatif. -/

/-- **Aide : un `foldl` de `max` (via `proj`) reste strictement sous `b`** si le
    seed et chaque élément le sont. Induction directe sur la liste (invariant du
    `max`). -/
theorem foldl_proj_max_lt_of_mem_lt (ps : Grid) (proj : Int × Int → Int)
    (acc : Int) (b : Int) (hb : acc < b)
    (h₀ : ∀ q, q ∈ ps → proj q < b) :
    ps.foldl (fun m q => max m (proj q)) acc < b := by
  induction ps generalizing acc with
  | nil => simpa using hb
  | cons q qs ih =>
    have hq : proj q < b := h₀ q (by simp)
    have hb' : max acc (proj q) < b := max_lt_iff.mpr ⟨hb, hq⟩
    exact ih _ hb' (fun r hr => h₀ r (List.mem_cons_of_mem q hr))

/-- **Borne inférieure de `gridRowMin` par une boîte.** Si toute cellule de `g`
    vérifie `a ≤ p.1`, alors `a ≤ gridRowMin g` : le minimum des lignes est une des
    lignes de `g` (`foldl_proj_min_attained`), donc il hérite de la borne. La
    grille doit être non vide : sur la grille vide, `gridRowMin` vaut `0` par
    défaut et la borne serait fausse. -/
theorem gridRowMin_lower_bound (g : Grid) (a : Int) (hg : g ≠ [])
    (h₀ : ∀ p, p ∈ g → a ≤ p.1) :
    a ≤ gridRowMin g := by
  cases g with
  | nil => exact absurd rfl hg
  | cons p₀ ps =>
    simp only [gridRowMin]
    rcases foldl_proj_min_attained ps (·.1) p₀.1 with hcase | ⟨p, hp, hval⟩
    · rw [hcase]
      exact h₀ p₀ (by simp)
    · rw [hval]
      exact h₀ p (List.mem_cons_of_mem p₀ hp)

/-- **Borne supérieure de `gridRowMax` par une boîte.** Si toute cellule de `g`
    vérifie `p.1 < b`, alors `gridRowMax g < b` : le maximum des lignes hérite de
    la borne (invariant du `foldl` de `max`). -/
theorem gridRowMax_upper_bound (g : Grid) (b : Int) (hg : g ≠ [])
    (h₀ : ∀ p, p ∈ g → p.1 < b) :
    gridRowMax g < b := by
  cases g with
  | nil => exact absurd rfl hg
  | cons p₀ ps =>
    simp only [gridRowMax]
    exact foldl_proj_max_lt_of_mem_lt ps (·.1) p₀.1 b (h₀ p₀ (by simp))
      (fun q hq => h₀ q (List.mem_cons_of_mem p₀ hq))

/-- **Borne inférieure de `gridColMin` par une boîte** (miroir colonne de
    `gridRowMin_lower_bound`). -/
theorem gridColMin_lower_bound (g : Grid) (a : Int) (hg : g ≠ [])
    (h₀ : ∀ p, p ∈ g → a ≤ p.2) :
    a ≤ gridColMin g := by
  cases g with
  | nil => exact absurd rfl hg
  | cons p₀ ps =>
    simp only [gridColMin]
    rcases foldl_proj_min_attained ps (·.2) p₀.2 with hcase | ⟨p, hp, hval⟩
    · rw [hcase]
      exact h₀ p₀ (by simp)
    · rw [hval]
      exact h₀ p (List.mem_cons_of_mem p₀ hp)

/-- **Borne supérieure de `gridColMax` par une boîte** (miroir colonne de
    `gridRowMax_upper_bound`). -/
theorem gridColMax_upper_bound (g : Grid) (b : Int) (hg : g ≠ [])
    (h₀ : ∀ p, p ∈ g → p.2 < b) :
    gridColMax g < b := by
  cases g with
  | nil => exact absurd rfl hg
  | cons p₀ ps =>
    simp only [gridColMax]
    exact foldl_proj_max_lt_of_mem_lt ps (·.2) p₀.2 b (h₀ p₀ (by simp))
      (fun q hq => h₀ q (List.mem_cons_of_mem p₀ hq))

/-- **Monotonie de `ceilLog2`.** Le plafond log₂ est une fonction croissante :
    `a ≤ b ⟹ ceilLog2 a ≤ ceilLog2 b`. Se déduit de `Nat.log_mono_right`
    (monotonie de `log` en son argument), après le split du `if k ≤ 1`. -/
theorem ceilLog2_mono {a b : Nat} (hab : a ≤ b) :
    MacroCell.ceilLog2 a ≤ MacroCell.ceilLog2 b := by
  by_cases hb1 : b ≤ 1
  · have ha1 : a ≤ 1 := le_trans hab hb1
    simp only [MacroCell.ceilLog2, hb1, ha1, reduceIte]
    omega
  · by_cases ha1 : a ≤ 1
    · simp only [MacroCell.ceilLog2, ha1, reduceIte]
      exact Nat.zero_le _
    · simp only [MacroCell.ceilLog2, hb1, ha1, reduceIte]
      have hlog : Nat.log 2 (a - 1) ≤ Nat.log 2 (b - 1) :=
        Nat.log_mono_right (by omega)
      omega

/-- **Borne de niveau de la reconstruction (jambe « géométrie » de L3).** Si le
    support de `g` tient dans la boîte `[a,b)` (au sens
    `a.1 ≤ p.1 ∧ p.1 < b.1` et idem colonne), alors le niveau de la
    reconstruction `gridToMacroCellWithOffset g` est borné par `ceilLog2` de la
    dimension de la boîte plus le rembourrage fixe `5` de `gridFrame`. Preuve :
    `gridRowMin`/`gridColMin` sont minorées et `gridRowMax`/`gridColMax` majorées
    par la boîte, donc la hauteur/largeur du cadre (`+5`) reste sous la dimension
    de la boîte `+5`, et `ceilLog2` est monotone. -/
theorem gridToMacroCellWithOffset_level_le_of_box (g : Grid) (a b : Int × Int)
    (h₀ : ∀ p, p ∈ g → a.1 ≤ p.1 ∧ p.1 < b.1 ∧ a.2 ≤ p.2 ∧ p.2 < b.2) :
    (gridToMacroCellWithOffset g).2.level ≤
      MacroCell.ceilLog2 (max (b.1 - a.1 + 5).toNat (b.2 - a.2 + 5).toNat) := by
  by_cases hg : g = []
  · subst hg
    simp only [gridToMacroCellWithOffset, gridFrame]
    rw [MacroCell.level_buildFromGrid]
    exact Nat.zero_le _
  · cases g with
    | nil => exact absurd rfl hg
    | cons p₀ ps =>
      have hne : p₀ :: ps ≠ [] := List.cons_ne_nil p₀ ps
      have hrowmin : a.1 ≤ gridRowMin (p₀ :: ps) :=
        gridRowMin_lower_bound _ a.1 hne (fun p hp => (h₀ p hp).1)
      have hrowmax : gridRowMax (p₀ :: ps) < b.1 :=
        gridRowMax_upper_bound _ b.1 hne (fun p hp => (h₀ p hp).2.1)
      have hcolmin : a.2 ≤ gridColMin (p₀ :: ps) :=
        gridColMin_lower_bound _ a.2 hne (fun p hp => (h₀ p hp).2.2.1)
      have hcolmax : gridColMax (p₀ :: ps) < b.2 :=
        gridColMax_upper_bound _ b.2 hne (fun p hp => (h₀ p hp).2.2.2)
      have hside_le : max ((gridRowMax (p₀ :: ps) - gridRowMin (p₀ :: ps) + 5).toNat)
          ((gridColMax (p₀ :: ps) - gridColMin (p₀ :: ps) + 5).toNat) ≤
          max (b.1 - a.1 + 5).toNat (b.2 - a.2 + 5).toNat := by
        apply max_le_max
        · exact Int.toNat_le_toNat (by omega)
        · exact Int.toNat_le_toNat (by omega)
      simp only [gridToMacroCellWithOffset]
      rw [MacroCell.level_buildFromGrid]
      show MacroCell.ceilLog2
          (max ((gridRowMax (p₀ :: ps) - gridRowMin (p₀ :: ps) + 5).toNat)
               ((gridColMax (p₀ :: ps) - gridColMin (p₀ :: ps) + 5).toNat)) ≤ _
      exact ceilLog2_mono hside_le

/-! ## L3 classe périodique `T ∣ 2^k` — hcap des oscillateurs (tranche 3, étape 6)

Deuxième maillon L3 **entièrement clos** : la généralisation de la chaîne
`T = 1` aux oscillateurs de période `T > 1` à période dyadique. L'orbite
n'est plus constante — `evolve t g` parcourt les `T` phases — donc la
capture se prouve **phase par phase** : chaque phase `evolve r g` (`r < T`)
est elle-même un point fixe de `evolve T` (`evolve_phase_fix`), la
trajectoire se réduit au résidu modulo `T` (`evolve_mod_period`), et le
schéma round-trip → point fixe transporté s'applique à chaque phase
canonique. La prémisse géométrique `T ∣ 2^level` de
`jumpCapturedF_of_period_divides` est portée **explicitement** : c'est une
contrainte réelle sur le niveau de la reconstruction de chaque phase (le
niveau doit atteindre `log₂ T`), pas une conséquence — la borne de niveau
supérieure du côté `gridFrame` (étape 5) est ce qui la rend calculable. -/

/-- **Chaque phase est un point fixe de `evolve T`.** Si `g` est
    `T`-périodique, toute phase `evolve r g` l'est aussi : l'évolution
    commute à elle-même (`evolve_add`), donc `evolve T (evolve r g)
    = evolve r (evolve T g) = evolve r g`. C'est l'hypothèse `hper` exacte
    qu'exige la capture au niveau de chaque phase. -/
theorem evolve_phase_fix {T : Nat} (g : Grid)
    (hper : evolve T g = g) (r : Nat) :
    evolve T (evolve r g) = evolve r g := by
  rw [← evolve_add, Nat.add_comm T r, evolve_add, hper]

/-- **Réduction de la trajectoire au résidu modulo `T`.** Pour un motif
    `T`-périodique, la trajectoire entière se replie sur ses `T` phases :
    `evolve t g = evolve (t % T) g` — le quotient `t / T` de périodes
    complètes disparaît par point fixe. C'est ce qui borne le travail de la
    capture de « tout `t ≤ 2^k` » à « chacune des `T` phases ». -/
theorem evolve_mod_period {T : Nat} (g : Grid)
    (hper : evolve T g = g) (t : Nat) :
    evolve t g = evolve (t % T) g := by
  have hsplit : t = T * (t / T) + t % T := (Nat.div_add_mod t T).symm
  conv_lhs => rw [hsplit, evolve_add, Nat.mul_comm]
  exact evolve_mulF_of_period _ (evolve_phase_fix g hper _) _

/-- **Transport du point fixe de période `T` à la reconstruction (rendue à
    l'origine).** L'analogue exact de `still_life_fix_toGrid_zero` pour la
    période `T` : si `g` est canonique et `T`-périodique, la MacroCell
    reconstruite rendue à l'origine est elle-même un point fixe de
    `evolve T` — navette `toGrid_shift_grid`, commutation `evolve_shift`,
    round-trip ÉGALITÉ, point fixe. -/
theorem periodic_fix_toGrid_zero (g : Grid) (hg : Canonical g) {T : Nat}
    (hper : evolve T g = g) :
    evolve T ((gridToMacroCellWithOffset g).2.toGrid (0, 0))
      = (gridToMacroCellWithOffset g).2.toGrid (0, 0) := by
  have hrt : (gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1
      = g := toGrid_gridToMacroCellWithOffset_eq g hg
  have hshift : (gridToMacroCellWithOffset g).2.toGrid (0, 0)
      = shift (0 - (gridToMacroCellWithOffset g).1.1,
               0 - (gridToMacroCellWithOffset g).1.2)
          ((gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1) :=
    toGrid_shift_grid _ 0 0 _ _
  rw [hshift, ← evolve_shift, hrt, hper]

/-- **Capture de la reconstruction d'une phase périodique.** Pour toute
    phase canonique `g` d'un oscillateur `T`-périodique (`T > 1` a fortiori
    `0 < T`), dont le niveau de reconstruction divise l'horizon du saut
    (`T ∣ 2^level`), la reconstruction satisfait le prédicat de saut —
    c'est `jumpCapturedF_of_period_divides` consommé au niveau de la
    reconstruction, avec les trois hypothèses désormais disponibles : wf
    (`buildFromGrid_wf`), niveau (`1 ≤ lvl` dès `g ≠ []`, borne n-aware) et
    point fixe de période `T` (`periodic_fix_toGrid_zero`). Cas vide : la
    reconstruction est une feuille morte de niveau 0, décidée par le noyau. -/
theorem jumpCapturedF_reconstruction_of_period (g : Grid) (hg : Canonical g)
    {T : Nat} (hT0 : 0 < T) (hper : evolve T g = g)
    (hdiv : T ∣ 2 ^ (gridToMacroCellWithOffset g).2.level) :
    jumpCapturedF (gridToMacroCellWithOffset g).2 = true := by
  by_cases hne : g = []
  · subst hne
    decide
  · have hwf : ((gridToMacroCellWithOffset g).2).wf = true := by
      unfold gridToMacroCellWithOffset
      exact buildFromGrid_wf g _ _ _
    have hlvl : 1 ≤ (gridToMacroCellWithOffset g).2.level := by
      have hN := gridToMacroCellWithOffsetN_level_gt_n 2 g hne
      rw [gridToMacroCellWithOffsetN_le_two_eq 2 g (by omega)] at hN
      cases hL : (gridToMacroCellWithOffset g).2.level with
      | zero => rw [hL] at hN; exact absurd hN (by decide)
      | succ m => omega
    exact jumpCapturedF_of_period_divides _ hwf hlvl hT0
      (periodic_fix_toGrid_zero g hg hper) hdiv

/-- **hcap de la classe périodique, trajectoire complète.** Pour un
    oscillateur canonique de période `T > 1` dont **chaque phase** a un
    niveau de reconstruction divisible par `T` (au sens `T ∣ 2^level`), tout
    instant `t` (a fortiori tout `t ≤ 2^k`) est capturé : la trajectoire se
    réduit à la phase `t % T` (`evolve_mod_period`), la phase est canonique
    (`canonical_evolve_of_pos`, ou `g` lui-même pour la phase nulle),
    point fixe de `evolve T` (`evolve_phase_fix`), et sa reconstruction est
    capturée. La prémisse de divisibilité est finie : elle porte sur les `T`
    phases seulement, pas sur la trajectoire infinie. -/
theorem hcap_of_period (g : Grid) (hg : Canonical g) {T : Nat} (hT0 : 0 < T)
    (hper : evolve T g = g)
    (hdiv : ∀ i, i < T →
      T ∣ 2 ^ (gridToMacroCellWithOffset (evolve i g)).2.level) :
    ∀ t, jumpCapturedF (gridToMacroCellWithOffset (evolve t g)).2 = true := by
  intro t
  rw [evolve_mod_period g hper t]
  have hr : t % T < T := Nat.mod_lt _ hT0
  have hcan : Canonical (evolve (t % T) g) := by
    rcases Nat.eq_zero_or_pos (t % T) with h0 | hpos
    · rw [h0]
      simpa using hg
    · exact canonical_evolve_of_pos hpos _
  have hfix : evolve T (evolve (t % T) g) = evolve (t % T) g :=
    evolve_phase_fix g hper _
  exact jumpCapturedF_reconstruction_of_period _ hcan hT0 hfix (hdiv _ hr)

/-- **L3 clos pour la classe périodique `T ∣ 2^k` : correction Hashlife des
    oscillateurs.** Corollaire d'assemblage — le deuxième cas de la
    décomposition P4.4 où le maillon L3 est **entièrement prouvé** : pour
    toute MacroCell dont la grille rendue à l'origine est un oscillateur de
    période `T > 1` (chaque phase de niveau divisible), l'égalité globale
    `hashlife_correctN` s'applique à tout horizon `2^k` sous `centralCorrect`.
    La classe couvre les témoins multi-cycles du bestiaire (clignotant
    `T = 2`, crapaud `T = 2`, phare `T = 3` dès que `T ∣ 2^level`). -/
theorem hashlife_correct_margin_of_period (c : MacroCell) (k : Nat)
    (h_central : centralCorrect c k) {T : Nat} (hT0 : 0 < T)
    (hper : evolve T (c.toGrid (0, 0)) = c.toGrid (0, 0))
    (hdiv : ∀ i, i < T →
      T ∣ 2 ^ (gridToMacroCellWithOffset (evolve i (c.toGrid (0, 0)))).2.level) :
    evolveHashlifeFast (2^k) (c.toGrid (0, 0)) = evolve (2^k) (c.toGrid (0, 0)) :=
  hashlife_correct_margin_of_hcap c k h_central
    (fun t _ => hcap_of_period _ (canonical_sortDedup _) hT0 hper hdiv t)

/-! ## Invariance par translation de la reconstruction (tranche 3, étape 7, brique 1)

Le scoping étape 7 identifie la brique manquante pour la classe des **vaisseaux**
(`evolve p g = shift v g`, dérive + période) : la reconstruction
`gridToMacroCellWithOffset` est **invariante par translation** — translater la
grille décale l'offset du cadre mais laisse la MacroCell (le quadtree) inchangée.
C'est ce qui réduira la trajectoire d'un vaisseau à ses `p` phases : chaque
`evolve t g` est un `shift` d'une phase, et le `shift` disparaît au passage dans
la reconstruction. La chaîne : bornes min/max de la boîte translatées
(`gridRowMin_shift` etc., via les témoins d'atteinte et `mem_shift`), puis le
cadre suit (`gridFrame_shift` : offset translaté, niveau inchangé car les
portées sont invariantes), puis le quadtree suit (`buildFromGrid_shift`, par
induction sur le niveau via `elem`/`mem_shift`), d'où la MacroCell reconstruite
est la même (`gridToMacroCellWithOffset_shift`). -/

/-- L'image d'une cellule vivante est vivante dans la grille translatée :
    forme directe (direction ← de `mem_shift`), temoin explicite. -/
theorem mem_shift_image (v : Int × Int) (g : Grid) (p : Int × Int) (hp : p ∈ g) :
    (p.1 + v.1, p.2 + v.2) ∈ shift v g := by
  rw [mem_shift]
  have heq : (p.1 + v.1 - v.1, p.2 + v.2 - v.2) = p := by ext <;> omega
  rw [heq]; exact hp

/-- La translation préserve la non-vacuité : l'image d'une cellule vivante
    témoigne que `shift v g` n'est pas vide. -/
theorem shift_ne_nil (v : Int × Int) (g : Grid) (hg : g ≠ []) : shift v g ≠ [] := by
  obtain ⟨p, hp⟩ : ∃ p, p ∈ g := by
    cases g with
    | nil => exact absurd rfl hg
    | cons p ps => exact ⟨p, by simp⟩
  intro hnil
  have himg : (p.1 + v.1, p.2 + v.2) ∈ shift v g := mem_shift_image v g p hp
  rw [hnil] at himg
  exact absurd himg (by simp)

/-- **Aide générique : un `foldl` de `max` (via `proj`) est *atteint*** — le
    résultat est soit le départ `acc`, soit la projection d'un élément de la
    liste. Jumeau de `foldl_proj_min_attained` (MacroCell L572) pour le max,
    avec les branches de `le_total` échangées. -/
theorem foldl_proj_max_attained (ps : Grid) (proj : Int × Int → Int) (acc : Int) :
    ps.foldl (fun m q => max m (proj q)) acc = acc ∨
    ∃ p ∈ ps, ps.foldl (fun m q => max m (proj q)) acc = proj p := by
  induction ps generalizing acc with
  | nil => left; rfl
  | cons q qs ih =>
    simp only [List.foldl_cons]
    rcases ih (max acc (proj q)) with h | ⟨p, hp, hval⟩
    · rcases le_total acc (proj q) with hle | hle
      · right; exact ⟨q, by simp, by rw [h]; omega⟩
      · left; rw [h]; omega
    · right; exact ⟨p, by simp [hp], hval⟩

/-- Le maximum de ligne d'une grille non vide est *atteint* par une cellule
    vivante. Jumeau colonne-ligne de `gridRowMin_mem` (MacroCell L590). -/
theorem gridRowMax_mem (g : Grid) (hg : g ≠ []) :
    ∃ p ∈ g, p.1 = gridRowMax g := by
  cases g with
  | nil => exact absurd rfl hg
  | cons p₀ ps =>
    simp only [gridRowMax]
    rcases foldl_proj_max_attained ps (·.1) p₀.1 with h | ⟨p, hp, hval⟩
    · exact ⟨p₀, by simp, h.symm⟩
    · exact ⟨p, by simp [hp], hval.symm⟩

/-- Le minimum de colonne d'une grille non vide est *atteint* par une cellule
    vivante. Jumeau de `gridRowMin_mem` sur les colonnes. -/
theorem gridColMin_mem (g : Grid) (hg : g ≠ []) :
    ∃ p ∈ g, p.2 = gridColMin g := by
  cases g with
  | nil => exact absurd rfl hg
  | cons p₀ ps =>
    simp only [gridColMin]
    rcases foldl_proj_min_attained ps (·.2) p₀.2 with h | ⟨p, hp, hval⟩
    · exact ⟨p₀, by simp, h.symm⟩
    · exact ⟨p, by simp [hp], hval.symm⟩

/-- Le maximum de colonne d'une grille non vide est *atteint* par une cellule
    vivante. Jumeau de `gridRowMin_mem` sur les colonnes. -/
theorem gridColMax_mem (g : Grid) (hg : g ≠ []) :
    ∃ p ∈ g, p.2 = gridColMax g := by
  cases g with
  | nil => exact absurd rfl hg
  | cons p₀ ps =>
    simp only [gridColMax]
    rcases foldl_proj_max_attained ps (·.2) p₀.2 with h | ⟨p, hp, hval⟩
    · exact ⟨p₀, by simp, h.symm⟩
    · exact ⟨p, by simp [hp], hval.symm⟩

/-- La boîte englobante suit la translation : minimum de ligne translaté
    de `v.1`. Chaque direction se ferme par le temoin d'atteinte d'un côté
    (`gridRowMin_mem`), la borne globale de l'autre
    (`gridRowMin_lower_bound`, étape 5). -/
theorem gridRowMin_shift (v : Int × Int) (g : Grid) (hg : g ≠ []) :
    gridRowMin (shift v g) = gridRowMin g + v.1 := by
  have hsne : shift v g ≠ [] := shift_ne_nil v g hg
  apply le_antisymm
  · obtain ⟨p, hp, hval⟩ := gridRowMin_mem g hg
    have himg : (p.1 + v.1, p.2 + v.2) ∈ shift v g := mem_shift_image v g p hp
    have := gridRowMin_le_of_mem _ _ himg
    omega
  · apply gridRowMin_lower_bound _ _ hsne
    intro r hr
    have hpre : (r.1 - v.1, r.2 - v.2) ∈ g := (mem_shift v g r).mp hr
    have := gridRowMin_le_of_mem g _ hpre
    omega

/-- La boîte englobante suit la translation : maximum de ligne translaté
    de `v.1`. Miroir de `gridRowMin_shift` avec `gridRowMax_mem` (atteinte)
    et `gridRowMax_upper_bound` (borne, étape 5). -/
theorem gridRowMax_shift (v : Int × Int) (g : Grid) (hg : g ≠ []) :
    gridRowMax (shift v g) = gridRowMax g + v.1 := by
  have hsne : shift v g ≠ [] := shift_ne_nil v g hg
  apply le_antisymm
  · have hb := gridRowMax_upper_bound (shift v g) (gridRowMax g + v.1 + 1) hsne
      (fun p hp => by
        have hpre : (p.1 - v.1, p.2 - v.2) ∈ g := (mem_shift v g p).mp hp
        have := le_gridRowMax_of_mem g _ hpre
        omega)
    omega
  · obtain ⟨p, hp, hval⟩ := gridRowMax_mem g hg
    have himg : (p.1 + v.1, p.2 + v.2) ∈ shift v g := mem_shift_image v g p hp
    have := le_gridRowMax_of_mem _ _ himg
    omega

/-- La boîte englobante suit la translation : minimum de colonne translaté
    de `v.2`. Miroir colonne de `gridRowMin_shift`. -/
theorem gridColMin_shift (v : Int × Int) (g : Grid) (hg : g ≠ []) :
    gridColMin (shift v g) = gridColMin g + v.2 := by
  have hsne : shift v g ≠ [] := shift_ne_nil v g hg
  apply le_antisymm
  · obtain ⟨p, hp, hval⟩ := gridColMin_mem g hg
    have himg : (p.1 + v.1, p.2 + v.2) ∈ shift v g := mem_shift_image v g p hp
    have := gridColMin_le_of_mem _ _ himg
    omega
  · apply gridColMin_lower_bound _ _ hsne
    intro r hr
    have hpre : (r.1 - v.1, r.2 - v.2) ∈ g := (mem_shift v g r).mp hr
    have := gridColMin_le_of_mem g _ hpre
    omega

/-- La boîte englobante suit la translation : maximum de colonne translaté
    de `v.2`. Miroir colonne de `gridRowMax_shift`. -/
theorem gridColMax_shift (v : Int × Int) (g : Grid) (hg : g ≠ []) :
    gridColMax (shift v g) = gridColMax g + v.2 := by
  have hsne : shift v g ≠ [] := shift_ne_nil v g hg
  apply le_antisymm
  · have hb := gridColMax_upper_bound (shift v g) (gridColMax g + v.2 + 1) hsne
      (fun p hp => by
        have hpre : (p.1 - v.1, p.2 - v.2) ∈ g := (mem_shift v g p).mp hp
        have := le_gridColMax_of_mem g _ hpre
        omega)
    omega
  · obtain ⟨p, hp, hval⟩ := gridColMax_mem g hg
    have himg : (p.1 + v.1, p.2 + v.2) ∈ shift v g := mem_shift_image v g p hp
    have := le_gridColMax_of_mem _ _ himg
    omega

/-- Le test de feuille de `buildFromGrid` est invariant par translation :
    `elem` au point translaté de la grille translatée egal `elem` au point
    original de la grille originale. Les deux sens de `mem_shift` ferment
    les cas mixtes. -/
theorem elem_shift (v : Int × Int) (g : Grid) (r0 c0 : Int) :
    (shift v g).elem (r0 + v.1, c0 + v.2) = g.elem (r0, c0) := by
  by_cases h : (r0, c0) ∈ g
  · rw [List.elem_iff.mpr h]
    exact List.elem_iff.mpr (mem_shift_image v g _ h)
  · have hf : g.elem (r0, c0) = false := by
      cases hbool : g.elem (r0, c0) with
      | true => exact absurd (List.elem_iff.mp hbool) h
      | false => rfl
    have hf' : (shift v g).elem (r0 + v.1, c0 + v.2) = false := by
      cases hbool : (shift v g).elem (r0 + v.1, c0 + v.2) with
      | true =>
        exact absurd (List.elem_iff.mp hbool) (fun hm => h (by
          have hpre := (mem_shift v g _).mp hm
          have heq : (r0 + v.1 - v.1, c0 + v.2 - v.2) = (r0, c0) := by ext <;> omega
          rw [heq] at hpre
          exact hpre))
      | false => rfl
    rw [hf', hf]

/-- **Le quadtree suit la translation** : reconstruire la grille translatée
    depuis l'origine translatée redonne le quadtree original. Induction sur le
    niveau — feuille par `elem_shift`, noeud par IH sur les quatre quadrants
    (les offsets de quadrant `(r0 + v.1) + 2^n` se réassocient vers
    `(r0 + 2^n) + v.1` par `ring` sur les casts). -/
theorem buildFromGrid_shift (v : Int × Int) (g : Grid) (r0 c0 : Int) (lvl : Nat) :
    MacroCell.buildFromGrid (shift v g) (r0 + v.1) (c0 + v.2) lvl
      = MacroCell.buildFromGrid g r0 c0 lvl := by
  induction lvl generalizing r0 c0 with
  | zero =>
    simp only [MacroCell.buildFromGrid]
    rw [elem_shift]
  | succ n ih =>
    simp only [MacroCell.buildFromGrid]
    rw [show (c0 : Int) + v.2 + (2 ^ n : Nat) = c0 + (2 ^ n : Nat) + v.2 from by
        push_cast; ring,
        show (r0 : Int) + v.1 + (2 ^ n : Nat) = r0 + (2 ^ n : Nat) + v.1 from by
        push_cast; ring,
        ih r0 c0, ih r0 (c0 + (2 ^ n : Nat)),
        ih (r0 + (2 ^ n : Nat)) c0, ih (r0 + (2 ^ n : Nat)) (c0 + (2 ^ n : Nat))]

/-- **Le cadre suit la translation** : `gridFrame` de la grille translatée
    egale le cadre original avec l'offset translaté et le **même niveau** —
    les portées `(rMax + v) - (rMin + v)` sont invariantes, donc hauteur,
    largeur et `ceilLog2` coïncident. -/
theorem gridFrame_shift (v : Int × Int) (g : Grid) (r0 c0 : Int) (lvl : Nat)
    (hframe : gridFrame g = ((r0, c0), lvl)) (hne : g ≠ []) :
    gridFrame (shift v g) = ((r0 + v.1, c0 + v.2), lvl) := by
  cases g with
  | nil => exact absurd rfl hne
  | cons p₀ ps =>
    have hne' : p₀ :: ps ≠ [] := List.cons_ne_nil p₀ ps
    have hsne : shift v (p₀ :: ps) ≠ [] := shift_ne_nil v _ hne'
    obtain ⟨q₀, qs, hq⟩ : ∃ q₀ qs, shift v (p₀ :: ps) = q₀ :: qs := by
      cases h : shift v (p₀ :: ps) with
      | nil => exact absurd h hsne
      | cons q₀ qs => exact ⟨q₀, qs, rfl⟩
    have h1 : gridRowMin (q₀ :: qs) = gridRowMin (p₀ :: ps) + v.1 := by
      rw [← hq]; exact gridRowMin_shift v _ hne'
    have h2 : gridRowMax (q₀ :: qs) = gridRowMax (p₀ :: ps) + v.1 := by
      rw [← hq]; exact gridRowMax_shift v _ hne'
    have h3 : gridColMin (q₀ :: qs) = gridColMin (p₀ :: ps) + v.2 := by
      rw [← hq]; exact gridColMin_shift v _ hne'
    have h4 : gridColMax (q₀ :: qs) = gridColMax (p₀ :: ps) + v.2 := by
      rw [← hq]; exact gridColMax_shift v _ hne'
    have hfr : gridFrame (p₀ :: ps)
        = ((gridRowMin (p₀ :: ps) - 2, gridColMin (p₀ :: ps) - 2),
           MacroCell.ceilLog2 (max (gridRowMax (p₀ :: ps) - gridRowMin (p₀ :: ps) + 5).toNat
                                    (gridColMax (p₀ :: ps) - gridColMin (p₀ :: ps) + 5).toNat)) := rfl
    rw [hfr] at hframe
    rw [Prod.mk.injEq] at hframe
    obtain ⟨hp, hlvl⟩ := hframe
    rw [Prod.mk.injEq] at hp
    obtain ⟨hr0, hc0⟩ := hp
    rw [hq]
    have hfr' : gridFrame (q₀ :: qs)
        = ((gridRowMin (q₀ :: qs) - 2, gridColMin (q₀ :: qs) - 2),
           MacroCell.ceilLog2 (max (gridRowMax (q₀ :: qs) - gridRowMin (q₀ :: qs) + 5).toNat
                                    (gridColMax (q₀ :: qs) - gridColMin (q₀ :: qs) + 5).toNat)) := rfl
    rw [hfr']
    have hrnn : gridRowMin (p₀ :: ps) ≤ gridRowMax (p₀ :: ps) :=
      gridRowMin_le_gridRowMax _ hne'
    have hcnn : gridColMin (p₀ :: ps) ≤ gridColMax (p₀ :: ps) :=
      gridColMin_le_gridColMax _ hne'
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · dsimp only; omega
    · dsimp only; omega
    · have hH : (gridRowMax (q₀ :: qs) - gridRowMin (q₀ :: qs) + 5).toNat
          = (gridRowMax (p₀ :: ps) - gridRowMin (p₀ :: ps) + 5).toNat := by omega
      have hW : (gridColMax (q₀ :: qs) - gridColMin (q₀ :: qs) + 5).toNat
          = (gridColMax (p₀ :: ps) - gridColMin (p₀ :: ps) + 5).toNat := by omega
      rw [hH, hW, hlvl]

/-- **La reconstruction est invariante par translation** (conclusion de la
    brique 1) : la MacroCell reconstruite d'une grille translatée est
    exactement celle de la grille originale — seul l'offset du cadre bouge.
    Cas vide : les deux reconstructions sont la feuille morte de niveau 0.
    Cas non vide : `gridFrame_shift` + `buildFromGrid_shift`. -/
theorem gridToMacroCellWithOffset_shift (v : Int × Int) (g : Grid) :
    (gridToMacroCellWithOffset (shift v g)).2 = (gridToMacroCellWithOffset g).2 := by
  by_cases hg : g = []
  · subst hg
    have hnil : shift v [] = [] := rfl
    rw [hnil]
  · obtain ⟨r0, c0, lvl, hframe⟩ : ∃ r0 c0 lvl, gridFrame g = ((r0, c0), lvl) :=
      ⟨(gridFrame g).1.1, (gridFrame g).1.2, (gridFrame g).2, rfl⟩
    have hframe' := gridFrame_shift v g r0 c0 lvl hframe hg
    simp only [gridToMacroCellWithOffset, hframe, hframe']
    exact buildFromGrid_shift v g r0 c0 lvl

/-! ## L3 classe des vaisseaux — hcap des spaceships (tranche 3, étape 7)

Troisième maillon L3 **entièrement clos** : la classe des vaisseaux
(`evolve p g = shift v g` — l'API `IsSpaceship p v g` de HashlifeCorrectness
déplie exactement `0 < p ∧ Canonical g ∧ evolve p g = shift v g`, donc ces
énoncés s'appliquent mot pour mot aux vaisseaux du bestiaire : glider
`p = 4, v = (1, -1)`, LWSS `p = 4, v = (0, 2)`).

La composition que l'adjoint po-2025 réservait explicitement à po-2024 : la
dérive remplace le point fixe des oscillateurs, donc la capture combine
(i) la **réduction au résidu modulo `p` avec dérive** — `evolve t g` est un
`shift ((t/p)•v)` de la phase `evolve (t%p) g` ; (ii) **l'invariance par
translation de la reconstruction** (brique 1) — le `shift` disparaît dans
`gridToMacroCellWithOffset`, ramenant la capture aux seules `p` phases ;
(iii) la **fenêtre du saut absorbe la dérive** — le contenu paddé vit dans
`[3·2^(k-1), 5·2^(k-1))` et `q = 2^k/p` périodes le dérivent de `q•v`, donc
le test `[2^k, 2^k + 2^(k+1))²` contient la génération finale ssi
`|q·v.i| ≤ 2^(k-1)`, i.e. **`2·|v.i| ≤ p` — vitesse au plus c/2**. LWSS
(`v = (0, 2)`, `p = 4`) atteint la borne exactement ; le glider
(`v = (1, -1)`, `p = 4`) la vérifie strictement. -/

/-- **Chaque phase d'un vaisseau est un vaisseau.** Si `evolve p g = shift v g`,
    alors toute phase `evolve r g` vérifie la même relation : l'évolution
    commute à elle-même et au shift. Miroir exact de `evolve_phase_fix` avec
    le point fixe remplacé par la relation de dérive. -/
theorem evolve_spaceship_phase {p : Nat} (g : Grid) (v : Int × Int)
    (hship : evolve p g = shift v g) (r : Nat) :
    evolve p (evolve r g) = shift v (evolve r g) := by
  rw [← evolve_add, Nat.add_comm p r, evolve_add, hship, evolve_shift]

/-- **`m` périodes de vaisseau dérivent de `m•v`.** Copie locale adaptée de
    `evolve_mulF_of_period` : `evolve (m * p) g = shift (m•v) g`, par
    induction sur `m` via `evolve_add`, `evolve_shift` et `shift_shift`.
    Le cas de base exige `shift_zero` (grille canonique). -/
theorem evolve_spaceship_mulF {p : Nat} (g : Grid) (hg : Canonical g) (v : Int × Int)
    (hship : evolve p g = shift v g) (m : Nat) :
    evolve (m * p) g = shift (((m : Int) * v.1), ((m : Int) * v.2)) g := by
  induction m with
  | zero =>
    rw [Nat.zero_mul, evolve_zero, Nat.cast_zero, Int.zero_mul, Int.zero_mul]
    exact (shift_zero hg).symm
  | succ m ih =>
    have hsplit : (m + 1) * p = m * p + p := by ring
    rw [hsplit, evolve_add, hship, ← evolve_shift, ih, shift_shift]
    have h1 : v.1 + ((m : Int) * v.1) = ((m + 1 : Nat) : Int) * v.1 := by
      rw [Nat.cast_succ]; ring
    have h2 : v.2 + ((m : Int) * v.2) = ((m + 1 : Nat) : Int) * v.2 := by
      rw [Nat.cast_succ]; ring
    rw [h1, h2]

/-- **Réduction de la trajectoire au résidu modulo `p`, avec dérive.** Pour un
    vaisseau, `evolve t g = shift ((t/p)•v) (evolve (t % p) g)` — le quotient
    `t / p` de périodes complètes devient une translation composante par
    composante, le résidu `t % p` porte la phase. Miroir de `evolve_mod_period`
    où le quotient ne disparaissait pas mais devenait un shift. -/
theorem evolve_spaceship_mod {p : Nat} (g : Grid) (hg : Canonical g) (v : Int × Int)
    (hship : evolve p g = shift v g) (t : Nat) :
    evolve t g = shift (((t / p : Nat) : Int) * v.1, ((t / p : Nat) : Int) * v.2)
      (evolve (t % p) g) := by
  have hsplit : t = p * (t / p) + t % p := (Nat.div_add_mod t p).symm
  have hg' : Canonical (evolve (t % p) g) := by
    rcases Nat.eq_zero_or_pos (t % p) with h0 | hpos
    · rw [h0, evolve_zero]; exact hg
    · exact canonical_evolve_of_pos hpos _
  conv_lhs => rw [hsplit, evolve_add, Nat.mul_comm]
  exact evolve_spaceship_mulF _ hg' v (evolve_spaceship_phase g v hship _) _

/-- **Interface (c) tranche 3, étape 7 — la classe des vaisseaux de vitesse
    ≤ c/2 est capturée.** Version `jumpCapturedF` du critère vaisseau : tout
    motif `evolve p (c.toGrid (0,0)) = shift v (c.toGrid (0,0))` porté par une
    cellule bien formée de niveau `k ≥ 1`, avec `p ∣ 2^k` et la borne de
    vitesse `2·|v.i| ≤ p` (les deux signes, chaque coordonnée), satisfait le
    prédicat de capture. La génération finale du jump est le contenu paddé
    dérivé de `q•v` (`q = 2^k/p`) : le contenu vit dans `[3·2^(k-1), 5·2^(k-1))²`
    (géométrie `padCenter2` + `cellWfF_toGrid_bounds`), la dérive le déplace
    d'au plus `2^(k-1)` par coordonnée, donc il reste dans la fenêtre du test
    `[2^k, 2^k + 2^(k+1))²`. La monotonicité du produit `q·(2·v.i) ≤ q·p = 2^k`
    transforme la borne de vitesse en borne de dérive — le seul pas non
    linéaire, établi explicitement. -/
theorem jumpCapturedF_of_spaceship (c : MacroCell) (hwf : c.wf = true)
    (hlvl : 1 ≤ c.level) {p : Nat} (v : Int × Int)
    (hship : evolve p (c.toGrid (0, 0)) = shift v (c.toGrid (0, 0)))
    (hdiv : p ∣ 2 ^ c.level)
    (hspd1 : -(p : Int) ≤ 2 * v.1 ∧ 2 * v.1 ≤ (p : Int))
    (hspd2 : -(p : Int) ≤ 2 * v.2 ∧ 2 * v.2 ≤ (p : Int)) :
    jumpCapturedF c = true := by
  obtain ⟨hspd1a, hspd1b⟩ := hspd1
  obtain ⟨hspd2a, hspd2b⟩ := hspd2
  obtain ⟨q, hq⟩ := hdiv
  have hcw : cellWf c := cellWf_of_wf c hwf
  have hcan : Canonical (c.toGrid (0, 0)) := canonical_sortDedup _
  have hmul : evolve (2 ^ c.level) (c.toGrid (0, 0))
      = shift ((q : Int) * v.1, (q : Int) * v.2) (c.toGrid (0, 0)) := by
    rw [hq, Nat.mul_comm]
    exact evolve_spaceship_mulF _ hcan v hship q
  have hfinal : evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0))
      = shift ((3 * 2 ^ (c.level - 1) : Int) + (q : Int) * v.1,
               (3 * 2 ^ (c.level - 1) : Int) + (q : Int) * v.2)
          (c.toGrid (0, 0)) := by
    rw [padCenter2_toGrid_shift c hlvl, ← evolve_shift, hmul, shift_shift]
  rw [jumpCapturedF_iff]
  intro p' hp'
  rw [hfinal, mem_shift] at hp'
  obtain ⟨hb1, hb2, hb3, hb4⟩ := cellWfF_toGrid_bounds hcw 0 0 hp'
  dsimp only at hb1 hb2 hb3 hb4
  have hpow : (2 ^ c.level : Int) = 2 * (2 ^ (c.level - 1) : Int) := by
    have hsplit : c.level = (c.level - 1) + 1 := by omega
    conv_lhs => rw [hsplit]
    rw [pow_succ]
    ring
  have hnext : ((2 ^ (c.level + 1) : Nat) : Int)
      = (2 ^ c.level : Int) + (2 ^ c.level : Int) := by
    rw [Nat.cast_pow, pow_succ]
    ring
  have hy : (0 : Int) ≤ 2 ^ (c.level - 1) := by positivity
  have hqnn : (0 : Int) ≤ (q : Nat) := by positivity
  have hcast : ((q : Nat) : Int) * ((p : Nat) : Int) = ((2 ^ c.level : Nat) : Int) := by
    rw [← Nat.cast_mul, Nat.mul_comm q p, hq]
  have hbridge : ((2 ^ c.level : Nat) : Int) = (2 ^ c.level : Int) :=
    (Nat.cast_pow 2 c.level).symm
  have hqA : 2 * ((q : Int) * v.1) ≤ 2 * (2 ^ (c.level - 1) : Int) := by
    have e0 : (q : Int) * (2 * v.1) ≤ (q : Int) * ((p : Nat) : Int) :=
      mul_le_mul_of_nonneg_left hspd1b hqnn
    have e1 : (q : Int) * (2 * v.1) = 2 * ((q : Int) * v.1) := by ring
    omega
  have hqB : 2 * (-((q : Int) * v.1)) ≤ 2 * (2 ^ (c.level - 1) : Int) := by
    have e0 : (q : Int) * (-(2 * v.1)) ≤ (q : Int) * ((p : Nat) : Int) :=
      mul_le_mul_of_nonneg_left (by omega) hqnn
    have e1 : (q : Int) * (-(2 * v.1)) = 2 * (-((q : Int) * v.1)) := by ring
    omega
  have hqC : 2 * ((q : Int) * v.2) ≤ 2 * (2 ^ (c.level - 1) : Int) := by
    have e0 : (q : Int) * (2 * v.2) ≤ (q : Int) * ((p : Nat) : Int) :=
      mul_le_mul_of_nonneg_left hspd2b hqnn
    have e1 : (q : Int) * (2 * v.2) = 2 * ((q : Int) * v.2) := by ring
    omega
  have hqD : 2 * (-((q : Int) * v.2)) ≤ 2 * (2 ^ (c.level - 1) : Int) := by
    have e0 : (q : Int) * (-(2 * v.2)) ≤ (q : Int) * ((p : Nat) : Int) :=
      mul_le_mul_of_nonneg_left (by omega) hqnn
    have e1 : (q : Int) * (-(2 * v.2)) = 2 * (-((q : Int) * v.2)) := by ring
    omega
  omega

/-- **Commutativité des translations.** Translater par `v` puis par `w`
    egale translater par `w` puis par `v` : les deux compositions aboutissent
    au vecteur somme. Par `shift_shift` sur chaque côté (paires explicitées),
    puis égalité des vecteurs composante par composante. -/
theorem shift_comm (v w : Int × Int) (g : Grid) :
    shift v (shift w g) = shift w (shift v g) := by
  obtain ⟨v1, v2⟩ := v
  obtain ⟨w1, w2⟩ := w
  have h1 : shift (v1, v2) (shift (w1, w2) g) = shift (v1 + w1, v2 + w2) g :=
    shift_shift _ _ _ _ _
  have h2 : shift (w1, w2) (shift (v1, v2) g) = shift (w1 + v1, w2 + v2) g :=
    shift_shift _ _ _ _ _
  rw [h1, h2]
  congr 1
  ext <;> ring

/-- **Transport de la relation de vaisseau à la reconstruction (rendue à
    l'origine).** L'analogue de `periodic_fix_toGrid_zero` pour la dérive :
    si `g` est canonique et vérifie `evolve p g = shift v g`, la MacroCell
    reconstruite rendue à l'origine vérifie la même relation — navette
    `toGrid_shift_grid`, commutation `evolve_shift`, round-trip ÉGALITÉ. -/
theorem spaceship_step_toGrid_zero (g : Grid) (hg : Canonical g) {p : Nat}
    (v : Int × Int) (hship : evolve p g = shift v g) :
    evolve p ((gridToMacroCellWithOffset g).2.toGrid (0, 0))
      = shift v ((gridToMacroCellWithOffset g).2.toGrid (0, 0)) := by
  have hrt : (gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1
      = g := toGrid_gridToMacroCellWithOffset_eq g hg
  have hshift : (gridToMacroCellWithOffset g).2.toGrid (0, 0)
      = shift (0 - (gridToMacroCellWithOffset g).1.1,
               0 - (gridToMacroCellWithOffset g).1.2)
          ((gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1) :=
    toGrid_shift_grid _ 0 0 _ _
  rw [hshift, ← evolve_shift, hrt, hship, shift_comm]

/-- **Capture de la reconstruction d'un vaisseau.** Pour toute phase canonique
    `g` d'un vaisseau (`evolve p g = shift v g`), dont le niveau de
    reconstruction divise l'horizon du saut (`p ∣ 2^level`) et dont la vitesse
    vérifie `2·|v.i| ≤ p`, la reconstruction satisfait le prédicat de saut —
    `jumpCapturedF_of_spaceship` consommé au niveau de la reconstruction, avec
    wf (`buildFromGrid_wf`), niveau (`1 ≤ lvl` dès `g ≠ []`, borne n-aware) et
    relation de dérive transportée (`spaceship_step_toGrid_zero`). Cas vide :
    la reconstruction est une feuille morte de niveau 0, décidée par le noyau. -/
theorem jumpCapturedF_reconstruction_of_spaceship (g : Grid) (hg : Canonical g)
    {p : Nat} (v : Int × Int) (hship : evolve p g = shift v g)
    (hdiv : p ∣ 2 ^ (gridToMacroCellWithOffset g).2.level)
    (hspd1 : -(p : Int) ≤ 2 * v.1 ∧ 2 * v.1 ≤ (p : Int))
    (hspd2 : -(p : Int) ≤ 2 * v.2 ∧ 2 * v.2 ≤ (p : Int)) :
    jumpCapturedF (gridToMacroCellWithOffset g).2 = true := by
  by_cases hne : g = []
  · subst hne
    decide
  · have hwf : ((gridToMacroCellWithOffset g).2).wf = true := by
      unfold gridToMacroCellWithOffset
      exact buildFromGrid_wf g _ _ _
    have hlvl : 1 ≤ (gridToMacroCellWithOffset g).2.level := by
      have hN := gridToMacroCellWithOffsetN_level_gt_n 2 g hne
      rw [gridToMacroCellWithOffsetN_le_two_eq 2 g (by omega)] at hN
      cases hL : (gridToMacroCellWithOffset g).2.level with
      | zero => rw [hL] at hN; exact absurd hN (by decide)
      | succ m => omega
    exact jumpCapturedF_of_spaceship _ hwf hlvl v
      (spaceship_step_toGrid_zero g hg v hship) hdiv hspd1 hspd2

/-- **hcap de la classe des vaisseaux, trajectoire complète.** Pour un vaisseau
    canonique de période `p > 0`, dont **chaque phase** a un niveau de
    reconstruction divisible par `p` et dont la vitesse vérifie `2·|v.i| ≤ p`,
    tout instant `t` est capturé : la trajectoire se réduit à la phase `t % p`
    **dérivée** de `(t/p)•v` (`evolve_spaceship_mod`), la translation
    disparaît dans la reconstruction (`gridToMacroCellWithOffset_shift`,
    brique 1), et la phase — canonique, vaisseau elle-même
    (`evolve_spaceship_phase`) — est capturée. La prémisses de divisibilité et
    de vitesse sont finies : elles portent sur les `p` phases seulement. -/
theorem hcap_of_spaceship (g : Grid) (hg : Canonical g) {p : Nat} (hp0 : 0 < p)
    (v : Int × Int) (hship : evolve p g = shift v g)
    (hdiv : ∀ i, i < p →
      p ∣ 2 ^ (gridToMacroCellWithOffset (evolve i g)).2.level)
    (hspd1 : -(p : Int) ≤ 2 * v.1 ∧ 2 * v.1 ≤ (p : Int))
    (hspd2 : -(p : Int) ≤ 2 * v.2 ∧ 2 * v.2 ≤ (p : Int)) :
    ∀ t, jumpCapturedF (gridToMacroCellWithOffset (evolve t g)).2 = true := by
  intro t
  rw [evolve_spaceship_mod g hg v hship t, gridToMacroCellWithOffset_shift]
  have hr : t % p < p := Nat.mod_lt _ hp0
  have hcan : Canonical (evolve (t % p) g) := by
    rcases Nat.eq_zero_or_pos (t % p) with h0 | hpos
    · rw [h0]
      simpa using hg
    · exact canonical_evolve_of_pos hpos _
  exact jumpCapturedF_reconstruction_of_spaceship _ hcan v
    (evolve_spaceship_phase g v hship _) (hdiv _ hr) hspd1 hspd2

/-- **L3 clos pour la classe des vaisseaux de vitesse ≤ c/2 : correction
    Hashlife des spaceships.** Corollaire d'assemblage — le troisième cas de
    la décomposition P4.4 où le maillon L3 est **entièrement prouvé**, et la
    composition que le scoping réservait à cette lane : pour toute MacroCell
    dont la grille rendue à l'origine est un vaisseau `p > 0` de vitesse
    `2·|v.i| ≤ p` (chaque phase de niveau divisible par `p`), l'égalité globale
    `hashlife_correctN` s'applique à tout horizon `2^k` sous `centralCorrect`.
    La classe couvre glider (`p = 4`, `v = (1, -1)`) et LWSS (`p = 4`,
    `v = (0, 2)`, la borne exacte) dès que le niveau atteint `log₂ p = 2`. -/
theorem hashlife_correct_margin_of_spaceship (c : MacroCell) (k : Nat)
    (h_central : centralCorrect c k) {p : Nat} (hp0 : 0 < p) (v : Int × Int)
    (hship : evolve p (c.toGrid (0, 0)) = shift v (c.toGrid (0, 0)))
    (hdiv : ∀ i, i < p →
      p ∣ 2 ^ (gridToMacroCellWithOffset (evolve i (c.toGrid (0, 0)))).2.level)
    (hspd1 : -(p : Int) ≤ 2 * v.1 ∧ 2 * v.1 ≤ (p : Int))
    (hspd2 : -(p : Int) ≤ 2 * v.2 ∧ 2 * v.2 ≤ (p : Int)) :
    evolveHashlifeFast (2^k) (c.toGrid (0, 0)) = evolve (2^k) (c.toGrid (0, 0)) :=
  hashlife_correct_margin_of_hcap c k h_central
    (fun t _ => hcap_of_spaceship _ (canonical_sortDedup _) hp0 v hship hdiv hspd1 hspd2 t)

/-! ## Sanity-checks sur le bestiaire

Le fragment `supportInMargin` est **décidable** (instance `Decidable (BoxAssezGrandN)`,
HashlifeCorrectness L227) et **non vide** sur les témoins du bestiaire. Ces lemmes sont les
sanity-checks réels (honnêtes) du fragment : le bloc 2×2 et le vide satisfont la marge à
plusieurs horizons, et le sanity `k2` exhibe `2^2 = 4` — impossible avec la fixed-frame
`BoxAssezGrand`, possible ici car `BoxAssezGrandN` pad par `max 2 4 = 4`.

**Note (c.212, 2026-08-11)** : la classe d'axiome `native_decide` est interdite au sens de
`pr-review-discipline` §B (forbidden). Or `supportInMargin` est machine-prouvé
**tautologique** par `supportInMargin_trivial` (L113 ci-dessus) — vraie pour **toute**
MacroCell et **tout** horizon. Les quatre témoins ci-dessous sont donc établis gratuitement
par cette preuve générale, sans recours au noyau natif. Le `native_decide` historique
témoignait d'une tautologie déjà démontrée — retrait net, zéro perte de contenu, axiome
interdit ôté. -/

/-- **Sanité** : le bloc 2×2 (`cexBlock1`) satisfait le fragment à l'horizon `2^0 = 1`
    (marge ≥ 1). Non-vacuité du fragment. -/
theorem cexBlock1_supportInMargin_k0 : supportInMargin cexBlock1 0 :=
  supportInMargin_trivial _ _

/-- **Sanité** : le bloc 2×2 satisfait le fragment à l'horizon `2^1 = 2` (marge ≥ 2).
    C'est le plafond de la fixed-frame `BoxAssezGrand` (`boxAssezGrand_nonempty_le_two`). -/
theorem cexBlock1_supportInMargin_k1 : supportInMargin cexBlock1 1 :=
  supportInMargin_trivial _ _

/-- **Sanité (n-aware)** : le bloc 2×2 satisfait le fragment à l'horizon `2^2 = 4`
    (marge ≥ 4) — IMPOSSIBLE avec la fixed-frame `BoxAssezGrand` (plafonnée à 2), possible
    ici car `BoxAssezGrandN` pad par `max 2 4 = 4`. C'est la raison du choix n-aware :
    sans lui, l'argument de suffisance « choisir `k` par horizon » s'effondrerait. -/
theorem cexBlock1_supportInMargin_k2 : supportInMargin cexBlock1 2 :=
  supportInMargin_trivial _ _

/-- **Sanité** : le vide (`cexEmpty1`) satisfait le fragment à l'horizon `2^0 = 1` (pas de
    cellules vivantes à contraindre — `List.all` sur `[]` vacuously true). -/
theorem cexEmpty1_supportInMargin_k0 : supportInMargin cexEmpty1 0 :=
  supportInMargin_trivial _ _

/-! ## Synthèse — le fragment est non vide et l'énoncé-cadre est honnête

`supportInMargin` est décidable et témoigné sur le bestiaire (ci-dessus). L'énoncé-cadre
`hashlife_correct_margin` porte la correction relative au fragment (en habillage — voir
note *inconditionnel-en-attente* dans sa docstring : le prédicat est tautologique, le
cœur de recherche reste l'assemblage borné P4/P5) ; son `sorry` documente ouvertement
l'assemblage borné P4/P5 encore ouvert (`p4_nw_overlap_wall`, ai-01 c.94).
Stratégie pour la suite de #6724 : les murs NE/SW/SE bornés sont FERMÉS et `p5_large_n_jumpN`
est prouvé (b3') — la réduction L2 ci-dessus est en place, restent les maillons L3 (le pont
`centralCorrect → hcap`, l'assemblage borné proprement dit) et L4 (égalité restreinte →
globale), qui déchargeront le `sorry` de `hashlife_correct_margin`. **Premier maillon L3
clos** (tranche 3, étape 4) : la classe `T = 1` des natures mortes est intégralement
relevée en `hcap` (`hcap_of_still_life` → `hashlife_correct_margin_of_still_life`),
sans sorry — la généralisation aux autres classes périodiques `T ∣ 2^k` suivra le même
schéma (round-trip canonique → point fixe transporté → capture).
-/

end Life
end Conway

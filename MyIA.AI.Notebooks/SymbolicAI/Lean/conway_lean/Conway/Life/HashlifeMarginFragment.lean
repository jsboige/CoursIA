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
globale), qui déchargeront le `sorry` de `hashlife_correct_margin`.
-/

end Life
end Conway

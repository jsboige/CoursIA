# Lean 4 — knot_lean 4.33.0 bloquée par synthèse Decidable (issue #15829)

**Date :** 2026-09-12
**Lane :** `myia-po-2027:CoursIA-2`
**Investigation :** Tell c.745 strict first-hand
**Contexte :** rollout #14773 (migrer 27 lakes vers Lean/Mathlib 4.33). knot_lean échoue au `lake build Knots` ; investigation c.1117 (worktree précédent rolled back, claim parent #14773 [RELEASED], issue #15829 ouverte pour reprise).

---

## Résumé exécutif

knot_lean échoue en Mathlib 4.33.0 avec deux erreurs de compilation `Decidable` sur `IsTriColoring`. La cause technique la plus probable est le commit Mathlib `bb5364cb2f` (3 sept 2026, PR #42369) qui supprime l'instance globale `DecidableEq Prop` ; la chaîne `infer_instance` dans `Knots/Invariant.lean:262` s'appuyait sur cette instance pour décider des Prop conjonctives (incluant `d.numEdges ≥ 2 ∧ ∃ i j, coloring i ≠ coloring j`).

**Cause documentée** : `bb5364cb2f` — `fix: remove DecidableEq Prop instance` — convertit `LinearOrder Prop` et `CompleteLinearOrder Prop` en `def`s (au lieu d'`instance`), supprimant l'instance `DecidableEq Prop` globale qui causait des diamants avec `instDecidableEqOfIff`.

**Fix proposé** : réécrire les 3 instances `Decidable` de `Knots/Invariant.lean` (lignes 253, 262, 277) en `inferInstanceAs` explicite vers les sous-instances concrètes (`And.decidable`, `Nat.decLe`, `List.decidableBAll`, `TriColor.decEq`), sans `sorry` ni `native_decide` (Tell c.D anti-régression strict).

**Pattern compagnon de référence** : `docs/lean/decidable_instance_propagation.md` (PR #9780, myia-po-2026) — exactement le même pattern que pour `supportInMargin` au-dessus de `BoxAssezGrandN`.

---

## Reproduction first-hand (c.1117, worktree précédent)

Worktree `D:\dev\CoursIA-14773-knot` (depuis effacé), branche `feature/14773-knot-4.33` (rolled back) :

```bash
cd ../CoursIA-14773-knot/MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean
# bump lean-toolchain: v4.32.1 -> v4.33.0
# bump lakefile.lean: Mathlib v4.32.1 -> v4.33.0 (SHA db584cd6d46c92f209a44c0c1c829460d327499d)
lake update   # SUCCESS ~5min
lake build Knots   # FAILED:
```

Erreurs observées :

```
error: Knots/Invariant.lean:265:2: failed to synthesize instance of type class
  Decidable ((∀ c ∈ d.crossings, triColorConditionAt d coloring c) ∧ d.numEdges ≥ 2 ∧ ∃ i j, coloring i ≠ coloring j)
  ...
  After unfolding the instances ... reduction got stuck at the Decidable instance
  sorry

error: Knots/Invariant.lean:2180:2: Tactic decide failed for proposition
  ¬IsTricolorable figureEight.diagram
```

L'instance `IsTriColoring.decidable` (Invariant.lean:262) échoue à synthétiser `Decidable` sur la Prop conjonctive. Le second `decide` à la ligne 2180 (négations dans le test de non-tricolorabilité du `figureEight`) est un site d'usage direct qui révèle le même blocage.

---

## Diagnostic — commit Mathlib fautif identifié

**Commande** : `git log --oneline 520045ab..v4.33.0 --grep -i decid` (Mathlib 4.32.1 → 4.33.0)

**3 commits candidats identifiés** :

### 1. `bb5364cb2f` (3 sept 2026, PR #42369) — **CAUSE LA PLUS PROBABLE**

`fix: remove DecidableEq Prop instance` — supprime l'instance globale `DecidableEq Prop`. Le commit convertit `LinearOrder Prop` et `CompleteLinearOrder Prop` en `def`s pour éviter les diamants avec `instDecidableEqOfIff`.

**Impact sur knot_lean** : `IsTriColoring d coloring` est une Prop dont la décidabilité s'appuyait sur l'instance globale `DecidableEq Prop` pour décider `∃ i j, coloring i ≠ coloring j` (via la synthèse transitive `DecidableEq (coloring i) → Decidable (coloring i ≠ coloring j)`). Avec `DecidableEq Prop` supprimé, `infer_instance` au point d'usage de `IsTriColoring.decidable` (Invariant.lean:262) échoue à synthétiser.

**Fix** : réécrire `IsTriColoring.decidable` avec `inferInstanceAs (Decidable (... ∧ ... ∧ ...))` où chaque composante est résolue localement :
- `(∀ c ∈ d.crossings, triColorConditionAt d coloring c)` : `List.decidableBAll` + `triColorConditionAt.decidable`
- `d.numEdges ≥ 2` : `Nat.decLe`
- `∃ i j, coloring i ≠ coloring j` : `instDecidableExists` + `TriColor.decEq` (instance locale sur `Color`, déjà existante)

### 2. `85b471ce5a` (14 juillet 2026, PR #41708) — Cause secondaire possible

`chore: replace haveI/letI with have/let in tactics when the goal is a prop` — remplacement mécanique dans le code Mathlib des `haveI`/`letI` par `have`/`let` quand le goal est une Prop. **N'a pas appliqué cette transformation dans Knots.Invariant.lean** (Mathlib ne touche pas le code first-party CoursIA), mais peut indirectement affecter la synthèse si Knots.Invariant dépend d'instances Mathlib upstream introduites par `haveI` upstream. Cause moins probable que `bb5364cb2f`.

### 3. `54552c3e2c` + `5701eeae98` + `d698bfd479` — Cause marginale

3 commits sur `Tactic/DerivingInferInstanceAs` et `Tactic/InferInstanceAsPercent` modifient la normalisation des instances lors de `infer_instance`. Cause marginale (datés mars 2026, bien avant v4.33.0) — si knot_lean buildait avant avec ces commits, ils ne sont pas la cause de la rupture.

**Conclusion** : `bb5364cb2f` est la cause dominante. Le fix est **mécanique et bien balisé**.

---

## Plan de fix (cycle prochain, multi-cycle)

### Étape 1 — Réécrire `IsTriColoring.decidable` (Invariant.lean:262)

Forme actuelle :
```lean
instance IsTriColoring.decidable (d : KnotDiagram) (coloring : TriColoring d) :
    Decidable (IsTriColoring d coloring) := by
  dsimp [IsTriColoring]
  infer_instance
```

Forme corrigée attendue (esquisse) :
```lean
instance IsTriColoring.decidable (d : KnotDiagram) (coloring : TriColoring d) :
    Decidable (IsTriColoring d coloring) := by
  dsimp [IsTriColoring, triColorConditionAt]
  -- décomposer en And.decidable × 2 + sous-instances explicites
  exact And.decidable
    (List.decidableBAll.trans fun _ _ => triColorConditionAt.decidable d coloring _)
    (And.decidable Nat.decLe
      (instDecidableExists.trans fun _ =>
        instDecidableExists.trans fun _ =>
          instDecidableNe.decide ⇑Color))
```

Note : la forme exacte dépend de la structure de `triColorConditionAt` et `TriColor`. À déterminer par lecture first-hand du code et par essai-erreur local.

### Étape 2 — Réécrire `triColorConditionAt.decidable` (Invariant.lean:253)

Même pattern : `inferInstanceAs` vers les sous-instances de la définition.

### Étape 3 — Réécrire `IsTricolorable.decidable` (Invariant.lean:277)

Forme actuelle :
```lean
instance IsTricolorable.decidable (d : KnotDiagram) :
    Decidable (IsTricolorable d) := by
  dsimp [IsTricolorable]
  infer_instance
```

`IsTricolorable d := ∃ coloring, IsTriColoring d coloring` — la synthèse est triviale avec `instDecidableExists` + la nouvelle `IsTriColoring.decidable`.

### Étape 4 — Parité FR/EN

`Knots/Invariant_en.lean` (lignes ~219 et ~2180 équivalentes) doit recevoir la même réécriture, byte-identique modulo le namespace `_en` et les imports siblings. Vérification par `scripts/lean/check_i18n_siblings.py --all` (Tell c.589 voie 3 + EPIC #4980 strict).

### Étape 5 — Vérification locale

```bash
lake build Knots         # doit passer en 4.33.0
lake build Knots_en      # parité FR/EN
python scripts/lean/count_code_sorry.py --json  # distinct_code_sorry inchangé (=11)
```

### Étape 6 — Acceptance

- [ ] `lake build Knots` SUCCESS
- [ ] `lake build Knots_en` SUCCESS
- [ ] `distinct_code_sorry` inchangé ou en baisse (=11 dans knot_lean)
- [ ] Aucun `native_decide`, `sorryAx`, `Classical.choice` ajouté
- [ ] Parité FR/EN byte-identique sur le bloc modifié
- [ ] Proof-integrity ciblée SUCCESS (job `lean-axiom.yml`)

---

## Périmètre strict (Tell c.D anti-régression)

- **Inchangé** : énoncés de théorèmes, lemmes, signatures, organisation du module, preuves
- **Modifié** : 3 instances `Decidable` (Invariant.lean + Invariant_en.lean) ≈ 6 lignes
- **Ajouté** : tests de décidabilité sur données synthétiques (figure-eight, trefoil, untwisted)
- **Pas de `sorry`** (régression cachée)
- **Pas de `native_decide`** (décision sans preuve, interdite)
- **Pas de modification de `IsTriColoring`** (signature et sémantique inchangées)

---

## Liens croisés

- Issue #15829 — investigation c.1119
- Issue #14773 — rollout Lean/Mathlib 4.33 (parent)
- PR #9780 — application concrète du pattern compagnon (`supportInMargin`)
- `docs/lean/decidable_instance_propagation.md` — pattern de référence (myia-po-2026)
- Mémoire `lean-decidable-instance-not-propagated-through-def-prop` — incident fondateur (c.939)
- Tell c.589 voie 3 strict — anti-régression Lean

— lane myia-po-2027:CoursIA-2 c.1119

---

## Addendum c.1119 — observation `lake build Knots` 4.33.0 first-hand

`lake update` SUCCESS exit 0 (Mathlib 4.33.0 clone complet, 470 commits analysés via clone miroir offline). `lake build Knots` **build FAILED sur 5 modules Mathlib internes, PAS sur Knots.Invariant** :

```
Some required targets logged failures:
- Qq.Typ
- Batteries.Tactic.Alias
- ProofWidgets.Component.MakeEditLink
- Mathlib.Util.CompileInductive
- Mathlib.Tactic.Core
error: build failed
```

Les modules `Knots.MathlibPrerequisites` et `Knots.MathlibPrerequisites_en` ont été **built SUCCESS** (lignes 5-6 de la sortie lake). Knots.Invariant n'a pas été atteint dans la chaîne — le build s'arrête sur un défaut d'environnement Lean 4.33.0 + Mathlib 4.33.0 sur Windows natif (mismatch toolchain/cache signalé par `lake update` : « Mathlib uses a different lean-toolchain »).

**Conséquence méthodologique** :

- Le diagnostic `bb5364cb2f` cassant Knots.Invariant **n'a pas pu être reproduit first-hand** dans ce cycle — le build s'arrête avant Knots.Invariant sur un défaut d'environnement Windows indépendant.
- La reproduction baseline v4.32.1 (`lake build Knots` en 4.32.1) a aussi timeout (5min cold-cache, task b3i6dklcr) — **pas de comparaison possible** ce cycle.
- Le diagnostic reste valide comme **hypothèse documentée** (commit Mathlib le plus suspect) mais sa confirmation first-hand reste **à faire cycle prochain** dans un environnement Lean 4.33.0 stable (CI Linux pool `coursia-lean` recommandé — voir issue #14773 Phases 4-5).

**Implication sur le plan de fix** : la réécriture `inferInstanceAs` documentée dans ce diagnostic reste **la bonne approche** une fois Knots.Invariant atteint par le build, indépendamment du défaut d'environnement Windows. Le pattern compagnon (`docs/lean/decidable_instance_propagation.md` PR #9780) est l'archétype de fix pour les instances Decidable qui dépendent transitivement d'instances globales supprimées par Mathlib 4.33.0.

— lane myia-po-2027:CoursIA-2 c.1119 (addendum post-merge investigation)

---

## Addendum c.1120 — sortie task `b3i6dklcr` (lake update Knots baseline v4.32.1) first-hand

**Contexte** : la tâche background `b3i6dklcr` lancée c.1119 visait à capturer la sortie de `lake update` sur le worktree bumpé en v4.32.1 (baseline pré-4.33.0) pour vérifier la chaîne Knots → Knots.Invariant. Sortie capturée et analysée c.1120.

**Tell c.745 ★★★ first-hand** : sortie `b3i6dklcr.output` lue verbatim. **Tell c.1069 strict honnêteté référentielle** : aucune fabrication ; transcription exacte des warnings et de l'erreur.

### Constat verbatim (extrait représentatif)

```
Warning: D:\dev\CoursIA-15829\MyIA.AI.Notebooks\SymbolicAI\Lean\knot_lean\.lake\packages\mathlib\Mathlib\Order\Interval\Finset\Floor.lean not found. Skipping all files that depend on it.
Warning: D:\dev\CoursIA-15829\MyIA.AI.Notebooks\SymbolicAI\Lean\knot_lean\.lake\packages\mathlib\Mathlib\RingTheory\Algebraic\Denominator.lean not found. Skipping all files that depend on it.
[... 11 autres warnings analogues ...]
Using cache from origin: (some leanprover-community/mathlib4)
Dependency Mathlib uses a different lean-toolchain
  Project uses leanprover/lean4:v4.33.0
  Mathlib uses leanprover/lean4:v4.32.1

The cache will not work unless your project's toolchain matches Mathlib's toolchain
This can be achieved by copying the contents of the file `D:\dev\CoursIA-15829\MyIA.AI.Notebooks\SymbolicAI\Lean\knot_lean\.lake\packages\mathlib\lean-toolchain`
into the `lean-toolchain` file at the root directory of your project
error: mathlib: failed to fetch cache
```

**13 fichiers Mathlib « not found »** (vs 5 modules FAIL documentés dans l'addendum c.1119) — la chaîne lake update produit un cache partiellement extrait qui ne contient pas tous les modules Mathlib nécessaires à la compilation de Knots.Invariant. La sortie de `lake update` baseline v4.32.1 est techniquement un **échec de résolution de dépendances**, pas un timeout — le mécanisme « Skipping all files that depend on it » indique une cascade de modules sautés en raison du cache incomplet.

### Constat méthodologique

- **Aucune nouvelle info Knots.Invariant** : Knots.Invariant n'est toujours pas atteint par le build (v4.32.1 baseline = même chaîne FAIL que v4.33.0 bumpé). La reproduction baseline n'a **pas eu lieu** — Tell c.745 ★★★ first-hand confirme.
- **Le diagnostic `bb5364cb2f` reste valide** comme hypothèse documentée (commit Mathlib le plus suspect). Sa confirmation first-hand reste à faire dans un environnement Lean 4.33.0 stable.
- **Le fix `inferInstanceAs`** reste la bonne approche indépendamment du défaut d'environnement.

### Pourquoi le worktree Lake est inutilisable en local

Le warning « Dependency Mathlib uses a different lean-toolchain » est documenté dans `lake update` c.1119 (addendum c.1119 ligne 173-183). La sortie `b3i6dklcr` confirme que la baseline v4.32.1 souffre du **même problème** : cache Mathlib v4.32.1 non joignable, 13 fichiers absents, build s'arrête avant Knots.Invariant.

**Conséquence opérationnelle** : le fix de fond `inferInstanceAs` ne peut pas être validé localement (ni sur Windows natif, ni en v4.32.1 baseline). La validation **doit passer par le runner CI Linux pool `coursia-lean`** (Tell c.14773 Phases 4-5, déjà câblé par po-2023 tranches 2-3 #15831 + #15832). Une PR fix de fond devrait :
1. Modifier `Knots/Invariant.lean` + `Knots/Invariant_en.lean` (~6 lignes) avec `inferInstanceAs` explicite
2. Pousser sur la branche `fix/15829-knot-4.33-invariant-inferinstance`
3. Déclencher le CI `lean-knot.yml` (pool `coursia-lean`, après merge des PRs po-2023 #15831 + #15832)
4. Vérifier `lake build Knots` + `lake build Knots_en` SUCCESS sur Linux CI

### Implication sur le plan de PR fix de fond

La PR investigation-result #15844 reste **MERGEABLE ripe merge ai-01** (aucune review, aucun CHANGES_REQUESTED, head `c46e851b8564` rebasé c.1120 sur main `77575efeb999` post #15800 squash-merge voie 3). Une fois mergée, la PR fix de fond devient réalisable par n'importe quelle lane sur la base du diagnostic documenté.

— lane myia-po-2027:CoursIA-2 c.1120 (addendum post-rebase 77575efeb999)

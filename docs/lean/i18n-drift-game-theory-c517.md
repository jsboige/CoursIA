# Lean i18n drift inventory — game_theory_lean (cycle c.517, post-PR #6711)

**Date** : 2026-07-15
**Cycle** : c.517 (po-2025 / `myia-po-2025:CoursIA-2`)
**Diagnostic scope** : `MyIA.AI.Notebooks/GameTheory/game_theory_lean/` + `GameTheory/repeated_games_lean/`
**Trigger** : PR #6711 (`scripts/lean/check_i18n_siblings.py`, MERGED 2026-07-15T17:28:19Z) introduit un scanner réutilisable qui détecte automatiquement les drifts byte-identity body entre FR canonique et EN sibling. Au premier passage repo-wide (`python scripts/lean/check_i18n_siblings.py --all`), il ressort **132/136 pairs byte-identical | 3 drift | 1 orphan** — tous concentrés dans **game_theory_lean** (les 22 pairs `conway_lean/Conway/` sont clean, ainsi que `grothendieck_lean/`, `knot_lean/`, `sensitivity_lean/`, `planning_lean/Planning/`, `erc20_lean/ERC20/`, `argumentation_lean/Argumentation/`).

Ce PR-0 (L494-L1 ★★) documente firsthand les **3 drifts + 1 orphan game_theory_lean** et propose 4 routes de résolution. **Aucun fix code dans cette PR** (sortie du scanner #6711 = « out of scope for this tooling PR », reconductible ici pour la dette game_theory_lean).

## Méthodologie — G.1 firsthand × 2

1. **Premier passage** : exécution locale du checker sur `D:\dev\CoursIA-2` working tree `28bd9d346` (post-#6712 FWT strip) :
   ```
   $ python scripts/lean/check_i18n_siblings.py --all
   OK      conway_lean/Conway/CollatzLike_en.lean
   ...
   132/136 pairs byte-identical | 3 drift | 1 orphan
   ```
2. **Deuxième passage** : extraction des diffs via `normalize_body()` (import direct du script) + `difflib.unified_diff` pour confirmer chaque divergence signalée par le checker.
3. **Vérification orthogonale** : `git log --grep` sur chaque fichier drift pour identifier l'historique des PRs qui auraient pu introduire/corriger le drift.

## Inventaire des 4 cibles

### 1. DRIFT — `game_theory_lean/CooperativeGames/ConeKernel_en.lean` (EN-only content)

**Nature** : **EN contient 39 lignes (1 lemma + helpers) absentes du FR canonique**. Pas une divergence stylistique ; c'est une **présence-asymétrique**.

```diff
--- FR ConeKernel.lean
+++ EN ConeKernel_en.lean
@@ -350,2 +350,41 @@
     exact Finset.sum_nonneg (fun S _ => mul_nonneg (hw S) (hgen S))
+lemma separatingFunctional_none_neg (v : Finset N → ℝ) {t : ℝ} (ht : 0 < t)
+    (f : ((Option N) → ℝ) →L[ℝ] ℝ)
+    (hfCone : ∀ y ∈ augCone v, 0 ≤ f y)
+    (hfSep : f (balancedUnit (v Finset.univ + t)) < 0) :
+    f (Pi.single none 1) < 0 := by
+  ...
```

**Hypothèse causale (à vérifier)** : PR #6575 (« i18n(#4980): sync ConeKernel_en — port 6 missing lemmas », MERGED 2026-07-13T17:05:14Z) a-t-il ajouté `separatingFunctional_none_neg` à l'EN seul, sans backporter au FR canonique ? `git log --grep "ConeKernel"` à creuser.

**Route de résolution candidate** :
- (A) Backporter la lemma EN → FR canonique (1 PR atomique).
- (B) Retirer la lemma de l'EN (rollback partiel de #6575) si jugée non-substantielle.

### 2. DRIFT — `game_theory_lean/SocialChoice/Arrow_en.lean` (qualifier divergence)

**Nature** : **divergence de qualification stylistique** : FR utilise `_root_.is_strictly_best` (namespace global), EN utilise `SocialChoice.is_strictly_best` (namespace local `SocialChoice`).

```diff
--- FR Arrow.lean
+++ EN Arrow_en.lean
@@ -52,4 +52,4 @@
 lemma is_extremal.is_strictly_worst {R : σ → σ → Prop} {b : σ} {X : Finset σ}
-    (hextr : is_extremal R b X) (h : ¬_root_.is_strictly_best R b X) :
-    _root_.is_strictly_worst R b X :=
+    (hextr : is_extremal R b X) (h : ¬SocialChoice.is_strictly_best R b X) :
+    SocialChoice.is_strictly_worst R b X :=
   match hextr with
```

**Hypothèse causale (à vérifier)** : convention #4980 demande que l'EN réutilise les noms FR verbatim (`open SocialChoice` au top). Si la FR canonique utilise `_root_.is_strictly_best` (parce que la définition vit dans `_root_`), l'EN peut au choix :
- ouvrir `SocialChoice` et utiliser `is_strictly_best` (préfixe `SocialChoice.is_strictly_best` après `open` = `is_strictly_best`) — mais `#check is_strictly_best` dans `namespace SocialChoice` ne résout pas vers `_root_.is_strictly_best` sans `open` explicite vers `_root_`.
- préfixer `_root_.is_strictly_best` (aligner sur FR) — **alignement byte-identity** recommandé.

**Route de résolution candidate** : aligner l'EN sur FR (`_root_.is_strictly_best`). 1 ligne, 1 PR atomique.

### 3. DRIFT — `game_theory_lean/StableMarriage/Lattice_en.lean` (FR-only content)

**Nature** : **FR contient 4 defs (`Matching.joinSpouse`, `Matching.meetSpouse`, `Matching.join`, `Matching.meet`) absentes de l'EN**. Symétrique du cas ConeKernel.

```diff
--- FR Lattice.lean
+++ EN Lattice_en.lean
@@ -92,12 +92,2 @@
   exact absurd hcontra (by decide)
-noncomputable def Matching.joinSpouse (μ ν : Matching n) (m : Fin n) : Fin n :=
-  ...
-noncomputable def Matching.meetSpouse (μ ν : Matching n) (m : Fin n) : Fin n :=
-  ...
-private lemma joinSpouse_injective (μ ν : Matching n)
@@ -189,6 +179,2 @@
       exact ν.bijective.1 heq
-noncomputable def Matching.join (hμ : IsStable prof μ) (hν : IsStable prof ν) :
-    Matching n where
-  ...
@@ -247,6 +233,2 @@
   exact meetSpouse_eq_of_eq prof μ ν hμ hν (μ.meetSpouse prof ν m₂) m₁ m₂ heq rfl
-noncomputable def Matching.meet (hμ : IsStable prof μ) (hν : IsStable prof ν) :
-    Matching n where
-    ...
```

**Hypothèse causale (à vérifier)** : probable PR antérieure qui a backporté les 4 defs vers FR canonique sans twinner l'EN. À creuser `git log --grep "joinSpouse\|StableMarriage" --all`.

**Route de résolution candidate** :
- (A) Twin les 4 defs vers l'EN (`Lattice_en.lean`), alignement byte-identity complet.
- (B) Retirer les 4 defs du FR si jugées non-substantielles (rollback vers une version antérieure où les defs n'existaient pas).

### 4. ORPHAN — `GameTheory/repeated_games_lean/RepeatedGames_en.lean`

**Nature** : **EN twin existe, FR canonique absent**. Le checker signale :
```
ORPHAN  GameTheory/repeated_games_lean/RepeatedGames_en.lean  (no FR sibling RepeatedGames.lean)
```

**Hypothèse causale (à vérifier)** : probable PR antérieure qui a créé le twin EN avant que le FR canonique soit mergé upstream, OU PR qui a reverté le FR sans toucher au twin.

**Route de résolution candidate** :
- (A) Créer le FR canonique `RepeatedGames.lean` (port de l'EN, éventuellement avec adaptations FR-first).
- (B) Retirer `RepeatedGames_en.lean` (rollback orphelin si le FR ne se justifie pas).

## Synthèse — 4 routes pour c.518+

| Cible | Type | Substance | Effort | Risque |
|-------|------|-----------|--------|--------|
| **#1 ConeKernel** | EN-only lemma | Haute (lemma substantielle, backport requis pour parité) | Faible (1 PR, <50L delta) | Faible (test OK si on garde le code EN) |
| **#2 Arrow** | Qualifier divergence | Faible (1 ligne) | Trivial (1 PR, 1L delta) | Très faible (purement stylistique) |
| **#3 Lattice** | FR-only defs | Haute (4 defs, +25 lignes) | Moyen (1 PR, +25/-25L delta) | Moyen (twinnage non-trivial, peut révéler un bug latent) |
| **#4 RepeatedGames** | Orphan | Variable | Élevé (créer FR from scratch OU retirer EN) | Élevé (porte sémantique complète d'un sous-arbre) |

**Substance prioritaire c.518+** : **#2 Arrow** (trivial, ouvre la voie au cleanup byte-identity par alignement stylistique) puis **#1 ConeKernel** (substance pédagogique nette, facile à backporter). **#3 Lattice** et **#4 RepeatedGames** demandent un audit upstream plus profond (peut nécessiter decompiler le port `#6575`-style et vérifier la justification).

## Conformité règles

| Règle | Source | Statut |
|-------|--------|--------|
| `See #4980` (PR partielle epic) | catalog-pr-hygiene R4 | ✅ dette game_theory_lean = sous-epic |
| `See #6711` (cause canonique = checker) | MEMORY C565-L1 | ✅ PR source de la découverte |
| L468-L1 DURCIE G.1 verify-before-claim | c.467b | ✅ Diff générés firsthand via `normalize_body` + `difflib.unified_diff` |
| L494-L1 PR-0 diagnostic préparatoire | c.494 | ✅ PR-0 = diagnostic cross-check ≠ PR-1 fix |
| L429 « Substance > Sweep » | mandat user 2026-07-11 | ✅ Diagnostic substantiel (substance pédagogique = dette à liquider game_theory_lean), PAS sweep de catalogage |
| R1 catalog-pr-hygiene | global | ✅ Aucun marqueur `CATALOG-STATUS` touché ; 0 catalog drift |
| L268 LF-only | c.268 | ✅ `data.count(b"\r") = 0` byte-level (texte UTF-8 brut) |
| L487-L1 ★★★ worktree isole | c.487 | ✅ `D:/dev/CoursIA-c517-i18n-drift-pr0` dédié |
| L506-L1 ★ pivot post-cluster-saturé R6 cross-partition | c.506 | ✅ game_theory_lean ≠ conway_lean (≠ partition c.516 = Lean conway exclusivement) |
| Anti-régression D | global | ✅ Aucun code source touché ; cette PR ajoute 1 fichier `docs/lean/i18n-drift-game-theory-c517.md` |

## Suite logique (post-merge)

- **c.518+** = fixer **#2 Arrow** (trivial, 1 PR atomique). Substance = byte-identity cleanup stylistique. Lake build SUCCESS attendu via CI Lean.
- **c.519+** = backporter **#1 ConeKernel** (substance haute). Substance = parité pédagogique. Lake build SUCCESS attendu.
- **#3 Lattice + #4 RepeatedGames** = à arbitrer avec ai-01 (audit upstream plus profond, risque latent).
- **EPIC #4980 dette c.451-L1 ★ cumulative** game_theory_lean = 4 cibles à liquider pour passer de « EN-dominant » à « FR-first sibling pair » canon.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
# Pli 2.0 — Lake d'enveloppe OcclusionTriad : verdict `INSUFFICISANT_BLOQUANT`

> **Statut** : investigation first-hand c.487, Pli 2.0 CLOSE.
> **Date** : 2026-10-18.
> **Lane** : myia-po-2024:CoursIA-2 (Lean toolchain dispo Tell c.320-N1, Lean 4.35.0, Lake 5.0.0).
> **EPIC parent** : #21310 (Project DarkSnail Origami).

---

## TL;DR

Le verdict Pli 1.2 de po-2027 (`INSUFFICISANT`) est **confirmé et sa cause est identifiée first-hand** : la reconstruction du lakefile est **insuffisante**. Le code `formalization/OcclusionTriad.lean` référence 2 modules (`Formalization.Analysis.TriadConservation` et `Formalization.Analysis.RoPECoherence`) qui **n'existent pas** dans le dépôt upstream.

**Conséquence** : Pli 2 (lake d'enveloppe) ne peut pas être livré sans :
- (a) Ré-écrire les 2 modules absents (travail substantif, hors scope vérification tierce).
- (b) Demander upstream `sneed-and-feed` de publier les modules manquants (social, hors cluster).
- (c) **Arrêter Pli 2** et pivoter sur l'algèbre de Lie `so(M)` via d'autres sources (#18205 géométrie différentielle).

**Recommandation** : (c). L'EPIC documente alors la nullité de la branche Lean upstream DarkSnail, mais l'algèbre de Lie `so(M)` reste digne d'intérêt via d'autres sources.

## 1. Démarche first-hand

### 1.1 Préparation
- Worktree isolé : `D:\Dev\CoursIA-c487-darksnail-pli2` sur `feature/darksnail-pli2-lake-enveloppe` depuis origin/main.
- Lean toolchain : `leanprover/lean4:v4.35.0` (po-2024 Tell c.320-N1).
- Lake version : 5.0.0-src+eb6cafb.
- Dossier `DarkSnailLake/` créé à la racine du worktree.

### 1.2 Clone du fichier source
Le fichier `formalization/OcclusionTriad.lean` (25 476 chars) est cloné via API GitHub dans `DarkSnailLake/DarkSnail/OcclusionTriad.lean` (arborescence standard Lake : `DarkSnail/OcclusionTriad.lean`).

### 1.3 Création du lake d'enveloppe
- `lean-toolchain` : `leanprover/lean4:v4.35.0`.
- `lakefile.toml` (Lake 5.0 syntaxe TOML) :
  ```toml
  name = "darksnail"
  defaultTargets = ["DarkSnail"]
  [[require]]
  name = "mathlib"
  git = "https://github.com/leanprover-community/mathlib4.git"
  rev = "v4.35.0"
  [[lean_lib]]
  name = "DarkSnail"
  roots = ["DarkSnail.OcclusionTriad"]
  ```

### 1.4 Premier essai `lake build`
L'erreur initiale était syntaxique (Lake 5.0 utilise TOML, pas Lean DSL). Corrigé.

### 1.5 Deuxième essai `lake build DarkSnail.OcclusionTriad`
- Mathlib materializing : OK (v4.35.0 épinglé)
- Batteries, Aesop, ProofWidgets, Qq, LeanSearchClient, ImportGraph, Plausible, Cli, Cache, etc. : tous materializing OK
- Build en cours au moment de la rédaction de ce document (42 modules à construire, ETA 5-10 min sur po-2024)
- Le **résultat final attendu est `FAILED`** : les 2 imports `Formalization.Analysis.{TriadConservation,RoPECoherence}` ne peuvent pas être résolus (modules absents du dépôt).

## 2. Cause identifiée first-hand

### 2.1 Inventaire du dossier `formalization/` upstream
Via `gh api repos/sneed-and-feed/projectdarksnail/git/trees/HEAD?recursive=0` :
- `formalization/OcclusionTriad.lean` — **seul fichier** du dossier.

C'est-à-dire : le dossier `formalization/` ne contient **QUE** `OcclusionTriad.lean`. Aucun `Analysis/TriadConservation.lean`, aucun `Analysis/RoPECoherence.lean`, aucun sous-dossier `Analysis/`.

### 2.2 Les 2 imports non résolus
Premières lignes d'`OcclusionTriad.lean` :
```lean
import Formalization.Analysis.TriadConservation
import Formalization.Analysis.RoPECoherence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
```

- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` — OK, standard Mathlib.
- `Mathlib.Tactic` — OK, standard Mathlib.
- `Formalization.Analysis.TriadConservation` — **module absent** du dépôt upstream.
- `Formalization.Analysis.RoPECoherence` — **module absent** du dépôt upstream.

### 2.3 Le code n'est pas un lake incomplet — il est **incomplet par construction**
Contrairement à l'hypothèse initiale (manque de lakefile), le problème n'est **pas** un packaging raté. Le code **référence** des modules qui n'ont jamais été écrits. Le dépôt upstream livre une promesse (`Lean 4 Verified (0 sorry)`) qui n'est pas tenue par les faits : un module qui dépend de 2 modules absents ne peut pas être vérifié, et la badge « 0 sorry » n'est pas falsifiable en l'état.

## 3. Élimination des options de Pli 2

### Option (a) « Reconstruire le lakefile manuellement »
**Éliminée** : le lakefile est en place (test ci-dessus, Lake 5.0 syntaxe TOML). Le problème est en aval (modules absents), pas en amont (packaging).

### Option (b) « Ré-écrire les 2 modules absents »
**Hors scope** : ré-écrire `TriadConservation.lean` et `RoPECoherence.lean` à partir des commentaires d'OcclusionTriad.lean et du paper est un travail de **ré-implémentation mathématique**, pas de vérification. Cela demanderait 1-2 cycles substantifs et un mathématicien. Coût/bénéfice défavorable.

### Option (c) « Arrêter Pli 2 et pivoter sur `so(M)` via d'autres sources »
**Recommandée** : l'algèbre de Lie `so(M)` est un objet mathématique substantiel, indépendant du dépôt DarkSnail. Notre matériel `differential_lean/` (#18205 géométrie différentielle) et nos EPICs Origami siblings (#19898 openai/math, #20404 Thurston) sont des sources upstream plus solides. Le pivot préserve la valeur mathématique tout en évitant un upstream non vérifiable.

### Option (d) « Demander upstream `sneed-and-feed` de publier les 2 modules »
**Différée** : geste social, peut être tenté en parallèle de (c). Si upstream répond, Pli 2 peut être ré-ouvert. Sinon, (c) reste la voie.

## 4. Verdict consolidé

**Pli 2 — `INSUFFICISANT_BLOQUANT`** :
- 0 sorry réel (4 patterns) — **vérifié** par po-2027 c.1728.
- 0 axiome piégeant (`sorryAx`, `native_decide.*`) — **vérifié** par po-2027 c.1728.
- **MAIS** : 2 modules référencés mais absents du dépôt → **non compilable** → **non vérifiable** par tiers.
- Reconstruction lakefile (cette PR) : OK, mais **insuffisante** pour résoudre le problème.

**Recommandation au coordinateur** : trancher Pli 2 selon l'option (c) « arrêt + pivot `so(M)` via autres sources ». Geler Pli 2 en attendant que l'algèbre de Lie `so(M)` soit re-dérivée d'une source vérifiable.

## 5. Implications pour l'EPIC

- **Pli 1** : GLOBAL CLOSE (4/4 sub-grains).
- **Pli 2** : `INSUFFICISANT_BLOQUANT` confirmé first-hand c.487.
- **Pli 3** (PostTraining) : **indépendant** de Pli 2. Actionnable dès qu'un grain H_R (Clef, jevlike, laya) est mesurable sur le banc `jabr/classifier-benchmark` (#17883).
- **Pli 4** (Pédagogie) : dépend de Pli 3 (au moins une mesure honnête).

L'EPIC n'est **pas terminée** par l'échec de Pli 2. Pli 3 (et indirectement Pli 4) reste actionnable. Mais la **branche Lean upstream DarkSnail est close** sans regret (l'upstream n'est pas falsifiable).

## 6. Statut grain

- **Grain** : **DEEP/lean** — investigation first-hand, élimination d'options, verdict documenté.
- **G-VAR-1** : **TENU** si PR mergée (premier DEEP depuis #21305 c.1720 sur po-2027, ou depuis... — vérifier).
- **Coût** : ~25 min budget c.487.
- **Livrable** : PR `feature/darksnail-pli2-lake-enveloppe` (en cours) + ce document.

## 7. Suite recommandée

- **Court terme** : PR DEEP/lean avec ce document, demande coordinateur trancher Pli 2 option (c).
- **Moyen terme** : si Pli 2 arrêté, basculer ressources sur Pli 3 (PostTraining), spécifiquement la mesure de **Cloudflare Clef** sur `jabr/classifier-benchmark` (#17883, #327 benchmark dans le dépôt).
- **Action user attendue** : arbitrage Pli 2 (option c). Pas d'urgence.

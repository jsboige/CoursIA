# Pli 2.0 — Lake d'enveloppe OcclusionTriad : verdict `INSUFFICISANT_BLOQUANT`

> **Etat mesure au 2026-10-29** : la **prémisse de ce verdict est falsifiée par la dérive amont** — les deux imports fantômes (`TriadConservation`, `RoPECoherence`) ont disparu du fichier amont, qui compile intégralement (build SUCCESS, 0 sorry, 0 `sorryAx`, 0 `native_decide`, 67 théorèmes sur le profil axiomatique Mathlib standard) dans une enveloppe minimale. C'est le cas de figure que l'option (d) ci-dessous prévoyait (« Si upstream répond, Pli 2 peut être ré-ouvert »). Le verdict ci-dessous reste celui de sa date (2026-10-22) sur la tête qu'il a mesurée ; la décision de rouvrir Pli 2 appartient au coordinateur. Mesure complète : [`concern-2026-10-29-build-verification.md`](concern-2026-10-29-build-verification.md).

> **Statut** : investigation first-hand c.487, Pli 2.0 CLOSE.
> **Date** : 2026-10-18 (verdict révisé le 2026-10-22).
> **Lane** : myia-po-2024:CoursIA-2 (Lean toolchain disponible, Lean 4.35.0, Lake 5.0.0).
> **EPIC parent** : #21310 (Project DarkSnail Origami).
> **Arbitrage coordinateur** : option (c) retenue — arrêt de Pli 2 et pivot `so(M)` par d'autres sources (revue ai-01 du 2026-10-21 sur la PR de ce document, réserve de fond reprise ici).

---

## TL;DR

Le verdict Pli 1.2 de po-2027 (`INSUFFICISANT`) est **confirmé et sa cause est identifiée first-hand** : la reconstruction du lakefile est **insuffisante**. Le code `formalization/OcclusionTriad.lean` référence des modules absents du dépôt upstream : `Formalization.Analysis.TriadConservation` et `Formalization.Analysis.RoPECoherence`.

**Conséquence** : Pli 2 (lake d'enveloppe) ne peut pas être livré sans :
- (a) Ré-écrire les modules absents (`TriadConservation`, `RoPECoherence` — travail substantif, hors scope vérification tierce).
- (b) Demander upstream `sneed-and-feed` de publier les modules manquants (social, hors cluster).
- (c) **Arrêter Pli 2** et pivoter sur l'algèbre de Lie `so(M)` via d'autres sources (#18205 géométrie différentielle).

**Recommandation** : (c). L'EPIC documente alors la nullité de la branche Lean upstream DarkSnail, mais l'algèbre de Lie `so(M)` reste digne d'intérêt via d'autres sources.

## 1. Démarche first-hand

### 1.1 Préparation
- Worktree isolé : `D:\Dev\CoursIA-c487-darksnail-pli2` sur `feature/darksnail-pli2-lake-enveloppe` depuis origin/main.
- Lean toolchain : `leanprover/lean4:v4.35.0` (installée sur po-2024).
- Lake version : 5.0.0-src+eb6cafb.
- Dossier `DarkSnailLake/` créé à la racine du worktree.

### 1.2 Clone du fichier source et provenance
Le fichier amont `formalization/OcclusionTriad.lean` est cloné via API GitHub dans `DarkSnailLake/DarkSnail/OcclusionTriad.lean` (arborescence standard Lake : `DarkSnail/OcclusionTriad.lean`).

Provenance du contenu lu : l'identité de blob (`git hash-object` sur la copie locale = blob amont au commit lu) prouve que la copie examinée est **exactement** la version upstream de ce commit, et non une reconstruction. Le détail figure au §8.

### 1.3 Ce qui est livré, ce qui ne l'est pas
**Livré** : ce document de verdict, seul.

**Non livré** : le lake d'enveloppe (`DarkSnailLake/`). Trois raisons, toutes vérifiées :
- il ne compile pas (§1.6) — il ne prouve donc rien que le présent document ne dise déjà ;
- il est posé à la racine du dépôt, hors de toute série, et son `defaultTargets` ne vise que ce seul fichier ;
- une copie de code amont n'a pas sa place dans ce dépôt public : elle est remplacée ici par sa **provenance citée** (URL, commit, blob, licence).

**Preuve de conservation** : rien n'est perdu. Le code amont reste publié sous `https://github.com/sneed-and-feed/projectdarksnail` au commit `90ef5bdfabc2f01bb4ae1218ffce659ef47ace6b`, sous licence `CC0-1.0`, et le document le cite ; le dépôt amont en conserve l'historique complet. Le retrait porte sur la copie locale, pas sur la source.

### 1.4 Création du lake d'enveloppe
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

### 1.5 Premier essai `lake build`
L'erreur initiale était syntaxique (Lake 5.0 utilise TOML, pas Lean DSL). Corrigé.

### 1.6 Deuxième essai `lake build DarkSnail.OcclusionTriad`
- Mathlib materializing : OK (v4.35.0 épinglé)
- Batteries, Aesop, ProofWidgets, Qq, LeanSearchClient, ImportGraph, Plausible, Cli, Cache, etc. : tous materializing OK
- Build relancé sur la même machine le 2026-10-22 pour remplacer l'attente annoncée par une **mesure** ; résultat reproduit en §1.7.

### 1.7 Résultat réel de la compilation — `FAILED`, code de sortie 1

Compilation directe du fichier cible dans l'environnement du lake (`lake env lean DarkSnail/OcclusionTriad.lean`, Lean 4.35.0), sortie verbatim :

```
DarkSnail/OcclusionTriad.lean:1:0: error: unknown module prefix 'Formalization'

No directory 'Formalization' or file 'Formalization.olean' in the search path entries:
DarkSnailLake/.lake/packages/mathlib/.lake/build/lib/lean
DarkSnailLake/.lake/build/lib/lean
...
```

Code de sortie : **1**. L'échec est **antérieur à toute élaboration** : c'est le premier import du fichier qui ne se résout pas. Le `lake build` complet, relancé le même jour, engageait la construction de la fermeture de dépendances de Mathlib alors que cette erreur était déjà acquise ; il a été arrêté sur ce constat, la cible ne pouvant pas aboutir.

Le verdict ne repose donc **pas** sur une attente, mais sur un code de sortie mesuré.

**Ce qui est établi** : le fichier amont, tel que publié, ne compile pas — et son premier import est précisément l'un des deux modules absents du dépôt amont (§2.1, §2.2).

## 2. Cause identifiée first-hand

### 2.1 Inventaire du dossier `formalization/` upstream
Via `gh api repos/sneed-and-feed/projectdarksnail/git/trees/HEAD?recursive=0` :
- `formalization/OcclusionTriad.lean` — **seul fichier** du dossier.

C'est-à-dire : le dossier `formalization/` ne contient **QUE** `OcclusionTriad.lean`. Aucun `Analysis/TriadConservation.lean`, aucun `Analysis/RoPECoherence.lean`, aucun sous-dossier `Analysis/`.

**Re-vérification** : le dépôt amont a avancé (`985a3185` du 2026-10-21, qui a modifié `OcclusionTriad.lean` lui-même). L'inventaire a été refait sur cette tête plus récente (`git/trees/985a3185...?recursive=1`) : `formalization/` ne contient **toujours** que `OcclusionTriad.lean`. Le constat du §2.2 tient donc sur le code amont courant, pas sur une version périmée.

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
Contrairement à l'hypothèse initiale (manque de lakefile), le problème n'est **pas** un packaging raté. Le code **référence** des modules qui n'ont jamais été écrits. Le dépôt upstream livre une promesse (`Lean 4 Verified (0 sorry)`) qui n'est pas tenue par les faits : un module qui dépend de modules absents ne peut pas être vérifié, et le badge « 0 sorry » n'est pas falsifiable en l'état.

## 3. Élimination des options de Pli 2

### Option (a) « Reconstruire le lakefile manuellement »
**Éliminée** : le lakefile est en place (test ci-dessus, Lake 5.0 syntaxe TOML). Le problème est en aval (modules absents), pas en amont (packaging).

### Option (b) « Ré-écrire les modules absents »
**Hors scope** : ré-écrire `TriadConservation.lean` et `RoPECoherence.lean` à partir des commentaires d'OcclusionTriad.lean et du paper est un travail de **ré-implémentation mathématique**, pas de vérification. Cela demanderait 1-2 cycles substantifs et un mathématicien. Coût/bénéfice défavorable.

### Option (c) « Arrêter Pli 2 et pivoter sur `so(M)` via d'autres sources »
**Recommandée** : l'algèbre de Lie `so(M)` est un objet mathématique substantiel, indépendant du dépôt DarkSnail. Notre matériel `differential_lean/` (#18205 géométrie différentielle) et nos EPICs Origami siblings (#19898 openai/math, #20404 Thurston) sont des sources upstream plus solides. Le pivot préserve la valeur mathématique tout en évitant un upstream non vérifiable.

### Option (d) « Demander upstream `sneed-and-feed` de publier les modules manquants »
**Différée** : geste social, peut être tenté en parallèle de (c). Si upstream répond, Pli 2 peut être ré-ouvert. Sinon, (c) reste la voie.

## 4. Verdict consolidé

**Pli 2 — `INSUFFICISANT_BLOQUANT`** :
- 0 sorry réel (4 patterns) — **vérifié** par po-2027 c.1728.
- 0 axiome piégeant (`sorryAx`, `native_decide.*`) — **vérifié** par po-2027 c.1728.
- **MAIS** : modules référencés mais absents du dépôt → **non compilable** (code de sortie 1, §1.7) → **non vérifiable** par tiers.
- Le lake d'enveloppe a été construit et a échoué comme prévu : il est **insuffisant** pour résoudre le problème. Il n'est pas livré (§1.3).

**Arbitrage rendu** : option (c) retenue — arrêt de Pli 2 et pivot `so(M)` par d'autres sources. Pli 2 est gelé ; l'algèbre de Lie `so(M)` reste à re-dériver d'une source vérifiable.

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
- **Livrable** : ce document de verdict ; la branche `feature/darksnail-pli2-lake-enveloppe` ne porte plus que lui (lake retiré, §1.3).

## 7. Suite recommandée

- **Court terme** : PR DEEP/lean portant ce document ; l'arbitrage option (c) est rendu (§4).
- **Moyen terme** : Pli 2 arrêté, basculer les ressources sur Pli 3 (PostTraining), spécifiquement la mesure de **Cloudflare Clef** sur `jabr/classifier-benchmark` (#17883, #327 benchmark dans le dépôt).
- **Action user** : **aucune attendue**. L'option (d) — écrire sur le dépôt amont sous notre identité — resterait subordonnée à un accord explicite du user ; elle n'est pas engagée et ne l'est pas dans ce cycle.

---

## 8. Provenance de la lecture

| Élément | Valeur |
|---|---|
| Dépôt amont | `https://github.com/sneed-and-feed/projectdarksnail` |
| Fichier lu | `formalization/OcclusionTriad.lean` |
| Commit lu | `90ef5bdfabc2f01bb4ae1218ffce659ef47ace6b` (2026-10-15) |
| Blob SHA amont = blob local | `72b0b67672e812f6102841cf71cdb295432318fc` |
| Tête amont re-vérifiée | `985a3185dfea9d3391659d47c87a79f30f147520` (2026-10-21) |
| Licence amont | `CC0-1.0` — `LICENSE` à la racine du dépôt |

Aucune copie du code amont n'est livrée dans ce dépôt : le document le cite et le laisse à sa source.

# Concern user du 2026-10-18 — build first-hand du contenu Lean : la prémisse du verdict Pli 2 est falsifiée

> **Statut** : mesure first-hand livrée ; le dépliage éventuel de Pli 2 reste au coordinateur (gel ai-01 du 2026-10-21 inchangé par ce document).
> **Date** : 2026-10-29.
> **Lane** : myia-po-2028:CoursIA-2 (WSL Ubuntu, Lean 4.33.0, Lake + elan).
> **EPIC parent** : #21310 (Project DarkSnail Origami).
> **Répond à** : le Concern user du 2026-10-18T22:13Z sur #21310 — « Je propose qu'on importe et qu'on builde nous-même le contenu Lean pour voir s'il tient la route, et surtout qu'on regarde dans quelle mesure le geste ébauché dans ce dépôt peut être validé et prolongé. »

---

## TL;DR

Le verdict [`INSUFFISISANT_BLOQUANT`](pli2-lake-enveloppe-verdict.md) du Pli 2 reposait sur une prémisse mesurée : « le fichier amont ne compile pas » (imports vers deux modules absents), donc « non vérifiable par tiers ». **Cette prémisse est fausse à la tête amont du 2026-10-29** : upstream a supprimé les imports fantômes, et le fichier compile intégralement dans une enveloppe de build minimale.

Mesures du 2026-10-29 sur le clone amont à `043c9d26` :

| Mesure | Résultat |
|---|---|
| `lake build` (enveloppe Mathlib v4.33.0) | **SUCCESS** — 3007 jobs, `OcclusionTriad` 19 s, `BlockBridge` 608 ms |
| Warnings de compilation | **0** (log complet consulté, pas seulement la queue) |
| `sorry` dans les sources | **0** (les deux fichiers) |
| `axiom` déclarés / `native_decide` dans les sources | **0 / 0** |
| `#print axioms` sur les 67 théorèmes | **5 sans aucun axiome** ; **62 sur le trio standard Mathlib** (`propext`, `Classical.choice`, `Quot.sound`) ; **0 `sorryAx`**, **0 `native_decide`** |

La claim README amont (« machine-checked in Lean 4 with zero sorry and zero compiler warnings ») est **vérifiée par tiers** au commit mesuré, au sens du typecheck et de l'intégrité axiomatique (réserves au §5).

## 1. Démarche first-hand

### 1.1 Clone et dérive mesurée depuis les verdicts du 18-22/10

Clone shallow du dépôt amont `sneed-and-feed/projectdarksnail` à la tête `043c9d26` (2026-10-29T06:50:32-07:00). Dérive par rapport aux têtes des verdicts précédents (`90ef5bdf` du 15/10, `985a3185` du 21/10) :

| Aspect | Mesure 18-22/10 (Pli 1.2 / Pli 2.0) | Mesure 29/10 (ce document) |
|---|---|---|
| Imports d'`OcclusionTriad.lean` | `Formalization.Analysis.TriadConservation` + `RoPECoherence` (**modules absents**) | `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` + `Mathlib.Tactic` **seuls** — les imports fantômes ont disparu |
| Taille d'`OcclusionTriad.lean` | 510 lignes (blob `72b0b676`) | **999 lignes** (blob `a2d3605d`) |
| `formalization/BlockBridge.lean` | inexistant | **nouveau, 289 lignes**, aucun import externe (namespace `DarkSnail.BlockBridge`) |
| Structure de build amont (lakefile/lean-toolchain) | absente | **toujours absente** |

C'est le cas de figure que la page Pli 2 nommait en option (d) : « Si upstream répond, Pli 2 peut être ré-ouvert ». Upstream a publié — pas sur sollicitation (aucune issue ouverte par le cluster, conformément au §7 de cette page), mais de lui-même.

### 1.2 Enveloppe de build (fournie par la lane, pas par upstream)

Upstream ne livre toujours ni `lakefile` ni `lean-toolchain` : l'enveloppe est la nôtre, minimale et reproductible :

- `lean-toolchain` : `leanprover/lean4:v4.33.0`
- `lakefile.toml` :
  ```toml
  name = "DsnailEnvelope"
  version = "0.1.0"

  [[require]]
  name = "mathlib"
  git = "https://github.com/leanprover-community/mathlib4"
  rev = "v4.33.0"

  [[lean_lib]]
  name = "DsnailEnvelope"
  roots = ["DsnailEnvelope", "Formalization.OcclusionTriad", "Formalization.BlockBridge"]
  ```
- Les deux fichiers `.lean` amont copiés tels quels (blobs cités au §7) sous `Formalization/`.
- `lake update` (rc=0) → `lake exe cache get` (rc=0, 8 690 fichiers déjà en cache) → `lake build Formalization.OcclusionTriad Formalization.BlockBridge` (rc=0).

Note de reproductibilité : le `lake build` nu rend « no default targets configured » avec cette forme de lakefile — les cibles se passent **explicitement** (`lake build Formalization.OcclusionTriad Formalization.BlockBridge`), c'est la commande mesurée ci-dessus.

### 1.3 Passe `#print axioms`

Un fichier `Axioms.lean` généré (script Python, 67 requêtes — tous les `theorem`/`lemma` des deux fichiers : 43 dans `Ultrametric.Analysis.OcclusionTriad`, 24 dans `DarkSnail.BlockBridge`) exécuté par `lake env lean Axioms.lean` (rc=0).

Les 5 théorèmes **sans aucun axiome** (tous dans `BlockBridge`) :
- `DarkSnail.BlockBridge.nb2_retargeting_count_invariant`
- `DarkSnail.BlockBridge.nb2_retargeting_all_counts_invariant`
- `DarkSnail.BlockBridge.nb2_retargeting_preserves_budget`
- `DarkSnail.BlockBridge.causal_triangle_window_frac_monotonicity`
- `DarkSnail.BlockBridge.causal_triangle_window_monotonicity`

Les 62 autres dépendent exactement de `[propext, Classical.choice, Quot.sound]` — le trio standard que transitivement porte toute preuve Mathlib ; aucun n'ajoute `sorryAx` ni aucun axiome `native_decide.*`. C'est le profil axiomatique d'une preuve Mathlib ordinaire.

## 2. Inventaire Python (le « gros du projet » nommé par le Concern)

41 357 lignes Python au même commit. Modules dominants :

| Module | Lignes | Rôle (lu dans les sources, pas déduit du README) |
|---|---|---|
| `darksnail/arc3.py` | 12 159 | évaluateur ARC-AGI-3 (le plus gros module du dépôt) |
| `darksnail/readout.py` | 2 845 | couche de lecture (readout) |
| `darksnail/gemma4.py` | 2 821 | intégration Gemma |
| `darksnail/shell.py` | 2 439 | hémisphère spatial / coque |
| `darksnail/hooks.py` | 1 531 | hooks d'exécution (session) |
| `llama_surgery/surgery.py` | 1 251 | chirurgie de poids Llama |
| `ultrametric/block_list.py` | 1 083 | noyaux ultramétriques (block lists) |

S'y ajoutent : 5 fichiers de tests (`test_darksnail.py`, `test_darksnail_arc3.py`, `test_darksnail_gemma4.py`, `test_hooks.py`, `test_verified_block_sparse.py`), des checkpoints routers safetensors (`gemma4_31b` 85,38 Mo ; `llama31_8b` 11,56 Mo), des notebooks Colab, et des résultats ARC-AGI-3 (63/183 niveaux affichés au README). La « chirurgie » que le Concern qualifiait de gros du projet est bien là : patch d'attention, hooks runtime, kernels ultramétriques — mesurée en structure, pas exécutée dans ce cycle.

## 3. Ce que cette mesure prouve — et ce qu'elle ne prouve pas

**Prouvé (au commit `043c9d26`, contre Mathlib v4.33.0)** :
1. Les deux fichiers compilent intégralement (élaboration complète, 0 erreur, 0 warning).
2. Aucune preuve n'est suspendue (`0 sorry`, `0 sorryAx` transitif).
3. Aucun axiome piégé (`0 native_decide`, `0 axiom` déclarée) ; seuls les trois axiomes standard de Mathlib.
4. La claim badge « Lean 4 Zero Sorry Verified » devient **falsifiable et vérifiée** : c'est précisément ce qui manquait au verdict du 18/10.

**Non prouvé (et non prouvable par un build)** :
1. **La fidélité des énoncés** à la physique et à l'architecture revendiquées (MHD/stellarator, MRxMHD/KAM, rotors SO(6) Kelvin-Mandel) : un build prouve que les preuves des énoncés *tels qu'écrits* sont complètes, pas que ces énoncés formalisent le système Python. C'est une revue de fond, humaine.
2. **La reproductibilité côté upstream** : l'enveloppe de build reste la nône ; upstream ne fournit toujours pas de structure de build. Le claim « L1–L982 » du README est d'ailleurs déjà périmé sur son propre fichier (il a presque doublé au HEAD mesuré).
3. **Le comportement du code Python** : inventaire structurel seulement dans ce cycle ; aucune exécution des tests amont.

## 4. Assessment d'extension dans CoursIA

Ce que la mesure débloque, sans déplier quoi que ce soit (Pli 2 gelé par arbitrage ai-01 du 21/10, inchangé) :

- **La branche Lean amont redevient falsifiable par tiers** : l'option (c) « la branche Lean upstream est close sans regret » reposait sur « l'upstream n'est pas falsifiable » — cette raison-là est tombée. La décision de rouvrir ou non Pli 2 appartient au coordinateur (la page Pli 2 prévoyait elle-même la ré-ouverture dans ce cas de figure, option (d)).
- **Matériel pédagogique candidat** (si le coordinateur déplie) : le fichier amont est un exemple réel, extérieur au cours, de formalisation Mathlib pure (analyse, SO(6), invariants MHD) vérifiable en ~20 s sur cache chaud — profil d'un carnet `notebook-lean` d'étude de preuve externe, sur le précédent du Pli 1.2.
- **Le pont BlockBridge** (`DarkSnail.BlockBridge`, autonome, 5 théorèmes sans aucun axiome) est le morceau le plus proche du code Python (budget causal par bloc, retargeting NB2) : c'est lui qui matérialise le « geste ébauché » que le Concern demande de « valider et prolonger ».

## 5. Statut grain

- **Grain** : DEEP/lean — vérification first-hand, mesure datée, falsification d'une prémisse de verdict, livraison documentée.
- **Livrable** : ce document + le commentaire de réponse au Concern sur #21310.
- **Non livré** : l'enveloppe elle-même (convention de la page Pli 2 §1.3 : une copie de code amont n'a pas sa place dans ce dépôt public ; elle est remplacée par sa provenance citée).

## 6. Suite recommandée

- Le coordinateur arbitre : rouvrir Pli 2 (l'upstream a publié) ou maintenir le pivot `so(M)` (option (c)). Ce document ne tranche pas.
- Si Pli 2 rouvre, le premier sous-grain naturel est la relecture de fond des **énoncés** (fidélité physique), pas un nouveau build.

---

## 7. Provenance de la lecture

| Élément | Valeur |
|---|---|
| Dépôt amont | `https://github.com/sneed-and-feed/projectdarksnail` |
| Tête mesurée | `043c9d26fc86816e4272d37e755c5918282bfb52` (2026-10-29T06:50:32-07:00) |
| `formalization/OcclusionTriad.lean` | 999 lignes, blob `a2d3605daf113206c34e242cb29888b0a1d06b33`, namespace `Ultrametric.Analysis.OcclusionTriad` |
| `formalization/BlockBridge.lean` | 289 lignes, blob `3353d3dc087c559ed3b1d76f672d2f9eedb95b4d`, namespace `DarkSnail.BlockBridge` |
| Licence amont | CC0-1.0 |
| Environnement de build | WSL Ubuntu, Lean `v4.33.0` (elan), Mathlib `v4.33.0` épinglée, cache Mathlib chaud |

Aucune copie du code amont n'est livrée dans ce dépôt : le document cite et laisse à sa source (convention établie par la page Pli 2).

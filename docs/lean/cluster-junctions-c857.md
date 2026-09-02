# Cluster Mathlib mutualization — Scan report (c.857, po-2024)

**Date** : 2026-09-02 (cycle c.857)
**Lane** : `myia-po-2024:CoursIA-2`
**Issue** : #13962 (V1 narrow : Scan, pas d'Apply)
**Script** : `scripts/lean/setup_shared_mathlib.ps1 -Mode Scan`
**Verdict** : **0 mutualisable actuellement** sur cette machine, **19 lacs partagent le même (toolchain, mathlib-rev)** et constituent un réservoir d'opportunité

## Commande

```bash
pwsh -NoProfile -Command "./scripts/lean/setup_shared_mathlib.ps1 -Mode Scan"
```

Exécutée depuis `C:/dev/CoursIA-c857-13962` (worktree `fix/c857-13962-mathlib-junctions-scan` @ `cd5905a73d`, à jour sur `origin/main`).

## Résultat brut

| Métrique | Valeur |
|---|---|
| Projets Lake avec dépendance `mathlib` (manifest scanné) | **24** |
| Groupes par manifest-identity (toolchain + toutes deps triées) | **6** |
| Groupe MUTUALISABLE (≥2 membres) | **1** — `leanprover/lean4:v4.32.1 + mathlib=520045ab` |
| Membres du groupe mutualisable | **19** |
| Groupes isolés (1 seul membre) | **5** |
| Checkouts `.lake/packages/mathlib/` présents | **0** |
| Économie totale potentielle (état actuel) | **0 GB** |

## Composition du groupe mutualisable (19 lacs)

```
MyIA.AI.Notebooks/GameTheory/assignment_lean
MyIA.AI.Notebooks/GameTheory/game_theory_lean
MyIA.AI.Notebooks/GameTheory/minimax_lean
MyIA.AI.Notebooks/GameTheory/repeated_games_lean
MyIA.AI.Notebooks/ML/learning_theory_lean
MyIA.AI.Notebooks/Probas/decision_theory_lean
MyIA.AI.Notebooks/QuantConnect/kelly_lean
MyIA.AI.Notebooks/Search/search_lean
MyIA.AI.Notebooks/Sudoku/sudoku_lean
MyIA.AI.Notebooks/SymbolicAI/Lean/calibration_lean
MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean
MyIA.AI.Notebooks/SymbolicAI/Lean/galois_lean
MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean
MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean
MyIA.AI.Notebooks/SymbolicAI/Lean/mathlib_examples
MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean
MyIA.AI.Notebooks/SymbolicAI/Planners/planning_lean
MyIA.AI.Notebooks/SymbolicAI/SmartContracts/erc20_lean
MyIA.AI.Notebooks/SymbolicAI/Tweety/argumentation_lean
```

Tous en `pas de checkout local` au moment du scan (worktree frais sur main, sans `lake update`).

## Groupes isolés (5 lacs, manifest distinct)

| Lac | Toolchain | mathlib rev | Raison d'isolement |
|---|---|---|---|
| `SymbolicAI/Lean/agent_tests/prover/session_state/reference_docs/stable_marriage/upstream` | `leanprover/lean4:v4.25.0` | `1ccd71f8` | Fixture prover — toolchain ancien |
| `GameTheory/conway_cgt_lean` | `leanprover/lean4:v4.31.0-rc2` | `acbd8f07` | Pre-release toolchain |
| `Search/discrepancy_lean` | `v4.32.1` | `520045ab` | MÊME toolchain + rev que le groupe 19 mais **manifest différent** (deps transitives distinctes) |
| `SymbolicAI/Lean/mimo_lean` | `v4.32.1` | `520045ab` | Idem — deps transitives distinctes |
| `GameTheory/social_choice_lean_peters` | `v4.32.1` | `520045ab` | Idem |

Les trois derniers sont **isolés malgré l'identité toolchain + mathlib-rev** parce que la clé de groupe est `toolchain + (name,rev) triées de TOUTES les deps transitives` (lignes 119-123 du script). Cette borne est délibérée — un replay Lake exige l'identité du graphe de packages entier, pas seulement de Mathlib (précondition durcie 2026-06-10, mentionnée en commentaire du script).

## Vérification falsifiable — manifest-identity est bien ce que l'instrument calcule

Le critère d'acceptance #13962 point 1 demande : « Le cluster doit être reconnu manifest-identique, pas seulement « même rev Mathlib » ». **L'instrument satisfait déjà ce point** : `Get-LeanProjects` (lignes 96-138) lit `lake-manifest.json`, trie les `packages` par nom, et concatène `name=rev` pour *toutes* les deps (pas seulement `mathlib`). Les 3 lacs `v4.32.1 + 520045ab` qui restent isolés sont la **preuve** que la discrimination est plus stricte que la simple rev Mathlib.

Note 188 du script : « l'alignement des manifests (#2611 étape 2) peut élargir les groupes » — c'est la voie d'investigation pour faire tomber ces 3 lacs dans le groupe 19, jamais un raccourci vers un Apply bâclé.

## Pourquoi 0 GB malgré 19 lacs mutualisables

Le calcul d'économie (`Invoke-Scan` lignes 179-184) agrège les tailles `Get-DirSizeGB $m.MathlibDir` pour les membres **qui ont un checkout physique** (`$m.HasCheckout`). Si **aucun** des 19 membres n'a de checkout, l'ensemble `$sizes` est vide et `$savings = 0`. C'est l'état sur ce worktree — `lake update` n'a été lancé sur aucun des 19 lacs parents.

Pour qu'une économie soit **réellement** matérialisée par un `Apply`, il faut :
1. Au moins un membre du cluster porte un checkout initial (le donneur)
2. Les autres membres sont configurés en junctions qui pointent vers le donneur
3. Les manifests de tous les membres sont alignés (ce qui est garanti par le clustering par manifest-identity)

**Aucun de ces prérequis n'est tenu** sur cette machine aujourd'hui. Le réservoir est identifié mais pas amorcé.

## Diagnostic séparé — `mimo_lean` checkout orphelin hors worktree c.857

Le commentaire de cycle précédent (`cycles-855-detail.md`, scan antérieur) rapportait un checkout `mimo_lean` de **1.18 GB** sur la machine. Il n'apparaît **pas** dans ce scan-ci. Cause : `Get-LeanProjects` lit **uniquement le répertoire courant** (`git -C $RepoRoot ls-files ...`) ; le checkout antérieur vivait dans un autre worktree (`C:/dev/c1331p450-12753` ou un cycle précédent), pas dans `C:/dev/CoursIA-c857-13962`. Le scanner est **worktree-local**, pas machine-global.

Conséquence : une économie **trans-worktree** n'est pas ce que cet instrument mesure. Si l'objectif est de récupérer 1.18 GB orphelin, c'est un nettoyage `Remove-Item` manuel sur le worktree source — pas un Apply. Ce diagnostic est noté pour suivi, pas pour action dans ce cycle.

## Bornes explicites du grain livré

- **V1 narrow** : lecture seule, rapport de mesure, pas de modification du script de production, pas d'Apply, pas de manipulation de `.lake/`.
- **Aucun fichier de code touché** — seulement ce rapport `docs/lean/cluster-junctions-c857.md`.
- **Pas de MEMORY addition** : `MEMORY.md` à 17498/17500 bytes, Tell c.423-L1 ★★ strict.

## Hors périmètre (à traiter en cycles séparés)

- **`lake update` sur un lac parent** : hors fenêtre cycle worker (clone Mathlib4 multi-minutes, Tell c.850-L2 ★★, bloqueur multi-cycle). Bloqueur connu, déjà tracé via #14178.
- **Alignement manifests (#2611 étape 2)** : investigation hors-scan, demande de regarder un par un les 3 lacs isolés qui partagent toolchain+rev. Substance distincte, grain séparé.
- **Nettoyage du checkout orphelin `mimo_lean` 1.18 GB** : action manuelle de l'opérateur sur le worktree source (pas un Apply).

## Suite logique

- **Issue #13962** : ce cycle ferme **V1 narrow** (Scan + rapport). V2 (Apply effectif) reste à programmer une fois qu'un lac parent porte un checkout initial — typiquement via #14178 (Mathlib cache absent pour `learning_theory_lean`) qui est sur la voie d'amorçage.
- **Issue #14178** : follow-up prioritaire pour faire atterrir un premier checkout dans le cluster.
- **Aucune PR ouvrable sur le scanner lui-même** : l'instrument est correct sur la discrimination manifest-identity. Le rapport tient lieu de livraison de mesure.

## Référence croisée

- Issue #13962 — grain parent (NTFS junctions Mathlib)
- Issue #2611 — alignement manifests (étape 2)
- Issue #14178 — Mathlib cache absent worktree (bloqueur amorçage)
- `scripts/lean/setup_shared_mathlib.ps1` — instrument de scan/apply/rollback
- `cycles-850-detail.md` — Tell c.850-L2 ★★ bloqueur clone Mathlib
- `cycles-855-detail.md` — observation antérieure checkout `mimo_lean` 1.18 GB (worktree-local, hors scope)

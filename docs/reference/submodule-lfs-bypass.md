# Submodule LFS bypass — worktree-based checkout sans réseau

Procédure de matérialisation d'un submodule LFS-lourd dans un worktree **sans appel réseau** (sans `git submodule update --init`, sans `git fetch`). Applicable à toute partition (Probas, Lean `peters/`, Argument_Analysis `Argumentum`, SmartContract `foundry-lib/`) dès lors que le submodule parent a déjà été fetché sur la machine locale et que le créneau cron est court (≤ 5 min).

**Source** : leçon **L510-L6 ★★★** (po-2025, c.510 — bump Argumentum `053257c7 → 7e72f3e5`, PR [#6641](https://github.com/jsboige/CoursIA/pull/6641), MERGED 2026-07-15T04:53Z). Pattern transférable cross-lane.

**Pourquoi cette procédure** : un submodule LFS-lourd (2 à 4 GB) sur 45 worktrees partagés = `git submodule update --init` timeout ≥ 5 min sur Windows (LFS smudge + checkout = réseau obligatoire). Sur un créneau cron 30 min worker, c'est rédhibitoire : on perd le créneau avant d'avoir pu matérialiser le working tree. Cette procédure fait le **même travail en 30 secondes locales** (0 network), à condition que le submodule ait déjà été fetché au moins une fois dans `~/.git/modules/<sub>` du repo principal.

## Pré-requis vérifiables (HARD)

Avant de tenter la procédure, ces **deux** vérifications sont obligatoires :

```bash
# 1. Les deux SHA (source + cible) sont présents dans le submodule gitdir partagé
git -C <repo>/.git/modules/<sub_path>/ cat-file -e <source_sha> && echo "source OK"
git -C <repo>/.git/modules/<sub_path>/ cat-file -e <target_sha> && echo "target OK"

# 2. Le repo principal est sur le bon remote + up-to-date avec la PR target
git -C <repo> fetch origin main
git -C <repo> rev-parse origin/main
```

Si **l'un des deux `cat-file -e` retourne non-zero** : la procédure ne marchera pas, retomber sur `git submodule update --init --reference <cache>` (chemin standard, mais coûteux). Cf section « Fallback » plus bas.

## Procédure (6 étapes)

Soit :
- `<repo>` = repo principal (`d:/dev/CoursIA-2` typique)
- `<branch>` = branche cible de la PR (ex `feature/6409-arg-pr1-bump`)
- `<sub>` = chemin du submodule relatif à `<repo>` (ex `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentum`)
- `<source_sha>` / `<target_sha>` = SHA submodule avant/après

### Étape 1 — worktree fresh depuis origin/main

```bash
cd <repo>
git worktree add <nouveau_worktree> -b <branch> origin/main
```

Typique : `<nouveau_worktree> = d:/dev/CoursIA-<topic>-<cycle>`.

### Étape 2 — créer le dossier gitdir du submodule dans le worktree

Le submodule gitdir doit vivre dans `<repo>/.git/worktrees/<worktree_name>/modules/<sub_path>/`. Calculer le path exact :

```bash
# Astuce : tab-complétion ou `git rev-parse --git-dir` depuis le worktree
git -C <nouveau_worktree> rev-parse --git-dir
#   → D:/dev/CoursIA-2/.git/worktrees/<worktree_name>
# Le submodule gitdir cible :
#   D:/dev/CoursIA-2/.git/worktrees/<worktree_name>/modules/<sub_path>
```

```bash
mkdir -p <repo>/.git/worktrees/<worktree_name>/modules/<sub_path>
```

**Important** : `<sub_path>` est le chemin relatif depuis la racine du repo, avec `/` remplacé par `/`. Sur Windows, garder le format POSIX pour les commandes internes.

### Étape 3 — copier le gitdir partagé du submodule vers le worktree

Le submodule gitdir partagé vit dans `<repo>/.git/modules/<sub_path>/`. On copie son contenu **complet** (objets, refs, packed-refs, HEAD, index, config, hooks) vers le gitdir cible.

```bash
cp -r <repo>/.git/modules/<sub_path>/. <repo>/.git/worktrees/<worktree_name>/modules/<sub_path>/
```

Astuce Windows : `Copy-Item -Recurse -Force` (PowerShell) ou `robocopy /E` en miroir si `cp -r` se plaint des symlinks.

### Étape 4 — re-bind `core.worktree` du submodule gitdir

Sans cette étape, le submodule gitdir pointe encore vers le working tree du **repo principal** et toute commande chdir dedans échoue avec :

```
fatal: cannot chdir to '../../../../../../MyIA.AI.Notebooks/...'
```

```bash
git config --file=<repo>/.git/worktrees/<worktree_name>/modules/<sub_path>/config core.worktree "D:/dev/<nouveau_worktree>/<sub_path>"
```

**Toujours** un chemin absolu Windows pour `core.worktree` (les chemins relatifs ne fonctionnent pas au-delà d'une profondeur 4, typique des submodules nichés dans des sous-arbres profonds comme `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentum`).

### Étape 5 — créer le fichier `.git` du submodule avec gitdir absolu

Le submodule working tree a besoin d'un fichier `.git` à sa racine qui pointe vers son gitdir :

```bash
echo "gitdir: D:/dev/<nouveau_worktree>/.git/worktrees/<worktree_name>/modules/<sub_path>" > <nouveau_worktree>/<sub_path>/.git
```

**Toujours** un chemin absolu Windows ici aussi. Les chemins relatifs échouent dès que la profondeur d'imbrication dépasse 4 niveaux (compté depuis la racine du worktree).

### Étape 6 — peupler le working tree du submodule

```bash
cd <nouveau_worktree>/<sub_path>
git checkout -- .
```

Si un checkout partiel survient (fichiers manquants ou LFS pointers non résolus), vérifier les pré-requis (`git cat-file -e <target_sha>` dans le gitdir source).

## Vérification finale

```bash
cd <nouveau_worktree>
git status                    # doit afficher uniquement le submodule pointer diff
git diff                      # doit afficher uniquement mode 160000, +1/-1
git submodule status          # doit afficher le submodule comme OK
```

Le diff final attendu (PR atomic submodule bump) :

```
diff --git a/<sub> b/<sub>
index <source_sha>..<target_sha> 160000
--- a/<sub>
+++ b/<sub>
@@ -1 +1 @@
-Subproject commit <source_sha>
+Subproject commit <target_sha>
```

## Performance observée

| Phase | `git submodule update --init` (réseau) | Procédure bypass (local) |
|---|---|---|
| Setup worktree | ~5 s | ~5 s |
| Init submodule | **timeout > 5 min** (LFS smudge + fetch) | ~30 s |
| Checkout fichiers | inclus dans init | ~5 s |
| **Total** | **≥ 5 min (échec fréquent sur cron)** | **~40 s** |

Le gain est principalement l'**absence de réseau** : `git submodule update --init --reference` reste une option de repli (cf section « Fallback »).

## Fallback (si pré-requis KO)

Si `git cat-file -e <target_sha>` échoue (SHA pas encore fetché dans le submodule gitdir partagé), trois options par ordre de préférence :

1. **`git submodule update --init --reference <cache_path>`** : utilise un cache LFS partagé, évite le re-fetch réseau. Demande quand même ~2-3 min sur LFS-lourd.
2. **`git fetch --recurse-submodules origin`** : force le fetch du submodule. Coûteux en réseau mais garanti. À éviter en cron worker.
3. **Pivot PR-0 diagnostic** : si le submodule est trop volumineux pour matérialiser dans le créneau, commenter l'issue/PR avec un diagnostic cross-check (cf [pr-review-discipline.md §H.4](../reference/pr-review-context.md)) et demander à ai-01 de merger depuis une machine SANS worktrees partagées (LAN isolée, cache LFS chaud). Pattern observé c.510 L510-L2 ★★.

## Anti-patterns interdits

- **`git submodule update --init` sans `--reference`** sur submodule LFS-lourd en cron worker = timeout quasi-garanti. À éviter.
- **Chemin relatif dans `core.worktree` ou `.git` file** dès que profondeur > 4 = erreur chdir ou gitdir introuvable.
- **Oublier `cp -r .../.`** (le `.` final) = copie du dossier parent sans son contenu, gitdir vide → checkout partiel.
- **Re-bind `core.worktree` APRÈS le checkout** = le checkout a populé avec le mauvais core.worktree (pointe vers main repo) ; il faut le faire AVANT.

## Voir aussi

- [CLAUDE.md global « Knowledge Preservation »](../../CLAUDE.md) — règle de consolidation durable
- [harness-hygiene.md](../../.claude/rules/harness-hygiene.md) — info 3 tiers (harnais / docs / dashboard)
- [MEMORY.md §L510-L6](../../.claude/projects/d--dev-CoursIA-2/memory/MEMORY.md) — leçon source (résumé)
- [catalog-pr-hygiene.md](../../.claude/rules/catalog-pr-hygiene.md) — règle R2 (rebase frais)
- [git-workflow.md](../../.claude/rules/git-workflow.md) — workflow général (branches, commits)
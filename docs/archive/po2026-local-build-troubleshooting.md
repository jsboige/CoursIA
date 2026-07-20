> **ARCHIVED** 2026-07-20 (c.700, owner-dispatch po-2026, See #7422 triage [#4208]).  
> **Raison** : procedure **transiente** d'un incident cluster unique (#6771 lake build failure modes c.466-c.469, recovery recipe validee c.473 knot_lean), **1 inbound reference** sur `origin/main` (`docs/reference/scripts-reference.md` L158, mise a jour c.700). **Procedures codifiees** dans `scripts/lean/po2026_recover_build.py` (309 lignes, idempotent, recete canonique B cache-get + build). Lecon durable dans `MEMORY.md` (L502). Pattern **transferable** mais **non-reference hors zone Lean po-2026** = candidat archive par critere #7422.  
> **Preservation** : deplace **tel quel** vers `docs/archive/po2026-local-build-troubleshooting.md` (cf L686 * NEW). Contenu intact 102 lignes, byte-identity hors preamble.

# po-2026 — Build Lean local : diagnostic des échecs + recette de récupération

**Source** : issue [#6771](https://github.com/jsboige/CoursIA/issues/6771) (priority-high, owner po-2026, self-repair règle F).
**Portée** : machines worker po-2026 (Windows, toolchain elan rc1). Documente les modes d'échec empiriques du `lake build` local et la procédure de récupération canonique.

## Contexte

[lean-merge-discipline.md](../../.claude/rules/lean-merge-discipline.md) §1 exige un **`lake build` SUCCESS local** avant merge sur toute PR Lean. Sur po-2026, ce gate local est devenu irréalisable (cycles c.466-c.469, 2026-07-16) — poussant les PR Lean à dépendre du seul build-gate CI + du build local ai-01 (WSL). Ce document consigne le diagnostic + la recette pour rétablir un gate local fiable sur po-2026.

## Modes d'échec (4, empiriquement établis)

| # | Symptôme | Cause racine | Où constaté |
| --- | ---------- | -------------- | ------------- |
| 1 | **Cold-build timeout** : rebuild Mathlib ~2900 modules > fenêtre de session (~8 min) | Pas de cache warm/trusted ; lake rebuild depuis la source | #6771 body, cycles c.466-c.469 |
| 2 | **OOM / access-violation** (`3221226505` / `3221225477`) sous build parallèle | Pic mémoire sur les gros modules tardifs ; toolchain rc1 complet (2419 `.olean.private` présents — ce n'est PAS un fichier manquant) | #6771 body |
| 3 | **Junction `.lake` worktree→shared inopérante** : timeout à 98 % (2894/2948) | Le lake DB ne propage pas le *trust* du build junctionné → rebuild from scratch → OOM/timeout | #6771 body, leçon L502 (memory po-2026) |
| 4 | **Clone mathlib4 réseau instable** : `git clone` de `.lake/packages/mathlib` échoue (`fetch-pack: invalid index-pack output` / `unexpected disconnect`) | Instabilité réseau/git sur le chemin de clone — **mitigeable** par `http.postBuffer 524288000` + `--depth 1` shallow clone | Empirique c.472 (FAIL) → **c.473 MITIGÉ** (clone SUCCESS + cache-get 38,7 s + build 61 s, knot_lean) |

## Recette de récupération canonique

### A. Build-gate local ai-01 (décision court terme, active)

Tant que le gate local po-2026 n'est pas rétabli, les PR Lean de po-2026 passent par le **build local ai-01 (WSL, env sain)** AVANT merge — déjà mandaté par [lean-merge-discipline.md](../../.claude/rules/lean-merge-discipline.md) §1 pour tout merge. po-2026 pousse avec caveat honnête au body (`gate local ai-01`), ai-01 build AVANT merge. **Double gate CI + local ai-01**.

### B. Cache Mathlib officiel (chemin rapide, quand le réseau est stable)

La voie rapide = télécharger les oleans précompilés officiels de Mathlib depuis Azure plutôt que rebuild la source :

**Recette validée empiriquement (c.473, knot_lean, firsthand po-2026)** :

```bash
cd <lake_lean>          # ex: knot_lean, calibration_lean, sensitivity_lean

# Étape 1 — mitiger le mode d'échec 4 (clone réseau instable) :
git config --global http.postBuffer 524288000     # 500 MB (élimine le `invalid index-pack output`)

# Étape 2 — cloner mathlib4 en shallow (4× moins de données, plus résilient) :
mkdir -p .lake/packages
git clone --depth 1 https://github.com/leanprover-community/mathlib4.git .lake/packages/mathlib

# Étape 3 — télécharger les .olean précompilés (Azure) via lake :
lake exe cache get      # décompresse les .olean précompilés — ~40-60 s

# Étape 4 — build (les .olean sont déjà présents → pas de rebuild source) :
lake build              # ~60 s pour knot_lean (vs ~8 min/OOM-timeout sans cache)
```

**Résultat empirique c.473** : `lake exe cache get` → SUCCESS 38,7 s (8473 fichiers décompressés, 8119 `.olean`) ; `lake build Knots` → **BUILD SUCCESS 61 s** (2959 jobs, sorry warnings = baseline prover connue, EXIT 0). Le chemin trusted-path (cache-get → build) est **VALIDÉ** : le build-gate local po-2026 passe de ~8 min/OOM-timeout à **~1 min SUCCESS**.

⚠ **Note résiduelle** : le mode d'échec 4 (clone réseau instable `invalid index-pack output`) n'est pas éliminé — il est **mitigé** par `http.postBuffer 524288000` + `--depth 1`. Sur un réseau très instable, le clone peut encore échouer (recommencer l'étape 2). Le cache Azure lui-même (`lake exe cache get`) est fiable une fois mathlib cloné.

### C. Limiter le parallélisme (dodge OOM)

Pour passer sous le plafond mémoire (mode d'échec 2) :

```bash
LAKE_JOBS=2 lake build        # ou : lake build --jobs 2
```

Réduit le pic mémoire sur les gros modules tardifs (Mathlib 98 %). Plus lent mais évite l'OOM `3221226505`.

### D. Partage `.lake` cross-worktree : copie, pas junction

Le mode d'échec 3 (junction non trusted) implique de **copier** le `.lake` (même toolchain) plutôt que junction :

```bash
# worktree frais : copier le .lake d'un lake chaud (même toolchain rc1)
cp -r ../CoursIA-2/<lake>/.lake <worktree>/<lake>/.lake
# (pas de junction NTFS — lake DB ne truste pas les reparse points)
```

### E. Vérifier RAM dispo pendant le build

L'OOM à 98 % (mode d'échec 2) suggère un pic sur les gros modules tardifs. Monitorer :

```bash
# Windows PowerShell, pendant lake build :
Get-Process lake,lean,lean.exe -ErrorAction SilentlyContinue | Select-Object WS,CPU
```

Si pic > 80 % RAM physique → `LAKE_JOBS=2` (option C) obligatoire.

## Workflow po-2026 PR Lean (état courant)

1. po-2026 développe sur worktree isolé.
2. Tente `LAKE_JOBS=2 lake build` local (option C). Si SUCCESS → gate local OK, pousser avec preuve. Si timeout/OOM → passez à étape 3.
3. po-2026 pousse la PR avec caveat honnête au body : `gate local ai-01 (po-2026 local build instable, #6771)`.
4. ai-01 build local WSL AVANT merge (double gate CI + local).
5. **Gate local rétabli (c.473)** : sur session réseau stable, exécuter la recette B (`postBuffer 524288000` + clone `--depth 1` + `lake exe cache get` + `lake build`) → BUILD SUCCESS ~1 min. Le gate local po-2026 est de nouveau atteignable (validation firsthand knot_lean).

## Suivi

- [x] ~~Valider chemin trusted : `lake exe cache get` + `lake build` < 2 min sur session réseau stable~~ **VALIDÉ c.473** (knot_lean : cache-get 38,7 s + build 61 s = ~1,5 min ; mitigation clone = `http.postBuffer 524288000` + `--depth 1`)
- [ ] Confirmer `LAKE_JOBS=2` évite l'OOM sur le lake mathlib-junction le plus gros
- [ ] Documenter RAM pic exact (mode d'échec 2) pour calibrer le jobs-limit
- See [#6771](https://github.com/jsboige/CoursIA/issues/6771), [#4980](https://github.com/jsboige/CoursIA/issues/4980), [#2874](https://github.com/jsboige/CoursIA/issues/2874)

## Voir aussi

- [lean-merge-discipline.md](../../.claude/rules/lean-merge-discipline.md) — §1 lake build SUCCESS local gate
- [i18n-sibling-patterns.md](i18n-sibling-patterns.md) — ORPHAN-TRAP globs/roots (distinct : ce doc = build local, pas i18n)
- Leçon **L502** (memory po-2026) : jonctions NTFS = false-negative d'énumération Windows sur reparse points ; discriminants fiables = `.LinkType`/`.Target` + build réel, PAS `Test-Path`/`fsutil`

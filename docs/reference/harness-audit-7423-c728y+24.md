# Audit harnais — sous-grain de #7423 (c.728y+24)

**Date** : 2026-07-22
**Lane** : myia-po-2025:CoursIA-2
**Issue parente** : #7423 [harness] Revue globale du harnais (CLAUDE.md + rules) — owner ai-01
**Scope sub-grain** : audit borné — stale-url + redondance inter-fichiers + règles superseded + périmètre cité vs existant
**Méthodologie** : G.1 firsthand `grep` / `Read` / `git ls-files` (cf CLAUDE.md §G.1 + [verify-before-claiming.md](../../.claude/rules/verify-before-claiming.md))
**Sortie** : 0 PR worker (gouvernance ai-01 — sub-grain audité livré comme signalement, à discrétion coordinateur pour suite ; cf pattern L901 ★ disclosure)
**Commit baseline** : `b28eaac9b docs(sudoku): reconcile '19 notebooks' → disk truth` (c.728y+24)

## TL;DR

**Le harnais est substantivement sain.** 7 findings, **1 seul actionnable** (F1 = 3 rules non citées dans CLAUDE.md cartographie). Aucun lien mort, aucune règle superseded, aucune section périmée.

## Périmètre audité

| Fichier | Lignes | Rôle |
|---------|--------|------|
| `CLAUDE.md` | 249 | index projet (auto-loaded chaque session) |
| `.claude/rules/*.md` × 24 | 1110 | règles auto-loaded spécialisées |
| `MEMORY.md` | per-machine, ~13 KB | index leçons durables |

Total harnais : **1359 lignes** sur 25 fichiers.

## Findings

### F1 — 3 rules non citées dans CLAUDE.md cartographie (LOW, actionnable)

`CLAUDE.md` section cartographie liste 21 references `.claude/rules/*.md`, mais le dossier en contient 24.

**Missing** :

- `.claude/rules/audit-reassessment.md` — protocole réassignement audit (L901 ★ source)
- `.claude/rules/secrets-roosync-policy.md` — politique secrets RooSync (mandat user 2026-07-02 reaffirmé 2026-07-03 + quorum 2026-07-14)
- `.claude/rules/verify-before-claiming.md` — verify before claiming (incident 2026-05-07 + 2026-04-24)

**Cause** : ajouts incrémentaux (per mandate user 2026-07-19 sur le « sans vision globale ») sans mise à jour systématique de l'index.

**Correctif proposé** (3 ajouts ligne 35-55, scope atomique 1 fichier) :

```diff
 - [.claude/rules/secrets-hygiene.md](.claude/rules/secrets-hygiene.md) - Pas de secrets inline (incident recurrent 2026-05-14)
+- [.claude/rules/secrets-roosync-policy.md](.claude/rules/secrets-roosync-policy.md) - Politique secrets RooSync + quorum de provisioning (mandat user 2026-07-02/14)
+- [.claude/rules/audit-reassessment.md](.claude/rules/audit-reassessment.md) - Audit reassessment 4 étapes avant fix sur FP findings (issue #499, L901 ★)
+- [.claude/rules/verify-before-claiming.md](.claude/rules/verify-before-claiming.md) - Verify before claiming (incidents 2026-05-07 / 2026-04-24)
```

### F2 — Pointeurs `docs/` dans CLAUDE.md (NONE)

16 pointeurs `docs/` uniques, **0 lien mort** vs `git ls-files docs/`.

| Pointeur | Existe ? |
|----------|----------|
| `docs/genai/genai-services.md` | ✓ |
| `docs/lean/` (dir, 7 files) | ✓ |
| `docs/qc/quantconnect.md` | ✓ |
| `docs/reference/architecture_mcp_roo.md` | ✓ |
| `docs/reference/claude-code-config.md` | ✓ |
| `docs/reference/cluster-agents.md` | ✓ |
| `docs/reference/common-commands.md` | ✓ |
| `docs/reference/env-python-reparation.md` | ✓ |
| `docs/reference/kernels-runtime.md` | ✓ |
| `docs/reference/procedures-recurrentes.md` | ✓ (× 3 occurrences, ancres `#productivité-...` + `#validation-...`) |
| `docs/reference/regles-validation-detail.md` | ✓ |
| `docs/reference/regles-vigilance-detail.md` | ✓ |
| `docs/reference/scripts-reference.md` | ✓ |
| `docs/reference/stale-tree-drift-scan.md` | ✓ |
| `docs/reference/subagents-reference.md` | ✓ |
| `docs/reference/teaching-context.md` | ✓ |

### F3 — Pointeurs `docs/` dans `.claude/rules/*.md` (NONE)

43 liens `docs/` uniques dans les 24 rules, **0 lien mort** vs `git ls-files docs/`.

Chemins résolus systématiquement via `../../docs/...` (depuis `.claude/rules/*.md`). Aucune path-relatif résiduel.

### F4 — Sections CLAUDE.md (NONE)

16 headers H2/H3/H4 détectés. Structure :

```
## Principes de collaboration (5)
## REGLES CRITIQUES (8 sections)
  ### A. Coordination & Git
  ### B. Reviews PR (5 points obligatoires)
  ### C. Notebooks (3 regles user 2026-04-26)
  ### D. Anti-regression (code de production)
  ### E. Code style (resume)
  ### F. Environnement — REPARER, ne JAMAIS contourner (HARD)
  ### G. Vigilance permanente — anti-complaisance
  ### H. Validation REELLE — pas de complaisance, jamais
## CARTOGRAPHIE & OUTILS
  ### Catalogue agents / skills / scripts — USAGE MANDATÉ
## PROCEDURES RECURRENTES
## REGLES AGENTS (Roo Code distants)
## QUANTCONNECT (resume)
## PROJECT OVERVIEW
```

Mapping numéros A→H cohérent (8 sections CRITIQUES), 5 Principes en intro, 4 sections closing. Pas de trou.

### F5 — Règles superseded par mandat plus récent (NONE)

**8 mandats user datés** trouvés dans le harnais (2026-05-06 env Python, 2026-05-11 productivite, 2026-05-20 labeling, 2026-05-23 agents/skills, 2026-05-26 kernels, 2026-05-28 user-blocker, 2026-06-01 harness-hygiene, 2026-06-09 model-delegation, 2026-07-21 variation-protocol). Tous incarnés par une rule dédiée ou une section dédiée du CLAUDE.md. **0 mandat superseded**.

8 incidents datés également vivants dans leur contexte (2026-03-13 force push, 2026-04-24 Arrow sorry, 2026-04-25 papermill collisions, 2026-05-07 mgs, 2026-05-08 pr-review, 2026-05-10/16 Lean prover, 2026-05-14 secrets leak, 2026-05-17 student soutenance, 2026-05-27 WSL kernels). Chaque incident contextualise une rule vivante.

### F6 — Liens inter-rules (NONE)

21 references rules→rules détectées dans CLAUDE.md, 0 dead link.

### F7 — Périmètre docs/archive/ (NONE)

Aucun pointeur vers `docs/archive/` dans le harnais. **L'archive est bien isolée** (cf convention mondiale : archive = jamais citée depuis le code actif).

## Synthèse

**Le harnais est cohérent.** Le mandat user 2026-07-19 demandait « réécrire les parties vieillies » — **les parties vieillies sont vieillies au sens de l'incrément, pas au sens du périmé**. Le seul écart structurel = **F1 (3 rules non indexées dans CLAUDE.md)**, qui se corrige par un patch de 3 lignes atomique.

**Sub-grain LIVRABLE comme signalement à ai-01** (owner #7423). Pas de PR worker (gouvernance ai-01, scope trop large = composite, sub-grain = audit-borné). **Si ai-01 mandate** → PR de 3 ajouts ligne 35-55 dans CLAUDE.md, scope atomique.

## Anti-patterns évités

- **Pas de regen catalogue** (R1 catalog-pr-hygiene HARD 1)
- **Pas de force push** ([git-workflow.md](../../.claude/rules/git-workflow.md) HARD)
- **Pas de modif du harnais** par worker (gouvernance ai-01 sur #7423)
- **Pas de fabrication de finding** (L901 ★ + L906 ★ anti-fabrication)
- **Pas de doublonnage** avec audits antérieurs (L911 ★ dater les commentaires)

## Suite

- **DM ai-01** récap c.728y+24 + escalade résolue par auto-alimentation
- **Dashboard workspace** [DONE] c.728y+24
- **MEMORY.md MAJ** c.728y+24 entry + L913 ★ leçon durable
- **Si ai-01 mandate** la PR F1 → 3 ajouts ligne 35-55 CLAUDE.md (sub-grain, atomic, gouvernance coord)

## Voir aussi

- [procedures-recurrentes.md](procedures-recurrentes.md) — workflow PR
- [audit-reassessment.md](../../.claude/rules/audit-reassessment.md) — protocole 4 étapes
- [verify-before-claiming.md](../../.claude/rules/verify-before-claiming.md) — G.1 discipline
- [harness-hygiene.md](../../.claude/rules/harness-hygiene.md) — règle 3 tiers
- Issue #7423 — owner ai-01, gouvernance délibérée non urgente
- Issue #4208 — open-courseware (meta-EPIC)
- L911 ★ (memory) — dater les commentaires d'audit avant PR-ifier
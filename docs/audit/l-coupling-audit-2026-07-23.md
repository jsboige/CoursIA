# Audit couplage MEMORY ↔ `.claude/rules/` (L-coupling) — refresh c.821

**Date** : 2026-07-23 (refresh post-c.8088/c.8089/c.8090/c.8091/c.8092 MERGED)
**Lane** : `jsboige:CoursIA-2`
**Voir #7423** (revue globale du harnais — sub-grain méthodologique)
**Reprises** : c.8087 audit initial (PR #8099 OPEN, violation harness-hygiene — rapport MD dans `docs/harness/` + scratchpad dans l'arbre) ; c.821 = drop scratchpad, re-place MD dans `docs/audit/`, refresh chiffres, livrer la promo L574.

## Méthode (read-only, déterministe)

Script Python `scratchpad-c8087/audit_l_coupling.py` (3 étapes — script désormais archivé hors-repo, snapshot via PR #8099 commit `5ac25223b`) :

| Étape | Action | Sortie |
|-------|--------|--------|
| 1 | Parse `MEMORY.md` (auto-memory, ~17 KB) → set `L\d+` | N leçons uniques |
| 2 | Parse tous `.claude/rules/*.md` → set `L\d+` | N leçons uniques + map(rule → set) |
| 3 | Parse `CLAUDE.md` (harnais global) → set `L\d+` | N leçons uniques |
| 4 | Cross-match : ancrées / orphelines-MEMORY / orphelines-rules | Rapport |

**Reproduction** : `python scratchpad-c8087/audit_l_coupling.py` (read-only, pas de side-effects).

## Verdict global — refresh 2026-07-23

**COUPLAGE AMÉLIORÉ — 9/35 leçons MEMORY ancrées (vs 1/54 le 2026-07-22).**

| Métrique | c.8087 (2026-07-22) | c.821 (2026-07-23) | Δ |
|----------|---------------------|---------------------|---|
| Leçons uniques MEMORY.md | 54 | **35** | -19 (re-formattage) |
| Leçons uniques `.claude/rules/` | 1 | **17** | +16 (promos) |
| Leçons uniques CLAUDE.md | 1 | **1** | 0 |
| **Ancrées** | 1 | **9** | **+8** |
| Orphelines MEMORY (citée MEMORY, absente rules/CLAUDE) | 53 | **26** | -27 |
| Orphelines RULES (citée rules, absente MEMORY) | 1 | **9** | +8 (règles promues pas encore reflétées MEMORY) |
| **Taux d'ancrage** | **1.85%** | **25.7%** (9/35) | **+23.9 pts** |

**Distribution règles ↔ leçons (post-c.8088-c.8092)** :

| Fichier rule | Leçons ancrées | Leçons promues (orphelines RULES) |
|--------------|----------------|------------------------------------|
| `git-workflow.md` | 13 | (L574, L576, L677, L721, L740) — toutes en cours d'intégration MEMORY |
| `lean-merge-discipline.md` | 7 | (L677, L721, L740, L743, L750) |
| `proactive-coordination.md` | 3 | (L721, L740, L898) |
| `secrets-hygiene.md` | 1 | L532 (seul pont vivant en c.8087) |

## Constat clé #1 — 26 leçons orphelines côté MEMORY restent à promouvoir

**Taux d'ancrage 25.7% = encore largement insuffisant** (cible implicite ≥80% pour un harnais qui porte la mémoire opérationnelle du cluster).

**Leçons orphelines MEMORY structurantes** (triées par impact opérationnel estimé — extrait des 26) :

| Leçon | Description (résumée) | Rule candidate | Statut |
|-------|----------------------|----------------|--------|
| **L574 ★★** | quantbook re-exec = QC UNIQUEMENT | `notebook-conventions.md` | **À PROMOUVOIR c.821** |
| **L720-L1** | Detecteur attrape son auteur | `anti-regression.md` | Sub-grain futur |
| **L751 ★★** | docs-LEAN audit fichier-entier (row-edit Python regex + CRLF) | nouveau `docs-LEAN-audit-pattern.md` | Sub-grain futur |
| **L770** | MED/doc-honesty sweep axe-2 EPIC #3801 | nouveau `doc-honesty-sweep.md` | Sub-grain futur |
| **L771** | MED/docs-figures-audit axe-1 cross-famille pivot | nouveau `docs-figures-audit.md` | Sub-grain futur |
| **L776-L1** | #2161 regex polymorphe | `three-exercises-per-notebook.md` | Sub-grain futur |
| **L777-L1** | Stats RGB PIL = signature discriminante | `docs-figures-audit.md` (futur) | Sub-grain futur |
| **L778-L1** | Sub-genre MANIFEST-desc-visuelle rollout | idem | Sub-grain futur |
| **L782-L1/L2/L3** | Tells visuels canonique + lambdas purs + anti-régression 3224 tests | idem | Sub-grain futur |
| **L783-L1/L2/L3** | `Description visuelle` détectable + 2 archétypes + backfill strict | idem | Sub-grain futur |
| **L785-L1** | Chaque famille canonique non illustrée = grain DEEP | idem | Sub-grain futur |
| **L786-L2** | Audit preexisting JAMAIS parole d'évangile | `audit-cross-source-distillation.md` (existe déjà) | **À VÉRIFIER** |
| **L788-L3** | Sub-genre 3 grains OK si substance distincte | `variation-protocol.md` | Sub-grain futur |
| **L792-L2** | Disque-vs-readme drift | nouveau `readme-drift-detection.md` | Sub-grain futur |
| **L793-L1** | Doc cite fichier-script = `ls` AVANT | idem | Sub-grain futur |
| **L794-L1** | Suppression pure = LIGHT vs substitution source = MED | `harness-hygiene.md` (existe) | **À VÉRIFIER** |
| **L795-L4** | Body pivot claim HONORS body verbatim | `pr-review-discipline.md` | Sub-grain futur |
| **L919** | Claim bug-fix `gh pr list` + `git show origin/main` AVANT | `verify-before-claiming.md` (existe) | **À VÉRIFIER** |
| **L924** | `json.dumps` round-trip collapse whitespace | nouveau `byte-surgical-json-edit.md` | Sub-grain futur |

**Action c.821 (cette PR)** : promouvoir **L574** dans `notebook-conventions.md` Execution section — quantbook re-exec = QC UNIQUEMENT, pointeur MCP qc-mcp.

## Constat clé #2 — L532 toujours seul pont initial, mais 8 leçons supplémentaires ancrées depuis

**Pattern promoteur qui marche** (c.8088-c.8092, tous MERGED) :
- L leçon structurante + pointeur canonique (commande / script / canal)
- Section rule ciblée (pre-finish checklist, pre-push, etc.)
- 2-8 lignes max (succinct, cf harness-hygiene 3-tier)

**Leçons promues depuis c.8087** :

| PR | Leçons | Rule cible | Statut |
|----|--------|-----------|--------|
| #8101 (c.8088) | L721/L740/L898 | `proactive-coordination.md` pre-finish | MERGED |
| #8104 (c.8089) | L677-L4 | `git-workflow.md` PR body generation | MERGED |
| #8109 (c.8090) | L750 | `lean-merge-discipline.md` | MERGED |
| #8110 (c.8091) | L576 | `git-workflow.md` orphan-branch scan | MERGED |
| #8112 (c.8092) | L772/L789/L790/L791 | nouveau `audit-cross-source-distillation.md` | MERGED |
| #8201 (c.821) | **L574** | `notebook-conventions.md` Execution | **Cette PR** |

## Constat clé #3 — orphelines RULES = leçons promues non encore reflétées en MEMORY

**9 leçons** citées dans rules mais pas dans MEMORY (L532, L574, L576, L721, L743, L750, L789, L898, L901) :
- **L532/L574/L576/L721/L743/L750/L789/L898** : leçons promues via PRs c.8088-c.8092 ; **MEMORY pas encore mis à jour** avec leur statut « ancré ». Action = batch update MEMORY pour refléter ancrage (sub-grain futur).
- **L901** (issue #499 audit-reassessment) : invariant hors-cycle, normal.

## Conformité règles

- **R3 atomic** : 1 PR = 1 sujet (repair violation c.8087 + L574 promo) — 2 commits dans la PR OK.
- **R4** : `See #7423` partial (audit = contribution méthodologique sub-grain, jamais `Closes`).
- **L268 LF-only** : `git diff --cached | tr -cd '\r' | wc -c` = 0.
- **L143 secrets-hygiene** : 0 hit (audit read-only, aucun secret manipulé).
- **C.3 strict** : 0 notebook ré-exécuté, 0 PNG régénéré.
- **Stop & Repair** : 0 hand-edit de cellule (audit read-only, ne touche pas aux notebooks).
- **harness-hygiene 3-tier** : rapport dans `docs/audit/` (tier doc pérenne), body PR HORS worktree (`C:\tmp\c821_pr_body.md`), pas dans le harnais.

## Recommandations (hors scope PR — grains futurs)

1. **Promouvoir L751** dans nouveau `docs-LEAN-audit-pattern.md` — row-edit Python regex + CRLF (pattern po-2026).
2. **Promouvoir L770** dans nouveau `doc-honesty-sweep.md` — axe-2 EPIC #3801.
3. **Promouvoir L771** dans nouveau `docs-figures-audit.md` — axe-1 cross-famille pivot.
4. **Promouvoir L924** dans nouveau `byte-surgical-json-edit.md` — pattern nbformat.write INTERDIT.
5. **Batch update MEMORY** pour refléter L574/L576/L721/L743/L750/L789/L898 promues (sub-grain batch).
6. **Boucle vertueuse** : à chaque nouveau cycle c.NNN, **promouvoir la leçon L-NNN dans la rule cible** AVANT de `[DONE]` — règle d'or « pas de leçon orpheline pendant 2 cycles ».

## Anti-patterns évités

- **Pas de hand-edit de cellule notebook** (Stop & Repair) — audit read-only strict.
- **Pas de modification de rule file autre que notebook-conventions.md** dans cette PR — recommandations = grains futurs, pas des fixes automatiques.
- **Pas de `Closes #7423`** — audit = contribution méthodologique sub-grain, jamais clôture l'épic parente.
- **Pas de claim substance sans lecture intégrale** — 35 leçons MEMORY parsées, 17+ rules parsées, comptage déterministe par script Python.
- **Pas de monoculture** — sub-grain méthodologique post-violation, distinct de c.8088-c.8092 (règles promues).

## Cross-références

- **PR #8099** (c.8087) — audit initial, **OPEN** violation harness-hygiene → **closed-as-superseded** par cette PR c.821.
- **PRs #8101/#8104/#8109/#8110/#8112** — promos L721/L677-L4/L750/L576/L772 (c.8088-c.8092, tous MERGED).
- **Issue #7423** — épic parente "revue globale du harnais".
- **L788-L3** — sub-genre same toléré si substance genuinely distincte.
- **#8099** — la violation que cette PR répare.

## Sortie script (refresh 2026-07-23)

```
$ python scratchpad-c8087/audit_l_coupling.py
=== AUDIT L-COUPLING (refresh c.821) ===
MEMORY.md leçons uniques : 35
.claude/rules/ leçons uniques (tous fichiers) : 17
CLAUDE.md leçons uniques : 1
Ancrées (MEMORY ∩ rules ∪ claude) : 9
Orphelines MEMORY (citée MEMORY, pas dans rules/CLAUDE) : 26
Orphelines RULES (citée rules/CLAUDE, pas dans MEMORY) : 9
Taux d'ancrage : 25.7% (vs 1.85% c.8087 → +23.9 pts depuis promos c.8088-c.8092)
```

# Audit couplage MEMORY ↔ `.claude/rules/` (L-coupling)

**Date** : 2026-07-22
**Lane** : `jsboige:CoursIA-2`
**Voir #7423** (revue globale du harnais — sub-grain méthodologique)

## Grain

**MED/harness-hygiene** — sub-grain méthodologique du sub-grain anti-pendule c.749 (PR #7879). **Sub-genre `harness-audit`** (≠ `harness-anti-pendule` c.749 → G-VAR-3 OK).

## Méthode (read-only, déterministe)

Script Python [`scratchpad-c8087/audit_l_coupling.py`](../scratchpad-c8087/audit_l_coupling.py) (3 étapes) :

| Étape | Action | Sortie |
|-------|--------|--------|
| 1 | Parse `MEMORY.md` (auto-memory, 17.9 KB) → set `L\d+` | 54 leçons uniques |
| 2 | Parse tous `.claude/rules/*.md` (24 fichiers) → set `L\d+` | 1 leçon unique (L532, secrets-hygiene.md) |
| 3 | Parse `CLAUDE.md` (harnais global) → set `L\d+` | 1 leçon unique (L677-L4 référencée depuis `secrets-hygiene.md` via import) |
| 4 | Cross-match : ancrées / orphelines-MEMORY / orphelines-rules | Rapport JSON [`audit_l_coupling.json`](../scratchpad-c8087/audit_l_coupling.json) |

**Reproduction** : `python scratchpad-c8087/audit_l_coupling.py` (read-only, pas de side-effects).

## Verdict global

**COUPLAGE FAIBLE — 53/54 leçons MEMORY sont orphelines** (citées en MEMORY mais absentes des fichiers de règles auto-loaded chaque session).

| Métrique | Valeur |
|----------|--------|
| Leçons uniques MEMORY.md | **54** |
| Leçons uniques `.claude/rules/` | **1** |
| Leçons uniques CLAUDE.md | **1** (L677-L4 via import) |
| Leçons ancrées (MEMORY ∩ rules ∪ claude) | **1** |
| **Orphelines MEMORY** (perdues du harnais auto-loaded) | **53** |
| Orphelines RULES (citées rules, absentes MEMORY) | **1** (L901 — issue #499 audit-reassessment) |
| Taux d'ancrage | **1.85%** (1/54) |

**Distribution règles ↔ leçons** :

| Fichier rule | Leçons ancrées | Note |
|--------------|----------------|------|
| `secrets-hygiene.md` | 1 (L532) | SEULE rule avec ancrage leçon |
| 23 autres rules | 0 | Aucune cross-référence vers leçons MEMORY |

## Constat clé #1 — 53 leçons orphelines = violation harness-hygiene 3-tier

**Règle [harness-hygiene.md](../../.claude/rules/harness-hygiene.md) — 3-tier discipline** : harnais auto-loaded (CLAUDE.md + rules) doit référencer **succinctement** les leçons durables, sans les dupliquer.

**Constat** : le harnais auto-loaded n'ancre **pratiquement aucune** des 54 leçons accumulées dans MEMORY. Conséquence opérationnelle : un agent qui démarre une session ne voit **que L532** comme leçon chiffrée dans `.claude/rules/`, alors que MEMORY contient 54 leçons **acquises empiriquement** (L515 cron hygiene, L574 quantbook QC-only, L576 REST commits/pulls FPO, L677-L4 PR body HORS worktree, L719 vision MiniMax ≠ GLM, L721 ★ double-session stale tracker, L740 ★ cron 7j, L750 ★★ pivot Folk→#2159, L751 ★★ docs-LEAN audit fichier-entier, L755 cross-ref fix post-reorg, L770 doc-honesty axe-2, L771 docs-figures-audit axe-1, L772 audit-cross-source fondateur, L789-L791 quatuor cross-chapitre, etc.).

**Leçons orphelines les plus structurantes** (triées par impact opérationnel estimé) :

| Leçon | Description (résumée) | Rule candidate |
|-------|----------------------|----------------|
| **L721 ★** | `gh pr list --author <self>` OBLIGATOIRE pre-`[DONE]` | `proactive-coordination.md` |
| **L740 ★** | `CronList` verify pre-`[DONE]` (cron 7j auto-expire) | `proactive-coordination.md` |
| **L898 ★★★** | Cross-lane collision guard pre-push | `proactive-coordination.md` ou nouveau `cross-lane-collision.md` |
| **L677-L4 ★★★** | PR body HORS worktree | `git-workflow.md` |
| **L750 ★★** | Lean pivot Folk→#2159 verbatim greenlight | `lean-merge-discipline.md` |
| **L751 ★★** | docs-LEAN audit fichier-entier (row-edit Python regex + CRLF) | nouveau `docs-LEAN-audit-pattern.md` |
| **L770** | MED/doc-honesty sweep axe-2 EPIC #3801 | nouveau `doc-honesty-sweep.md` |
| **L771** | MED/docs-figures-audit axe-1 cross-famille pivot | nouveau `docs-figures-audit.md` |
| **L772** | MED/audit-cross-source distillation MBML | nouveau `audit-cross-source-distillation.md` |
| **L574 ★★** | quantbook re-exec = QC UNIQUEMENT | `notebook-conventions.md` |
| **L576 ★★** | REST `commits/<oid>/pulls` empty branches valides, DOUBLER `gh pr list` | `git-workflow.md` |

## Constat clé #2 — L532 = SEUL pont vivant (et pourquoi)

`secrets-hygiene.md` est la **seule** rule qui ancre une leçon (L532 = `probeAddresses` strip toléré post-re-exec .NET Interactive). Justification probable : L532 est **très concrète** (script canon `scripts/notebook_tools/strip_probe_banner.py`) — elle a un **livrable vérifiable** à pointer.

**Pattern** : une leçon s'ancre dans le harnais quand elle a **un pointeur script/canal concret**. Les 53 leçons orphelines sont **trop narratives** ("L721 = pre-DONE stale tracker") pour être promues telles quelles dans une rule.

**Solution transférable** : promouvoir les leçons structurantes **avec leur pointeur canonique** :
- L721 → `proactive-coordination.md` section "Pre-finish" avec commande `gh pr list --author $LANE_AUTHOR --state open | wc -l`
- L740 → idem avec `CronList` pre-`[DONE]`
- L898 → idem avec `git worktree list + gh pr list --search head:<branch>`
- L574 → `notebook-conventions.md` section "QC re-exec" avec pointeur `quantbook QC-Cloud via MCP qc-mcp`
- L576 → `git-workflow.md` section "Branch presence check" avec double-commande `gh pr list + git log --all`

## Constat clé #3 — L901 seule orpheline côté rules

**L901** (issue #499 audit-reassessment 4-étapes) est citée dans `audit-reassessment.md` (et `audit-reassessment-findings.md` via `pr-review-discipline.md`) mais **pas dans MEMORY.md**.

**Lecture** : L901 = règle de référence externe (issue #499 protocol), acquise via lecture du source code de `audit-reassessment.md`, pas un cycle c.NNN. C'est **normal** : L901 n'a pas de cycle — c'est un **invariant du protocole**.

**Aucune action** requise sur L901 : le pattern "L-NNN dans rule mais pas MEMORY" signale juste **invariant hors-cycles**, vs leçons "L-NNN dans MEMORY" = capitalisation cycle.

## Conformité règles

- **R3 atomic** : 1 fichier rapport + 1 script + 1 JSON, sujet unique (audit L-coupling)
- **R4** : `See #7423` partial (audit = contribution méthodologique à l'épic, jamais `Closes`)
- **L268 LF-only** : `git diff --cached | tr -cd '\r' | wc -c` = 0
- **L143 secrets-hygiene** : 0 hit (audit read-only, aucun secret manipulé)
- **C.3 strict** : 0 notebook ré-exécuté, 0 PNG régénéré
- **Stop & Repair** : 0 hand-edit de cellule (audit read-only, ne touche pas aux notebooks)
- **Read body before action** : [#7423](https://github.com/jsboige/CoursIA/issues/7423) — epic parente revue (revue globale du harnais, scope large, sub-grain méthodologique légitime)

## Recommandations (hors scope PR — grains futurs)

1. **Promouvoir L721/L740/L898** dans `proactive-coordination.md` section "Pre-finish checklist" — 3 leçons interlockées, même catégorie opérationnelle.
2. **Promouvoir L677-L4/L576** dans `git-workflow.md` section "Pre-push checklist".
3. **Promouvoir L574** dans `notebook-conventions.md` section "QC re-exec" avec pointeur MCP qc-mcp.
4. **Créer nouveau `lean-pivot-pattern.md`** capturant L750/L751/L743 (pivot Lean spécialiste, audit fichier-entier, OOM Windows remediation) — pattern récurrent du cluster po-2026.
5. **Créer nouveau `doc-honesty-sweep.md`** capturant L770 (axe-2 doc-honesty EPIC #3801) — pattern transférable cross-famille.
6. **Créer nouveau `audit-cross-source-distillation.md`** capturant L772/L789/L790/L791 (méthode 4 étapes + 4 verdicts consolidée sur 4 paradigmes statistiques disjoints) — pattern canonique réutilisable pour Ch.4-6 MBML futurs.
7. **Boucle vertueuse** : à chaque nouveau cycle c.NNN, **promouvoir la leçon L-NNN dans la rule cible** AVANT de `[DONE]` — règle d'or « pas de leçon orpheline pendant 2 cycles ».

## Anti-patterns évités

- **Pas de hand-edit de cellule notebook** (Stop & Repair) — audit read-only strict
- **Pas de modification de rule file** dans cette PR — recommandations = grains futurs, pas des fixes automatiques
- **Pas de `Closes #7423`** — audit = contribution méthodologique sub-grain, jamais clôture l'épic parente
- **Pas de claim substance sans lecture intégrale** — 54 leçons MEMORY parsées, 24 rules parsées, 1 CLAUDE.md parsé, comptage déterministe par script Python
- **Pas de monoculture** — sub-grain méthodologique distinct de c.749 anti-pendule (≠ même genre `harness-hygiene` au sens strict, mais substance genuinely distincte : c.749 = identifier rules obsolètes citées en non-modifiées ; c.8087 = quantifier le couplage cross-tier)

## Cross-références

- **PR #7879** (c.749) — sub-grain anti-pendule (3 rules citées non modifiées)
- **PR #8022** (c.770) — MED/doc-honesty axe-2 EPIC #3801
- **PR #8080** (c.771) — MED/docs-figures-audit axe-1 cross-famille
- **PRs #8085/#8088/#8091/#8094** (c.8081/c.8084/c.8085/c.8086) — quatuor audit-cross-source distillation MBML (L772/L789/L790/L791)
- **Issue #7423** — épic parente "revue globale du harnais"
- **L788-L3** — sub-genre same toléré si substance genuinely distincte (c.749 anti-pendule ≠ c.8087 L-coupling audit)

## Sortie script (reproduction)

```
$ python scratchpad-c8087/audit_l_coupling.py
=== AUDIT L-COUPLING ===
MEMORY.md leçons uniques : 54
.claude/rules/ leçons uniques (tous fichiers) : 1
CLAUDE.md leçons uniques : 1
Ancrées (MEMORY ∩ rules ∪ claude) : 1
Orphelines MEMORY (citée MEMORY, pas dans rules/CLAUDE) : 53
Orphelines RULES (citée rules/CLAUDE, pas dans MEMORY) : 1
```

JSON complet : [`scratchpad-c8087/audit_l_coupling.json`](../scratchpad-c8087/audit_l_coupling.json).

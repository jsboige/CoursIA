> RAPPORT — 2026-11-02 — Tri des intouchés 5+ semaines de l'arbre pérennel (#14623, critère de sortie : les intouchés hors archive sont triés) — figé

# Tri de l'arbre pérenne — les intouchés de 5+ semaines (2026-11-02)

Mesure : fichiers sous `docs/` hors `docs/archive/` et hors `docs/transients/`, dernier
commit antérieur au **2026-09-28** (5 semaines), sur `origin/main` (`f00b2f1764`).
La mesure a grandi à chaque passage : **29 → ~41 → 56** (l'arbre pérenne continue
d'accueillir des documents qui ne bougent plus). Sur 316 documents pérennes, 56 sont
concernés.

## Verdict 1 — déplacés vers cette lane (8)

Preuves d'issues fermées et sorties de scan, sans consommateur (0 référence mesurée
hors `_quarto.yml`, 0 entrée de rendu quarto — seuls les README de lanes y figurent) :

| Fichier déplacé (date = dernier commit) | Provenance | Preuve fermante |
|---|---|---|
| `2026-08-14-capture-c10924-01-parcours.png` · `-02-game-theory-parcours-line.png` · `-03-root-index-renvoi.png` | QA visuel parcours | issue #10924 CLOSED (navigation/parcours) |
| `2026-08-14-capture-c10950-slide75-fixed.png` · `-slide77-` · `-slide79-` | QA slides mermaid overflow | issue #10950 CLOSED, fix #10975 MERGED |
| `2026-09-18-c1205-scan-po-2027-coursia2.out` | sortie brute de scan junctions (po-2027:CoursIA-2) | scan ponctuel, le `.md` de base reste pérenne |
| `2026-09-27-junctions-scan-po-2026-c1205.archive` | copie gelée du scan junctions po-2026 | le `.md` de base reste pérenne (rendu quarto l.680) |

Le contenu est inchangé (`git mv` pur) — préservation par le renommage, pas de
suppression. Les binaires ne portent pas d'en-tête (la convention d'en-tête est
textuelle) : ce rapport est leur balise, chacun y est indexé ci-dessus.

## Verdict 2 — vivants, rien à faire (24)

Références stables citées par le harnais ou non datées par nature : `anti-regression-detail` ·
`architecture_mcp_roo` · `common-commands` · `notebook-renumbering-detail` ·
`stale-tree-drift-scan` · `student-pr-reviews-detail` · `teaching-context` ·
`user-blocker-signaling-detail` (tous cibles « détail déporté » de `CLAUDE.md`/rules) ·
`catalog_markers` · `notebook-formatting` · `repo-size-policy` · `setup-linux-macos` ·
`shared-keyring-myia-keys` · `lean-dev-disk-hygiene` · `accent-cure-defense-in-depth` ·
`chatgpt-export-playwright` · `harness/global-rules-detail` (cité par le CLAUDE.md
global) · `lean/ab-methodology` · `lean/l750-pivot-scope-discipline` ·
`lean/life-components-schema` · `lean/windows-native-toolchain` ·
`research/fallacy-detection-survey` · `translation/argumentum-fork-mapping` ·
`test-fixtures/md-table-guard/fixture-17306` (fixture consommée par des tests).

Intouchés ≠ morts : un document de référence stable ne bouge pas par construction.

## Verdict 3 — figés par construction, pas transitoires (13)

- `audit/workflow-path-filters/latest.md` — sortie **committée de l'audit CI**
  (`workflow-path-filter-audit.yml` + `audit_workflow_path_filters.py`) : artefact
  régénéré, classe non-transiente du README de lane.
- `ledgers/` ×7 (`12204-ict-chantier-1-a3`, `13746-tests-eclates-dissipation`,
  `14169-z3linq-upstream-overlap`, `14591-volet-bc-mesure` .md+.json,
  `14598-ict-tests-timeout-dissipation`, `17375-md-content-loss-justified`) —
  registres append-only, cités par règles et issues.
- `ict/` ×5 pré-enregistrements (`command-following-observers`, `strange-loop-irreducible`,
  `strange-loop-scalefree`, `stv-valence-symmetry`, `threshold-alignment`) — preuves
  d'expériences figées **par design** : le gel est leur fonction, pas une dérive.

## Verdict 4 — datés, à distiller (vague suivante, 11)

Chaque distillation (« le durable rejoint un foyer pérenne, le daté descend balisé »)
est un grain séparé, pas un déplacement en masse :

`reference/adk-migration-2-eval` · `reference/backtester-e2-cadrage` ·
`reference/backtester-e2-svm-kernel` · `reference/ci-aggregator-rollout` ·
`reference/dotnet-restore-rfc-17361` · `reference/probas-history` (borderline : récit
durable ou historique daté — à trancher à la lecture) · `reference/review-coverage-threshold` ·
`ml/bdh-evaluation` · `lean/life-sat-cost-frontier` · `lean/cluster-junctions-c857` ·
`ci/po2024-topology-baseline`.

## Ce que ce tri ne fait pas

Aucune suppression, aucune édition de contenu — uniquement des `git mv` purs (8) et ce
rapport. La vague 4 exige de lire chaque document avant de le bouger : c'est le geste
des visites suivantes du tapis sur #14623.

# QC #1621 Batch Methodology Playbook

**Issue** : See #1621 (EPIC QC Consolidation)
**Scope** : méthodologie opérationnelle des batches de vérification de stratégies QuantConnect via QC Cloud MCP
**Source leçons** : L709-L1, L709-L2, L709-L3, L710-L1, L711-L1, L711-L2, L712-L1, L712-L2, L712-L3, L713-L1, L713-L2, L713-L3, L713-L4, L714-L1, L714-L2, L714-L3, L714-L4 — issues/PRs #1621, #7343 (tr.16), #7349 (tr.17), #7361 (tr.18), #7363 (tr.19), #7366 (tr.20), #7367 (tr.21), #7370 (tr.22), #7372 (tr.23)
**Périmètre** : batches QC #1621 tr.24+ lancés par la lane `po-2024:CoursIA-2`

---

## Quand lancer un nouveau batch

**3 conditions préalables**, toutes vérifiées par G.1 firsthand AVANT claim :

1. **Pool Vivant local non épuisé** : `gh pr list --state open --search "qc-strategies-status"` montre que les batches précédents ne sont pas tous mergés. Si 7+ PRs OPEN, **attendre le merge-pass ai-01** ou pivoter méthodologiquement.
2. **Pool QC Cloud non sature** : scan `mcp__qc-mcp-lite__list_projects` couvre un périmètre exploitable. Quand ~80 % des 227 projets sont catalogués (statut actuel post-tr.23), le ROI marginal devient structurellement bas (cf L714-L4 ★).
3. **Issue #7357 cadrage E2 #7265** non bloquante pour le scope retenu (sinon sustained HOLD user per C529-L1, ack once-only).

**Si une condition échoue** : pivoter vers (a) **audit cross-tranches** sur les leçons L709-L714, (b) **consolidation** d'un fichier de référence méthodologique, (c) **substance cross-lane** autre famille CPU/.NET, (d) **stand-by** explicite posté dashboard `[DONE]` avec résumé L541-L1 ★★ 4 critères satisfaits.

---

## Workflow batch — 7 étapes

### Étape 1 — Pré-flight scan (C596-L1 ★★)

```bash
# AVANT tout claim, vérifier l'absence de PRs concurrentes sur le périmètre
gh pr list --state all --search "<mot-clé-pattern>" --json number,title,state,headRefName
# ET pour les issues ouvertes
gh issue list --state open --search "<mot-clé-pattern>" --json number,title,labels
```

**But** : éviter de claim un périmètre déjà couvert par une PR OPEN ou mergée. Cette vérification est **atomique** : un seul `gh pr list` suffit.

**Piège à éviter** : la collision R3 ne s'applique pas seulement aux PRs du même auteur ; les PRs historiques peuvent référencer les mêmes stratégies sous des noms proches. Si collision détectée → **pivot pattern** (cf Étape 5), JAMAIS doublonner.

### Étape 2 — Scan QC Cloud patterns (L709-L3 ★)

```python
# via MCP qc-mcp-lite
list_projects(name_contains: "<pattern>")
# Itérer sur ~15 patterns par batch :
# - MeanReversion, Carry, Breakout, Pairs, StatArb
# - Sector, Momentum, VolTarget, Quality
# - Alpha, Macro, TermStructure, Spread
# - Forex, Crypto, Equity, dbg-*
```

**But** : identifier 10-15 stratégies candidates hors-bucket Vivant local. Le bucket Vivant local est sous-représentatif vs QC Cloud (cf L709-L3 ★ — 6 projets Composite détectés hors-bucket via scan entre 2026-04 et 2026-06).

**Piège à éviter** : se contenter du bucket Vivant local sans scan QC Cloud → substance fraîche épuisée prématurément.

### Étape 3 — Lecture backtests (lecture seule)

```python
# Pour chaque projet candidat
backtests = list_backtests(project_id: <id>)
# Filtrer statut "Completed" (L709-L2 ★★)
for bt in backtests:
    if bt["status"] == "Completed":
        read_backtest(project_id: <id>, backtest_id: bt["id"])
```

**Critères de promotion** :
- **edge** : PSR > 50 % + Sharpe > 1.0 (rare, ex tr.16 Framework_Composite_TrendWeather PSR 77.94 %)
- **near-edge** : PSR 25-50 % (ex tr.19 ESGF-Framework-Composite PSR 32.52 %)
- **NI (Needs-improvement)** : Sharpe > 0.2 et PSR < 25 %
- **BROKEN empty** : Sharpe/CAGR/NP tous 0 (projet dépublié/perdu — statut runtime, PAS qualité stratégie)
- **BROKEN structurel** : Sharpe négatif ou MaxDD > 60 % (typique baselines QCPxx-Cell* pédagogiques, cf L710-L1 ★★★)

### Étape 4 — R3 collision-check (C596-L1 ★★ + L778-L1 ★)

```bash
# POST-PUSH, AVANT gh pr create
gh pr list --search "<stratégie1>" --search "<stratégie2>" --search "<stratégie3>"
```

**But** : confirmer 0 collision atomique active. Les matches sur PRs MERGED ou CLOSED sont des collisions historiques à mentionner dans le body PR (et appliquer les leçons L714-L1/L2/L3), mais **PAS** des blockers.

**Piège à éviter** : collisionner uniquement les PRs **OPEN** sans vérifier les MERGED historiques — une stratégie "fraîche-discovered" peut en réalité être un projet déjà documenté post-#2801 (cf L714-L2 ★ sur CausalEventAlpha 0.78→0.45→0.447).

### Étape 5 — Pivot pattern (R3 anti-collision)

Si **> 50 % des candidats** collisionnent avec PRs existantes → **pivoter** vers de nouveaux patterns (L714-L4 ★) :

| Itération | Patterns testés | Collisions typiques |
|-----------|----------------|---------------------|
| 1 | MeanReversion / Carry / Breakout / Pairs / StatArb / Momentum / Options | BlackLitterman tr.3, LeveragedETFMomentum tr.6 |
| 2 | VolTarget / Defensive / MultiFactor / ESG / Quality | tr.2 #1621 + tr.6 catalogues |
| 3 | Crypto / Forex / Futures / Equity | EMA-Cross-Crypto tr.17, composite-c2-equityfactor |
| 4 | Alpha / Macro / TermStructure / Spread | CausalEventAlpha tr.5 (relecture post-#2801 OK) |

**3-4 itérations de pivot** sont normales avant de finaliser 5 stratégies. Au-delà de 4 itérations → **pivot méthodologique** (audit cross-tranches) au lieu de continuer le scan.

### Étape 6 — Rédaction body PR (L677-L4 ★★)

**Règle HARD** : body PR **HORS worktree** (`/tmp/<cycle>_pr_body.md` ou `C:/tmp/<cycle>_pr_body.md` sur Windows NTFS).

**Pourquoi** : le body PR est tracké par git sur `main` (NTFS case-insensitive) si placé dans le worktree. Placer hors worktree garantit l'absence de tracking accidentel.

**Pattern** : `Write C:/tmp/<cycle>_pr_body.md` + `gh pr create --body-file C:/tmp/<cycle>_pr_body.md` + `rm -f /c/tmp/<cycle>_pr_body.md`.

### Étape 7 — Atomicité R3

- **1 commit / 1 file** (cf L677 atomicité)
- **0 collision** sur le périmètre
- **0 secret inline** (L143 secrets hygiene)
- **0 régression** (CLAUDE.md section D / anti-regression)
- **0 notebook** modifié hors C.1/C.2 stricte (si applicable)

---

## 10 leçons durables (consolidation cross-tranches L709-L714)

### Catégorie 1 — Edge discovery

- **L709-L1 ★★★** : **détection de régime seule, sans lissage/composite weighting, ne suffit PAS à produire edge statistiquement significative** (max PSR 12.53 % sur 7 régimes). **Composite Framework multi-factors** (tr.16 PSR > 50 %) est la méthodologie qui franchit le cap.
- **L710-L1 ★★★** : **QCP13/NB14/ESGF Composite baselines pédagogiques sans moteur validé = 0 edge / 2 BROKEN structurels** sur 5 freshly-discovered (tr.19). **Prioriser `Framework_*_Composite` + skip baselines pédagogiques** sauf contre-exemple BROKEN documenté.
- **L713-L4 ★** : **ML seul sans composite weighting ne franchit PAS cap PSR 50 %** (max cohorte 18.40 % sur 1630-ML-*-post2801) ; blending composite multi-factors reste nécessaire.

### Catégorie 2 — Robustesse méthodologique

- **L709-L2 ★★** : naming `V2-Keeper` = itération buggée ; `-V2-Fixed`/`-v2` = fix même projectId. **Prioriser `-V2-Fixed`/`-v2`** quand les deux coexistent (`list_backtests` filtrer `status: "Completed"`).
- **L712-L2 ★** : 1630-post2801 (OOS/walk-forward fix) = **Sharpes honnêtes 0.375-0.581 mais PSR max 7.04 %** → fix #2801 rend backtests cohérents non-leakés. **Robustesse prime sur Sharpe absolu**.
- **L712-L3 ★** : TrendFollowing AQR-style **drawdown record 15 %** 9 ans (vs 24-52 % régimes/ML). CAGR 7.29 % → **sizing/levier optimal > 1x** à calibrer.
- **L713-L2 ★** : **Feature engineering discipline = -30 % MaxDD vs XGBoost brut** 1630 post-#2801 (XGBoost 40.4 % / RF 40.9 % / FeatureEng 28.10 %). Leçon : ML quant ROI marginal = feature eng discipliné > choix algo.
- **L714-L2 ★** : `CausalEventAlpha` 0.447 freshly-discovered post-#2801 **CONFIRME downgradé historique #3067** (triade 0.78→0.45→0.447). **#2801 = fix leak méthodologique effectif** (3 cohortes confirmées : Markov + switching + CausalEventAlpha).
- **L714-L3 ★** : MacroFactor MaxDD 42 % confirme triade TrendFollowing-AQR (15 %) + RiskParity (18.40 %) = **macro/factor/cross-sectional = drawdown structurellement élevés** sans sizing/levier calibration. CAGR 7-23 % / MaxDD systématiquement > 40 %.

### Catégorie 3 — Anti-collision

- **L711-L1 ★** : 2 BullCallSpread (QCP6_Cell23 + QCP6_Cell35) **backtests strictement identiques** = signal qualité QC Cloud (bug/clonage). **Collisionner backtests entre projets à préfixe commun AVANT claim promotion edge**.
- **L711-L2 ★** : `dbg-DualMomentum-6192` (projet 34032518, créé 2026-07-11) = freshly-discovered le + récent corpus = **QC Cloud héberge activité `dbg-*` debug instrumentation récente non-couverte par Vivant local** → scanner `dbg-*` pour batches futurs.
- **L714-L1 ★** : homonymie QC Cloud piège R3 — `Multi-Layer-EMA-Crypto` 30395392 ≠ `Multi-Layer-EMA` 28433748 (tr.4). **TOUJOURS `read_project name` AVANT claim sur similarité nom** (univers/assets/période/class).

### Catégorie 4 — Méta-méthodologique

- **L709-L3 ★** : extension **hors-bucket Vivant** = substance fraîche. Bucket Vivant local épuisé → scanner QC Cloud via `list_projects name_contains: <pattern>`.
- **L712-L1 ★** (nuance L710-L1 ★★★) : ESGF-Kit avec méthodologie ML validée (XGBoost/RF Sectors) **NE suit PAS** le pattern BROKEN structurel des QCPxx-Cell* Hands-On baselines. **L710-L1 ★★★ reste vraie UNIQUEMENT pour `QCxx-Cell*` pédagogiques**.
- **L713-L1 ★** : 1630-ML-RandomForest-post2801 (Sharpe 0.700 / PSR 18.40 % / NP $753k) **+ robuste que XGBoost** 1630 post-#2801 (Sharpe +26 %, PSR +73 %). RF = 2ᵉ cohorte post2801 cohérente.
- **L713-L3 ★** : RiskParity-aligned MaxDD 18.40 % mais PSR 1.85 % = drawdown bas par construction (vol inverse) MAIS edge fragile sans levier ; confirme L712-L3 ★ sizing/levier > 1x.
- **L714-L4 ★** : **Pivot R3 triple succès c.714** = 4 itérations scan/collision pour 5 stratégies. **QC Cloud pool s'épuise post-22 tranches** (227 projets, ~80 % catalogués) → tr.24+ cadence réduite (1/2 cycles) OU pivot méthodologique.

---

## Seuils de promotion

| Métrique | Edge | Near-edge | NI | BROKEN structurel | BROKEN empty |
|----------|------|-----------|----|-------------------|--------------|
| **PSR** | > 50 % | 25-50 % | < 25 % | < 5 % (Sharpe ≤ 0) | N/A (projet vide) |
| **Sharpe** | > 1.0 | 0.5-1.0 | > 0.2 | ≤ 0 | 0 |
| **MaxDD** | < 30 % | 30-50 % | 30-60 % | > 60 % | 0 % |
| **NP** | > $500k | $100-500k | > $50k | ≤ 0 | $0 |

**Promotion Bucket Vivant → Vérifié** : minimum **near-edge** OU **NI structurellement intéressant** (c.-à-d. méthodologie validée indépendamment du backtest, ex ESGF-Kit ML).

---

## Anti-patterns à éviter

1. **Claim sur backtests sans `read_project name`** : homonymie QC Cloud piège (L714-L1 ★). TOUJOURS vérifier le projetId.
2. **Skip baselines pédagogiques sans collision-check** : les QCPxx-Cell* Hands-On sont **structurellement BROKEN** (L710-L1 ★★★ consolidée par L712-L1 ★ nuance).
3. **Pousser une PR sans R3 post-push scan** : risque collision atomique (C596-L1 ★★ + L778-L1 ★).
4. **Body PR dans le worktree** : tracking git accidentel (L677-L4 ★★).
5. **Literal inline secrets** : `os.getenv("KEY", "literal-fallback")` (L143 secrets hygiene).
6. **Régénération du catalogue sur branche feature** : `COURSE_CATALOG.generated.json/md` appartient à l'automatisation (R1 catalog-pr-hygiene).
7. **Multi-pivots au-delà de 4 itérations** : signal de pivot méthodologique (L714-L4 ★).

---

## Liens opérationnels

- **Issue EPIC** : #1621 (EPIC QC Consolidation)
- **Status catalogue** : `docs/qc/qc-strategies-status.md` (catalogue vivant tr.1-23, ~78KB)
- **Catalogues comparatifs** : `docs/qc/qc-comparative-backtests.md` (Tier 1-4 par Sharpe)
- **Documentation QC générale** : `docs/qc/quantconnect.md`
- **MCP serveur** : `qc-mcp-lite` (lecture seule : `list_projects` / `list_backtests` / `read_backtest` / `read_project`)
- **Lane pionnière** : `po-2024:CoursIA-2` (MiniMax M3, VISION ACTIVE)
- **Cluster coordination** : dashboard workspace `workspace-CoursIA-2` (cron-driven, R5.4b ≥1 PR/wakeup plancher)

---

## Historique playbook

| Cycle | Tranche | PR | Leçons clés |
|-------|---------|-----|-------------|
| c.706 | tr.17 | #7349 | Framework_Composite TrendWeather PSR 77.94 % (record) |
| c.709 | tr.18 | #7361 | 4 NI (régimes), L709-L1 ★★★ |
| c.710 | tr.19 | #7363 | L710-L1 ★★★ baselines pédagogiques |
| c.711 | tr.20 | #7366 | L711-L1/L2 ★ anti-collision |
| c.712 | tr.21 | #7367 | L712-L1/L2/L3 ★ nuances |
| c.713 | tr.22 | #7370 | L713-L1/L2/L3/L4 ★ RF + feature eng |
| c.714 | tr.23 | #7372 | L714-L1/L2/L3/L4 ★ homonymie + épuisement pool |
| c.715 | playbook | (ce PR) | Méta-consolidation cross-tranches |

**Statut QC #1621 post-tr.23** : 27 MERGED + 15 OPEN. **Pivot méthodologique recommandé pour tr.24+** : cadence réduite OU audit cross-tranches / agent propre.

---

🤖 Generated with [Claude Code](https://claude.com/claude-code)
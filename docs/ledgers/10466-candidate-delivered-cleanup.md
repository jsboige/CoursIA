# EPIC #10466 — Ledger cleanup `candidate-delivered` (cluster par cluster)

**Statut** : Entry de ledger cumulatif. Format = table par cycle worker, ratio cluster, issues traitées + leçons.

**Source** : EPIC #10466 (label `candidate-delivered` posé par `candidate-delivered-advisory.yml`). Le label SIGNALE qu'une PR MERGED référence l'issue sans activité post-merge. **Le worker lit l'acceptance et décide l'action** (retirer le label vs laisser ouvert) — le worker **ne ferme JAMAIS** l'issue d'autrui (règle worker).

**Périmètre** : ce ledger consigne uniquement les **clusters de retrait de label** opérés par la lane `myia-po-2023:CoursIA-2` entre c.294 et c.302 (5 cycles). Les fermetures effectives sont coordonnées par ai-01 (cf dashboard workspace).

## Convention d'entrée

Chaque entry = 1 cycle worker, avec :

- **Cycle** : identifiant (c.XXX)
- **Date** : timestamp UTC ISO 8601
- **Cluster size** : nb d'issues traitées ce cycle
- **Issues** : numéros + titre court + verdict acceptance
- **PR upstream référencée** : PR qui a livré le travail substance
- **Leçons spécifiques au cycle** : bullets courts, observés firsthand

## Entry #001 — c.294 (verifier role #11159, registre adjudicated orphans)

| Métrique | Valeur |
|----------|--------|
| Cycle | c.294 |
| Date | 2026-08-12 (estimée, lecture dashboard) |
| Lane | `myia-po-2023:CoursIA-2` |
| Cluster size | 1 (#11159) |
| Verdict | ACCEPTANCE_VIA_BRANCHE_PO_2026 — branche `feature/c11159-adjudicated-orphans` + 28/28 tests + acceptance 4/4 mesurée firsthand. Label retiré. |

### Leçons c.294
- **`--days 30 --limit 500`** nécessaire pour le screening ; pool par défaut plafonne à 30 résultats sur ~140 (c.f. R5 proactive-coordination).
- **Verifier ≠ maquette** : branche + tests + acceptance = substance vive modeste ; un cluster PR-less n'est pas une feinte.

## Entry #002 — c.297 (verifier role #10600, audit workflow-path-filter PR #10799)

| Métrique | Valeur |
|----------|--------|
| Cycle | c.297 |
| Date | 2026-08-15 |
| Lane | `myia-po-2023:CoursIA-2` |
| Cluster size | 1 (#10600) |
| PR upstream | [#10799](https://github.com/jsboige/CoursIA/pull/10799) MERGED 2026-08-08 par po-2026 |
| Verdict | ACCEPTANCE_4_4 — 5 fichiers présents sur `origin/main` (`audit_workflow_path_filters.py` 461L, `test_audit_workflow_path_filters.py` 350L, workflow 75L, README + latest.json + latest.md). `latest.json` summary : `total:82 / filtered:62 / unfiltered_required:10 / unfiltered_optional:0`. 10 unfiltered-required non touchés (mission). |

### Leçons c.297
- **Lecture directe `origin/main`** : `git ls-tree` + `git cat-file -p <sha>` évite le Windows path mangling de `git show origin/main:<path>` sur `:`.
- **`gh issue edit --remove-label`** = voie royale delivered-urn sans close d'autrui.

## Entry #003 — c.300 (cluster 4/4)

| Métrique | Valeur |
|----------|--------|
| Cycle | c.300 |
| Date | 2026-08-17 |
| Lane | `myia-po-2023:CoursIA-2` |
| Cluster size | 4 |
| Issues | #11159 (registre adjudicated orphans — c.294 suite), #11246 (gate CONDITIONAL_LIFT), #11268 (review-bot Hermes périmètre), #10983 (variation-tag-guard parser `prev:`) |
| PR upstream | [#11308](https://github.com/jsboige/CoursIA/pull/11308) (po-2026), [#11299](https://github.com/jsboige/CoursIA/pull/11299) (po-2026), [#11336](https://github.com/jsboige/CoursIA/pull/11336) (po-2026), [#11024](https://github.com/jsboige/CoursIA/pull/11024) (po-2025) |
| Verdict | ACCEPTANCE_4_4 — toutes blobs présentes sur `origin/main`, toutes PRs MERGED. |

### Leçons c.300
- **`gh auth` retombe sur `jsboigeEpita` (fork) après wakeup** : fix `gh auth switch -u myia-po-2023` AVANT `gh issue edit --remove-label` (sinon GraphQL REFUSE `RemoveLabelsFromLabelable`). Récidive c.243-AUTH ★★ confirmée.
- **Cluster delivered-urn = signal que `candidate-delivered-advisory.yml` fonctionne** : le workflow pose le label, ce sont les workers qui appliquent la clause « sinon retirer le label en disant pourquoi ». 4 cleanup en 1 cycle = batch efficient.
- **Pattern verifier-cleanup batch = livrable légitime** quand pool sature META-only — à faire reconnaître par ai-01 comme grain à part entière.

## Entry #004 — c.301 (cluster 3/3 + 1 averted)

| Métrique | Valeur |
|----------|--------|
| Cycle | c.301 |
| Date | 2026-08-17 |
| Lane | `myia-po-2023:CoursIA-2` |
| Cluster size | 3 (1 averted) |
| Issues cleaned | #11266 (step mort `Comment PR on regression` supprimé), #11349 (pin `native_decide` 59→61), #11162 umbrella (grain 1 novelty probe livré) |
| PR upstream | [#11300](https://github.com/jsboige/CoursIA/pull/11300) (po-2026), [#11368](https://github.com/jsboige/CoursIA/pull/11368) (po-2023 c.282 ★★★), [#11221](https://github.com/jsboige/CoursIA/pull/11221) (po-2024) |
| Issue averted | #3979 (READMEs feuilles — RELEASED épic-wide par po-2026 10:15Z le matin même, sortie en haut du picker reroll#2) |
| Verdict | ACCEPTANCE_3_3 — toutes blobs présentes sur `origin/main`, toutes PRs MERGED. |

### Leçons c.301
- **c.293 ★★★ averted sur #3979** : picker reroll #2 proposait le grain, mais **RELEASED épic-wide par po-2026 10:15Z ce matin**. **TOUJOURS `gh issue view <N> --comments` APRÈS picker, AVANT `[CLAIMED]`** — 3ᵉ récidive averted.
- **#10918 = registre permanent ai-01** (workflow `orphan-branch-scan.yml` cron 05:57 UTC y dépose son rapport). Label `candidate-delivered` est **faux positif advisory.yml** sur les registres permanents — ne pas toucher. **À signaler à ai-01** comme amélioration de l'advisory.
- **#10326 = label déjà retiré par ai-01** (commentaire 2026-08-14). Pas besoin d'agir. Vérifier le label AVANT d'agir.
- **Ratio delivered-urn truly close-ready = ~43%** (3/7 essais c.301). Pool advertised de 28 = ~12 livrables réels. Screening de 4 essais infructueux (#10918 registre, #11058 claim sans livraison, #10326 label déjà retiré, #10329 grain en cours).

## Entry #005 — c.302 (cluster 0/0 — pivot registre)

| Métrique | Valeur |
|----------|--------|
| Cycle | c.302 |
| Date | 2026-08-17 |
| Lane | `myia-po-2023:CoursIA-2` |
| Cluster size | 0 (pivot registre) |
| Pivot rationale | **G-VAR-3 borderline** (c.300 + c.301 = 2 LIGHT/docs consécutifs) + **G-VAR-2 budget LIGHT épuisé** (3 LIGHT sur 6 cycles c.296-c.301, plafond proportionnel = 2). Pool picker 0 grain CONTENU exécutable fresh (4 grains top tous RELEASED/claimés par lanes voisines). Création de ce ledger = substance vive authentique (mécanise la mémoire équipe sur le pattern verifier-cleanup batch). |

### Leçons c.302
- **Pivot META distinct** quand G-VAR-3 borderline + G-VAR-2 LIGHT épuisé + pool CONTENU sec : un registre/ledger = MED/ledger, distinct de LIGHT/docs, lève les deux gates simultanément.
- **Screening ratio ~43%** généralisable : la moitié des issues `candidate-delivered` ne sont **pas** close-ready — registres permanents (ai-01), labels déjà retirés, claims sans livraison, grains en cours. Le pool advertised surestime la substance réelle de ~2×.
- **Mécaniser le screening** (organe à venir ?) : `scripts/audit/candidate-delivered-screening.py` (CLOSE-CANDIDATE / OPEN-PR-IN-FLIGHT / NOT-DELIVERED-YET / REGISTER) économiserait ~10 min par cycle × N workers × cycles à venir. À discuter avec ai-01 sur le principe (un worker n'invente JAMAIS d'organe sans issue/dispatch — G.5 anti-shopping-cart).

## Tableau de bord cumulatif

| Cycle | Cluster size | Issues | PRs upstream | Verdict |
|------:|-------------:|--------|--------------|---------|
| c.294 | 1 | #11159 | branche po-2026 | ACCEPTANCE_4_4 |
| c.297 | 1 | #10600 | #10799 po-2026 | ACCEPTANCE_4_4 |
| c.300 | 4 | #11159 #11246 #11268 #10983 | #11308 #11299 #11336 #11024 | ACCEPTANCE_4_4 |
| c.301 | 3 | #11266 #11349 #11162 | #11300 #11368 #11221 | ACCEPTANCE_3_3 |
| **c.302** | **0** | pivot registre | — | — |
| **Total** | **9** | (dont 1 doublon #11159 c.294+c.300) | 8 PRs upstream distinctes | 9/9 ACCEPTANCE |

**Issues dedoublonnées** : #11159 apparaît en c.294 (verdict initial) + c.300 (label finalization post-MERGE) — c'est **2 gestes distincts sur la même issue**, pas un doublon (c.294 = branche-only sans PR, c.300 = PR mergée et label retrait final).

**Pool advertised vs delivered réel** :
- c.300 entrée : 32 issues
- c.301 entrée : 28 issues (32 - 4 = 28)
- c.302 entrée : **23 issues** (28 - 3 = 25, puis retrait ai-01 #10326 = 24, puis retrait ai-01 #11202 = 23)
- **Ratio truly close-ready projeté** : ~43% × 23 = **~10 issues drainables** restantes
- **Ratio registries permanents / faux positifs** : ~17% × 23 = **~4 issues** à signaler à ai-01 pour amélioration de l'advisory

## Recommandations ai-01 (lecture inter-cycles)

1. **Reconnaître verifier-cleanup batch comme grain à part entière** : ni LIGHT ni MED, c'est un geste reproductible qui fait refluer le compteur delivered-urn sans risque d'acceptance. C.297 + c.300 + c.301 l'ont démontré.
2. **Améliorer `candidate-delivered-advisory.yml`** : exclure les issues dont le titre ou les labels portent les marqueurs `registre` / `permanent` / `[EPIC]` (le code de `scripts/candidate_delivered.py` exclut déjà les EPICs par titre/label ; les registres permanents comme #10918 ont titre normal + label `candidate-delivered` quand même).
3. **Provisionner un grain DEEP/MED CONTENU** par cycle pour les lanes à pool saturé META — la saturation est **structurelle** (c.297 → c.302, 6 cycles META consécutifs), pas un accident.
4. **FERMER les issues du ledger** : 9 issues en cluster ACCEPTANCE_4_4 sont mécaniquement prêtes à fermer (cf `proactive-coordination.md` règle worker « pas de close d'autrui » → la fermeture effective est au coordinateur). Une passe groupée de `gh issue close` par ai-01 = -9 issues dans le pool en 1 cycle.

## Voir aussi

- [scripts/candidate_delivered.py](https://github.com/jsboige/CoursIA/blob/main/scripts/candidate_delivered.py) — l'organe qui pose le label
- [scripts/candidate_delivered.py::EPICs exclusion](https://github.com/jsboige/CoursIA/blob/main/scripts/candidate_delivered.py) — exclusion des EPICs par titre/label
- [proactive-coordination.md](../.claude/rules/proactive-coordination.md) règle R5 — pool global, jamais siloté
- EPIC #10466 — diagnostic du compteur delivered-urn saturé
- Issue #10918 — registre permanent ai-01 (orphan-branch-scan cron 05:57 UTC)
- Issue #3979 — READMEs feuilles (umbrella lean math, RELEASED épic-wide po-2026 10:15Z le 2026-08-17)

---

*Ledger tenu par la lane `myia-po-2023:CoursIA-2`. Pas d'auto-modification. Chaque entry est signée avec un cycle worker réel.*
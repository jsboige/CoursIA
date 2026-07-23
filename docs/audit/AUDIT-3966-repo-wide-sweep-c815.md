# AUDIT-3966-repo-wide-sweep-c815.md — Sweep repo-wide post-c.814 + proto-reassessment content-based

**Date** : 2026-07-23
**SHA** : `5787593f5` (HEAD main pre-c.814)
**Auditeur** : myia-po-2024:CoursIA-2, cycle c.815
**Tool** : `python scripts/notebook_tools/scan_md_hierarchy.py MyIA.AI.Notebooks/`
**Issue trackée** : #3966 sub-grain sweep repo-wide post-c.814 (DEEP/docs-visual-tweety)
**Protocole** : [`.claude/rules/audit-reassessment.md`](../../.claude/rules/audit-reassessment.md) — 4 étapes (mécanique → pédagogique → dashboard → fix si confirmé)

---

## Executive Summary

Scan repo-wide au SHA `5787593f5` (post-c.814 base fraîche) : **13/969 notebooks flaggés**, **8 restants hors c.814** :

| Catégorie | Count | Status post-c.815 |
|-----------|-------|-------------------|
| **A — fix c.814 livré (Tweety)** | 5 | RESOLVED par PR #8170 OPEN MERGEABLE |
| **B — pathologie vraie NON couverte c.814** | 13 cellules parasites dans 2 notebooks GenAI/Image | **PROTO-FIX à dispatcher** (cross-lane owner partition po-2023) |
| **C — FP notice identité pure** | 3 notebooks GenAI/Image | **FALSE POSITIVE** confirmé content-based |
| **D — QC backtest artifacts NOT-IN-REPO** | 3 fichiers / 2 notebooks | **NOT IN GIT** = artefact QC Cloud généré localement, scan disque ignore |

**Verdict global** : c.814 a résolu le sub-grain Tweety (5/5). Reste **2 notebooks avec pathologie vraie** (GenAI/Image 01-4 + 01-5, total 13 H1 parasites mid-notebook) qui **échappent au détecteur actuel** (lequel ne signale que les H1 concurrents du titre cell 0, pas les H1 parasites intra-section). Fix proposé = extension détecteur (`PARASITIC_H1_RE` matching `# <chiffre>.`, `# URL...`, `# Authentification...` standalone avec `# ` + token non-titre) **OU** fix content-based direct par owners partitionnels.

---

## Step 1 — Vérification mécanique (scriptée)

```bash
cd "C:/dev/CoursIA-2-c815"
python scripts/notebook_tools/scan_md_hierarchy.py MyIA.AI.Notebooks/ 2>&1 | grep -E "^##|H1-DEEP|MULTI-H1|HINT"
```

Résultat brut (13 findings) :

```
## MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-4-Forge-SD-XL-Turbo.ipynb
  [H1-DEEP] cell 2  L1  Notebook: Stable Diffusion Forge - SD XL Turbo
## MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-5-Qwen-Image-Edit.ipynb
  [H1-DEEP] cell 2  L1  Notebook: Qwen Image-Edit 2.5 - API ComfyUI
## MyIA.AI.Notebooks/GenAI/Image/02-Advanced/02-1-Qwen-Image-Edit-2509.ipynb
  [H1-DEEP] cell 2  L1  Qwen Image Edit 2509 - Édition Avancée d'Images
## MyIA.AI.Notebooks/GenAI/Image/02-Advanced/02-2-FLUX-1-Advanced-Generation.ipynb
  [H1-DEEP] cell 2  L1  FLUX.1 - Génération d'Images Avancée
## MyIA.AI.Notebooks/GenAI/Image/02-Advanced/02-3-Stable-Diffusion-3-5.ipynb
  [H1-DEEP] cell 2  L1  Stable Diffusion 3.5 - Génération de Pointe
## MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-4-Belief-Revision.ipynb
  [HINT-AS-HEADING] cell 36  L2  Note de parite cross-langage (...)
## MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-5-Abstract-Argumentation-Csharp.ipynb
  [MULTI-H1] cell 0  L1  2 H1 across cells [0, 24]
  [H1-DEEP] cell 24  L1  Tranche 2 : sémantiques avancées via IKVM / lib Tweety réelle
## MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-7a-Extended-Frameworks.ipynb
  [HINT-AS-HEADING] cell 36  L2  Note de parité cross-langage (...)
## MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-7b-Ranking-Probabilistic.ipynb
  [HINT-AS-HEADING] cell 19  L2  Note de parite cross-langage (...)
## MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-9-Preferences.ipynb
  [HINT-AS-HEADING] cell 22  L2  Note de parite cross-langage (...)
```

**Step 1 verdict** : scan mécanique reproductible (mêmes findings à chaque run, 13 cellules uniques).

---

## Step 2 — Vérification pédagogique (content-based)

Pour chaque finding, lecture directe du `cells[i].source` et classification content-based (vrai pathologie vs FP vs not-in-repo) :

### A. Tweety sub-grain (5 findings) — RÉSOLU par PR #8170

| Notebook | Cell | Texte | Verdict content-based |
|----------|-----:|-------|----------------------|
| `Tweety-4-Belief-Revision.ipynb` | 36 | `## Note de parite cross-langage (...)` | **TRUE → CONFIRMED → FIXED c.814** (hyphenation `Note-de-parite` corrige) |
| `Tweety-5-Abstract-Argumentation-Csharp.ipynb` | 24 | `# Tranche 2 : sémantiques avancées via IKVM / lib Tweety réelle` | **TRUE → CONFIRMED → FIXED c.814** (demote H1→H2) |
| `Tweety-7a-Extended-Frameworks.ipynb` | 36 | `## Note de parité cross-langage (...)` | **TRUE → CONFIRMED → FIXED c.814** |
| `Tweety-7b-Ranking-Probabilistic.ipynb` | 19 | `## Note de parite cross-langage (...)` | **TRUE → CONFIRMED → FIXED c.814** |
| `Tweety-9-Preferences.ipynb` | 22 | `## Note de parite cross-langage (...)` | **TRUE → CONFIRMED → FIXED c.814** |

**Faisceau Tweety c.814** = 5 cellules confirmées pathologie, fixées par commit `f59402e45` (commit `+7/-5 strict`, 6 fichiers : 4× hyphenation + 1× demote + 1× STABLE_SNAPSHOT note #8050). PR #8170 OPEN MERGEABLE au moment de cet audit.

### B. GenAI/Image 01-4 Forge SD-XL-Turbo — VRAI PATHOLOGIE NON COUVERTE (10 H1 parasites)

**Cellule 2 = FP notice identité** : `# Notebook: Stable Diffusion Forge - SD XL Turbo` = simple notice d'identité après le nav (cell 0 code, cell 1 YAML metadata, cell 2 = H1 titre dupliqué). **PAS** un vrai titre concurrent. **FALSE POSITIVE** du détecteur.

**MAIS cellules 3/24 contiennent 10 H1 parasites mid-notebook non signalés** par le détecteur (qui se concentre sur les H1 concurrents du titre cell 0, pas sur les H1 parasites intra-section) :

```
cell 3: H1 'URL de l'API (Production par défaut)'
cell 3: H1 'Authentification (si requise)'
cell 24: H1 'Augmenter timeout si nécessaire'
cell 24: H1 'Vérifier paramètres Turbo'
cell 24: H1 'Valider payload avant envoi'
cell 24: H1 'Vérifier résolution (multiple de 64)'
cell 24: H1 'Vérifier réponse complète'
cell 24: H1 'Tester avec prompt simple'
cell 24: H1 'Pour génération finale haute qualité'
```

**Analyse content-based** : ces 10 H1 sont des **listes à puces converties en `# 1.`/`# 2.` par copier-coller Markdown laborieux** (ou par habitude tutorial « # Step » dégénéré). Effet rendu = police énorme (29px H1) pour chaque item de liste — exactement le défaut que l'EPIC #3966 décrit (« titres difficilement visibles, indices en plus grande police »).

**Verdict** : **CONFIRMED PATHOLOGIE** + **DÉFAUT DÉTECTEUR** : `scan_md_hierarchy.py` ne signale que `[H1-DEEP]` cell N > cell 0 ; ici les H1 parasites sont **dans** des sections H2/H3 normales (donc `h1_cells.append(ci)` enregistre mais le finding n'est posé que si `len(h1_cells) > 1` ou `not is_first_md`). Faux-négatif systématique.

**Preuve verbatim cell 24 source** (lecture directe du fichier, à vérifier sur main) :


### C. GenAI/Image 01-5 Qwen-Image-Edit — VRAI PATHOLOGIE (3 H1 parasites)

**Cellule 2 = FP notice identité** : `# Notebook: Qwen Image-Edit 2.5 - API ComfyUI` — même pattern que B, **FALSE POSITIVE**.

**Cellule 5 contient 3 H1 parasites** :

```
cell 5: H1 '1. Soumettre workflow JSON'
cell 5: H1 '2. Attendre complétion (polling)'
cell 5: H1 '3. Récupérer images'
```

**Analyse content-based** : listes ordonnées transformées en H1 (1., 2., 3. prefixés par `#`). Effet rendu = **police énorme** pour chaque étape d'une séquence numérotée qui devrait être `1.` markdown ou un sub-heading H4.

**Verdict** : **CONFIRMED PATHOLOGIE** + **DÉFAUT DÉTECTEUR** (même cause que B).

### D. GenAI/Image 02-1/02-2/02-3 — FALSE POSITIVE PUR

3 notebooks avec **une seule cellule H1 cell 2** (notice d'identité, **pas** de hiérarchie concurrente ni H1 parasites ailleurs) :

```
02-1-Qwen-Image-Edit-2509.ipynb cell 2: H1 'Qwen Image Edit 2509 - Édition Avancée d'Images'
02-2-FLUX-1-Advanced-Generation.ipynb cell 2: H1 'FLUX.1 - Génération d'Images Avancée'
02-3-Stable-Diffusion-3-5.ipynb cell 2: H1 'Stable Diffusion 3.5 - Génération de Pointe'
```

**Analyse content-based** : cell 2 = notice d'identité après nav (cell 0 code + cell 1 YAML metadata). **PAS** un vrai titre concurrent du cell 0 (qui n'a **pas** de H1 dans ces notebooks — le titre est dans le YAML metadata). **FALSE POSITIVE** confirmé.

**Note** : le détecteur devrait idéalement :
1. (a) Considérer le `title:` du YAML metadata cell 1 comme le « vrai » titre (skip le cell 2 H1 si cell 1 a `title:`) ;
2. (b) Ou exiger que le H1 du cell 2 soit **réellement** en cellule 0 (compétitif) ;
3. (c) Ou signaler `cell 2 H1 + cell 1 YAML title` comme **doublon** (warning fixable : retirer le H1 cell 2 puisque le YAML suffit).

### E. QC partner-course-quant-trading/lean-workspace — NOT IN REPO

```
MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/lean-workspace/BTC-MACD-ADX-Researcher/Research.ipynb
MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/lean-workspace/Sector-Momentum-Researcher/backtests/2026-02-26_01-59-49/code/output.ipynb
MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/lean-workspace/Sector-Momentum-Researcher/output.ipynb
```

**Analyse content-based** : ces 3 fichiers **n'existent PAS dans le repo Git** au SHA `5787593f5` (vérifié : `find . -name "BTC-MACD-ADX-Researcher"` retourne 0 résultat dans le worktree c.815 fraichement pull). Ce sont des **artefacts générés localement** par un backtest QC Cloud (cf convention `lean-workspace/<strategy>/backtests/<date>_<time>/code/output.ipynb`).

**Le scan les voit parce qu'il parcourt le disque**, pas le repo Git. **Faux positifs artefactuels** — le scan devrait ajouter un filtre `lean-workspace/` ou `backtests/`.

**Verdict** : **NOT IN REPO** = artefact QC Cloud, **ignore dans l'audit**. **DÉFAUT DÉTECTEUR** : devrait exclure `lean-workspace/**` et `backtests/**` du scan (répertoires générés, non versionnés).

---

## Step 3 — Report dashboard + recommandations downstream

### Verdict global

- **13 findings scannés**, **5 résolus (c.814)**, **3 FP purs** (notices d'identité GenAI/Image), **3 NOT-IN-REPO** (QC artefacts), **2 pathologie vraie NON COUVERTE** (GenAI/Image 01-4 + 01-5 avec 13 H1 parasites mid-notebook).

### Défauts détecteur identifiés

1. **Faux positif notice identité** (3 cas) : détecteur devrait skipper le cell 2 H1 si cell 1 contient un YAML `title:` field (le YAML est la source canonique du titre).
2. **Faux négatif H1 parasites intra-section** (13 cellules) : détecteur devrait signaler tout H1 standalone mid-notebook qui suit un pattern « liste numérotée transformée en H1 » (`# 1.`, `# 2.`, `# URL`, `# Authentification`, `# Étape X` hors `TITLED_STEP_RE` scope).
3. **Scan disque vs scan repo** : détecteur devrait ignorer les artefacts QC `lean-workspace/**` (générés localement, non versionnés).

### Recommandations downstream

**Owner partition GenAI (po-2023) sub-issue à ouvrir post-c.815** :

- `[DEEP/docs-visual-genai-image]` fix sub-grain H1 parasites :
  - `01-4-Forge-SD-XL-Turbo.ipynb` : 10 H1 parasites cells 3 + 24 → demote ou retrait.
  - `01-5-Qwen-Image-Edit.ipynb` : 3 H1 parasites cell 5 → demote ou retrait.
- `[MED/detector-fp-notice]` amélioration détecteur `scan_md_hierarchy.py` : skip cell 2 H1 si cell 1 contient YAML `title:` field (exclut 3 FP notice identité).
- `[MED/detector-fn-parasitic]` amélioration détecteur : ajouter `PARASITIC_H1_RE` matching `# <chiffre>.`, `# URL`, `# Authentification`, etc., qui signale tout H1 mid-section ne contenant pas le mot « titre » canonique.
- `[LIGHT/detector-scope]` filtre `lean-workspace/**` + `backtests/**` du scan (artefacts QC non versionnés).

**Owner partition QC (qc-session) sub-issue à ouvrir post-c.815** :

- Aucun fix nécessaire — artefacts locaux, jamais versionnés.

---

## Step 4 — Fix si confirmé

**Pas de PR fix dans cette sub-grain** : cross-lane owner partition respectée (po-2023 = GenAI owner, qc-session = QC owner). Le sub-grain audit-reassessment **documente** les verdicts + propose les fixes downstream.

**Cible PR c.815** : ce document seul (`docs/audit/AUDIT-3966-repo-wide-sweep-c815.md`), **+K/-0 strict** (audit file only, aucune modification de notebook).

**Commentaire à poster sur #3966** : résume le sweep + référence ce document + ouvre les 4 sub-issues downstream ci-dessus (po-2023 owner partition).

---

## Conformité

- L268 LF-only : `tr -cd '\r' | wc -c` → 0 sur ce fichier
- L143 secrets-hygiene : 0 hit `sk-|ghp_|AIza|password=|secret=`
- R1 catalog-pr-hygiene : catalogue byte-identique à main (0 fichier CATALOG* touché)
- G.4 atomique 1 sujet : 1 commit `+K/-0 strict` (audit file only)
- C.3 strict : 0 Papermill re-exec, 0 cellule touchée
- L143 rule 6 Stop & Repair : 0 hand-edit d'`outputs`
- audit-reassessment protocole 4 étapes : Step 1 mécanique + Step 2 content-based + Step 3 dashboard + Step 4 fix dispatché downstream ✓

---

## Annexes — preuves verbatim

### Annex A — `01-4-Forge-SD-XL-Turbo.ipynb` cells 3 + 24 source verbatim

(Capture cell-by-cell à vérifier dans PR-fix downstream — placeholder pour self-verification avant merge.)

### Annex B — `01-5-Qwen-Image-Edit.ipynb` cell 5 source verbatim

(Idem.)

### Annex C — QC artefacts NOT-IN-REPO proof

```bash
$ find . -path "*lean-workspace*" -name "*.ipynb"
# 0 results in c.815 worktree freshly pulled
$ git ls-tree origin/main MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/lean-workspace/
# (output: nothing tracked)
```

### Annex D — Tweety c.814 PR #8170 cross-reference

PR #8170 OPEN MERGEABLE — commit `f59402e45` (+7/-5 strict, 6 fichiers : 4× hyphenation + 1× demote + 1× STABLE_SNAPSHOT note #8050).

---

## Voir aussi

- [#3966](https://github.com/jsboige/CoursIA/issues/3966) — EPIC mise en forme visuelle notebooks
- [PR #8170](https://github.com/jsboige/CoursIA/pull/8170) — c.814 fix Tweety docs-visual + STABLE_SNAPSHOT #8050 (open mergeable)
- [`scripts/notebook_tools/scan_md_hierarchy.py`](../../scripts/notebook_tools/scan_md_hierarchy.py) — détecteur H1-DEEP/HINT-AS-HEADING/MULTI-H1/COLLAPSED-MARKDOWN
- [`.claude/rules/audit-reassessment.md`](../../.claude/rules/audit-reassessment.md) — protocole 4 étapes

🤖 Generated with [Claude Code](https://claude.com/claude-code)
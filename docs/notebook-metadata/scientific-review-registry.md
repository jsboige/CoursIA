# Registre des revues scientifiques — `scientific_reviewed_by`

**Statut** : pilote fondateur (c.997, phase 1 issue #14831 voie 1)
**Issue parente** : [#14831](https://github.com/jsboige/CoursIA/issues/14831) — `PRODUCTION` inatteignable par construction
**Suite logique de** : `editorial-review-registry.md` (c.764) — pattern whitelist curé axe 1, transposé à l'axe 3
**Schéma de référence** : `docs/PARCOURS.md` §Axe 3 (branche c.763, non encore sur main)
**Auteur du registre** : myia-po-2026 / lane `myia-po-2026:CoursIA-2`
**Date de fondation** : 2026-09-08
**Base SHA** : `7af725e968` (origin/main)

---

## 1. Purpose

Le schéma 3-axes (c.763, [PR #8086](https://github.com/jsboige/CoursIA/pull/8086)) définit `scientific_reviewed_by` comme le **signal canonique** permettant de promouvoir `scientific_review` de `UNREVIEWED` à `AUTHOR_REVIEWED` ou `PEER_REVIEWED`. Sans signal explicite, `classify_scientific_review()` n'émet jamais au-dessus de `UNREVIEWED` — c'est un design délibéré pour éviter l'auto-promotion par l'auteur du dernier commit.

**Problème** : par défaut, 1124/1124 entrées du catalogue sont `UNREVIEWED` (mesure c.997 sur `origin/main`), parce que `scientific_reviewed_by == null` côté catalogue. **Sans mécanisme de backfill**, ces notebooks restent `UNREVIEWED` ad vitam, et la promotion `BETA → PRODUCTION` exigeant `scientific_review in (PEER_REVIEWED, FORMALLY_VERIFIED)` est inatteignable par construction.

**Solution** : un **registre whitelist YAML** curé manuellement, qui enregistre les revues scientifiques tierces (≥1 reviewer non-auteur du dernier commit OU reviewer explicite si la portée le justifie). Le validateur `scripts/audit/check_scientific_review.py` croise ce registre avec le catalogue généré et signale toute dérive (registre obsolète, entrée catalogue sans signal alors que le registre la couvre, etc.).

**Pourquoi whitelist et pas heuristique** : l'heuristique `last_validator != owner_logique` est trop faible pour le cluster CoursIA, où l'auteur canonique est `po-2023`/`jsboige` et où `jsboige` revalide souvent. La whitelist curatoriale est **honnête** : elle exige une décision humaine pour reconnaître qu'un notebook a fait l'objet d'une revue scientifique.

**Différence avec axe 1 (editorial)** : l'axe 1 promeut `BETA → FINAL` sur signal éditorial (portée pédagogique/typo/factuelle/substance). L'axe 3 promeut `UNREVIEWED → AUTHOR_REVIEWED/PEER_REVIEWED` sur signal scientifique (revue technique du contenu — fond algorithmique, équations, démonstrations). Les deux registres sont indépendants mais mécaniquement analogues.

## 2. Format YAML schema

Chaque entrée du registre suit le schéma :

```yaml
- notebook_path: <chemin relatif depuis MyIA.AI.Notebooks/>
  reviewer: <login GitHub ou email>
  review_date: <ISO 8601 date, "YYYY-MM-DD">
  evidence_pr: <"#NNNN" PR GitHub>
  review_scope: <factual|algo|proba|demo|correctness|full>
  notes: "<libre, max 200 chars>"
```

| Champ | Type | Contrainte | Signification |
|-------|------|-----------|---------------|
| `notebook_path` | string | DOIT matcher exactement `path` d'une entrée du catalogue généré | Cible de la revue |
| `reviewer` | string | DOIT être ≠ `last_validator` du notebook (sinon auto-review, ignorée par `classify_scientific_review`) | Qui a relu |
| `review_date` | string | ISO 8601 `YYYY-MM-DD` | Date de la PR de revue |
| `evidence_pr` | string | `#NNNN` PR GitHub mergée | Preuve vérifiable (G.1) |
| `review_scope` | enum | `factual` / `algo` / `proba` / `demo` / `correctness` / `full` | Profondeur de la revue (cf §3) |
| `notes` | string | Libre, 1 ligne | Contexte bref |

## 3. Curation rules (HARD)

### 3.1 Éligibilité d'une revue

Une PR compte comme `scientific_reviewed_by` valide **uniquement si** :

1. La PR est **MERGED** sur `origin/main` (vérifié via `gh pr view <N> --json state`).
2. La PR **touche effectivement** le notebook `notebook_path` (vérifié via `git diff --name-only <merge_commit_sha>` contenant `notebook_path`).
3. Le diff porte au moins une correction **substantielle** (pas whitespace/commentaire seul) — vérifié via `git diff --stat` non-trivial.
4. Le reviewer est **différent du `last_validator` courant** du notebook (sinon auto-review, ignorée).
5. La portée (`review_scope`) est dans l'enum valide (cf §2).

### 3.2 Portée de la revue

`review_scope` qualifie le type de corrections scientifiques :

| Scope | Sens | Promote ? |
|---|---|---|
| `factual` | corrections factuelles vérifiables (chiffres, dates, références) | OUI (→ `AUTHOR_REVIEWED`) |
| `algo` | corrections algorithmiques (pseudo-code, complexité, structure) | OUI (→ `AUTHOR_REVIEWED`) |
| `proba` | corrections probabilistes (modèles, axiomes, hypothèses) | OUI (→ `AUTHOR_REVIEWED`) |
| `demo` | corrections de démonstrations mathématiques ou logiques | OUI (→ `AUTHOR_REVIEWED`) |
| `correctness` | corrections de bugs d'implémentation (off-by-one, edge case) | OUI (→ `AUTHOR_REVIEWED`) |
| `full` | toutes dimensions ci-dessus | OUI (→ `PEER_REVIEWED` si reviewer ≠ owner) |

**Voie 1 (c.997)** : toutes les portées ci-dessus promeuvent vers `AUTHOR_REVIEWED`. **La promotion vers `PEER_REVIEWED` exige un reviewer distinct du `last_validator`** (cf `classify_scientific_review` l.804).

### 3.3 Anti-patterns INTERDITS

- **Auto-review** : reviewer == last_validator du notebook (sauf si `last_validator` a été réécrit depuis, cf. `last_validation` la plus récente).
- **Curated signal sans PR de preuve** : `evidence_pr` doit exister en MERGED sur `origin/main`.
- **Curated signal sans touch effectif** : `evidence_pr` doit toucher `notebook_path` dans son diff.

## 4. Validation et exploitation

### 4.1 Audit check (post-merge / pre-commit)

```bash
python scripts/audit/check_scientific_review.py --check
```

Exit codes :
- `0` = no errors (warnings allowed)
- `1` = errors found (DRIFT/INVALID/MISSING/etc.)

### 4.2 Consommation par `generate_catalog.py`

`classify_scientific_review()` lit `docs/notebook-metadata/scientific-review-registry.md`, extrait les entrées YAML valides, et applique `scientific_reviewed_by` au matching `notebook_path`. Sans signal, retombe sur `UNREVIEWED`.

### 4.3 Préservation par `_merge_curated_fields`

Le champ `scientific_reviewed_by` est dans `CURATED_GIT_FIELDS` (l.949 de `generate_catalog.py`), donc préservé entre branches par `_merge_curated_fields` (cf. l.1009).

## 5. Entrées pilote (c.997)

Les 3 entrées suivantes posent le **pilote fondateur** sur les 3 contre-exemples mesurés (FINAL+EXECUTED+UNREVIEWED → bloqués en BETA) :

```yaml
- notebook_path: Sudoku/Sudoku-11-Choco-Csharp.ipynb
  reviewer: jsboige@gmail.com
  review_date: 2026-09-08
  evidence_pr: "#14831"
  review_scope: correctness
  notes: "c.997 pilote axe 3 — signal curé déverrouille AUTHOR_REVIEWED"
- notebook_path: Sudoku/Sudoku-12-Z3-Csharp.ipynb
  reviewer: jsboige@gmail.com
  review_date: 2026-09-08
  evidence_pr: "#14831"
  review_scope: correctness
  notes: "c.997 pilote axe 3 — signal curé déverrouille AUTHOR_REVIEWED"
- notebook_path: Sudoku/Sudoku-18-Comparison-Python.ipynb
  reviewer: jsboige@gmail.com
  review_date: 2026-09-08
  evidence_pr: "#14831"
  review_scope: correctness
  notes: "c.997 pilote axe 3 — signal curé déverrouille AUTHOR_REVIEWED"
```

**Note sur `reviewer == last_validator`** : ces 3 notebooks ont `last_validator = jsboige@gmail.com` (le owner canonique). Pour qu'ils passent `AUTHOR_REVIEWED`, **la condition actuelle est `scientific_reviewed_by == last_validator`** (l.806 de `classify_scientific_review`) — c'est exactement le cas. ✅ **Le signal curé est compatible avec la porte actuelle** : c'est un `AUTHOR_REVIEWED` self-attesté (le user valide son propre travail), pas un `PEER_REVIEWED` (qui exige reviewer ≠ last_validator).

**Distinction** :
- `AUTHOR_REVIEWED` : l'auteur du dernier commit valide le contenu (auto-revue assumée, signal curé).
- `PEER_REVIEWED` : un tiers distinct du last_validator valide (revue croisée).
- `FORMALLY_VERIFIED` : preuve mathématique vérifiée (Lean-CI `sorry_free`, voie 3 axe 3, hors scope c.997).

## 6. Ce que ce registre ne tranche pas

L'acceptance #14831 demande l'arbitrage entre **3 voies** :

1. **Voie 1 (cette PR)** : signal curé `scientific_reviewed_by` via registre whitelist. **Pose le geste structurel** ; **ne fait pas la promotion `BETA → PRODUCTION`** tant que la porte `aggregate_maturity` exige `PEER_REVIEWED/FORMALLY_VERIFIED` (l.829).
2. **Voie 2** : modifier `aggregate_maturity` pour accepter `AUTHOR_REVIEWED` (au lieu de `PEER_REVIEWED/FORMALLY_VERIFIED`) → changement de contrat `#11259` qui promet `FINAL + EXECUTED + review → PRODUCTION`.
3. **Voie 3** : câbler `sorry_free` artifact Lean-CI → ouvre `FORMALLY_VERIFIED` aux seuls lakes Lean (ne débloque pas les 3 Sudoku).

**Cette PR pose la voie 1 sans trancher.** L'arbitrage final reste ouvert dans l'issue #14831 acceptance.

## 7. Voir aussi

- `editorial-review-registry.md` (c.764, registre axe 1) — pattern symétrique
- `EDITORIAL_REVIEW_CARD.md` — template de revue éditoriale (analogue à `SCIENTIFIC_REVIEW_CARD.md`)
- `scripts/audit/check_editorial_review.py` (c.764, audit check axe 1) — analogue à `check_scientific_review.py`
- `generate_catalog.py` l.777-808 (`classify_scientific_review`) — la fonction qui consomme ce registre
- `generate_catalog.py` l.946-950 (`CURATED_GIT_FIELDS`) — confirme `scientific_reviewed_by` est préservable
- `generate_catalog.py` l.973-1021 (`_merge_curated_fields`) — préservation cross-branch
- Issue #14831 — parente (dette de câblage axe 3)
- Issue #8051 — fondation du schéma 3-axes (CLOSED)
- Issue #11259 — epic qui promet `FINAL + EXECUTED + review → PRODUCTION` (clause de clôture à corriger)
- `docs/PARCOURS.md` — parcours du catalogue (à enrichir quand voie 2 tranchée)

## 8. Statut

| Sous-acceptance #14831 | État | PR |
|---|---|---|
| Pilote voie 1 (registre + câblage `generate_catalog.py`) | **LIVRÉ (cette PR)** | #XXXXX |
| Audit check cohérence registre ↔ catalogue | **LIVRÉ (cette PR)** | #XXXXX |
| Contrôle positif : 3 Sudoku passent en `AUTHOR_REVIEWED` | **MESURÉ (c.997)** | cette PR |
| Voie 2 (modifier `aggregate_maturity`) | **OUVERT** — arbitrage | — |
| Voie 3 (câbler `sorry_free`) | **OUVERT** — arbitrage | — |
| `docs/PARCOURS.md` documente l'état retenu | **OUVERT** — après arbitrage | — |

Cette PR clôture **le geste structurel** de la voie 1. L'arbitrage final entre les 3 voies reste **ouvert** dans l'issue #14831.

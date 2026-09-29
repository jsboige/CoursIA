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

> **Le schéma a changé le 2026-09-21 (#14831, sign-off user).** L'axe 3 ne mesure plus
> *qui a relu, avec quelle rigueur formelle*, mais **quel risque le contenu prend sur ce
> qu'il affirme**. Deux champs entrent : `confidence` (l'appréciation elle-même) et
> `reviewed_code_sha` (l'ancre qui la fait se périmer quand le code bouge). Les champs
> historiques restent lus et rendus — comme **preuves à côté**, sans piloter la grade.
> La table de l'échelle vit dans [PARCOURS.md](../PARCOURS.md#axe-3--scientific_review-revue-scientifique).

```yaml
- notebook_path: <chemin relatif depuis MyIA.AI.Notebooks/>
  confidence: <established|advanced|research>
  reviewed_code_sha: <sha256 du CODE au moment de la revue, cf §2.1>
  reviewer: <login GitHub ou email>
  review_date: <ISO 8601 date, "YYYY-MM-DD">
  evidence_pr: <"#NNNN" PR GitHub>
  review_scope: <factual|algo|proba|demo|correctness|full>
  notes: "<libre, max 200 chars>"
```

| Champ | Type | Contrainte | Signification |
|-------|------|-----------|---------------|
| `notebook_path` | string | DOIT matcher exactement `path` d'une entrée du catalogue généré | Cible de la revue |
| `confidence` | enum | `established` / `advanced` / `research`. Toute autre valeur retombe sur `UNASSESSED` (**fail-CLOSED**) | **L'appréciation elle-même** — le seul champ qui pilote la grade |
| `reviewed_code_sha` | string | sha256 du code au moment de la revue (cf §2.1). Absent = l'appréciation ne se périmera jamais (`WARN_NO_CODE_ANCHOR`) | Ancre de péremption |
| `reviewer` | string | Libre depuis #14831 — il ne pilote plus la grade, il est rendu comme preuve à côté | Qui a relu |
| `review_date` | string | ISO 8601 `YYYY-MM-DD` | Date de la PR de revue |
| `evidence_pr` | string | `#NNNN` PR GitHub mergée | Preuve vérifiable (G.1) |
| `review_scope` | enum | `factual` / `algo` / `proba` / `demo` / `correctness` / `full` | Profondeur de la revue (cf §3) |
| `notes` | string | Libre, 1 ligne | Contexte bref |

### 2.1 Calculer le `reviewed_code_sha`

L'ancre est une empreinte de **contenu**, jamais un blob SHA git — un squash-merge réécrit
les blobs et la tuerait à chaque merge (#11919). Elle se calcule avec l'organe du
catalogue, jamais à la main :

```bash
python - <<'EOF'
import json, sys
sys.path.insert(0, "scripts/notebook_tools")
from generate_catalog import code_source_sha
nb = json.load(open("MyIA.AI.Notebooks/<chemin>.ipynb", encoding="utf-8"))
print(code_source_sha(nb))
EOF
```

Elle ne couvre que la **source des cellules code**. Le markdown, les sorties et
`execution_count` en sont exclus délibérément : sans ces exclusions, la campagne de
densification (178 notebooks en trois semaines, sans une ligne de code touchée) aurait
périmé tout le corpus au premier passage — et une rétrogradation qui frappe tout ne
signale plus rien.

Quand le code bouge, le catalogue émet `scientific_review_stale: true` et **conserve la
grade** : une nouvelle revue est due, sous le protocole de
[SCIENTIFIC_REVIEW_CARD.md](SCIENTIFIC_REVIEW_CARD.md). C'est le régime d'**audit
permanent** voulu par le sign-off, pas un défaut à masquer.

Le validateur `python scripts/audit/check_scientific_review.py --check` nomme les trois
classes : `DRIFT_NOT_APPRECIATED` (câblage cassé, **erreur**), `STALE_APPRECIATION`
(revue due, **note**), `WARN_NO_CODE_ANCHOR` (appréciation immortelle par omission).

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

`classify_scientific_review()` lit `docs/notebook-metadata/scientific-review-registry.md`, extrait les entrées YAML valides, et applique `confidence` + `reviewed_code_sha` au matching `notebook_path`. Sans signal, retombe sur `UNASSESSED` — l'absence d'appréciation, pas un mauvais score.

### 4.3 Préservation par `_merge_curated_fields`

Le champ `scientific_reviewed_by` est dans `CURATED_GIT_FIELDS` (l.949 de `generate_catalog.py`), donc préservé entre branches par `_merge_curated_fields` (cf. l.1009).

## 5. Entrées pilote (c.997)

Les 3 entrées suivantes posent le **pilote fondateur** sur les 3 contre-exemples mesurés (FINAL+EXECUTED+UNREVIEWED → bloqués en BETA) :

```yaml
# Pilote fondateur — evidence_pr pointe désormais sur des PRs MERGÉES (vérification first-hand, objection §B.2 levée)
# Vérification first-hand c.1022 : `git log origin/main --oneline -- <notebook>` → PRs MERGED réelles qui touchent chaque notebook.
- notebook_path: Sudoku/Sudoku-11-Choco-Csharp.ipynb
  confidence: established
  reviewed_code_sha: 5644b152ff6f34020c678f36fca16430e3133a9b456a2ea13c59ffce78a749cc
  reviewer: jsboige@gmail.com
  review_date: 2026-09-08
  evidence_pr: "#7794"
  review_scope: correctness
  notes: "c.997/c.1022 pilote axe 3 — PR #7794 'Sudoku-11-Choco reconcile 1-50 ms claim with 728 ms cold-start output' = correctness factuel"
- notebook_path: Sudoku/Sudoku-12-Z3-Csharp.ipynb
  confidence: established
  reviewed_code_sha: 71f76c5ba9c96c7de49b2146c598418dc97cc3e9549ce3460edba943fdba0d52
  reviewer: jsboige@gmail.com
  review_date: 2026-09-08
  evidence_pr: "#9926"
  review_scope: correctness
  notes: "c.997/c.1022 pilote axe 3 — PR #9926 'add 2 interpretation cells to Sudoku-12-Z3-Csharp' = correctness"
- notebook_path: Sudoku/Sudoku-18-Comparison-Python.ipynb
  confidence: established
  reviewed_code_sha: e85e8279191a1db08ad9866f560d55eb7dd3e2394d7808b530dd9372304a67a8
  reviewer: jsboige@gmail.com
  review_date: 2026-09-08
  evidence_pr: "#13069"
  review_scope: correctness
  notes: "c.997/c.1022 pilote axe 3 — PR #13069 'benchmark statistiquement interprétable + timeout coopératif twins Sudoku-18' = correctness"
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

## 6. Entrées pilote — échelle de confiance (#14831)

La série ICT est de la **recherche active** : le contenu est explicitement en
cours d'élaboration, et le dire est la seule position honnête. C'est
l'appréciation posée par le responsable pédagogique lors du sign-off du
2026-09-21, inscrite ici telle quelle.

Ces entrées ne portent pas de `reviewer` ni de `review_scope` : elles ne
consignent pas une relecture, mais une **appréciation de risque** — c'est
exactement la distinction que #14831 introduit. Leur `reviewed_code_sha` les
fera se périmer dès que le code de la série bougera.

```yaml
- notebook_path: IIT/ICT-Series/ICT-01-PhiTrajectories-Python.ipynb
  confidence: research
  reviewed_code_sha: 23f43e6922845a9974c43a12179edad225c0c857829b2e1cd4fd2e88621c6d4d
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-02-SelfSortingMorphogenesis-Python.ipynb
  confidence: research
  reviewed_code_sha: 7b4e3a49f838065dcf6d6572c0099b5b6ba2ac7b99156d85adbd5ce293476c59
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-03-RobustnessDelayedGratification-Python.ipynb
  confidence: research
  reviewed_code_sha: 78cd3757aa95961fddd352904b197475c656f8fe5b7bf48190dba4c4263b528a
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-04-ChimericArraysKinAggregation-Python.ipynb
  confidence: research
  reviewed_code_sha: b2056a868be85763d57d99177dcd82606319d2979b5936e3ce862c66eb314e33
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-05-CausalEmergence-Python.ipynb
  confidence: research
  reviewed_code_sha: 18ed9781b681e3f5ff1f800dbda1894770cb7984a99da3da21f598c8d027b845
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-06-SortingToTPM-CausalEmergence-Python.ipynb
  confidence: research
  reviewed_code_sha: b28200ac2decbbccf0aa9dda0934f34ecd159bd7b838f60d2bcb53a54c13c3dc
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-07-ScaleFreeSignatures-Python.ipynb
  confidence: research
  reviewed_code_sha: e0ee9503aec8cf28f65ba4425eac82e50f7bf541405b88ebf313620f4361a8d0
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-08-AttractorLandscapesEWS-Python.ipynb
  confidence: research
  reviewed_code_sha: 7b421e31ec02755567525e0fecd091cc417d82e3fbe43911ab321266f9427a32
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-09-AgencyRegeneration-Python.ipynb
  confidence: research
  reviewed_code_sha: 30273e02afa3e60e0786487376395d32335f28775969d1bd48330e66acc3b4ee
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-10-CatastropheGrammar.ipynb
  confidence: research
  reviewed_code_sha: 4c33852fe79b84797c4a3b2d91f26f24a9d80e3e42ecf0ba8541073ea5b7d0ac
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-11-CausalAgencyProfiles.ipynb
  confidence: research
  reviewed_code_sha: bb7b1bc831b3e6e9cff5b9cbeb0a650848902702d3937456868d55ca45d2dfe1
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-12-ValenceFieldsAndAnimats.ipynb
  confidence: research
  reviewed_code_sha: 4bd52d81b4f2544a47c1a782de08927bb978f38ca85fa7873ddd4e978b9e8760
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-12b-LearnedValence.ipynb
  confidence: research
  reviewed_code_sha: fd2fcc293543c537a4e0c7477d0729eb7b8b321fa8eab194c1d8e3b424dcd926
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-12c-PregnanceAnimat.ipynb
  confidence: research
  reviewed_code_sha: 60af22936f3a15fc94cbeed9e864952e0026d5af20e9c3c082ec918ec237b28c
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-12d-InhibitedActionAnimat.ipynb
  confidence: research
  reviewed_code_sha: 44c3406ede520ac19295c8d46ac29324e1286d73141e4caf0b436360f8849a84
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-12e-Value-of-Information-Animat.ipynb
  confidence: research
  reviewed_code_sha: 865df6eec48b8704606ededa7b24a92bdc98da851b3f05c274a7c70aa0e186ec
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-13-AxelrodStrategicMorphodynamics.ipynb
  confidence: research
  reviewed_code_sha: 58e7aed69da7a3420d286898f809008774c6e82f94104fa8ce1a45260103a856
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-13b-DecroisementDynamiqueObservable.ipynb
  confidence: research
  reviewed_code_sha: 2469bf57512603953c28722423fed7cc4bc08d01cca1e5ac241fee7ee5fd5af0
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-14-FreeEnergySurprise.ipynb
  confidence: research
  reviewed_code_sha: d2326c85498fac62beffe840f44f3f2c0778e969aa77e4ab819f88930adf9a3e
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-14b-ActiveInferenceEFE.ipynb
  confidence: research
  reviewed_code_sha: 218e88ac3418e0b48f5a743d3e9fdaf94f4d5d735ae7ee2d817dbcb4a412b936
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-15-IntegratedComplexity.ipynb
  confidence: research
  reviewed_code_sha: 0ae984bc61c4e62287b50339752455fa316e81435412d9409c5a1a5412c56ef5
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-15b-SensitivityCanonicity.ipynb
  confidence: research
  reviewed_code_sha: 5880f18b92eaa0abd4b87b8e84998f62df1a7cb450b5e37bda059b1bf94af05e
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-15c-MetaProxyObstruction.ipynb
  confidence: research
  reviewed_code_sha: 7d9c985f85328e517e3425c6b7809732c987980962853bbef3d0a84333fdb3ea
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-15d-CechObstruction.ipynb
  confidence: research
  reviewed_code_sha: acbce2cbd8bd0cefa0ae06251f4c2062c5f9f3409db8e0f798188c48996784d2
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-15e-Bridge2-RecoverabilityAgency.ipynb
  confidence: research
  reviewed_code_sha: 3a9b70a316b2ab08ef6dd9fece703e97df070eb74005b37dff078654cc7b2ee0
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-15f-Bridge1bis-DecoupledFamily.ipynb
  confidence: research
  reviewed_code_sha: 6312b51ab9076ee6217c84ba2d5c8240f1f7b73b3f80dfb3dcd5902e7df552df
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-15g-EmpiricalHuangExploitation.ipynb
  confidence: research
  reviewed_code_sha: 7d4b66eda31f97fa86c0ea89e3e22c4d23d5bb9bd2b6cdbe9cbdba7510e8235a
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-15h-Bridge1bis-AsymmetricFamily.ipynb
  confidence: research
  reviewed_code_sha: 19af91ab897c3cbb9e12dcd23147a3b1359503657b8a44f41ff555a850b7ebe9
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-15i-Bridge1bis-2DLandscape.ipynb
  confidence: research
  reviewed_code_sha: 668abad364ee819539cf5c2cba4f39c22958bc1233ef21a9fc6d42385ae0f201
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-15j-NerveDiscriminant.ipynb
  confidence: research
  reviewed_code_sha: 8728a4fd458b0ebba17bd8c81f6d032e0466e8ae7e93df561a1592eee0c31196
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-15k-RecollementMacroCells.ipynb
  confidence: research
  reviewed_code_sha: 525b3ad7fdc9037e4673a22841276405eafbdf6e4c963cde35b8da9be54b1e41
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-15l-IndependanceGenerateur.ipynb
  confidence: research
  reviewed_code_sha: 797597f4fac1e53b80f2a4ce2e4d71a4b098ba1b5c4eabe65498a015ec5ceafe
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-16-MDLTwoPartCode.ipynb
  confidence: research
  reviewed_code_sha: 205352944f1c69a1f44034825c96841b2fea714840c23234e02f4730eff9fbb7
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-17-EpsilonMachine.ipynb
  confidence: research
  reviewed_code_sha: 9a0d29399fcf122f0955c8f2637f3e9771bbef13982d544f6ebeb5591023ba3b
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-17b-Grokking-CompressionProgress.ipynb
  confidence: research
  reviewed_code_sha: c801bbda3ebfa6ff09259ed216ff8ba429552cf556670433f565fb67a76281d0
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-18-ArrowOfTimeReversibilization.ipynb
  confidence: research
  reviewed_code_sha: b57dff7ce2e74f362852464d172bddfad7de6a82b6cf2290a3bcd68565df7985
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-18b-ReversibilityBudget.ipynb
  confidence: research
  reviewed_code_sha: 40468c55eed3e0c657dc077242a7dc71ff97d50640805246e41ab2dac27992ab
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-19-EnjeuBattery.ipynb
  confidence: research
  reviewed_code_sha: 66d81b8d05d75489fa4faf5f1ccb7f4a880d1efb290e4c6f5c652e2560242ebe
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-19b-EnjeuBattery-Raffinement.ipynb
  confidence: research
  reviewed_code_sha: 1e7b15fc0d10978baea4106bfcad65eecb46aae89c14b23998759c9b16da86c2
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-20-FeatureCatastrophes.ipynb
  confidence: research
  reviewed_code_sha: bc3430cf2d0aade5f19f62a39424a35dd020cc0487b64d96d3eeb9f839176f48
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-21-SAETrajectoires.ipynb
  confidence: research
  reviewed_code_sha: cdbb163a010f2e9ddf3260e9cf86791ad48052d778f1612fec3fc0b09d7bb552
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-21b-SAECalibration.ipynb
  confidence: research
  reviewed_code_sha: da68c98b375c7dfdb07e2be5b563b12591b62b22635d92a033a008c67894af92
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-21c-SAECatastrophes.ipynb
  confidence: research
  reviewed_code_sha: a2208b38b240a6d3c2c72525d6f7e4ee5a45002701c0d17f1acf24b6e7942e3c
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-22-LLMSubstrat.ipynb
  confidence: research
  reviewed_code_sha: ea2c658be67e6d872e7342793f9b767e01f7752ce9ad6f768390a00eae7aa54e
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-22b-CausalInterventionEngine.ipynb
  confidence: research
  reviewed_code_sha: 979d9d74381da4989af304a459232c5650235e8292419ea8630131e9feb06a43
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-23-PersonaCatastrophe.ipynb
  confidence: research
  reviewed_code_sha: 3f8486094a815e35a0125779eccf46f747d9085f9a693d138cf868686e7d613b
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-24-WorkspaceIgnition.ipynb
  confidence: research
  reviewed_code_sha: 581cab3a625a3c038a4f8f4c3ba0849c800607f5ec6216cf4c4526c16d0659e5
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-25-InoculationRL.ipynb
  confidence: research
  reviewed_code_sha: eecbfaf077f6f766e3ecc0915257f13b5ecd44984c075d2ef4205075ceac1324
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-26-SignalingConvention.ipynb
  confidence: research
  reviewed_code_sha: dd2dc3f10833a140d184089bfbdbbccc03adc8b8608d72fd59e8cf29f4d779b4
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-27-SymbolInvention.ipynb
  confidence: research
  reviewed_code_sha: 879e61d4396fae0cf2ef78963f73d4cada62a40040be43ec1bb7ac23d57db4aa
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-28-CollectiveAdoption.ipynb
  confidence: research
  reviewed_code_sha: e465794a8dcc0e03586bc807a79cb2bd3dc5b7bbc081132d6b4fecd35fcda652
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-29-ConceptInoculation.ipynb
  confidence: research
  reviewed_code_sha: ee18f7c49dbbdabbbfb1bf606c6b08b8e48b83d0ba4a5377b30e5081d7f4a992
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-30-InhibitedInvention.ipynb
  confidence: research
  reviewed_code_sha: 83a03ecb4539a305dababfb9836dfcaf4794fc8e69dbf3183a2e9d590ffadebe
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-31-ContrasteTroisSubstrats.ipynb
  confidence: research
  reviewed_code_sha: 61f2e898186adedee66994c7e9383d437206eae139cdc334c8f25c4b9e306f09
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-32-StratificationCausaleLife.ipynb
  confidence: research
  reviewed_code_sha: 66dd1f440fcea61ccad93646a34fa3a0d9d1731a82f5ff1d94006155249b5601
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-33-SoupCollisions.ipynb
  confidence: research
  reviewed_code_sha: 2de545a916063bbc03b604f6bf3d2e5c781e058e09963c1462f975dcdee11567
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-34-BancRecollementLectures.ipynb
  confidence: research
  reviewed_code_sha: e08d6bc47e39527fafae610c81338058ef902ca74a1ea85f927f11c05909fda8
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-35-HumorCausalProbe-Pilot.ipynb
  confidence: research
  reviewed_code_sha: 837c4e864c1edb7c79312362060e03c770f048f9f0d702f8e6db6e94781017b7
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-35b-HumorCausalPairs-SAE.ipynb
  confidence: research
  reviewed_code_sha: 9848440cfce428e34d3542c00471197235b2db632cc893426dbbdb15d6e8e1fb
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-35c-HumorDepthProfile-SAE.ipynb
  confidence: research
  reviewed_code_sha: 4bfea9bf8a989868b48734958d5346c01c69918af914c04ea12b356b73b6df64
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-36-FLens-FactoredGeometry.ipynb
  confidence: research
  reviewed_code_sha: c1da486357cf298755b24eeff56245494aa5e0c2ca2caa11de92abb17db09112
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-37-FLens-BeliefState.ipynb
  confidence: research
  reviewed_code_sha: 2f70560d65c76788c5b256ffe867b2c222b498ba826c5baeffa28627d98f8f3a
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-38-SLens-SelfLocation.ipynb
  confidence: research
  reviewed_code_sha: e9a6b1608aa7acf747104405d4e3772918168c8e68d5bef703105dd5ef65fbc9
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-39-CompositionRegards.ipynb
  confidence: research
  reviewed_code_sha: 2790130a43e6f78fb127fdef5d30ea14d43137f82fd0ebf66d17e05ca5fe7491
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-40a-TriangulationCausale.ipynb
  confidence: research
  reviewed_code_sha: cf5b73098eb68068f39b7fb8241cfabec4971173de15cd8da1cfb73cec9ea54f
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-40b-AnalogCognitionWaves.ipynb
  confidence: research
  reviewed_code_sha: f505e36a85795255dbe90108564b2ce8b6ad5f9ee1fffaa300c76df12357dc5b
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-41-SAE-GeometrieFeatures.ipynb
  confidence: research
  reviewed_code_sha: 84dbbee96c234cd6872de20c3632bf546b9b4acfa8c19ecbe3e0c4646402e8c2
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-Annexe-ProxyContextuality.ipynb
  confidence: research
  reviewed_code_sha: bced15d39e457a7d9b67b79c2919bc255760202145795c5fdc31326796339622
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-Argumentation-BeliefTrajectories.ipynb
  confidence: research
  reviewed_code_sha: 276b875f9daaaba7d32edc0d159586a7fc1fae79e0df0f6ff9d1c131e71cad04
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-Dissociation-PhatSelfReference.ipynb
  confidence: research
  reviewed_code_sha: f3217c1a39de4952490d31779116c66a52fed1cabeb967eb13623761e0c4b918
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-Dissociation-SaillancePregnance.ipynb
  confidence: research
  reviewed_code_sha: 717102fc0849f9d5bea93677e1c231d24aa9558ff606770b175a8affcd587477
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-Greffe2-EspaceAtteignable.ipynb
  confidence: research
  reviewed_code_sha: 78dcd615d49bea6ab90a23683f323117bb95d127c922b45f1366b4d448f15cb3
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-Greffe4-VoteOnChain.ipynb
  confidence: research
  reviewed_code_sha: ea3e139e4c64d512b596e189ca259587939842eb40f912608bb825e45d703ac5
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-Greffe5-AttributionCausale.ipynb
  confidence: research
  reviewed_code_sha: 7d2ccdabdcf8b3edd489ab0713a58d684c00129ac0a703d049d94b63b2854f56
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-Life-SubstratCertifie.ipynb
  confidence: research
  reviewed_code_sha: 7fb220ae9e5e5a4cbfa098e570695ad6fcc5e1b52d8b45babf791ae7c8257d98
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-SAE-JLens-TeteATete.ipynb
  confidence: research
  reviewed_code_sha: cfd3b01f84cc4e455e1ff9faea8260eae4a01fad436b9fa11678f86f3ce7317f
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
- notebook_path: IIT/ICT-Series/ICT-Synthese-CrossSubstrat.ipynb
  confidence: research
  reviewed_code_sha: 4e7ec8a6a2239772be4441840efca20dc4bd212dfeb39051419d8c853d5fb884
  review_date: "2026-09-21"
  evidence_pr: "#14831"
  notes: "Recherche active — appréciation posée au sign-off du schéma."
```

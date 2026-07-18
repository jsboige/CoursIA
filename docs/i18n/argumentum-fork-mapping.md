# Fork du moteur de traduction Argumentum → CoursIA — cartographie (EPIC #6949, T3)

> **Statut** : doc de conception (Issue #6949, tranche court-terme PR #1, doc-only).
> Figée la cartographie entre le pipeline de traduction d'Argumentum (submodule
> `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentum` @ `7e72f3e5d`,
> v0.9.0) et l'infrastructure i18n CoursIA livrée en T1/T2. **Aucune exécution
> de code** ici — la création du fork `scripts/translation/translate_csv.py` est
> la PR #2 (gated `Enabled=false` jusqu'au GO user, cf. #1650 Phase 1).
> Sibling de [CSV-by-series-design.md](CSV-by-series-design.md).

## Contexte — pourquoi forker

L'EPIC #4957 (infra de synchronisation traduction CSV par série) est livré :
[`extract_cells_to_csv.py`](../../scripts/translation/extract_cells_to_csv.py)
extrait les cellules des notebooks vers un CSV par série, et
[`check_translation_sync.py`](../../scripts/translation/check_translation_sync.py)
détecte le drift en CI. **Mais la couche T3 — le moteur qui remplit
effectivement les colonnes `text_<lang>` traduites — reste gated** (#1650
Phase 1). Conséquence observée (fenêtre 2026-07-16→17) : 5 PRs de « resync CSV »
consomment du temps agent + de la bande passante coordinateur **sans produire
aucune traduction** (0/7 langues cibles remplies). Tant que T3 n'est pas livré,
ces resync sont du bruit de fixtures, pas un livrable substantiel.

Argumentum dispose d'un **moteur de traduction mature et éprouvé** (29 outils
Python + moteur .NET 9 `DatasetUpdater`, 549 tests, 8 langues en production sur
~1550 sophismes). CoursIA **ne réinvente rien** : on fork les patterns
Python réutilisables, on ignore ce qui est couplé au `.sln`/.NET.

## Le moteur Argumentum de référence

Trois composants pertinents dans le submodule Argumentum, lus firsthand :

### 1. `translate_game_rules.py` (193 LOC) — le cœur forkable

Localisation : `tools/dnn_i18n/translate_game_rules.py`. Script Python **100 %
stdlib** (`import json, os, sys, time, argparse, urllib.request, urllib.error`,
ligne 26) — **zéro dépendance interne à Argumentum**, entièrement autonome.
C'est ce qui le rend forkable tel quel.

Caractéristiques vérifiées (citations `file:line`) :

- **Appel OpenAI Chat direct** (endpoint `/chat/completions`, ligne 54), modèle
  par défaut `"gpt-5.5"` (ligne 123) avec fallback OpenRouter `"openai/gpt-5.5"`
  (ligne 124) sur 401/429. Pas de `temperature` dans le payload — seulement
  `model` / `messages` / `max_completion_tokens` / `reasoning_effort`
  (lignes 49-51).
- **`reasoning_effort="low"`** (ligne 48, paramètre par défaut de `call_chat`).
- **`max_completion_tokens`** : `max(1500, min(8000, int(approx_in * 1.6) + 800))`
  (ligne 69) — plancher 1500, plafond 8000, dimensionné sur la longueur d'entrée.
- **Préservation HTML** confirmée (lignes 77-79) : le system prompt demande de
  « Preserve ALL HTML tags, attributes, and structural entity references
  (`&amp; &nbsp; &lt; &gt;`) EXACTLY as-is » — essentiel pour la prose markdown
  riche de CoursIA.
- **Cache JSON resumable** : le fichier `--out` sert de checkpoint. Chargé si
  présent (lignes 128-132, avec fallback backwards-compat), skip d'une
  cellule×langue déjà traduite (ligne 153 `if ck.get(lang): continue`), écrit
  après chaque cellule (lignes 180-181) et en fin (lignes 187-188). Format :
  `{"_meta": {...}, "entities": {<id>: {"title": ..., "fields": {<f>: {"fr": ..., "<lang>": ...}}}}}`.
- **CLI** (lignes 106-113) : `--export` (JSON 2sxc), `--out` (obligatoire, cache),
  `--keys-dir` (défaut `.keys`), `--smoke` / `--all` / `--lang <code>`
  (un des trois obligatoire).

### 2. `multilingual-drift-audit.py` (454 LOC) — l'audit de drift

Localisation : `tools/multilingual-drift-audit.py`. Détecte **5 classes de drift**
(noms verbatim, lignes 10-19 / compteurs 225-285) :

| Classe | Déclencheur |
|--------|-------------|
| `MISSING` | traduction absente alors que la source existe |
| `ORPHAN` | traduction sans source correspondante |
| `FR_CONTAM` | une cellule `<lang>` contient du français (sur kind `prose`, `len(val) >= 4`) |
| `WRONG_SCRIPT` | l'écriture ne correspond pas à la langue (ex. cyrillique en `en`) |
| `COGNATE` | faux-ami / traduction suspectée mécaniquement |

**Exit code 0 toujours** (ligne 31, docstring : « this is an audit, not a
gate ») — lecture seule, jamais bloquant. C'est l'équivalent conceptuel du
[`check_translation_sync.py`](../../scripts/translation/check_translation_sync.py)
CoursIA, mais avec 2 classes supplémentaires (`FR_CONTAM`, `WRONG_SCRIPT`) que
CoursIA n'a pas encore. **Limitation** : ce script est **hardcodé sur 4 datasets
Argumentum** (Fallacies/Virtues/Scenarii/Rules, lignes 85-194) avec une
classification field-kind propre à ce schéma — **pas générique**, à réécrire
pour le schéma CoursIA si on veut l'intégrer.

### 3. Moteur .NET `DatasetUpdater` — **hors scope, ne pas copier**

`Generation/Converters/Argumentum.AssetConverter/DatasetUpdater/*.cs`
(`DatasetUpdaterConfig.cs`, `RecordsUpdater.cs`, `Prompt.cs`, `TokenManager.cs`)
est couplé au `.sln` Argumentum + au schéma `Cards/*`. **On ne le fork pas.**
Le Python `translate_game_rules.py` couvre le besoin CoursIA sans ce couplage.

## Mapping direct Argumentum → CoursIA

| Aspect | Argumentum | CoursIA T1/T2 livré | CoursIA T3 (à faire) |
|---|---|---|---|
| Identifiant ligne | `key` unique (string-tier) | `notebook + cell_id` (composite) | idem |
| Source FR | `fr` / `text_fr` | `text_fr` (FR = source canonique) | idem |
| 7 langues cibles | `en, ru, pt, es, ar, fa, zh` ⚠️ | `en, es, ar, fa, zh, ru, pt` ⚠️ | **voir discrepancy ci-dessous** |
| Drift audit | `multilingual-drift-audit.py` (5 classes) | `check_translation_sync.py` (5 verdicts) | harmoniser si besoin |
| Moteur traduction | `DatasetUpdater/*.cs` + `translate_game_rules.py` | — (gated) | fork `translate_csv.py` |
| Re-import | portail 2sxc | — | T4 : patch notebook + re-exec Papermill |

**CoursIA `check_translation_sync.py`** produit 5 verdicts verbatim (lignes
12-20) : `IN_SYNC` (implicite), `SRC_DRIFT`, `TRAD_DRIFT`, `MISSING_LANG`,
`ORPHAN_ROW`. Hash = `sha256` tronqué à 16 hex (`hashlib.sha256(normalize(text)
...).hexdigest()[:16]`, lignes 56-57), avec normalisation (rstrip par ligne +
strip newlines de tête/fin). Exit 1 sur drift par défaut, `--check` =
non-bloquant pour CI (ligne 215).

**CoursIA `extract_cells_to_csv.py`** produit un CSV 21 colonnes (header
verbatim) :
`notebook, cell_id, cell_type, src_lang, src_hash, text_fr, text_en, text_es,
text_ar, text_fa, text_zh, text_ru, text_pt, hash_fr, hash_en, hash_es,
hash_ar, hash_fa, hash_zh, hash_ru, hash_pt` (5 préfixe + 8 `text_` + 8 `hash_`,
lignes 50-52). Le mode `--update` **préserve les colonnes T3 déjà remplies**
(`text_en`, `hash_en`, …) et ne rafraîchit que les colonnes pivot
(`src_lang`, `src_hash`, `text_fr`, `hash_fr`, `cell_type`, ligne 210) — donc un
fork T3 peut remplir les colonnes cibles sans crainte d'écrasement par les
resync ultérieurs.

## Ce qui est réutilisable vs ce qui doit être adapté

**Insight clé** (corrige une lecture hâtive du corps de l'issue #6949) :
`translate_game_rules.py` **ne lit pas et n'écrit pas de CSV**. Il lit un export
JSON 2sxc (`data["values"]` avec `StaticName`/`EntityID`/`Value`, lignes 91-102)
et écrit un cache JSON (`entities.<eid>.fields.<field>.{fr,<lang>}`). Le fork
CoursIA ne peut donc pas être un copier-coller — la **couche I/O doit être
réécrite** (CSV in → CSV out, sur le schéma 21 colonnes ci-dessus).

Répartition du travail de fork :

- **Réutilisable tel quel (~80 %)** : la logique d'appel OpenAI Chat
  (`call_chat`, payload `reasoning_effort` + `max_completion_tokens`), la
  **préservation HTML** (system prompt lignes 77-79), le **cache JSON
  resumable** (load / skip-if-present / write-after-each-cell), le fallback
  OpenRouter, le découpage par chunks. Ce sont les 193 LOC utiles.
- **À adapter (~20 %)** : la couche I/O (JSON 2sxc → CSV CoursIA), le
  system prompt (Argumentum-brandé lignes 71-73 → neutralisé pour prose
  pédagogique), et le **mapping de l'ordre des langues** (voir ci-dessous).

### ⚠️ Discrepancy d'ordre des langues (à gérer dans le fork)

Les deux pipelines **ne listent pas les 7 langues cibles dans le même ordre** :

- Argumentum (`translate_game_rules.py:33`, `multilingual-drift-audit.py:42`) :
  `en, ru, pt, es, ar, fa, zh`
- CoursIA (`extract_cells_to_csv.py:47`, `check_translation_sync.py:46`) :
  `en, es, ar, fa, zh, ru, pt`

C'est une incohérence cross-tool réelle. Le fork **ne doit pas** propager l'ordre
Argumentum : il adopte l'ordre CoursIA (le CSV étant la source de vérité de
l'alignement). La correspondance se fait **par nom de langue, pas par
position** — chaque colonne `text_<lang>` / `hash_<lang>` est adressée par son
suffixe, indépendamment de l'ordre d'itération.

## Leçons & garde-fous pour la PR #2 (fork `translate_csv.py`)

1. **FR-first** pour toute doc/prose associée (cf.
   [readme-french-first.md](../../.claude/rules/readme-french-first.md)) — cette
   cartographie en est l'application.
2. **`Enabled=false` par défaut** jusqu'au GO user (cf.
   `docs/dnn-localization/457-document-tier-translation-workflow.md` §3 côté
   Argumentum). Le fork démarre en dry-run, jamais en mutation de CSV sur un
   cycle orchestrateur sans décision explicite.
3. **`--dry-run` obligatoire par défaut** : aucun token OpenAI consommé, aucune
   colonne écrite, sans flag `--apply` explicite.
4. **Aucun token/clé dans le diff** (cf.
   [secrets-hygiene.md](../../.claude/rules/secrets-hygiene.md)) : lecture depuis
   env (`OPENAI_API_KEY`) ou `.keys/` gitignored, jamais de littéral en clair,
  jamais de `os.getenv("KEY", "<default-literal>")`.
5. **Cache resumable** : réutiliser le pattern JSON checkpoint d'Argumentum pour
   qu'un run interrompu reprenne où il s'est arrêté (utile sur un catalogue de
   milliers de cellules).
6. **Préservation HTML byte-for-byte** : la prose CoursIA est riche en balises
  (`<sub>`, `<sup>`, `<br>`, entités `&nbsp;`/`&amp;`). Le system prompt
  Argumentum est la référence à conserver telle quelle.
7. **Anti-idle du coordinateur** : une fois T3 livré et activé, les resync CSV
  vides (cf. PRs #6929 #6939 #6943 #6945 #6947) n'ont plus de raison d'être
  livrées comme livrables autonomes — le drift se résout via le moteur, pas via
  des `git checkout` répétitifs de CSV.

## Livrables à venir (court + moyen terme)

- **PR #2** (court terme, post-cette-doc) : `scripts/translation/translate_csv.py`
  (~250 LOC), fork de `translate_game_rules.py` adapté au schéma CSV 21 colonnes
  CoursIA, `Enabled=false`, `--dry-run` par défaut, cache resumable, aucun token
  en clair. Test round-trip fixture-first.
- **PR #3** (moyen terme, gated GO user) : activation `Enabled=true` + token
  OpenAI live, premier run sur 1 CSV test (ex. Search-8 DancingLinks ou SMT
  z3-api), proof 7 langues produites, audit drift post-run = `TRAD_DRIFT = 0`.
- **T4** : re-import notebook — patcher les `xxx_<lang>.ipynb` depuis le CSV
  traduit (regex sur `cell_id` + replace body), re-exécution Papermill
  (cf. [notebook-conventions.md](../../.claude/rules/notebook-conventions.md) C.2),
  commit avec outputs.
- **CI gate** (analogue `catalog-drift.yml`) : si un CSV a `text_fr` rempli mais
  `text_en` vide sans marqueur `_todo` → FAIL. Empêche le retour à l'état
  antérieur (resync vides).

## Hors scope (à NE PAS toucher)

- **Submodule pointer Argumentum** déjà à jour (`7e72f3e5d` = v0.9.0, synchro
  origin/master). Pas de MAJ.
- **Moteur .NET `DatasetUpdater/*.cs`** : couplé `.sln` + `Cards/*`, on ne copie
  pas.
- **PRs de sync CSV individuelles** `#6929 #6939 #6943 #6945 #6947` : ne pas
  contester (= cleanup fixtures utile), mais à l'avenir gating sur T3 forked
  avant toute nouvelle resync.

## Liens

- Issue : #6949 (T3 moteur de traduction — fork Argumentum)
- Epic parent traduction : #1650 (gating Phase 1)
- Epic CSV sync : #4957 (infra T1/T2 livrée)
- Sibling design doc : [CSV-by-series-design.md](CSV-by-series-design.md)
- PRs resync vides (exemples du problème) : #6929 #6939 #6943 #6945 #6947

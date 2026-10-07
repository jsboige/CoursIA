# Banc de référence TTS — schéma v1, append idempotent

> Cadrage : issue [#19695](https://github.com/jsboige/CoursIA/issues/19695) — `feat(audio): banc de référence persistant des moteurs TTS : accumulate wer/RTF/VRAM par (motor, extract, seed) pour les runs à venir`. Dispatch coordinateur `ai-01` posé le 07/10/2026 09:08Z sur la lane `myia-po-2027:CoursIA-2`. Échéance interne : avant les issues soeurs `CosyVoice3 #19692` et `S2 Pro local #19694`.

## Pourquoi un banc ?

Chaque campagne de mesure TTS du cluster (`bakeoff_small/measure_*.py`, `bakeoff_large/banc_phase_a0.py`, `p7_verify.py`) produit un JSON isolé. Sans schéma persistant :

- **Pas de cumul** : les chiffres WER/RTF/VRAM d'un run sont perdus quand la campagne se ferme.
- **Pas de comparaison cross-campagne** : impossible de répondre à « ce moteur est-il meilleur que cet autre sur l'extrait Boule de Suif ? » au-delà du run qui les a mesurés.
- **Signal de falsification faible** : un run qui dégrade sur le même extrait est invisible.

Le banc résout ces trois lacunes par :

1. Un **schéma versionné** (`bank_schema_v1.json`) qui fixe les champs et leur sémantique.
2. Un **append idempotent** (`bake_append.py`) : un upsert par clé `(motor, extract, seed)`.
3. Un **rapport à la demande** (`bake_report.py`) qui trie par WER/RTF/etc. et se poste sur l'issue de coordination — **non commité** dans l'arbre (les rapports vivent sur l'issue, pas dans le dépôt).

## Schéma v1 — `bank_schema_v1.json`

Champs :

| Champ | Type | Description |
|---|---|---|
| `ts` | string (ISO-8601 UTC) | Timestamp du run (collecte first-hand). |
| `machine` | enum | Lane : `myia-po-2027`, `myia-ai-01`, `myia-po-2024`, etc. |
| `motor` | string (snake_case) | Identifiant moteur (ex : `chatterbox_mtl_v3`, `qwen3_tts_12hz_1_7b_customvoice`). |
| `extract` | string | Identifiant extrait (`A`, `B`, `C`, etc.). |
| `seed` | integer | Graine de génération. |
| `wer` | number \| null | Word Error Rate (Levenshtein normalisé, 0.0–1.0). Null si ASR non chargé. |
| `rtf` | number \| null | Real-Time Factor = wallclock / duration_s. |
| `vram_mb` | integer \| null | VRAM pic en MB (null si CPU-only). |
| `duration_s` | number | Durée du clip rendu. |
| `voice_stable` | bool \| null | Verdict subjectif stabilité vocale (DRIFTING détecté par 3ASR). |
| `hallu_per_100_syl` | number \| null | Hallucinations par 100 syllabes. |
| `inserted_words` | integer \| null | Mots insérés par l'ASR (faux positifs, défaut CosyVoice3). |
| `omitted_segments` | integer \| null | Segments ≥3 mots absents de ≥2 ASR sur 3. |
| `asr_models` | array \| null | Modèles Whisper utilisés (`tiny`, `small`, `large-v3`, etc.). |
| `notes` | string \| null | Notes libres (≤ 200 chars par ingestion auto). |

**Unicité** : la clé `(motor, extract, seed)` est unique. Un second append avec la même clé **remplace** l'ancien (upsert), ne crée pas de doublon.

## `bake_append.py` — append idempotent

Trois formes d'usage :

```bash
# 1) Append d'un run isolé (JSON inline) :
python bake_append.py --bank runs/bake_bank.json --run '{
  "ts": "2026-10-08T01:00:00Z",
  "machine": "myia-po-2027",
  "motor": "chatterbox_mtl_v3",
  "extract": "A",
  "seed": 42,
  "wer": 0.4179,
  "duration_s": 17.4,
  "asr_models": ["tiny"]
}'

# 2) Append depuis un fichier JSON (un objet OU une liste) :
python bake_append.py --bank runs/bake_bank.json --file runs/new_run.json

# 3) Ingestion depuis un répertoire bakeoff_small (discovery auto) :
python bake_append.py --bank runs/bake_bank.json \
  --ingest-root MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/bakeoff_small/results
```

Codes de retour :

| Code | Sens |
|---|---|
| 0 | Succès (run ajouté ou remplacé). |
| 1 | Erreur de validation (champ manquant, type incorrect, enum invalide). |
| 2 | Aucun run fourni (`--run`/`--file`/`--ingest-root` tous absents). |
| 3 | IO erreur. |

## `bake_report.py` — rapport markdown trié

```bash
# Vers stdout :
python bake_report.py --bank runs/bake_bank.json --sort wer

# Vers un fichier (typiquement pour poster sur l'issue de coordination) :
python bake_report.py --bank runs/bake_bank.json --sort wer --out runs/bake-report-2026-10-08.md

# Filtre par moteur :
python bake_report.py --bank runs/bake_bank.json --motor chatterbox_mtl_v3
```

Sortie : tableau markdown trié par `--sort` (`wer` par défaut, `rtf`, `duration_s`, `ts`), avec un résumé `N run(s) / N moteur(s)` en tête et les notes par run en pied. Les runs dont le champ de tri est `null` apparaissent en fin de tableau.

**Le rapport n'est PAS commité** (cadrage coordinateur #19695 point 3). Il est généré à la demande et posté sur l'issue de coordination (`gh issue comment 19695 --body-file runs/bake-report-YYYY-MM-DD.md`).

## `test_bake_bank.py` — couverture des invariants

| Test | Vérifie |
|---|---|
| `test_schema_valid` | `bank_schema_v1.json` est un JSON-Schema syntaxiquement valide. |
| `test_append_dry_run_valid` | Dry-run accepte un run complet sans écrire. |
| `test_append_validation_failure` | Champ obligatoire manquant → rc=1. |
| `test_append_validation_type_error` | Type incorrect (`string` au lieu de `number`) → rc=1. |
| `test_append_idempotence` | 2 appends même clé = 1 ligne. |
| `test_append_upsert_updates_field` | 2ᵉ append remplace les champs du 1ᵉʳ (pas de doublon, maj des champs). |
| `test_report_format` | Tri `wer` croissant, `null` en fin, comptage en-tête. |
| `test_ingest_bakeoff_small` | Ingestion depuis `bakeoff_small/results` produit ≥4 runs. |

Sortie : `python test_bake_bank.py` → `8/8 passed` (c.1467).

**Câblage CI** : pas de gate bloquant (cadrage coordinateur #19695 point 4). Le test tourne dans la suite `Scripts & Notebook-Tools Tests` existante via le runner `Scripts Tests (CPU)`.

## Convention d'ingestion — bootstrap c.1467

Le banc est amorcé avec 6 runs mesurés first-hand :

| Moteur | Extract | Seed | WER | Source | Notes |
|---|---|---|---|---|---|
| `chatterbox_mtl_v3` | A | 42 | 41,79 % | bakeoff_small `bake_results.json` (PR #17661) | Run 24/09, Whisper-tiny. |
| `chatterbox_mtl_v3` | B | 42 | 25,00 % | bakeoff_small `bake_results.json` (PR #17661) | Run 24/09, Whisper-tiny. |
| `chatterbox_mtl_v3` | C | 0 | 93,65 % | A0C c.1462 (mesure ai-01) | DRIFTING détecté 3ASR, 2 omissions. Re-rendu chunked ordonné par ai-01 11:09Z 07/10 (#17586). |
| `qwen3_tts_12hz_1_7b_customvoice` | C | 0 | 32,94 % | A0C c.1462 (mesure ai-01) | Instruct « voix posée, débit lent » cause 5× inflation WER. |
| `pocket_tts` | A | 42 | — | bakeoff_small `A__pocket_tts.json` (PR #17661) | CPU run, Whisper-tiny non chargé (`wer_explanation`). |
| `pocket_tts` | B | 42 | — | bakeoff_small `B__pocket_tts.json` (PR #17661) | CPU run, Whisper-tiny non chargé. |

Le rapport bootstrap est dans `runs/bake-report-2026-10-08.md` (à la racine du worktree, **non commité**).

## Suite opérationnelle

| Cible | Dépendance | Statut |
|---|---|---|
| CosyVoice3 #19692 (pivot narrateur) | n'attend **pas** ce banc (cadrage coordinateur 07/10 point 1) | parallèle |
| S2 Pro local #19694 (dé-API-iser Fish Audio) | n'attend **pas** ce banc | parallèle |
| Issue UAT #17586 (gate pré-UAT) | dépendra du banc pour la non-régression WER (#15002 critère #3) | après remplissage |
| Re-rendu Chatterbox chunked #19739 (phase 2 garde ASR) | append direct après mesure (3ASR) | à venir |

## Anti-patterns interdits

- **Commiter un rapport** : les rapports vivent sur l'issue, pas dans l'arbre (cadrage coordinateur 07/10 point 3 + CLAUDE.md §A « rapports sur le dashboard, jamais dans le repo »).
- **Régénérer le catalogue** dans une PR touchant ce banc : voir [catalog-pr-hygiene.md](../../.claude/rules/catalog-pr-hygiene.md).
- **Bypasser la validation schéma** (`--strict` non respecté, JSON inline invalide) : le test unitaire détecte ces cas.
- **Append de runs avec secrets / chemins absolus Windows** dans `notes` : la note doit être < 200 chars et ne pas contenir de chemins machine (cf [secrets-hygiene.md](../../.claude/rules/secrets-hygiene.md)).

## Pointeurs

- Schéma : [bank_schema_v1.json](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/bank_schema_v1.json)
- Append : [bake_append.py](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/bake_append.py)
- Rapport : [bake_report.py](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/bake_report.py)
- Test : [test_bake_bank.py](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/test_bake_bank.py)
- Issue parente : [#19695](https://github.com/jsboige/CoursIA/issues/19695)
- EPIC parent : [#1028](https://github.com/jsboige/CoursIA/issues/1028) (recette UAT Audiobook)

— daté 2026-10-08, lane `myia-po-2027:CoursIA-2`, cycle c.1467
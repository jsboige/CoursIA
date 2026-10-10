# Banc de référence persistant des moteurs TTS

**Issue** : [#19695](https://github.com/jsboige/CoursIA/issues/19695)
**Schéma** : `prosody_lab/bank_schema_v1.json`
**Outils** : `prosody_lab/bake_append.py` · `prosody_lab/bake_report.py` · `prosody_lab/bootstrap_bank.py`
**Tests** : `prosody_lab/test_bake_bank.py`

## À quoi ça sert

Chaque campagne de mesure TTS (`bakeoff_small/measure_*.py`, `bakeoff_large/banc_phase_a0.py`, re-rendus UAT sur `G:/Mon Drive/MyIA/Projets/BibliothequesSonores/A0-review-*`) produit un JSON isolé. **Avant le banc**, ces silos ne se cumulent pas : impossible de dire « PocketTTS est meilleur que CosyVoice3 sur la famille Boule de Suif » sans rouvrir chaque fichier un par un.

**Avec le banc** : un fichier `bake_bank.json` (**tableau JSON**, un objet par run) cumule les runs par `(motor, extract, seed)`.

**Soclage** : le socle d'écriture (`bake_append.py`, `bake_report.py`, `bank_schema_v1.json` requis) vient du socle durci mergé par #19820 ; cette PR (#19722) porte la couche étendue — ingestion bootstrap (`bootstrap_bank.py`) et champs optionnels de fidélité/prosodie/traçabilité moteur. **Deux vocabulaires de fidélité coexistent** dans le schéma : celui du socle (`inserted_words`, `omitted_segments`, `voice_stable`, `hallu_per_100_syl`) et les champs étendus du banc TTS (gate pré-UAT #17586 : `fidelity_added_words` 0 = pass, `fidelity_omitted_segments_3plus` 0 = pass, `voice_consistent` true = pass). Les deux sont optionnels : un run du socle seul reste valide.

## Schéma v1

| Champ | Type | Description |
|---|---|---|
| `schema_version` | const `"v1"` | Version figée. Évolutions → v2/v3, jamais casser v1. |
| `ts` | ISO 8601 UTC | Timestamp du run. |
| `machine` | enum | `myia-po-2023`, `myia-po-2024`, `myia-po-2025`, `myia-po-2026`, `myia-po-2027`, `myia-ai-01`, `other`. |
| `motor` | string | Identifiant normalisé (ex. `qwen3_tts_1_7b_customvoice`). |
| `motor_size_b` | number | Taille en milliards de paramètres. |
| `motor_license` | string SPDX | Licence (Apache-2.0, MIT, Research-Only, etc.). |
| `extract` | enum A-E | Identifiant du passage de référence (A=erreur narratif, B=dramatique, C-E=à venir). |
| `extract_text_sha256_prefix` | hex 16 | Verrou anti-réécriture silencieuse du texte. |
| `seed` | int ou null | Graine de sampling (null si non applicable). |
| `wer` | float | Word Error Rate mesuré (0.0 = parfait). |
| `wer_model` | string | Modèle ASR utilisé (`openai/whisper-large-v3`, etc.). |
| `rtf` | float | Real-Time Factor (audio/wallclock). |
| `vram_mb` | float | Pic VRAM (Mo). |
| `duration_s` | float | Durée audio synthétisée. |
| `fidelity_added_words` | int | Mots ajoutés au-delà du ref (0 = pass). |
| `fidelity_omitted_segments_3plus` | int | Segments 3+ mots omis sous ≥2 ASR/3 (0 = pass). |
| `voice_consistent` | bool | Voix stable sur la durée (true = pass). |
| `hallu_per_100_syl` | float | Densité d'hallucinations par 100 syllabes. |
| `inserted_words` | int | Mots insérés par l'ASR (vocabulaire socle #19820). |
| `omitted_segments` | int | Segments ≥3 mots absents de ≥2 ASR/3 (vocabulaire socle #19820). |
| `voice_stable` | bool | Stabilité vocale, verdict 3-ASR (vocabulaire socle #19820). |
| `notes` | string ≤ 2000 | Notes libres. |
| `source_path` | string | Chemin source ingéré (traçabilité bootstrap). |

## Usage

### Bootstrap (ingestion des sources existantes)

```bash
python prosody_lab/bootstrap_bank.py --bank prosody_lab/bake_bank.json
# mode dry-run pour tester sans écrire :
python prosody_lab/bootstrap_bank.py --bank prosody_lab/bake_bank.json --dry-run
# limiter à une source (bakeoff_small | bakeoff_large | gdrive | all) :
python prosody_lab/bootstrap_bank.py --bank prosody_lab/bake_bank.json --source bakeoff_small
```

Le bootstrap scanne `bakeoff_small/results/`, `bakeoff_large/results/` et `BibliothequesSonores/A0-review-*`, mappe chaque JSON vers un run (socle + champs étendus présents) et **délègue l'écriture à `bake_append.py` du socle** (CLI `--run`). Les types hétérogènes entre campagnes sont normalisés (`size` `"0.5B"` → `0.5`, `g_st_range`/`g_cv` → `prosody_*`, sous-dicts GDrive `wer.wer`/`seed.base`/`synth.*` aplatis, graphie moteur ramenée en snake_case). Idempotent : l'upsert de `bake_append.py` par `(motor, extract, seed)` remplace un run de même clé au lieu de le dupliquer.

### Append manuel (un run isolé)

```bash
python prosody_lab/bake_append.py \
    --bank prosody_lab/bake_bank.json \
    --machine myia-po-2023 \
    --run '{
      "ts": "2026-10-10T12:00:00Z",
      "machine": "myia-po-2023",
      "motor": "qwen3_tts_1_7b_customvoice",
      "extract": "A",
      "seed": 42,
      "duration_s": 14.2,
      "wer": 0.08,
      "motor_license": "Apache-2.0",
      "source_path": "runs/run-20260924-143012/A0C-bakeoff/qwen3_tts_customvoice/metrics.json"
    }'
```

Autres modes du socle : `--run fichier.json` (chemin vers un fichier JSON), `--file` (objet ou liste), `--ingest-root` (scan d'un répertoire de résultats), `--dry-run`, `--strict`.

### Lecture (gate #17586)

```bash
# Sortie stdout
python prosody_lab/bake_report.py --bank prosody_lab/bake_bank.json
# Écriture fichier (NON versionnée — usage local)
python prosody_lab/bake_report.py --bank prosody_lab/bake_bank.json \
    --out /tmp/bake_report_$(date +%Y%m%d-%H%M).md
```

Le tableau est trié par `extract` (A→E), secondaire par `WER` croissant, tertiaire par `motor`.

### Tests unitaires (suite CI existante — décision ai-01 sur #19695)

```bash
python MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/test_bake_bank.py
```

Script autonome (exit 0/1), collecté par la jambe `Scripts Tests (CPU)` de `.github/workflows/scripts-tests.yml` — ses fichiers-sujets (`bake_append.py`, `bake_report.py`, `bootstrap_bank.py`, `bank_schema_v1.json`) sont dans ses déclencheurs `paths:`. Pas de nouveau workflow CI bloquant (décision ai-01).

13 cas : schéma valide, dry-run valide, échecs de validation (champs manquants, type, enum union), idempotence, upsert, tri du rapport (WER, chrono `--sort ts`), ingestion bakeoff_small, **couche #19722** (champs étendus optionnels au schéma, mapping `bootstrap_bank._metrics_to_run`, décodeurs GDrive).

## Hook best-effort dans p7_verify

`p7_verify` (le runner de mesure du pipeline v4) appelle optionnellement `bake_append.py` à la fin de chaque run. L'échec d'ingestion **n'arrête pas** la mesure : c'est un signal, pas un gate.

```python
# p7_verify.py (pseudo-code)
result = measure_pipeline(...)
try:
    subprocess.run(["python", "prosody_lab/bake_append.py",
                    "--bank", "prosody_lab/bake_bank.json",
                    "--run", json.dumps({
                        "ts": result.ts, "machine": result.machine,
                        "motor": result.motor_id, "extract": result.extract_id,
                        "seed": result.seed, "duration_s": result.duration_s,
                        "wer": result.wer, "source_path": result.metrics_path,
                    }, ensure_ascii=False)],
                    check=False, timeout=30)
except Exception as e:
    log.warning(f"bake_append a échoué : {e}")
```

## Critères d'acceptance

1. **Schéma versionné** (`bank_schema_v1.json`) commité, avec champs typés et commentaires. ✅
2. **Au moins 6 runs ingérés** (3 moteurs × 2 extraits) au moment de la PR.
3. **Rapport markdown** généré, trié par WER. NON commité (lecture locale).
4. **CI** : vérif schéma et unicité via `pytest test_bake_bank.py` — **pas** de nouveau workflow CI (décision ai-01).
5. **Documentation** : ce README (usage, schéma, comment rejouer une mesure). ✅

## Pré-requis pour les 2 autres issues audio

- **#19692** (CosyVoice3 pivot narrateur) : banc d'entrée `extract=A` au moment du pivot.
- **#19694** (S2 Pro local) : banc d'entrée `extract=B` au moment du dé-API.

Ces deux issues sont **bloquées** par la disponibilité d'au moins 1 run par `(motor, extract)` à comparer.

## Anti-patterns

- **Modifier le schéma v1** : casserait la rétrocompat. Évolutions = v2.
- **Committer le rapport** : comme "preuve" — l'audit peut le régénérer via la commande, le diff d'un rapport n'est pas un signal de progression.
- **Ajouter une colonne au CSV sans version** : la table ne se lit qu'en tableau JSON validé par le schéma, ou alors exporter en CSV via un script dédié (out of scope v1).
- **Sauter la validation `jsonschema`** : le validateur interne est un filet, pas la garantie principale. Si jsonschema n'est pas disponible, `pip install jsonschema` dans le venv avant la première ingestion.

# Banc de référence persistant des moteurs TTS

**Issue** : [#19695](https://github.com/jsboige/CoursIA/issues/19695)
**Schéma** : `prosody_lab/bank_schema_v1.json`
**Outils** : `prosody_lab/bake_append.py` · `prosody_lab/bake_report.py` · `prosody_lab/bootstrap_bank.py`
**Tests** : `prosody_lab/test_bake_bank.py`

## À quoi ça sert

Chaque campagne de mesure TTS (`bakeoff_small/measure_*.py`, `bakeoff_large/banc_phase_a0.py`, re-rendus UAT sur `G:/Mon Drive/MyIA/Projets/BibliothequesSonores/A0-review-*`) produit un JSON isolé. **Avant le banc**, ces silos ne se cumulent pas : impossible de dire « PocketTTS est meilleur que CosyVoice3 sur la famille Boule de Suif » sans rouvrir 5 fichiers.

**Avec le banc** : un fichier `bake_bank.jsonl` cumule les runs par `(motor, extract, seed)`, avec les **champs de fidélité** (gate pré-UAT #17586) : `fidelity_added_words` (0 = pass), `fidelity_omitted_segments_3plus` (0 = pass), `voice_consistent` (true = pass).

## Schéma v1

| Champ | Type | Description |
|---|---|---|
| `schema_version` | const `"v1"` | Version figée. Évolutions → v2/v3, jamais casser v1. |
| `ts` | ISO 8601 UTC | Timestamp du run. |
| `machine` | enum | `myia-po-2023`, `myia-po-2024`, `myia-po-2025`, `myia-po-2026`, `myia-po-2027`, `myia-ai-01`, `myia-web2`. |
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
| `notes` | string ≤ 2000 | Notes libres. |
| `source_path` | string | Chemin source ingéré (traçabilité bootstrap). |

## Usage

### Bootstrap (ingestion des sources existantes)

```bash
python prosody_lab/bootstrap_bank.py --bank prosody_lab/bake_bank.jsonl
# mode dry-run pour tester sans écrire :
python prosody_lab/bootstrap_bank.py --bank prosody_lab/bake_bank.jsonl --dry-run
```

Le bootstrap scanne `bakeoff_small/results/`, `bakeoff_large/results/` et `BibliothequesSonores/A0-review-*`. Idempotent : un run déjà présent (clé `motor+extract+sha256+seed+ts`) est sauté sans erreur.

### Append manuel (un run isolé)

```bash
python prosody_lab/bake_append.py \
    --bank prosody_lab/bake_bank.jsonl \
    --metrics runs/run-20260924-143012/A0C-bakeoff/qwen3_tts_customvoice/metrics.json \
    --machine myia-po-2023 \
    --motor qwen3_tts_1_7b_customvoice \
    --extract A \
    --motor-license Apache-2.0 \
    --source-path runs/.../metrics.json
```

### Lecture (gate #17586)

```bash
# Sortie stdout
python prosody_lab/bake_report.py --bank prosody_lab/bake_bank.jsonl
# Écriture fichier (NON versionnée — usage local)
python prosody_lab/bake_report.py --bank prosody_lab/bake_bank.jsonl \
    --out /tmp/bake_report_$(date +%Y%m%d-%H%M).md
```

Le tableau est trié par `extract` (A→E), secondaire par `WER` croissant, tertiaire par `motor`.

### Tests unitaires (pas de workflow CI dédié — décision ai-01 sur #19695)

```bash
# unittest
python -m unittest prosody_lab/test_bake_bank.py -v
# pytest
python -m pytest prosody_lab/test_bake_bank.py -v
```

8 cas : record minimal, full record, enum invalide, hash invalide, champ non-autorisé, schema_version ≠ v1, idempotence, tri du rapport, rapport vide.

## Hook best-effort dans p7_verify

`p7_verify` (le runner de mesure du pipeline v4) appelle optionnellement `bake_append.py` à la fin de chaque run. L'échec d'ingestion **n'arrête pas** la mesure : c'est un signal, pas un gate.

```python
# p7_verify.py (pseudo-code)
result = measure_pipeline(...)
try:
    subprocess.run(["python", "prosody_lab/bake_append.py",
                    "--bank", "prosody_lab/bake_bank.jsonl",
                    "--metrics", result.metrics_path,
                    "--motor", result.motor_id,
                    "--extract", result.extract_id,
                    "--source-path", result.metrics_path],
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
- **Ajouter une colonne au CSV sans version** : la table ne se lit qu'en JSONL avec validation jsonschema, ou alors exporter en CSV via un script dédié (out of scope v1).
- **Sauter la validation `jsonschema`** : le validateur interne est un filet, pas la garantie principale. Si jsonschema n'est pas disponible, `pip install jsonschema` dans le venv avant la première ingestion.
# a0c_rerun — scripts de re-rendu A0C pour gate pré-UAT #17586

## Cadrage (audio c.1467, DM ai-01 11:09 le 07/10)

Suite à l'audit de la mesure A0C précédente (c.1462) :

- **Qwen3-TTS-12Hz-1.7B-CustomVoice** : 5× inflation "débit lent" sur le WER, trace de l'instruct « voix posée, débit lent, ton narratif » passé au modèle.
- **Chatterbox Multilingual V3** : 93,65 % WER, voice DRIFTING, hallucination `« Ah, blâme ! Moi... »`, **2 segments omis** sous 3 ASR sur 3 (« des artilleurs sombres alignés avec des fantassins divers », « sur leurs épaules de fanfarons »).

Re-rendu A0C ordonné par ai-01 :

- Qwen3-TTS en réglage **NEUTRE** (sans « débit lent »).
- Chatterbox **découpé par phrase** avec un wav de référence.
- Mesure : WER sur 3 ASR (tiny / small / large-v3), prosodie, omissions (segments ≥ 3 mots omis sous ≥ 2 ASR sur 3).
- Délai : avant 08/10 18:00 (date annoncée à l'association).

## Scripts

| Fichier | Rôle | Venv | GPU |
|---|---|---|---|
| `rerun_a0c_neutral_qwen3.py` | Synthèse Qwen3-TTS CustomVoice **sans --instruct** (neutre) | `venv-qwen3tts` | cuda |
| `rerun_a0c_chatterbox_chunked.py` | Synthèse Chatterbox MTL v3 **découpée par phrase** + ref_wav = phrase 1 | `venv` | cuda |
| `measure_3asr.py` | WER sur 3 ASR (tiny / small / large-v3) + détection d'omissions | `venv` | cuda (tiny/small OK CPU) |

## Pipeline complet

```bash
# 1) Préparer le dossier de revue (côté GDrive, hors dépôt)
mkdir -p "G:/Mon Drive/MyIA/Projets/BibliothequesSonores/A0-review-20261007"
cp "G:/Mon Drive/MyIA/Projets/BibliothequesSonores/A0-review-20261006/extract_C_long_narration.txt" \
   "G:/Mon Drive/MyIA/Projets/BibliothequesSonores/A0-review-20261007/"

# 2a) Re-rendu Qwen3-TTS neutre (charge 1.7B, ~3-4 GB VRAM, ~5-10 min)
cd D:/dev/CoursIA-2
./venv-qwen3tts/Scripts/python.exe \
  MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/a0c_rerun/rerun_a0c_neutral_qwen3.py \
  --text-file "G:/Mon Drive/MyIA/Projets/BibliothequesSonores/A0-review-20261007/extract_C_long_narration.txt" \
  --out-dir "G:/Mon Drive/MyIA/Projets/BibliothequesSonores/A0-review-20261007" \
  --speaker serena --language French --device cuda --dtype bf16

# 2b) Re-rendu Chatterbox chunked (à lancer APRÈS le Qwen3, GPU partagé)
./venv/Scripts/python.exe \
  MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/a0c_rerun/rerun_a0c_chatterbox_chunked.py \
  --text-file "G:/Mon Drive/MyIA/Projets/BibliothequesSonores/A0-review-20261007/extract_C_long_narration.txt" \
  --out-dir "G:/Mon Drive/MyIA/Projets/BibliothequesSonores/A0-review-20261007" \
  --lang fr --device cuda

# 3) Mesure 3 ASR (à lancer après CHAQUE rendu, met à jour metrics.json)
./venv/Scripts/python.exe \
  MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/a0c_rerun/measure_3asr.py \
  --wav "G:/Mon Drive/MyIA/Projets/BibliothequesSonores/A0-review-20261007/A0C-qwen3tts-customvoice-neutral.wav" \
  --ref-text-file "G:/Mon Drive/MyIA/Projets/BibliothequesSonores/A0-review-20261007/extract_C_long_narration.txt" \
  --metrics-json "G:/Mon Drive/MyIA/Projets/BibliothequesSonores/A0-review-20261007/A0C-qwen3tts-customvoice-neutral-metrics.json" \
  --asr-models tiny small large-v3
```

## Sortie

Pour chaque run, dans `A0-review-20261007/` :

- `A0C-qwen3tts-customvoice-neutral.wav` (+ `-metrics.json`)
- `A0C-chatterbox-mtl-v3-chunked.wav` (+ `-metrics.json`)

Le `metrics.json` est enrichi en place par `measure_3asr.py` :

- `wer.by_model` : WER tiny / small / large-v3, hyp complet, durée de transcription.
- `omissions` : segments ≥ 3 mots absents de ≥ 2 ASR sur 3, avec liste des ASR où l'absence est constatée.
- `prosody` : à mesurer par `verify_prosody.py` (gate pré-UAT ne dépend pas que de WER).

## Verdict attendu vs. mesure c.1462

| Mesure | c.1462 | Re-rendu attendu |
|---|---|---|
| Qwen3-TTS WER (tiny) | 32,94 % (5× inflation "débit lent") | < 15 % (sans l'instruct qui fabrique l'amplification) |
| Chatterbox WER (tiny) | 93,65 % (DRIFTING, hallucination) | < 30 % (chunking + ref_wav doivent stabiliser) |
| Omissions Chatterbox | 2 segments omis (3 ASR sur 3) | 0 ou 1 (chunking par phrase ne saute plus) |

## Acceptance

- [ ] Qwen3-TTS neutre livré (WAV + metrics.json enrichi 3ASR)
- [ ] Chatterbox chunked livré (WAV + metrics.json enrichi 3ASR)
- [ ] Verdict gate pré-UAT #17586 sur les 2 mesures (pass / fail par moteur)
- [ ] DM ai-01 avec les chiffres + dépôt `A0-review-20261007/`

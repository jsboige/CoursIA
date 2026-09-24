# bakeoff_small — Phase A0 banc TTS modèles tenant sur 8 GB

Banc de mesure pour les modèles TTS Open Weights qui tiennent sur un GPU
8 GB (RTX 4060). Driver distinct de `bench.py` (matrix lourde FishAudio /
Qwen VoiceDesign / Higgs / Kokoro / OpenAI) : ici on vise **un seul
modèle à la fois en VRAM**, swap entre cellules, mesures via les mêmes
instruments `prosody_metrics` + `syllable_pitch`.

## Modèles ciblés (4 cellules)

| ID | Modèle | Taille | Licence | HF |
|---|---|---|---|---|
| `chatterbox_mtl_v3` | Chatterbox Multilingual V3 (Resemble AI) | 0.5B | Apache-2.0 | `ResembleAI/chatterbox-multilingual` |
| `kyutai_tts_1_6b` | Kyutai tts-1.6b-en_fr | 1.6B | CC-BY-4.0 | `kyutai/tts-1.6b-en_fr` |
| `pocket_tts` | pocket-tts (kyutai-labs) | 100M | Apache-2.0 | `kyutai/pocket-tts` |
| `fun_cosyvoice_3_0_5B` | Fun-CosyVoice 3.0 (FunAudioLLM) | 0.5B | Apache-2.0 | `FunAudioLLM/Fun-CosyVoice-3.0-0.5B` |

## Usage

```bash
# Lister les cellules et leurs deps
python bake.py --list

# Test fumé sur Chatterbox seul (env check)
python bake.py --extracts A --cells chatterbox_mtl_v3 --quick --no-wer

# Banc complet sur les 4 modeles (A0)
python bake.py --extracts A B --cells all --gdrive-root "G:\\Mon Drive\\MyIA\\Projets\\BibliothequesSonores\\run-20260924-093628\\A0-bakeoff"
```

## Sortie par cellule

Pour chaque couple (extract, client) :

- `<cell>.wav` — clip rendu (16 kHz mono PCM côté driver, 24 kHz natif Chatterbox)
- `<cell>.json` — métriques `prosody_metrics` + `syllable_pitch` + WER Whisper-tiny
- `<cell>.log` — stdout / stderr du client

Destination GDrive par défaut :
`G:\Mon Drive\MyIA\Projets\BibliothequesSonores\run-20260924-093628\A0-bakeoff\`

Fallback (GDrive inaccessible) : `outputs/bakeoff_small/` à côté de ce dossier.

## État au 2026-09-24

| Client | Import | Load (CUDA) | Generate | Mesures prosody | WER |
|---|---|---|---|---|---|
| Chatterbox MTL V3 | ✅ | ✅ | ✅ (smoke OK) | ✅ | ✅ |
| Kyutai tts-1.6b | ⚠️ pkg absent | — | — | — | — |
| pocket-tts | ⚠️ pkg absent | — | — | — | — |
| Fun-CosyVoice 3.0 | ⚠️ pkg absent | — | — | — | — |

**Seul Chatterbox est mesurable de bout en bout à ce jour.** Les 3
autres clients exposent un skeleton `warm()` qui retourne `None` avec
un log explicite tant que les packages manquent (`moshi` / `pocket-tts`
/ CosyVoice). L'installation de chaque package se fait via
`pip install moshi-tts`, `pip install pocket-tts`, ou
`git+https://github.com/FunAudioLLM/CosyVoice`.

## Acceptance (issue #17586 Phase A0)

- [ ] Chatterbox mesuré sur A + B (1 WAV + 1 JSON + WER)
- [ ] Kyutai installé + mesuré sur A + B
- [ ] pocket-tts installé + mesuré sur A + B
- [ ] Fun-CosyVoice installé + mesuré sur A + B
- [ ] Tableau comparatif `prosody_metrics` × `WER` × vitesse de rendu
- [ ] 1 ligne par modèle postée en commentaire sur #17586

## Hors scope

- Réécriture des clients v4 (FishAudio, Qwen, etc.) : leur scope reste
  `prosody_lab/` parent, géré par `myia-po-2023:CoursIA-2`.
- Tuning d'hyperparamètres au-delà du mode expressif par défaut.
- Comparaison avec les modèles >8 GB (Qwen VoiceDesign 7B, Higgs v3,
  Kokoro 82M, OpenAI gpt-4o-mini-tts) — c'est le scope `bench.py` parent.

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
| Chatterbox MTL V3 | ✅ | ✅ (3.07 GB VRAM FP16) | ✅ | ✅ | ✅ |
| Kyutai tts-1.6b | ⚠️ pkg absent | — | — | — | — |
| pocket-tts | ⚠️ pkg absent | — | — | — | — |
| Fun-CosyVoice 3.0 | ⚠️ pkg absent | — | — | — | — |

## Mesures Chatterbox Multilingual V3 (first-hand, 2026-09-24)

Pipeline : `ChatterboxMultilingualTTS.from_pretrained("cuda")` + `generate(text, language_id="fr")` à 24 kHz mono.

| Extrait | WER | ST range | CV | Velocity st/s | n_syll | motion st/syll | flat% | Verdict global | Verdict syllable |
|---|---|---|---|---|---|---|---|---|---|
| A narration (451 chars) | 0.418 | 15.47 st | 0.296 | 33.15 | 51 | 6.05 | 8.0% | EXPRESSIVE | INSUFFICIENT |
| B dialogue (423 chars) | 0.250 | 15.87 st | 0.33 | 23.61 | 63 | 2.94 | 33.9% | EXPRESSIVE | EXPRESSIVE |

**Constats** :
- Contour global (ST range, velocity) sort **EXPRESSIVE** sur les deux extraits — le modèle module effectivement.
- Syllable motion : 6.05 st/syll sur A (fort), 2.94 sur B (moyen). Mais flat% élevé sur B (33.9 %) indique des passages syllabe-à-syllabe monotones dans le dialogue.
- WER 0.418 sur A est élevé — l'hypothèse Whisper-tiny déraille dès la 2e phrase ("dès l'embeau d'armée en déroute à fait traverser" au lieu de "des lambeaux d'armée en déroute avaient traversé"). À vérifier si c'est (a) Chatterbox qui produit mal, ou (b) Whisper-tiny qui hallucine sur audio Chatterbox.

**Fichiers JSON mesurable dans `results/chatterbox_mtl_v3/`** :
- `bake_results.json` (métriques + WER + transcription partielle, **schéma inchangé** depuis PR #17661 v1)
- ~~`A__chatterbox_mtl_v3.wav` (835 KB, 17.4 s)~~ — **retiré** au commit `2c817263` (mandat ai-01 strict : « ne commite aucun audio »). Régénérable via `python -m bakeoff_small.measure_chatterbox_mtl_v3 --extract-dir <chemin> --out-dir results/chatterbox_mtl_v3 --device cuda --seed 42` (helper `compute_wer_for_wav` ajouté c.870 dans `bakeoff_small.bake`, lève l'`ImportError` de la v1).
- ~~`B__chatterbox_mtl_v3.wav` (1.01 MB, 21.0 s)~~ — **retiré**, même motif, même commande.

## Acceptance (issue #17586 Phase A0)

- [x] Chatterbox Multilingual V3 mesuré sur A + B (JSON + WER ; **WAV retirés du dépôt**, régénérables via `measure_chatterbox_mtl_v3.py`)
- [ ] Kyutai tts-1.6b installé + mesuré (`pip install moshi-tts` ou `git+https://github.com/kyutai-labs/delayed-streams-modeling`) — verdict **RECOVERABLE-MACHINE** (CDN HF xet-bridge Read timed out, voir Tell c.805 ★★★)
- [ ] pocket-tts installé + mesuré (`pip install pocket-tts`) — banc CPU first-hand livré (résultats A + B dans `results/pocket_tts/`, `wer: null` documenté par `wer_explanation` : Whisper-tiny non chargé au run CPU c.805 ; re-générable via `measure_pocket_tts.py` créé c.870)
- [ ] Fun-CosyVoice 3.0 installé + mesuré (`git+https://github.com/FunAudioLLM/CosyVoice`) — verdict **RECOVERABLE-MACHINE** (4.5 GB total + clone branche 3.0 manuel)
- [x] Tableau comparatif partiel (Chatterbox seul pour cette PR)
- [x] 1 ligne Chatterbox postée sur #17586

## Hors scope

- Réécriture des clients v4 (FishAudio, Qwen, etc.) : leur scope reste
  `prosody_lab/` parent, géré par `myia-po-2023:CoursIA-2`.
- Tuning d'hyperparamètres au-delà du mode expressif par défaut.
- Comparaison avec les modèles >8 GB (Qwen VoiceDesign 7B, Higgs v3,
  Kokoro 82M, OpenAI gpt-4o-mini-tts) — c'est le scope `bench.py` parent.

## Notes techniques

- `torchcodec 0.16.0` (la cible officielle de `torchaudio.save` Chatterbox) demande torch 2.6.x — incompatible avec notre torch 2.13.0+cu126. Solution : `soundfile.write` (libsndfile, indépendant de torch).
- Le forcing EOS Chatterbox coupe le sampling au token 435/1000 (A) ou 526/1000 (B) — repetition detection ou long_tail, pas une fin de phrase. Le WAV produit est incomplet (le texte source a plus de mots que ce qui est prononcé).
- VRAM Chatterbox Multilingual : 3.07 GB FP16 sur RTX 4060 8 GB. Reste 5 GB libre pour les 3 autres modèles séquentiellement.

# Shortlist modèles TTS — Phase A0 EPIC #1028 / Issue #17586

**Filtres** : poids ouverts · VRAM pic ≤ 24 GB (cible RTX 3090) · français natif ou multilingue · expressivité narrateur.

**Statut** : veille **complète** c.815 (sub-agent haiku `a19c5213ede6a3ba3`, durée 117 s, 27 tool_uses, evidence-cited Tell c.c.c.d.G.1 ★★★★).

## Modèles déjà mesurés dans le dépôt (références — pas de nouveau banc)

| Modèle | Statut | Notes |
|---|---|---|
| FishAudio S2-Pro (cloné) | référence | voix clone, déjà dans `ab_engine_test.py` |
| Qwen3-TTS VoiceDesign (route narrator #15002/#15016) | référence | reroute narrateur |
| Kokoro 82M | référence | floor léger, déjà mesuré |
| Chatterbox | référence | déjà mesuré |
| Higgs Audio (v1) | référence | licence non commerciale à signaler |

## Shortlist A0 (veille c.815)

| Modèle | Repo HF | Params | VRAM pic | Langues (FR ?) | Licence | Voice cloning | Notes |
|---|---|---|---|---|---|---|---|
| **CosyVoice3-0.5B-2512** | [FunAudioLLM/Fun-CosyVoice3-0.5B-2512](https://huggingface.co/FunAudioLLM/Fun-CosyVoice3-0.5B-2512) | 0.5B | ~4-6 GB BF16 | **FR natif** (9 langues + 18 dialectes CN) | Apache-2.0 | Oui (zero-shot cross-lingual) | MAJ 2025/12 ; SOTA content consistency, prosodie naturelle, latence streaming 150 ms. **Cible A0 audiobooks.** |
| **Qwen3-TTS-12Hz-1.7B** | [Qwen/Qwen3-TTS-12Hz-1.7B](https://github.com/QwenLM/Qwen3-TTS) | 1.7B | ~8-10 GB BF16 (FA2) | **FR natif** (10 langues + dialectes CN) | Apache-2.0 | Oui (clone 3 s, ref audio local/URL/base64/numpy) | Release 2026-01 ; Voice Design par prompt NL, latence E2E 97 ms. **Concurrent direct FishAudio S2-Pro.** |
| **Qwen3-TTS-12Hz-0.6B** | [Qwen/Qwen3-TTS-12Hz-0.6B](https://github.com/QwenLM/Qwen3-TTS) | 0.6B | ~3-5 GB BF16 (FA2) | **FR natif** | Apache-2.0 | Oui (3 s clone) | Variante légère du 1.7B ; idéal pour bench A0 budget VRAM serré |
| **MOSS-TTS Local** | [OpenMOSS-Team/MOSS-TTS](https://huggingface.co/OpenMOSS-Team/MOSS-TTS) | 1.7B | ~8 GB BF16 | **FR natif** (20 langues) | Apache-2.0 | Oui (zero-shot court + continuation prefix) | Variante "Local" 1.7B ; collection maj 2026-07. Variante 8B ("Delay") au-dessus de 24 GB → exclue |
| **Zonos-v0.1-transformer** | [Zyphra/Zonos-v0.1-transformer](https://huggingface.co/Zyphra/Zonos-v0.1-transformer) | 2B | **6 GB+** (RTX 3000+) | **FR natif** (EN/JA/CN/FR/DE) | Apache-2.0 | Oui (zero-shot 10-30 s + audio prefix) | 44 kHz natif, RTF ~2× sur RTX 4090 ; contrôle fin pitch/rate/émotion. **Marge VRAM confortable sur 3090.** |
| **Higgs TTS 2 (3B-base)** | [bosonai/higgs-tts-2-3b-base](https://huggingface.co/bosonai/higgs-tts-2-3b-base) | 6B (3.6B LLM + 2.2B audio FFN) | ~14-18 GB BF16 | 4 langues (FR **non confirmé** sur la card) | CC-BY-NC-SA-4.0 | Oui (zero-shot + multi-speaker) | Seed-TTS SIM 67.70 (meilleur du comparatif), win-rate émotions 75.7 % vs gpt-4o-mini-tts. **Limite : non-commercial + FR à vérifier.** |
| **OuteTTS-1.0-1B** | [OuteAI/Llama-OuteTTS-1.0-1B](https://huggingface.co/OuteAI/Llama-OuteTTS-1.0-1B) | 1B (BF16) | ~6-8 GB | **FR natif** (high-tier) | CC-BY-NC-SA-4.0 (base Llama3.2) | Oui (one-shot 10 s) | 60 k h audio ; optimal 42 s/run (~32 s avec ref 10 s). **Non-commercial.** |
| **CosyVoice2-0.5B** | [FunAudioLLM/CosyVoice2-0.5B](https://huggingface.co/FunAudioLLM/CosyVoice2-0.5B) | 0.5B | ~4-6 GB | **FR natif** (9 langues) | Apache-2.0 | Oui (zero-shot cross-lingual) | Base 2024/12, maj 2025/08 (triton trtllm) ; **préférer CosyVoice3 si neuf OK** |

### Modèles écartés (et pourquoi)

- **Spark-TTS-0.5B** : FR non supporté (EN/CN uniquement), CC-BY-NC-SA-4.0. → [card](https://huggingface.co/SparkAudio/Spark-TTS-0.5B)
- **MeloTTS-French** : pas de voice cloning, prosodie plate (VITS2), orienté CPU. → [card](https://huggingface.co/myshell-ai/MeloTTS-French)
- **GPT-SoVITS v2/v3** : pas de FR natif dans la liste documentée (EN/JA/KO/Cantonais/CN). → [repo](https://github.com/RVC-Boss/GPT-SoVITS)
- **MetaVoice-1B-v0.1** : anglais uniquement. → [card](https://huggingface.co/metavoiceio/metavoice-1B-v0.1)
- **IndexTTS-2** : FR non confirmé sur la card ; papier 2025-06. → [card](https://huggingface.co/IndexTeam/IndexTTS-2)
- **Kyutai Pocket TTS** : CPU-only 100M, design on-device — utile pour notebook de comparaison CPU vs GPU, pas pour A0 GPU. → [card](https://huggingface.co/kyutai/pocket-tts)

## Recommandation banc A0 (3-4 slots prioritaires)

1. **CosyVoice3-0.5B-2512** — Apache-2.0, FR natif, zero-shot, SOTA 2025/12, ~5 GB VRAM.
2. **Qwen3-TTS-12Hz-1.7B** — Apache-2.0, VoiceDesign NL, clone 3 s, remplace FishAudio S2-Pro + Qwen3-TTS VoiceDesign existants.
3. **Zonos-v0.1-transformer** — Apache-2.0, 6 GB, contrôle émotion + pitch, RTF 2×.
4. *(option)* **Higgs TTS 2** — si la license CC-BY-NC-SA-4.0 est acceptable (audiobook interne cours = OK, redistribution publique = à arbitrer user).

## Plan de banc séquentiel

1. Installer l'env (règle F : pas de contournement) : `pip install -r bakeoff_large/requirements.txt` avec transformers, accelerate, torch>=2.5, etc.
2. Pour chaque modèle (1 PR par modèle) :
   - `clients/<modele>.py` (interface uniforme `synth(text, out_wav, **kwargs) -> dict`)
   - Banc via `python prosody_lab/ab_engine_test.py --model <modele> --extract A|B --out runs/<run-id>/A0-bakeoff/<modele>/`
   - Verdict plancher : `python scripts/tts_verification/verify_prosody.py --single <wav>` + WER Whisper
   - Une ligne par modèle sur #17586 dès mesurée
3. Aucun binaire audio dans le dépôt — tout sur GDrive `G:\Mon Drive\MyIA\Projets\BibliothequesSonores\<run-id>\A0-bakeoff\`
4. Rythme : 1 modèle par cycle (pas de lot), poster chaque mesure sur #17586.

## Sources citées (Tell c.c.c.d.G.1 ★★★★)

Toutes les URLs HuggingFace / GitHub sont vérifiées par le sub-agent. Données VRAM et params extraites des cards/model cards.

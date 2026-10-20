# Garde d'attaque par chunk — détection de l'onset-drop et re-roll ciblé

> Cadrage : issue [#19739](https://github.com/jsboige/CoursIA/issues/19739) — `feat(audio,#19692): phase 2 -- garde d'attaque ASR par chunk (onset-drop CV3 mesure, porte #17586 non conforme)`. Phase 1 : [PR #19699](https://github.com/jsboige/CoursIA/pull/19699) (organe `p7`, vote 2/3 ASR). Phase 2 CPU : [PR #19829](https://github.com/jsboige/CoursIA/pull/19829) (`corpus_damage_chunk.py`, classification des spans déjà mesurés). **Cette étape : la garde elle-même, son plan de re-roll, et leur mesure sur un corpus réel.**

## Le défaut que la garde traque

CosyVoice3 peut rendre un chunk **en commençant au milieu du texte fourni** : la première proposition n'est jamais prononcée. C'est la signature d'un *onset-drop* — l'attaque du chunk disparaît du rendu.

Trois faits mesurés en phase 1, qui commandent la conception de la garde :

| Fait | Conséquence pour la garde |
|---|---|
| Le défaut est **graine-dépendant** (seg 57 : graines 4243/4244/4245) | un **re-roll** de la graine suffit ; il faut donc connaître le chunk fautif, pas seulement le segment |
| Le texte d'entrée est propre, la parole commence à t=0,0 | ce n'est pas une troncature de fichier : c'est le **moteur** qui ne dit pas le début |
| Un span d'omission qui commence au **mot 0** est la signature | la garde est un **cas particulier de l'organe d'omission p7**, pas un détecteur concurrent |

D'où la règle de conception : **la garde réutilise l'organe d'omission** (`v4.p7_verify._missing_word_spans`, `_normalize_words`) au lieu de réécrire une convention de comparaison. Un verdict « attaque manquante » et un span d'omission ne peuvent donc pas diverger.

## Ce que fait l'organe

`v4/attack_guard.py` — CPU pur, déterministe, sans réseau ni GPU.

### Le verdict

`detect_missing_attack(source_text, transcript)` répond par chunk, sur **un seul signal** : la **perte de tête**.

La perte de tête est le nombre de mots source perdus **sans trou depuis le mot 0**. C'est la définition opérationnelle d'un onset-drop : le rendu commence plus loin dans le texte source, donc ses premiers mots n'ont pas été prononcés. Elle est calculée en interrogeant l'organe d'omission p7 à `min_words=1` — pour isoler les groupes perdus — puis en prenant le groupe qui commence au mot 0, prolongé par les groupes qui enchaînent sans trou. L'alignement n'est pas réécrit : la garde mesure ce que mesure p7.

Le seuil est **3 mots**, celui de l'organe d'omission p7. C'est un choix délibéré : sous ce seuil, une faute de prononciation sur un mot n'est pas une attaque perdue, et une garde qui crierait au loup sur chaque rendu imparfait ne servirait à rien.

> **Un critère de *présence* ne suffit pas — mesuré.** Une première version jugeait l'attaque perdue sur la *présence* des mots de tête dans la transcription (au moins 3 absents sur les 12 premiers mots). Sur les rendus réels de la mesure ci-dessous, ce critère signalait **9 chunks sur 10** alors que leurs transcriptions commencent bien par le texte source : l'ASR se trompe sur quelques mots, et une absence *quelque part* n'est pas une attaque perdue. Le critère retenu est positionnel ; la séparation observée est 0/10 et 10/10.

### Le re-roll

`plan_reroll` produit la graine du re-roll avec la **formule de p5** : `seed + i + attempt * 104_729` (`i` = index du chunk dans le segment). L'`attempt` 0 reproduit la graine d'origine — un chunk sain ne bouge pas, seul un chunk fautif est perturbé. Le pas de 104 729 est celui de `p5_tts._CV3_RETRY_SEED_STRIDE` (premier, sans rapport avec `seed + seg_index`).

La garde s'insère dans la boucle de rendu de p5, qui re-roule déjà sur un plancher de durée : le point d'insertion est l'acceptation du chunk rendu, avant qu'il ne soit concaténé.

### Deux chemins d'ASR

| Mode | Chemin | Usage |
|---|---|---|
| `--asr http` | serveur Whisper local, `POST /v1/audio/transcriptions`, modèle `large-v3-turbo` — **même chemin que p7** | la machine qui porte les services du pipeline |
| `--asr local` | transformers local, `openai/whisper-large-v3-turbo` | mesure auto-portante, sans service à lever |

## Utilisation

```bash
# 1. decouper le corpus avec le chunker mesure de p5 (<= 280 caracteres)
python v4/prosody_lab/render_corpus_attack_guard.py --phase chunk \
    --out-dir out --paragraphs 6

# 2. rendre chaque chunk (GPU, moteur TTS reel)
python v4/prosody_lab/render_corpus_attack_guard.py --phase render \
    --out-dir out --engine chatterbox

# 3. transcrire chaque rendu
python v4/prosody_lab/render_corpus_attack_guard.py --phase asr --out-dir out

# 4. la garde statue, chunk par chunk
python -m v4.attack_guard --manifest out/chunks.json \
    --transcripts out/transcripts.json --out out/attack_report.json
```

Sur la machine qui porte le pipeline, l'étape 3 est remplaçable par le serveur Whisper : `--asr http` fait la transcription au moment de l'évaluation.

## Mesure

Mesure du 2026-10-19, GPU 2 de `myia-ai-01`, moteur et ASR réels.

| Étape | Choix | Sortie |
|---|---|---|
| Corpus | `MyIA.AI.Notebooks/GenAI/Audio/04-Applications/boule_de_suif_full.txt` (Maupassant, domaine public), 6 premiers paragraphes | ~1,8 k caractères |
| Découpe | chunker **mesuré** de p5 (`_chunk_narration`, ≤ 280 car., frontières de phrases) | 10 chunks |
| Rendu | **Chatterbox** (TTS réel), graine `42 + index`, `CUDA_VISIBLE_DEVICES=2`, sr 24 000 Hz | 10 wav, 7,7 s à 17,3 s |
| Contrôle positif | les **mêmes** rendus, amputés de leurs 1,5 premières secondes | 10 wav tronqués |
| Transcription | `openai/whisper-large-v3-turbo` (transformers, local), `language=fr` | 20 transcriptions |

Verdict de la garde, mesuré :

| Jeu | Chunks | Attaques signalées | Réaction de la garde |
|---|---|---|---|
| Rendus naturels | 10 | **0** | aucun re-roll |
| Contrôle positif (tronqués) | 10 | **10** (`reason: leading_span`) | re-roll proposé pour les 10 |

La perte de tête mesurée sur le contrôle positif va de **3 mots** (chunk 6) à **35 mots** (chunk 2, dont la transcription tronquée est une hallucination de l'ASR sur quasi-silence) — le seuil de 3 mots est atteint par le plus petit écart mesuré.

## Contrôles

| Contrôle | Attendu | Observé |
|---|---|---|
| **Négatif** — rendus naturels (l'ASR se trompe sur le début) | aucun signalement | **0/10** |
| **Positif** — mêmes rendus, attaque amputée | signalement systématique | **10/10** |
| Témoins codés en test | chunk 0 naturel **et** chunk 0 tronqué, avec les transcriptions réelles | `test_measured_render_with_asr_noise_is_not_an_attack`, `test_measured_truncated_render_is_an_attack` |
| Formule de re-roll | identique à p5 (`seed + i + attempt * 104_729`), `attempt 0` = graine d'origine | `test_spaced_seed_matches_the_p5_formula` |

Suite de tests : `12 passed` (`v4/tests/test_attack_guard.py`), CPU pur, sans réseau ni GPU.

## Limites

- **Portée de la mesure** : 10 chunks, un seul paragraphe de corpus, un seul moteur (Chatterbox), un seul modèle d'ASR. La séparation 0/10 et 10/10 est **observée**, pas garantie. Ce qui est mesuré ici est la **sensibilité et la spécificité de la garde**, pas le taux d'attaque de Chatterbox (0/10 sur 10 rendements).
- **Le défaut cible reste CosyVoice3** : la phase 1 l'a établi (graines 4243/4244/4245 sur le segment 57). Chatterbox, ici, ne perd pas son attaque sur 10 rendus — la garde n'a donc pas encore rencontré un chunk *naturellement* fautif, ni vérifié qu'un re-roll récupère un chunk réellement en faute.
- **La transposition dans la boucle de p5 n'est pas faite** : les PRs #21451 et #21379 modifient `p5_tts.py`. Le point d'insertion est documenté (acceptation du chunk rendu, avant concaténation) et la garde s'y branche par `evaluate_chunk(chunk, transcript)` ; l'ASR est injecté, donc le test et le mode en ligne ont la même signature.
- **Le seuil de 3 mots n'a pas été balayé** : c'est celui de p7, repris tel quel.
- **L'ASR hallucine sur le silence** : 2 des 10 troncages (chunks 2 et 9) produisent « Sous-titrage Société Radio-Canada » au lieu d'une transcription. Comportement connu de Whisper sur quasi-silence ; la garde le signale comme attaque (le début manque entièrement), ce qui est le bon verdict.
- **Le WER de ce couple (Chatterbox → Whisper) n'est pas mesuré ici** : l'ASR est bruité sur la voix TTS, ce qui est une donnée réaliste et utile pour la sensibilité de la garde, mais ce n'est pas une mesure de fidélité.

## Voir aussi

- [audio-onset-chunk-detection.md](audio-onset-chunk-detection.md) — la phase 2 CPU : classification `onset_drop` / `mid_omission` / `end_drop` / `spread` des spans déjà mesurés.
- [audio-bakeoff-bank.md](audio-bakeoff-bank.md) — banc de référence TTS (WER, RTF, VRAM par moteur).
- `v4/p7_verify.py` — organe d'omission (vote 2/3 ASR), dont la garde réutilise la normalisation et le calcul de spans.
- `v4/p5_tts.py` — rendu narrateur (chunker ≤ 280 car., boucle de re-roll sur plancher de durée).

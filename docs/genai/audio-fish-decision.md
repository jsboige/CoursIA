> REFERENCE — vivante — dernière révision 2026-11-20

# Décision Fish Audio S2 Pro — voie API vs voie locale (issue #19694)

> **Cadrage** : issue [#19694](https://github.com/jsboige/CoursIA/issues/19694) — évaluer l'adoption de **Fish Audio S2 Pro** pour la voix du pipeline audiobook. Le fil porte **deux voies** : l'API Fish (le service `tts-fishaudio:8197`, **auto-hébergé sur la flotte**) et la voie locale (le modèle S2 Pro en GGUF servi par `audio.cpp` sur le GPU de la flotte). **Ce document est l'artefact du critère 5** du grain : il consolide l'évidence déjà mesurée dans le fil et pose la recommandation argumentée. **Il ne tranche pas** — la décision finale (basculer / hybride / garder l'API) appartient au coordinateur ou à l'user, et la jambe d'intégration (critère 4) n'exécute qu'après elle.

## L'évidence mesurée

### Licence (critère 3) — **tenu**

Vérifiée firsthand par `myia-po-2023:CoursIA` (2026-10-17/18) à partir des sources du modèle : le S2 Pro est **compatible** sous la clause **Non-Commercial Purpose** du dépôt. Le pipeline audiobook de la flotte est d'usage non-commercial — le critère licence est satisfait pour la voie locale.

### Voie locale `audio.cpp` (critères 1-2) — **mesurée**

Mesure du 2026-11-09 (`myia-po-2023:CoursIA`), GPU local **RTX 3080 Ti 16 Go** :

| Métrique | Valeur mesurée |
|---|---|
| Pile | `audio.cpp` v0.9.4 + S2 Pro **GGUF Q8_0** |
| Exécution | `t1/t2/t3` **RC 0** |
| RTF (real-time factor) | **2,839** |
| Pic VRAM | **9 712 MiB** (≪ 16 Go) |
| WER (Whisper `large-v3-turbo` local) | **6,4 %** |
| WER baseline narrateur (#19454) | **9,7 %** |

La voie locale est **viable sur la 3080 Ti 16 Go** (pic VRAM ~9,7 GiB) et **bat la baseline narrateur** en WER (6,4 % < 9,7 %) — c'est-à-dire qu'elle tient la barre de qualité de la **narration** (voix de fond, batch), sans dépendance externe et sans coût par appel.

### Voie Fish — service auto-hébergé (état courant)

Le pipeline audiobook consomme actuellement le service Fish **auto-hébergé sur la flotte** (`tts-fishaudio:8197`) — c'est un endpoint interne, **pas un SaaS externe à quota**. Sur les **turns dramatiques** (interactivité, registre expressif), la voie Fish est mesurée à **WER 0,000** — une mesure de fidélité sur ce sous-ensemble, sans mesure tête-à-tête contre la voie locale sur les mêmes turns.

> **Limite de comparabilité** : le WER local (6,4 %) est mesuré sur la **narration batch**, le WER Fish (0,000) sur les **turns dramatiques** — ce sont deux sous-ensembles distincts, pas une mesure tête-à-tête sur le même corpus. Aucun classement de qualité entre les deux voies n'est donc mesuré ici : le WER n'évalue que la fidélité de transcription, pas l'expressivité, et il n'est pas relevé sur le même corpus de part et d'autre. L'attribution du chemin expressif à l'API est un **choix de conception** du routage (les turns dramatiques / interactifs y sont envoyés aujourd'hui), pas un résultat mesuré.

## Les trois options

| Option | Qualité narration | Qualité dramatique | Coût par appel | Coût GPU | Dépendance |
|---|---|---|---|---|---|
| **Garder le service Fish** (auto-hébergé `tts-fishaudio:8197`) | non mesurée en narration | WER 0,000 (dramatique, non comparé) | 0 (auto-hébergé, sans facturation par appel) | GPU du service Fish (sur la flotte) | interne à la flotte |
| **Basculer 100 % local** (`audio.cpp`) | WER 6,4 % (narration) | non mesurée sur les turns dramatiques | 0 | ~9,7 GiB (local) | aucune |
| **Hybride** (recommandation) | WER 6,4 %, en local | WER 0,000, en Fish (non comparé) | 0 | les deux chemins (batch local + expressif Fish) | interne au chemin expressif |

## Recommandation argumentée

La recommandation portée par le fil est l'**hybride**, **à la condition** que le routage expressif vers le service Fish soit retenu (prémisse de conception, non une qualité mesurée) : **narration batch en local** (`audio.cpp` + S2 Pro Q8_0) + **chemin expressif/interactif sur le service Fish**.

- La narration, qui est le gros du volume d'un audiobook, passe en local : qualité au-dessus de la baseline (WER 6,4 % < 9,7 %) et **zéro dépendance externe** sur le chemin majoritaire. L'absence de **facturation par appel** n'est pas un coût nul : le coût réel du chemin local est le **GPU** (~9,7 GiB VRAM) plus l'électricité et l'exploitation.
- Le chemin expressif (turns dramatiques, interactivité) passe sur le service Fish, qui y est aujourd'hui mesuré à WER 0,000 ; ce routage expressif vers le service Fish est la **prémisse** du choix hybride, pas une qualité mesurée contre la voie locale.
- L'hybride n'occupe le GPU sur le batch (narration, ~9,7 GiB sur 16 Go) **et** sur le chemin expressif (service Fish auto-hébergé) ; il n'y a **aucune dépendance externe** — les deux chemins tournent sur la flotte.

Ce document pose l'évidence et la recommandation ; **il n'engage pas la décision**.

## Ce que chaque décision implique

- **Garder le service Fish** : ce document suffit (critère 5) — le statu quo est documenté.
- **Basculer / hybride** : l'intégration **critère 4** devient due — serveur **OpenAI-compatible** devant `audio.cpp`, routage `_synthesize_fishaudio_path` → `audiocpp_fish_audio` dans `MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/p5_tts.py`, et **tests hérmétiques**. C'est le changement **conséquentiel** de route TTS du pipeline ; il n'exécute qu'après la décision.

## État

- **Critère 5 (ce document)** : **livré** — `docs/genai/audio-fish-decision.md`.
- **Critère 4 (intégration)** : **en attente de la décision** du coordinateur/user ; recommandé : l'hybride.
- **Critères 1, 3** : **tenus** (mesure locale 2026-11-09 ; licence 2026-10-17/18) — voir le fil #19694.
- **Critère 2** : **non déclaré tenu** — il requiert une **comparaison 5 segments + écoute** pas encore réalisée ; les mesures WER ci-dessus (fidélité de transcription) ne suffisent pas à le tenir.

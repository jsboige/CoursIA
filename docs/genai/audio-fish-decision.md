> REFERENCE — vivante — dernière révision 2026-11-17

# Décision Fish Audio S2 Pro — voie API vs voie locale (issue #19694)

> **Cadrage** : issue [#19694](https://github.com/jsboige/CoursIA/issues/19694) — évaluer l'adoption de **Fish Audio S2 Pro** pour la voix du pipeline audiobook. Le fil porte **deux voies** : l'API Fish (service distant) et la voie locale (le modèle S2 Pro en GGUF servi par `audio.cpp` sur le GPU de la flotte). **Ce document est l'artefact du critère 5** du grain : il consolide l'évidence déjà mesurée dans le fil et pose la recommandation argumentée. **Il ne tranche pas** — la décision finale (basculer / hybride / garder l'API) appartient au coordinateur ou à l'user, et la jambe d'intégration (critère 4) n'exécute qu'après elle.

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

### Voie API (état courant)

Le pipeline audiobook consomme actuellement l'API Fish (`tts-fishaudio:8197`). Sur les **turns dramatiques** (interactivité, registre expressif), la voie API est mesurée à **WER 0,000** — une fidélité supérieure à la voie locale sur ce sous-ensemble.

> **Limite de comparabilité** : le WER local (6,4 %) est mesuré sur la **narration batch**, le WER API (0,000) sur les **turns dramatiques** — ce sont deux sous-ensembles distincts, pas une mesure tête-à-tête sur le même corpus. Le contraste exploitable est donc *local = narration suffisante* / *API = expressivité supérieure*, pas *local < API globalement*.

## Les trois options

| Option | Qualité narration | Qualité dramatique | Coût / dépendance | VRAM |
|---|---|---|---|---|
| **Garder l'API** | dépend du quota API | la plus haute (0,000) | dépendance service + quota | 0 (local) |
| **Basculer 100 % local** | bonne (WER 6,4 %) | inférieure à l'API | aucune dépendance, coût nul | ~9,7 GiB |
| **Hybride** (recommandation) | bonne, en local | haute, en API | dépendance limitée au chemin expressif | ~9,7 GiB (chemin local) |

## Recommandation argumentée

La recommandation portée par le fil est l'**hybride** : **narration batch en local** (`audio.cpp` + S2 Pro Q8_0) + **chemin expressif/interactif en API**.

- La narration, qui est le gros du volume d'un audiobook, passe en local : qualité au-dessus de la baseline (WER 6,4 % < 9,7 %), **zéro coût par appel**, **zéro dépendance de quota** sur le chemin majoritaire.
- Le chemin expressif (turns dramatiques, interactivité) reste en API, là où sa fidélité supérieure (WER 0,000) a de la valeur.
- L'hybride n'importe la dépendance externe que sur le sous-ensemble expressif, et n'occupe le GPU (~9,7 GiB sur 16 Go) que pour le batch.

Ce document pose l'évidence et la recommandation ; **il n'engage pas la décision**.

## Ce que chaque décision implique

- **Garder l'API** : ce document suffit (critère 5) — le statu quo est documenté.
- **Basculer / hybride** : l'intégration **critère 4** devient due — serveur **OpenAI-compatible** devant `audio.cpp`, routage `_synthesize_fishaudio_path` → `audiocpp_fish_audio` dans `MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/p5_tts.py`, et **tests hérmétiques**. C'est le changement **conséquentiel** de route TTS du pipeline ; il n'exécute qu'après la décision.

## État

- **Critère 5 (ce document)** : **livré** — `docs/genai/audio-fish-decision.md`.
- **Critère 4 (intégration)** : **en attente de la décision** du coordinateur/user ; recommandé : l'hybride.
- **Critères 1-3** : **tenus** (mesure locale 2026-11-09 ; licence 2026-10-17/18) — voir le fil #19694.

# Mentions légales tierces — Third-Party Notices

> Inventaire des licences des **sous-modules**, **bibliothèques vendored**,
> **modèles GenAI** et **médias pédagogiques** inclus ou référencés dans ce
> dépôt. Le code du dépôt lui-même est sous licence **MIT**
> (cf. [`LICENSE`](LICENSE) — Copyright © 2022 Jean-Sylvain Boige).
>
> Cette notice couvre **trois familles** : (a) le code tiers directement inclus
> dans l'arbre du dépôt, (b) les **poids de modèles GenAI** consommés par les
> notebooks de la série `MyIA.AI.Notebooks/GenAI/`, et (c) les **médias
> pédagogiques** (illustrations, extraits) sous licence distincte du code.
> Les **datasets** sont suivis séparément dans
> [`docs/notebook-metadata/DATASET_REGISTRY.md`](docs/notebook-metadata/DATASET_REGISTRY.md).
>
> Source : issue #8055 (tranches 1 + 2 livrées ; tranche 3 = datasets #8055 tr.2
> intégrée dans `DATASET_REGISTRY.md`).

## 1. Code du dépôt

| Composant | Licence | Détenteur du copyright |
|-----------|---------|------------------------|
| CoursIA (ce dépôt) | **MIT** | © 2022 Jean-Sylvain Boige |

Badge : `License: MIT`.

## 2. Sous-modules git

Chaque sous-module est pinné à un commit précis (cf. `.gitmodules` +
`git submodule status`). La licence applicable est celle du dépôt amont au
commit pinné.

| Sous-module | Dépôt amont | Commit pinné | Licence (SPDX) | Copyright |
|-------------|-------------|--------------|----------------|-----------|
| forge-std | <https://github.com/foundry-rs/forge-std> | `b3bc8b154382` | **Apache-2.0** | Copyright Contributors to Forge Standard Library |
| openzeppelin-contracts | <https://github.com/OpenZeppelin/openzeppelin-contracts> | `5a3b28fc5` | **MIT** | © 2016-2026 Zeppelin Group Ltd |
| account-abstraction ⚠️ | <https://github.com/eth-infinitism/account-abstraction> | `1c6b669d0` | **GPL-3.0-only** | GNU GPL v3.0 |
| MetaGeneticSharp | <https://github.com/jsboige/MetaGeneticSharp> | `0433fad0c` | **MIT** | © 2020-2026 Jean-Sylvain Boige & contributors |
| Z3.Linq | <https://github.com/MyIntelligenceAgency/Z3.Linq> | `b68438c89` | **MIT** | © Bart De Smet, Ricardo Niepel, Jean-Sylvain Boige, Karel Frajtak, endjin |
| Automata | <https://github.com/MyIntelligenceAgency/Automata> | `cfbf436af` | **MIT** † | © Microsoft Corporation |
| Argumentum ⚠️ | <https://github.com/ArgumentumGames/Argumentum> | `7e72f3e5d` | **LGPL-3.0-only** | GNU LGPL v3.0 |
| semantic-fleet | <https://github.com/MyIntelligenceAgency/semantic-fleet> | `0468481f5` (branche `stable-from-v0343`) | **MIT** | © 2023 MyIA |

> **⚠️ Copyleft (à vérifier avant publication open-courseware, epic #4208).**
> `account-abstraction` est sous **GPL-3.0-only** et `Argumentum` sous
> **LGPL-3.0-only**. Ces licences copyleft imposent des obligations de
> redistribution (notamment la GPL-3.0, virale sur la distribution). Si le
> projet publie ou distribue le code de ces sous-modules, une revue
> licence-compatibilité est requise. En usage interne / build-time / sous-module
> non distribué, les obligations sont allégées.
>
> **† Automata — licence effective = MIT.** Le fichier `LICENSE` commence par une
> ligne-titre `Automata.NET` qui fait que l'API GitHub classifie la licence comme
> `NOASSERTION`, mais le corps est **verbatim** le texte standard de la licence
> MIT (© Microsoft Corporation). Ne pas se fier au seul badge de l'API GitHub ici.

## 3. Bibliothèques vendored (copiées dans l'arbre)

| Bibliothèque | Chemin | Licence | Copyright |
|--------------|--------|---------|-----------|
| difflogic (Petersen, NeurIPS 2022 — _Differentiable Logic Gate Networks_) | `MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/vendor/difflogic/` | **MIT** | © 2021-2023 Dr. Felix Petersen |
| Metagol (programmation logique inductive) | `MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/vendor/metagol/` | **BSD-3-Clause** | © 2016, Metagol authors |

> `foundry-lib/` (`MyIA.AI.Notebooks/SymbolicAI/SmartContracts/foundry-lib/`)
> est un **échafaudage propre** au projet (`foundry.toml` + `lib/`) qui consomme
> les trois sous-modules Solidity ci-dessus (forge-std, openzeppelin-contracts,
> account-abstraction) ; ce n'est pas une bibliothèque tierce à part entière.

## 4. Dépendances Lake (Lean)

Les projets Lean déclarent leurs dépendances dans `lakefile.lean` / `lake-manifest.json`.
Elles sont **résolues au build** (téléchargées par Lake dans `.lake/packages/`), non
copiées dans le dépôt. Principale dépendance tierce notable :

| Dépendance | Source | Commit pinné | Licence |
|------------|--------|--------------|---------|
| Mathlib 4 | <https://github.com/leanprover-community/mathlib4> | cf. `lake-manifest.json` par projet | Apache-2.0 |
| SocialChoiceLean (Dominik Peters) | <https://github.com/DominikPeters/SocialChoiceLean> | `355075e3` | _à confirmer_ |

> `social_choice_lean_peters/` est une **visite guidée locale** (propre au dépôt)
> qui importe la bibliothèque Lake de Peters comme dépendance — ce n'est pas une
> copie vendored de son code.

## 5. Modèles GenAI (poids et licences)

Les notebooks `MyIA.AI.Notebooks/GenAI/` (**Image / Audio / Video / Texte**)
invoquent des modèles tiers par **API propriétaire** (OpenAI, Stability Cloud)
ou par **chargement local** des poids (HuggingFace, GitHub releases). Chaque
modèle est livré avec sa propre licence — souvent distincte de la licence MIT
du code de ce dépôt. Les poids **ne sont pas** commités dans l'arbre (téléchargés
à l'exécution) mais leur consommation reste régie par la licence amont.

### 5.1 Modèles Image (génération, édition, restauration)

| Modèle | Fournisseur | Source | Licence (SPDX / label amont) | Conditions clés |
|--------|-------------|--------|------------------------------|-----------------|
| **DALL-E 3** | OpenAI | API only | _Proprietary API_ | Pas de poids publiés ; usage via OpenAI API sous usage policies |
| **gpt-image-1** | OpenAI | API only | _Proprietary API_ | Idem DALL-E 3 ; remplace DALL-E 3 par défaut en 2025 |
| **GPT-5 / GPT-4o / GPT-4o-mini** (multimodal) | OpenAI | API only | _Proprietary API_ | Usage multimodal image via OpenAI API |
| **Sora / Sora 2** | OpenAI | API only | _Proprietary API_ | Génération vidéo via OpenAI API |
| **SDXL-Lightning-4step** | ByteDance | HF `ByteDance/SDXL-Lightning` | **OpenRAIL++-M** (`openrail++`) | Source-available ; restrictions d'usage RAIL (use-based) |
| **SD XL Turbo** | Stability AI | HF `stabilityai/sdxl-turbo` | **SAI Non-Commercial Community License** | ⚠️ NC par défaut ; commercial = membership Stability AI |
| **Stable Diffusion 3.5 Large** | Stability AI | HF `stabilityai/stable-diffusion-3-5-large` | **Stability AI Community License** | ⚠️ Gratuit pour entités < $1M revenu annuel ; au-delà = Enterprise License. Gated |
| **Qwen-Image-Edit** (Phase 29, fp8 e4m3fn) | Alibaba (Qwen) | HF `Qwen/Qwen-Image-Edit` | **Apache-2.0** | Permissif ; commercial OK avec attribution + patent grant |
| **Qwen-Image-Edit 2509** | Alibaba (Qwen) | HF `Qwen/Qwen-Image-Edit-2509` | **Apache-2.0** | Idem ; **bloquant VRAM 24 GB FP16** (cf. `cost:` frontmatter) |
| **FLUX.1-schnell** | Black Forest Labs | HF `black-forest-labs/FLUX.1-schnell` | **Apache-2.0** | Permissif ; gated (login requis) |
| **FLUX.1-dev** | Black Forest Labs | HF `black-forest-labs/FLUX.1-dev` | **FLUX.1 [dev] Non-Commercial License** | ⚠️ NC sur les poids ; **outputs commercial OK** par licence. Gated |
| **Lumina-Next-SFT** (Lumina-Image 2.0) | Alpha-VLLM (Shanghai AI Lab) | HF `Alpha-VLLM/Lumina-Next-SFT` | **Apache-2.0** | Permissif |
| **Z-Image / Z-Image-Turbo** | Alibaba (Tongyi Lab) | HF `alibaba-pai/Z-Image` | _à confirmer_ | Page HF gated au moment de l'inventaire ; convention Tongyi = Apache-2.0 probable mais non vérifié firsthand |
| **SD Forge** (Stable Diffusion WebUI Forge) | lllyasviel | Local install (ComfyUI-adjacent) | **Apache-2.0** (Forge wrapper) + licence du checkpoint SD chargé | Wrapper permissif ; la licence effective dépend du checkpoint (sdxl-base, SDXL-Lightning, etc.) |
| **Real-ESRGAN** | Xintao Wang (Tencent ARC Lab) | GitHub `xinntao/Real-ESRGAN` | **BSD-3-Clause** | Permissif ; upscaling restauration |

### 5.2 Modèles Video (génération, animation, interpolation)

| Modèle | Fournisseur | Source | Licence (SPDX / label amont) | Conditions clés |
|--------|-------------|--------|------------------------------|-----------------|
| **HunyuanVideo 1.5** | Tencent | HF `tencent/HunyuanVideo` | **Tencent Hunyuan Community License** | Custom ; gated ; termes commerciaux complets dans `LICENSE` amont |
| **LTX-Video / LTX-2** | Lightricks | HF `Lightricks/LTX-Video` | **LTX-Video Open Weights License** (custom) | Custom non-standard SPDX ; fichier `LTX-Video-Open-Weights-License-0.X.txt` |
| **Wan 2.1 / 2.2** (T2V-A14B) | Alibaba (Wan-AI) | HF `Wan-AI/Wan2.2-T2V-A14B` | **Apache-2.0** | Permissif ; "freedom to use your generated contents" granted |
| **Stable Video Diffusion 1.1** (SVD) | Stability AI | HF `stabilityai/stable-video-diffusion-img2vid-xt-1-1` | **Stability AI Community License** | ⚠️ < $1M revenu annuel gratuit ; au-delà = Enterprise License. Gated |
| **AnimateDiff** | Yuwei Guo / CUHK + Tencent | HF `guoyww/animatediff` | **Apache-2.0** | Code + motion modules permissifs |

### 5.3 Modèles Audio (TTS, music, separation)

| Modèle | Fournisseur | Source | Licence (SPDX / label amont) | Conditions clés |
|--------|-------------|--------|------------------------------|-----------------|
| **Kokoro TTS** (Kokoro-82M) | hexgrad (+ Silero) | HF `hexgrad/Kokoro-82M` | **Apache-2.0** | Permissif ; ⚠️ _le notebook `01-5-Kokoro-TTS-Local.ipynb` indique « MIT » — c'est une **hallucination à corriger** (vérifié firsthand via model card HF : Apache-2.0)_ |
| **Chatterbox Turbo / Chatterbox TTS** | Resemble AI | HF `resemble-ai/chatterbox` | _à confirmer_ | Page HF gated (401) au moment de l'inventaire ; pas de SPDX firsthand |
| **Qwen3-TTS** (0.6B / 1.7B Base & CustomVoice) | Alibaba (Qwen) | HF `Qwen/Qwen3-TTS-12Hz-1.7B-Base` | **Apache-2.0** | Permissif |
| **Coqui XTTS v2** | Coqui AI (archivé 2024) | HF `coqui/XTTS-v2` | **CPML — Coqui Public Model License** (custom) | ⚠️ Coqui AI shut down 2024 ; **CPML reste applicable** sur les poids redistribués. Custom non-standard SPDX. Gated |
| **FishAudio S2-Pro** | Fish Audio | HF `fishaudio/s2-pro` | **Fish Audio Research License** (custom) | ⚠️ Research / non-commercial gratuit ; commercial = licence séparée via business@fish.audio |
| **Dia TTS** (Dia-1.6B) | Nari Labs | HF `nari-labs/Dia-1.6B` | **Apache-2.0** | Permissif |
| **MusicGen** (Large/Medium/Melody/Small) | Meta (AudioCraft) | HF `facebook/musicgen-large` | **CC-BY-NC-4.0 (weights)** + MIT (code) | ⚠️ **Poids NC** — usage commercial interdit ; code seul = MIT |
| **SongGeneration 2 / LeVo** (v2-large) | Tencent AI Lab | HF `tencent/SongGeneration` | _à confirmer_ | HF gated (401) ; arXiv 2506.07520 = CC-BY 4.0 sur le **papier**, pas sur les poids |
| **ACE-Step v1.5** (3.5B) | ACE Studio / Huawei | GitHub `ace-step/ACE-Step-1.5` | **MIT** | Permissif |
| **SkyTNT MIDI** (Skywork) | Skywork (Kunlun Inc.) | HF `Skywork/SkyTNT-01-Midi` | _à confirmer_ | HF gated (401) au moment de l'inventaire |
| **TADA 3B ML** | _non localisé_ | _HF introuvable_ | _à confirmer_ | Pas de model card primaire localisé ; possiblement confusion avec Microsoft TADA 3D |
| **Demucs / htdemucs_ft** | Meta (Facebook Research) | GitHub `facebookresearch/demucs` | **MIT** | Permissif ; séparation de sources audio |
| **Whisper** (large-v3, medium, base, small, tiny) | OpenAI | HF `openai/whisper-large-v3` | **Apache-2.0** | ⚠️ Note : API OpenAI Whisper = payante ; **poids open-source = Apache-2.0** |
| **faster-whisper** (CTranslate2 conversion) | SYSTRAN (Guillaume Klein) | HF `SYSTRAN/faster-whisper-large-v3` | **MIT** | Permissif (code de conversion) ; les poids sous-jacents Whisper restent Apache-2.0 |

### 5.4 Synthèse — modèles à restriction commerciale ⚠️

Avant publication open-courseware (EPIC #4208), revue obligatoire pour les
modèles suivants dont la licence **interdit ou restreint l'usage commercial** :

| Modèle | Restriction | Action requise |
|--------|-------------|----------------|
| **SD XL Turbo** | NC par défaut | Membership Stability AI ou exclure |
| **SD 3.5 Large** | < $1M revenu annuel gratuit | Vérifier seuil de l'entité qui distribue |
| **SVD 1.1** | < $1M revenu annuel gratuit | Idem |
| **FLUX.1-dev** | Poids NC (outputs commercial OK) | Documenter clairement |
| **MusicGen** | Poids CC-BY-NC-4.0 | Exclure ou obtenir licence Meta |
| **Coqui XTTS v2** | CPML custom | Lire CPML ; vérifier compatibilité distribution |
| **FishAudio S2-Pro** | Research-only | Exclure (commercial = licence séparée) |
| **HunyuanVideo 1.5** | Tencent custom | Lire LICENSE amont intégralement |
| **LTX-Video** | Custom non-standard SPDX | Lire `LTX-Video-Open-Weights-License-0.X.txt` |
| **SongGeneration 2 / LeVo** | _à confirmer_ (Tencent custom probable) | Vérifier post-publication model card |
| **Chatterbox Turbo** | _à confirmer_ (HF gated) | Re-vérifier page HF post-auth |
| **Z-Image** | _à confirmer_ (HF gated) | Re-vérifier page HF post-auth |
| **SkyTNT MIDI** | _à confirmer_ (HF gated) | Re-vérifier page HF post-auth |
| **TADA 3B ML** | _à confirmer_ (card introuvable) | Identifier la bonne source upstream |

### 5.5 Méthodologie de vérification

- **Vérification firsthand via WebFetch** des model cards HuggingFace et des
  pages OpenAI docs, menée le 2026-07-23 par `myia-po-2025:CoursIA-2`.
- **Cross-check via sub-agent haiku async** (`Agent(model: "haiku")`,
  `run_in_background: true`) : 28 modèles scannés, 24 vérifiés firsthand
  (24/28 = 86%), 4 gated ou introuvables au moment de l'inventaire
  (Z-Image, Chatterbox Turbo, SongGeneration 2 / LeVo, SkyTNT MIDI, TADA 3B ML).
- **Anti-hallucination** : une erreur factuelle a été détectée et corrigée
  dans le notebook `01-5-Kokoro-TTS-Local.ipynb` qui prétendait "MIT" pour
  Kokoro TTS — la model card HF officielle indique **Apache-2.0**.
  Cette erreur sera corrigée dans une PR séparée (sub-grain notebook).

## 6. Médias pédagogiques / extraits

Les notebooks de la série `MyIA.AI.Notebooks/GenAI/` produisent ou référencent
des **médias** (images générées, samples audio, clips vidéo, illustrations
tirées d'ouvrages). Ces médias sont l'objet d'une **double licence** :

- **Média généré par un modèle** : la licence du média suit la licence du
  modèle qui l'a produit (cf. §5). Les **outputs** sont en général libres
  d'usage (même pour les modèles NC sur les poids, ex. FLUX.1-dev), mais
  cela dépend du modèle — vérifier §5.4.
- **Média emprunté / extrait** : illustrations, captures d'écran d'ouvrages
  publiés, photos sous licence tierce. Chacun de ces médias **DOIT** être
  tracé dans une `DATASET_CARD.md` locale (chemin du notebook) avec URL
  source, licence amont, attribution, et éventuelles restrictions.

Les datasets (texte, image, audio) qui alimentent les notebooks sont suivis
séparément dans
[`docs/notebook-metadata/DATASET_REGISTRY.md`](docs/notebook-metadata/DATASET_REGISTRY.md)
(cf. `DATASET_CARD` schema, c.795 pilote).

## 7. Distinction code vs contenu pédagogique

La licence **MIT** couvre le **code** de ce dépôt. Les **supports pédagogiques**
(narration, exercices, choix didactiques, prose markdown dans les cellules)
sont l'œuvre de l'auteur et leur réutilisation est régie par la même licence
MIT, sauf mention contraire explicite dans le répertoire concerné (ex.
médias/extraits tiers — cf. § 6 ; modèles GenAI tiers — cf. § 5).

---

**Statut** : **tranches 1 + 2 de #8055 livrées** (THIRD_PARTY_NOTICES central —
sous-modules + vendored + modèles GenAI + médias pédagogiques). La tranche
suivante (datasets) est traitée dans
[`docs/notebook-metadata/DATASET_REGISTRY.md`](docs/notebook-metadata/DATASET_REGISTRY.md)
pilote V0 (c.795, PR #8083 MERGED 2026-07-23T00:13:43Z).

Mettre à jour cette notice si un sous-module est ajouté/supprimé/mis à jour
(cf. `git submodule status`), si un nouveau modèle GenAI est intégré à un
notebook, ou si un média tiers est emprunté à un ouvrage publié.

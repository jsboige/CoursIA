# Service tts-zonos3 — ZONOS3-Mini (backend ggml/CUDA)

Serveur TTS du moteur **ZONOS3-Mini** (Zyphra), exposé sur `127.0.0.1:1919`,
dans la même famille que `tts-kokoro`, `tts-tada`, `tts-qwen` et
`tts-fishaudio` (`docker-configurations/services/`). Issue de référence :
**#25835**, tranche 3.

Le service **appelle le runtime officiel** : aucun source de l'amont n'est
recopié dans ce dépôt (règle *organ-first*). Le `Dockerfile` compile
`servers/ggml` au commit épinglé ; l'image finale ne contient que les deux
binaires et les quatre bibliothèques ggml compilées avec eux, jamais les poids.

Les quatre bibliothèques vivent dans `/usr/local/lib/zonos3/`, déclarées par
`/etc/ld.so.conf.d/zonos3.conf` puis `ldconfig`. Ce n'est pas un choix
cosmétique : les binaires sortent du CMake avec un RUNPATH vers l'arbre de
compilation (`/src/zonos3/servers/ggml/build-cuda/ggml/src`, `readelf` mesuré
sur l'image le 2026-11-27), chemin qui n'existe pas dans l'image d'exécution.
Elles sont aussi résolues ainsi sans toucher au `LD_LIBRARY_PATH` que pose
l'image NVIDIA, et sans y laisser entrer les *stubs* du pilote CUDA qui ont
servi à l'édition de liens.

## Versions épinglées

| Élément | Pin | Licence |
|---|---|---|
| Runtime (code) | `github.com/Zyphra/ZONOS3-Mini` @ `a50e14117d99181ba7f28047b451ba03ba1a09a9` | MIT (`LICENSE`, Zyphra 2026) |
| Poids | `huggingface.co/Zyphra/ZONOS3-Mini` @ `2921b8821772b0bd10a04456863d21abf9d2f283` | Apache-2.0 (carte du modèle), `gated: false` — **aucun jeton requis** |
| Image de base | `nvidia/cuda:12.8.1-devel-ubuntu24.04` (construction), `12.8.1-runtime-ubuntu24.04` (exécution) | NVIDIA |
| Backend | ggml (sous-module `a05c9922613c`) + les 11 correctifs de `servers/ggml/patches/` (6 CUDA, 5 Metal) appliqués par le CMake amont à la configuration ; CUDA, `CMAKE_CUDA_ARCHITECTURES` = 86 (RTX 3090 / 3080 Ti) | MIT (ggml authors) |
| Normalisation de texte | `zyphra-textnorm` (sous-module `170c571e7503`), construit par CMake avec la chaîne Rust **`1.100.0`** (épinglée : l'amont ne livre pas de `rust-toolchain.toml` et ne déclare qu'un MSRV de 1.88) | MIT ; ports tiers Apache-2.0 / MIT / Unicode-3.0 |
| Chaîne de compilation | mesurée dans l'image de construction le 2026-11-27 : `rustc 1.100.0`, `cmake 3.28.3`, `nvcc` (CUDA 12.8.93), `gcc 13.3.0`, `ggml 0.27.0` (sous-module `a05c992`, « -dirty » : les correctifs amont appliqués à la configuration) | — |

La chaîne Rust ne sert qu'à construire : elle reste dans l'étape de
compilation et n'entre pas dans l'image d'exécution.

Les deux pins (commit du runtime, révision des poids) sont les **seules**
sources de vérité : le commit dans `Dockerfile` (`ARG ZONOS3_COMMIT`) et la
révision dans `fetch_models.py` (`REVISION`). Les changer à un seul endroit.

## Décision de backend : `servers/ggml`

L'amont livre trois serveurs qui exposent **la même API** sur le même port
(`127.0.0.1:1919`) : `servers/ggml` (C++/ggml), `servers/sgl` (SGLang, pile
Python/CUDA) et `servers/mlx` (Apple Silicon, noyau Metal). Le service retient
**ggml**, pour trois raisons mesurables :

1. **Une image sans pile d'inférence Python.** Le binaire est autonome ; rien
   de la chaîne `torch`/`sglang` n'entre dans l'image, donc rien n'y dérive à
   chaque version de `pip`. Les plugins Python du serveur (`--python-src`,
   `--worker-python`) restent hors périmètre.
2. **Le banc de la tranche 2 a mesuré ce code-là** (`MyIA.AI.Notebooks/`
   `GenAI/Audio/04-Applications/v4/mesures/zonos3/`) : même runtime natif ggml,
   mais **pas le même binaire**. Le clone du banc a tourné le 2026-11-13 à
   21:53:14Z, et 17 commits de `main` sont datés après ce moment — dont cinq
   touchent la génération : normalisation de texte native (`zyphra-textnorm`
   0.2.0, grammaires Rust pour les 43 langues), textes courts (pause et
   remplissage), limiteur de sortie appliqué au WAV du CLI, sélection GPU du
   décodeur indépendante du backbone, arrondi de préfixe noyau FP32. Son JSON
   de mesure porte `runtime_commit: null` et l'empreinte de binaire
   `3236df3b21b50755…`, qui n'est pas celui construit ici. Les chiffres du banc
   restent la référence du **moteur** ; ceux du **binaire de ce service** se
   mesurent contre lui, et un rejeu à graine 42 n'a aucune raison d'être
   identique d'un binaire à l'autre.
3. **`servers/mlx` est hors sujet sur une machine Linux** (noyau Metal), et
   `servers/sgl` ajoute une pile Python complète pour un endpoint identique.

Le serveur ggml est **CPU par défaut sur Linux** et lie **`127.0.0.1`** : les
deux défauts rendraient le port injoignable depuis l'hôte et la synthèse
beaucoup plus lente. `entrypoint.sh` force `--host 0.0.0.0 --gpu`, et c'est
l'hôte qui borne l'exposition (`127.0.0.1` dans `docker-compose.yml`).

## Poids : jeu minimal

Les poids ne sont **jamais** dans l'image : ils vivent dans un répertoire hôte
monté en lecture seule.

```bash
python fetch_models.py --dest D:/hf-models/zonos3
```

Le jeu par défaut suffit au service. Tailles mesurées sur le téléchargement de
la révision épinglée :

| Fichier | Taille | Rôle |
|---|---|---|
| `gguf/backbone-ptq.gguf` | 663 150 624 o (0,66 Go) | backbone génératif (obligatoire) |
| `gguf/zac-keep2.gguf` | 452 325 440 o (0,45 Go) | décodeur audio ZAC (obligatoire) |
| `gguf/spk-encoder.gguf` | 45 385 728 o (45 Mo) | encodeur de locuteur, voix `embedding` |
| `gguf/steer.gguf` | 204 960 o (0,2 Mo) | bundle de steering, axes de `GET /v2/controls` |
| `gguf/voices/` | 21 561 134 o (21,6 Mo) | 27 voix `embedding`, 10 langues — servies par `GET /v2/speakers` |

Total du jeu minimal : **1,18 Go**. La seule voix française livrée est
`French/Gaspard_fr_M_1` ; les 26 autres couvrent anglais (10), allemand,
hindi, italien, coréen, mandarin, portuguese, espagnol et télougou (2 chacune).

**Hébergement au plus petit quant** (règle `genai-config`) : l'éditeur ne
publie qu'un seul backbone pour ce runtime à la révision épinglée,
`backbone-ptq.gguf` (663 150 624 o), plus son jumeau d'édition
`backbone-ptq-edit.gguf` (663 491 840 o) — liste de l'arbre Hugging Face
mesurée le 2026-11-27 ; aucune variante fp16 ou fp32 n'y figure. Ce que
« PTQ » veut dire, lu dans les en-têtes GGUF le même jour : Q4_0 pour 85,2 %
des éléments du backbone, Q8_0 pour 3,0 %, F16 pour 11,8 % ; le décodeur audio
`zac-keep2.gguf` n'est pas quantifié (F16 77,4 %, F32 22,6 %) et l'encodeur de
locuteur est en F32. La recherche
du même jour trouve un dérivé communautaire, `groxaxo/ZONOS3-Mini-GPTQ-Pro-INT4`
(327 Mo) : il est fait de couches `overlay/*.safetensors` et d'un runtime
Python pour la pile SGLang, sans aucun fichier GGUF — le serveur ggml de ce
service ne le lit pas. La seconde moitié de la règle, dormir quand il ne sert
pas, n'a pas d'équivalent dans ce runtime (section « Veille et résidence »).

Compagnons **optionnels**, nommés par ce qu'ils ouvrent :

```bash
python fetch_models.py --dest D:/hf-models/zonos3 --with raw-reference
python fetch_models.py --dest D:/hf-models/zonos3 --with raw-reference --with edit
```

- `raw-reference` : `zac-encoder.gguf` + `ssl-teacher.gguf`, pour le clonage
  depuis un clip brut (`speaker_audio_base64`, `speaker_mode: reference`) ;
- `edit` : `gguf/edit/accents.gguf`, pour l'édition de parole (`/v2/edit*`) —
  **hors périmètre** de cette tranche.

Le dossier `gguf/` de la révision épinglée pèse **9,89 Go** en 91 fichiers
(taille de l'arbre Hugging Face, mesurée le 2026-11-27). L'écart avec les
1,18 Go du jeu minimal vient de quatre fichiers que le service n'utilise pas :
`zac-encoder.gguf` (4,03 Go), `zac.gguf` (2,20 Go), `ssl-teacher.gguf`
(1,55 Go) et `edit/accents.gguf` (0,26 Go), plus le backbone d'édition.

## Démarrage

```bash
cp .env.example .env       # adapter ZONOS3_MODELS_PATH et ZONOS3_GPU_ID
docker compose up -d --build
docker compose ps          # healthy = GET /v2/health répond {"status":"ok"}
```

**Cycle de vie.** Le conteneur ne redémarre pas de lui-même
(`restart: "no"`) et aucun monitor ne l'arrête : il reste chargé en VRAM tant
qu'on ne l'arrête pas. On l'arrête à la fin de chaque session de travail —
d'autant plus que la VRAM croît avec le trafic sans se rendre (section
« Mesures du conteneur »).

```bash
docker compose stop        # libère la VRAM ; docker compose start recharge le modèle
docker compose down        # retire aussi le conteneur et son réseau
```

Côté notebook, le démarrage à la demande se fait par l'appelant :
`service_wake.ensure_service_up("tts-zonos3", "http://127.0.0.1:1919/v2/health")`
(motif dans « Veille et résidence »).

| Variable | Défaut | Rôle |
|---|---|---|
| `ZONOS3_PORT` | `1919` | port hôte (publié sur `127.0.0.1` seulement) |
| `ZONOS3_MODELS_PATH` | — (obligatoire) | répertoire hôte du jeu de poids, monté sur `/models:ro` |
| `ZONOS3_GPU_ID` | `1` | GPU réservé (1 = RTX 3090 sur ce siège) |
| `ZONOS3_BATCH` | vide (= défaut amont, 8) | synthèses simultanées |
| `ZONOS3_ACCESS_TOKEN` | vide (= pas d'authentification) | s'il est défini, le serveur exige `Authorization: Bearer <jeton>` sur **toute** route (`403` sinon) |
| `TZ` | `Europe/Paris` | fuseau des journaux |

Le serveur **n'arme aucune authentification par défaut** : publié sur la boucle
locale de l'hôte, il n'est joignable que depuis elle. Le runtime sait en plus
exiger un jeton — si `ZONOS3_ACCESS_TOKEN` est présent dans l'environnement du
conteneur, un filtre **en amont de tout routage** rend l'API en `403` sauf
`Authorization: Bearer <jeton>` ou le cookie `zonos3_access` (source :
`servers/ggml/src/server/http.cpp` du commit épinglé). L'image ne l'arme pas ;
le compose le laisse passer s'il est défini.

Le service a son **propre réseau** (`zonos3-network`), comme `tts-fishaudio`
(`fishaudio-network`) : `tts-network` appartient au projet compose `tts-multi`
— mesuré sur l'hôte, `com.docker.compose.project=tts-multi` — et un second
projet ne peut pas le déclarer sans conflit. Les carnets de l'hôte l'atteignent
par le port publié : le défaut du client v4 est `http://localhost:1919`
(`v4/zonos3_client.py:40`). Le rejoindre en `external: true` est l'étape du
routage par la passerelle, hors de cette tranche.

### Veille et résidence

Le runtime **ne sait pas mettre le modèle en veille** : la seule libération
partielle des options est `--reference-idle-unload N`, qui libère l'encodeur de
référence et le professeur SSL après N secondes d'inactivité — deux poids que
le jeu minimal ne contient même pas. Il n'y a donc pas d'équivalent du
`--enable-sleep-mode` de vLLM ni du `/free` de ComfyUI. Le conteneur se charge
quand on le démarre (`docker compose up -d`, ou `service_wake.ensure_service_up`
côté appelant) et se libère quand on l'arrête ; c'est une **limite mesurée de
l'image**, pas un réglage oublié.

Le sidecar `idle-monitor` de la maison (`services/shared/`) n'est **pas** adopté
ici : son détecteur d'activité compare l'empreinte du corps de la sonde, et
`GET /v2/health` rend invariablement `{"status":"ok"}` (schéma `Health`,
propriété unique) — il arrêterait le conteneur `IDLE_TIMEOUT` après son
démarrage, y compris pendant une synthèse. Le pipeline v4 suspend d'ailleurs ce
monitor pendant ses chaînes (`v4/idle_monitor.py`).

## Mesures du conteneur

Relevés sur le conteneur de **ce** compose (image construite depuis le commit
épinglé, RTX 3090, 2026-11-27 ; conteneur démarré à 16:43:02Z puis recréé à
16:53:15Z sous les bornes ci-dessous). Ce sont les chiffres du **binaire de ce
service** ; les mesures du **moteur** (WER, prosodie) restent celles du banc de
la tranche 2 (`v4/mesures/zonos3/`), dont le binaire diffère (section
« Décision de backend », point 2).

| Ce qui est mesuré | Valeur |
|---|---|
| Démarrage : `compose up` → premier `200` de la sonde | 7,1 s |
| Empreinte au repos (`memory.current` du cgroup) | 546 à 553 Mio |
| Synthèse seule, 18,6 s d'audio | 1,90 s (RTF 0,10) |
| Synthèse seule, 45,8 s d'audio | 3,9 à 4,1 s (RTF 0,084 à 0,089) |
| Lot de 8 simultané, 355 à 385 s d'audio | 9,8 à 11,0 s (RTF 0,023 à 0,030) |
| Lot de 8 au plafond, 1 062 s d'audio | 24,7 à 28,9 s (RTF 0,023 à 0,027) |
| Plafond d'une requête | 133,3 s d'audio |
| Pic mémoire, charge longue soutenue (5 vagues) | 1 665,6 Mio |
| Pic mémoire, 20 vagues d'appels courts | 1 135,1 Mio |
| Entrées `pids` au pic, threads compris | 38 |
| VRAM ajoutée au repos / en charge longue | +1 884 / +2 496 Mio |
| Rejeu à graine et texte identiques | empreinte du WAV identique (`e0256c86…`) |

**Le plafond de 133,3 s est dur.** Une trame vaut 2 940 échantillons à
44,1 kHz, soit 1/15 s ; le checkpoint annonce `max_tokens: 2000` dans
`GET /v2/capabilities`, donc 2 000 × 1/15 s. Un texte plus long est **coupé**,
pas refusé : 2 682 caractères rendent 132,73 s d'audio. Donner
`max_tokens: 4000` explicitement ne change rien — mesuré, la réponse reste à
132,73 s. Un texte de roman se découpe donc côté appelant, en morceaux dont la
durée estimée reste sous le plafond.

**Les bornes du compose viennent de ces chiffres.** `mem_limit` et
`memswap_limit` valent `3g` (swap désactivé) : le pire cas mesuré, 1 665,6 Mio,
occupe 54 % de la borne. Une première passe à `2g` a été écartée : le même pic
y occupait 81 %, et l'empreinte ne redescend pas au repos — trop juste pour un
conteneur qui ne redémarre pas de lui-même. `pids_limit: 128` couvre 38 entrées
mesurées. `start_period: 60s` couvre les 7,1 s observés à cache de pages chaud.
`memory.events` est resté à `max 0 oom 0 oom_kill 0` sur toute la campagne.

**La mémoire ne redescend pas, et la VRAM ne se rend pas.** Après un lot, la
mémoire du cgroup reste à son niveau, dominée par l'anonyme (1 048 Mio
d'anonyme pour 1 135 Mio au total après vingt vagues courtes) ; elle ne revient
pas à l'empreinte de repos. La VRAM suit le même mouvement : 12 139 Mio sur la
carte au repos hôte, +1 884 Mio conteneur chargé, +2 496 Mio en charge longue,
puis une croissance qui **ralentit sans s'annuler** sur les appels courts —
+1 122 Mio sur les dix premières vagues, +268 Mio sur les dix suivantes (une
vague = une synthèse seule et un lot de huit ; vingt vagues font un peu plus de
deux heures d'audio), jusqu'à 15 413 Mio au plus haut, soit +3 274 Mio. Aucun
plateau n'a été observé dans cette fenêtre, et la cause n'est pas établie
(allocateur CUDA ou tampons de session : non tranché). Conséquence pratique :
**redémarrer le conteneur entre deux sessions** plutôt que le laisser tourner
des jours — `docker compose down` puis `up -d` rend la VRAM, mesuré au retour
exact des 12 139 Mio de référence.

## API

| Route | Usage |
|---|---|
| `GET /v2/health` | sonde de santé (`{"status":"ok"}`) |
| `GET /v2/capabilities` | capacités du checkpoint chargé (dont `start_token`, `steer_release`) |
| `GET /v2/controls` | axes de steering servis par le bundle chargé |
| `GET /v2/speakers` | voix disponibles (`id`, `label`, modes `embedding`/`reference`) |
| `POST /v2/generate` | synthèse native (`format: "wav"` ou PCM float32 44,1 kHz, `stream`) |
| `POST /v1/audio/speech` | façade compatible OpenAI |
| `GET /v2/phonemize`, `/v2/edit*`, `/v2/projects*`, `/v2/media/{sha256}` | phonémisation, édition, projets, médias |

L'en-tête **`X-Seed`** renvoie la graine réellement utilisée : c'est elle qu'on
consigne pour rejouer une synthèse à l'identique.

Exemple :

```bash
curl -s http://127.0.0.1:1919/v2/generate \
  -H 'Content-Type: application/json' \
  -d '{"text":"Bonjour.","language":"fr_fr","seed":42,"format":"wav",
       "stream":false,"speaker_embedding_id":"default_517319c805b927e9"}' \
  -o bonjour.wav -D - | grep -i x-seed
```

Deux pièges du contrat, mesurés sur le binaire de ce service le 2026-11-27 :

- **`"stream": false` est obligatoire pour `format: "wav"`.** Le `stream` du
  serveur vaut `true` par défaut ; sans la clé, la requête rend
  `400 {"detail":"format=wav needs stream=false"}`. Sans clé `format` du tout,
  la réponse est du PCM brut (`audio/pcm`) en `200`.
- **L'identifiant de voix se relève, il ne se devine pas.** `GET /v2/speakers`
  rend 27 voix (`{"speakers": [...]}`) ; la seule française livrée est
  `default_517319c805b927e9` (`Gaspard fr M 1`). L'ancien libellé de fichier
  (`French/Gaspard_fr_M_1`) n'est pas un identifiant d'API, et un identifiant
  inconnu rend un `400` au message trompeur (voir « Dépannage »).

Langues : les codes TTS sont ceux du registre embarqué (`model/src/zonos3/`
`registries/languages.json`, 44 entrées). Le français y est **`fr_fr`** ;
`fr` est le code « parlé » (reconnaissance), pas un code TTS — envoyé à
`/v2/generate`, il rend `400 Unsupported language code: 'fr'. Supported:
en_us, en_gb, fr_fr, de, …`.

### Pilotage : `controls` et `control_spans`

Deux champs distincts, deux formes distinctes :

- **`controls`** : dictionnaire `{"<axe>": <dose>}`, une dose constante sur
  toute la synthèse. Les noms d'axes sont ceux de `GET /v2/controls` (bundle
  `studio_mect60k_x10`, 65 directions au checkpoint épinglé).
- **`control_spans`** : une **liste** de fenêtres, chacune portant son propre
  dictionnaire de doses — `[{"start": 0, "end": 4, "controls": {"<axe>": <dose>}}]`.
  Envoyer un **dictionnaire** (la forme « par axe ») rend
  `422 unexpected instance type` : la forme dictionnaire n'existe pas côté
  serveur, quelle que soit la clé utilisée.

Bornes de fenêtre et de longueur : `decode_context` (30 trames par défaut,
450 au maximum) et `max_tokens` (2 000 trames au checkpoint, soit 133,3 s
d'audio) sont les valeurs annoncées par `GET /v2/capabilities` ; elles ne se
déduisent pas de la longueur du texte (section « Mesures du conteneur »).

## Provenance et licences

Aucun code de l'amont n'est recopié : le service **construit et appelle** le
runtime officiel. Les licences ci-dessous sont celles des fichiers du commit
épinglé (`LICENSE`, `NOTICE`, `third_party/licenses/`) et de la carte du
modèle sur Hugging Face, relevées le 2026-11-27.

- **Runtime** : MIT (Copyright (c) 2026 Zyphra, Inc.).
- **Poids** : Apache-2.0, dépôt public non restreint (`gated: false`).
- **Tiers liés dans ce binaire** (`NOTICE` et `servers/ggml/` du commit épinglé) :
  - **ggml** (sous-module `servers/ggml/ggml`) : MIT, « The ggml authors ». Le
    binaire n'est pas le ggml nu : le `CMakeLists.txt` amont applique à la
    configuration les 11 correctifs de `servers/ggml/patches/` (6 CUDA, 5
    Metal) au sous-module épinglé. Ce sont des correctifs **portés par
    l'amont**, versionnés avec le commit du runtime ; aucun correctif local
    n'est ajouté ici ;
  - `json-schema-validator` (`servers/ggml/vendor/`) : MIT, Patrick Boettcher ;
  - **LMDB** 0.9.36 (`servers/ggml/vendor/lmdb`) : OpenLDAP Public License 2.8 ;
  - `zyphra-textnorm` (sous-module, bibliothèque statique Rust) : MIT ; ses
    ports tiers sont **NVIDIA NeMo-text-processing** (Apache-2.0),
    **sacremoses** (MIT) et les tables **CLDR 49** (Unicode-3.0).
- **Tiers de l'amont absents de cette image** : Mini-SGLang (MIT, backend
  `servers/sgl`), mlx-lm (MIT, backend `servers/mlx`), FuseAlign
  (Apache-2.0, édition de parole), z-speech-alignment (MIT, édition).
- **`espeak-ng`** (GPL-3.0) : aucun fichier du dépôt ne le contient, et le
  `CMakeLists.txt` du serveur ggml précise qu'il est « dlopen'ed at run time
  (`ZONOS3_ESPEAK_NG_LIBRARY`), never linked ». L'image ne l'installe pas et
  ne fixe pas cette variable : il n'est **jamais chargé**. La phonémisation
  suit le port embarqué (`servers/ggml/src/zonos3-phonemes.cpp`,
  `servers/ggml/src/server/phonemize.cpp`) et le lexique de prononciation.

L'image embarque ces textes sous `/usr/local/share/zonos3/` (`LICENSE`,
`NOTICE`, `third_party/licenses/`, les `LICENSE`/`NOTICE` de `ggml`,
`zyphra-textnorm`, `json-schema-validator` et `lmdb`) : MIT exige que l'avis
de copyright et la permission accompagnent toute copie, Apache-2.0 que le
`NOTICE` soit reproduit. Une image **publiée** avec ces binaires doit les
conserver ; les poids, eux, ne sont jamais dans l'image.

## Dépannage

| Symptôme | Cause | Geste |
|---|---|---|
| `exit 2` au démarrage, « fichier de modele absent » | le volume ne contient pas `backbone-ptq.gguf` ou `zac-keep2.gguf` | vérifier `ZONOS3_MODELS_PATH`, relancer `fetch_models.py` |
| `CUDA driver version is insufficient for CUDA runtime version` | pilote hôte trop ancien pour CUDA 12.8.1 | mettre à jour le pilote, ou reconstruire avec un `CUDA_VERSION` supporté |
| `no kernel image is available for execution on the device` | image construite pour une autre architecture | reconstruire avec `--build-arg CUDA_ARCH=<votre sm>` (86 par défaut) |
| port occupé | `1919` déjà pris sur l'hôte | changer `ZONOS3_PORT` (et l'URL du client) |
| `GET /v2/speakers` vide | le répertoire `voices/` n'a pas été monté | il doit être sous `ZONOS3_MODELS_PATH` |
| `403 Access denied` sur toute route, la sonde de santé comprise | `ZONOS3_ACCESS_TOKEN` est défini dans l'environnement du conteneur | présenter `Authorization: Bearer <jeton>`, ou retirer la variable |
| `400 {"detail":"format=wav needs stream=false"}` | `stream` vaut `true` par défaut côté serveur | ajouter `"stream": false` au corps de la requête |
| `400 Unsupported language code: 'fr'. Supported: …` | `fr` est le code « parlé » (reconnaissance), pas un code TTS | envoyer `language: "fr_fr"` |
| `400 Cached speaker operations require the X-TTS-Session-ID header.` | l'identifiant de voix est inconnu du serveur ; le message vient d'une autre route et ne décrit pas la cause | relever les identifiants par `GET /v2/speakers` (la voix française livrée est `default_517319c805b927e9`) |
| `422` sur `control_spans` | envoyé en dictionnaire « par axe » | envoyer une **liste** de fenêtres `{"start", "end", "controls"}` (section « Pilotage ») |
| la VRAM ne redescend pas après une session | comportement mesuré du runtime (section « Mesures du conteneur ») | `docker compose down` puis `up -d` entre deux sessions |

## Périmètre de cette tranche

**Livré ici** : l'image reproductible (runtime et poids épinglés, quatre
bibliothèques ggml autonomes), le compose borné par la mesure, la sonde de
santé, le jeton d'accès optionnel, la documentation de provenance et les
mesures du conteneur ci-dessus.

**Mesuré ici**, contre le binaire de ce service : démarrage, empreintes mémoire
et VRAM, RTF en simple et en lot, plafond de longueur, déterminisme au rejeu,
réponses du serveur aux requêtes mal formées.

**Hors périmètre** : l'édition de parole (`/v2/edit*`, poids
`edit/accents.gguf`), les plugins Python du serveur, le routage par la
passerelle, et les mesures du moteur (WER, prosodie) qui restent celles de la
tranche 2 — voir sur l'issue #25835 l'état des critères 3 à 8 (décision par
rôle, pilotage à trois axes, sidecar d'annotation, MP3/M4B).

**Écart connu, hors de ces fichiers** : confronté à ce serveur, le client v4
(`v4/zonos3_client.py`) envoie `language: "fr"` par défaut, `control_spans` en
dictionnaire et `format: "wav"` sans `stream: false` — trois formes que le
serveur refuse (`400`, `422`, `400`). Les tests du client assertent la forme
dictionnaire. La correction se fait dans une PR à part, sur les fichiers du
client.

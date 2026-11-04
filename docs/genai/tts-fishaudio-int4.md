# `tts-fishaudio` — la route 4 bits, enfin réelle

Service : `docker-configurations/services/tts-fishaudio/` (image officielle `fishaudio/fish-speech:latest`, GPU 1, RTX 3090 24 Go).

Ce document est le **rapport de mesure** de la quantification int4 du modèle FishAudio S2-Pro. Il complète l'« état mesuré » de `docs/genai/genai-services.md` (PR #23241) : celui-ci corrige l'**annonce** de quantification, celui-ci rend le 4 bits **réel**.

Grain : `DEEP/genai` — lane `myia-po-2023:CoursIA` — issue #23415 — parent #23252.

---

## 1. Le chemin réel : int4 weight-only **de l'image amont**, sans fork

L'image officielle embarque son propre quantificateur :

| Élément | Emplacement dans l'image | Ce que c'est |
|---|---|---|
| l'outil | `tools/llama/quantize.py` | CLI `click` : `--checkpoint-path`, `--mode int8\|int4`, `--groupsize`, `--timestamp` |
| la sortie | `checkpoints/fs-1.2-int4-g{groupsize}-{timestamp}/model.pth` | poids quantifiés **weight-only**, par canal et par groupe |
| la branche du chargeur | `fish_speech/models/text2semantic/llama.py` (`from_pretrained`) | `if "int4" in str(Path(path))` → `WeightOnlyInt4QuantHandler` |
| l'empaquetage | `torch.ops.aten._convert_weight_to_int4pack` | int4 affine par groupe, `groupsize` ∈ {32, 64, 128, 256} |

Le nom du dossier produit porte **deux** informations que le chargeur relit : le mot `int4` (sélection de la branche) et le segment `-g128-` (`path.name.split("-")[-2]`, qui doit commencer par `g`). L'outillage amont produit donc, par construction, un dossier que son propre chargeur sait lire.

**Ce n'est pas du bitsandbytes NF4.** Le mécanisme est un quantifié weight-only affine par groupe (ligne `torch.ops.aten`), pas le format NF4 de bitsandbytes. La distinction n'est pas cosmétique : l'image ne contient ni `bitsandbytes` ni `accelerate`, et aucun chemin `bnb4` — donc un checkpoint NF4 (comme ceux publiés pour S2-Pro) n'y est **pas** chargeable, ce que confirme le model card du dérivé « not a legacy int4 or int8 export ».

## 2. Les quatre défauts de l'outillage amont, et ce qu'on leur oppose

### 2.1 L'empaquetage int4, cassé sur le torch de l'image (le défaut décisif)

L'amont appelle `_convert_weight_to_int4pack(codes_int32, ...)`, écrit pour un torch où l'op acceptait des codes int32. Sur le torch 2.8 de l'image, l'op exige un tenseur **uint8** à **deux codes 4 bits par octet**, le code d'indice **pair dans le nibble haut** ; sans correctif : `RuntimeError: Expected in.dtype() == at::kByte to be true`. Et le `scales_and_zeros` doit rester en **bfloat16** — en fp32 le noyau rend une constante, en fp16 des valeurs aberrantes (mesuré, dans l'image, par round-trip sur des codes connus).

**Correctif :** le wrapper réécrit `prepare_int4_weight_and_scales_and_zeros` (re-empaquetage uint8) et **s'auto-contrôle avant d'écrire** : un round-trip `pack → mm` sur une matrice de codes connus doit restituer les codes à l'identique (erreur max `0.0` mesurée) — sinon il sort sans produire de checkpoint. C'est ce contrôle qui distingue un empaquetage vérifié d'un empaquetage plausible.

### 2.2 Le pic mémoire

`quantize()` dépose le modèle sur CPU (`device = "cpu"`), et la construction d'un `nn.Linear` se fait en float32 par défaut. Sur le modèle `dual_ar` de S2-Pro (36 couches de texte, `dim` 2560, `intermediate_size` 9728, plus 4 « fast layers » et leur tête de sortie — **201 `nn.Linear` au total**, toutes quantifiées), la construction seule dépasse la RAM disponible du siège — et le siège héberge des runners CI dans WSL.

**Correctif :** construire et charger directement sur GPU. `torch.set_default_device("cuda")` + `torch.set_default_dtype(torch.bfloat16)` avant la construction, et `device="cuda"` au chargement. Le quantificateur amont déplace de toute façon chaque matrice de poids sur le CUDA pour l'empaquetage (`prepare_int4_weight_and_scales_and_zeros` fait `.to("cuda")`) : le GPU était déjà requis, il est simplement mis au bon endroit.

### 2.3 Le dossier de sortie, inexploitable tel quel

`quantize()` recopie le dossier source dans le dossier quantifié, **shards `.safetensors` et `model.safetensors.index.json` compris**. Or le chargeur privilégie l'index, puis le shard unique, et ne tombe sur `model.pth` qu'**en dernier** :

```text
index_json.exists()  -> shards bf16   (choisi ici)
elif single_st.exists() -> shard bf16
elif pth_file.exists() -> model.pth quantifie   (jamais atteint)
```

Sans correction, le service chargerait les poids **bf16 d'origine** : la quantification serait un succès apparent et un effet nul — le pire des deux mondes, puisque la VRAM mesurée ne baisserait pas.

**Correctif :** retirer les shards bf16 et l'index du dossier de sortie après production. Le chargeur prend alors la branche `model.pth`.

### 2.4 Le chargeur int4 plante sur un chemin `str` (côté serveur)

La branche int4 du chargeur relit le groupsize dans le **nom** du dossier : `path.name.split("-")` — donc elle exige un `pathlib.Path`. Or l'API server passe le chemin en **chaîne** (`init_model` → `from_pretrained`, mesuré dans l'image) : le chargement d'un checkpoint int4 s'arrête sur

```text
AttributeError: 'str' object has no attribute 'name'
```

juste après le message `Using int4 quantization!`. Le quantificateur amont ne voit jamais ce défaut : click lui fournit déjà un `Path` (`path_type=Path`).

**Correctif :** le wrapper [`serve_int4.py`](../../docker-configurations/services/tts-fishaudio/serve_int4.py) convertit `checkpoint_path` en `Path` avant l'appel, puis exécute `tools/api_server.py` avec les arguments reçus inchangés. Le compose le monte en lecture seule et ne l'utilise que sur la variable `FISHAUDIO_SERVE_SCRIPT` — le chemin fp16 par défaut ne passe pas par lui.

### 2.5 Cohérence du padding (vérifiée, pas subie)

Le quantificateur et le runtime partagent **le même** prédicat `_check_linear_int4_k(k, groupsize, inner_k_tiles)` :

- si le prédicte est vrai → ni le checkpoint ni le runtime ne paddent ;
- sinon → les deux paddent à `find_multiple(in_features, 1024)`.

Avec `groupsize=128`, `inner_k_tiles=8` : `dim=2560` et `intermediate=9728` sont divisibles par 128 → **aucun padding**, des deux côtés. L'égalité des formes est donc structurelle, pas fortuite — c'est ce qui autorise `load_state_dict(..., strict=False)` sans `size mismatch`.

## 3. La recette reproductible

Script : [`docker-configurations/services/tts-fishaudio/quantize_int4.py`](../../docker-configurations/services/tts-fishaudio/quantize_int4.py).

```bash
cd docker-configurations/services/tts-fishaudio

docker run --rm --gpus '"device=1"' \
  --entrypoint /app/.venv/bin/python \
  -v "$PWD/checkpoints:/app/checkpoints" \
  -v "$PWD/quantize_int4.py:/app/quantize_int4.py:ro" \
  -w /app fishaudio/fish-speech:latest \
  /app/quantize_int4.py --checkpoint-path checkpoints/s2-pro --groupsize 128 --timestamp 20261030
```

Deux points qui ne se devinent pas :

- **`--entrypoint /app/.venv/bin/python` est obligatoire.** L'entrypoint de l'image lance `run_webui.py`, qui intercepte les arguments et sort en `unrecognized arguments` (le compose du service le signale d'ailleurs dans ses commentaires).
- **La commande `quantize` de l'amont est un objet `click.Command`** : l'appeler directement lève `TypeError: 'PosixPath' object is not iterable`. Le wrapper appelle `.callback`.

Sortie : `checkpoints/fs-1.2-int4-g128-20261030/`.

### 3.1 Servir le checkpoint

Le service lit le checkpoint par deux variables du compose (aucune édition de fichier) :

```bash
FISHAUDIO_SERVE_SCRIPT=serve_int4.py \
FISHAUDIO_HALF_FLAG= \
LLAMA_CHECKPOINT_PATH=checkpoints/fs-1.2-int4-g128-20261030 \
  docker compose up -d tts-fishaudio
```

- `FISHAUDIO_SERVE_SCRIPT` prend le correctif de chargement du §2.4 (relatif au répertoire de travail de l'image, `/app`) ;
- `FISHAUDIO_HALF_FLAG` **vide** retire `--half` : l'int4 exige ses `scales_and_zeros` en bfloat16, et `--half` les caste en fp16 (le noyau rend alors des valeurs aberrantes, mesuré). La forme `${VAR-default}` du compose ne se replie que si la variable est **indéfinie** — `${VAR:-default}` se replierait aussi sur une variable vide et collerait `--half` de force.

## 4. Les mesures

Toutes prises sur le siège `myia-po-2023`, GPU 1 (RTX 3090 24 Go), image `fishaudio/fish-speech:latest` (torch 2.8), le même jour, même texte de test et `seed=42` des deux côtés.

### 4.1 Checkpoint

| | bf16 (source) | int4 g128 (produit) |
|---|---|---|
| poids du modèle de texte | 9,12 Go (2 shards safetensors) | **2,96 Go** (`model.pth`, 35 % de la source) |
| contenu | 201 `nn.Linear` en bf16 | 4,05 Md de poids à 4 bits + 0,58 Md non quantifiés (embeddings, normes) en bf16 |
| production | — | 364 s sur GPU 1, contrôle d'empaquetage erreur max **0.0** |

### 4.2 Service au warm-up

| | fp16 (`--half`) | int4 (bf16, `FISHAUDIO_HALF_FLAG=`) |
|---|---|---|
| journal du chargeur | `All keys matched successfully` | `Using int4 quantization!` puis `All keys matched successfully` — aucun `size mismatch`, aucune clé manquante |
| VRAM GPU 1, totale mesurée après une synthèse | 23 061 MiB | **17 429 MiB** |
| VRAM attribuable au service (plancher partagé de la carte : 5 022 MiB — `tts-api`, `tts-tada`, `tts-qwen`, `tts-kokoro`) | ~18,0 Gio | **~12,4 Gio** |
| temps de la synthèse (même texte) | 17,5 s | 23,2 s |

Le gain attribuable au service est **−5,6 Gio (−31 %)** — cohérent avec les poids (9,12 − 2,96 = 6,16 Go soustraits, plus les copies de chargement). La carte 24 Go passe de « saturée » (23,1/24,6 Gio) à « 7 Gio de marge ».

### 4.3 Qualité audio (mesure, pas impression)

Même texte, même graine, métriques du signal du wav produit (RMS, pic, taux de passage à zéro, enveloppe d'énergie par trames de 20 ms — stdlib `wave`/`array`) puis transcription indépendante par le service `whisper-api` local :

| | fp16 | int4 |
|---|---|---|
| durée du wav | 6,04 s | 7,38 s (+22 %) |
| RMS / pic | 5 510 / 27 968 (non saturé) | 5 050 / 23 168 (non saturé) |
| taux de passage à zéro | 0,072 | 0,128 (plage parole ; un rendu bruité serait > 0,4) |
| transcription whisper fr | « Bonjour, ceci est un test de la quantification 4 bits du modèle de synthèse vocale de fiches audio. » | **la même, mot pour mot** |

Verdict : sortie **non muette, non bruitée, intelligible** — la transcription indépendante est identique mot à mot. La dégradation réelle est **prosodique** : débit plus lent (+22 % de durée) et enveloppe d'énergie décorrélée de la sortie fp16 (corrélation 0,32) — le modèle parle différemment, pas moins bien de façon mesurable. On ne prétend pas ici que l'int4 « vaut » le fp16 : on mesure que la route produit de la parole fidèle au texte demandé, et que le coût observable est le rythme.

## 5. Ce que ce document ne dit pas

- Il ne dit pas que le NF4 est faux : le NF4 **est** un format valide, simplement il n'est **pas chargeable** par cette image (ni `bitsandbytes`, ni branche `bnb4`). La voie du fork (`groxaxo/fish-speech-int4-patch`) reste ouverte et n'est pas abandonnée — elle est simplement **différée**, la voie amont étant sans fork et sans téléchargement.
- Il ne dit pas que 4 bits vaut mieux que 8 bits : le choix `int4` / `int8` de l'amont existe, et `int8` (weight-only symétrique par canal) est un repli à coût de mémoire moindre.
- Les chiffres de VRAM de la section 4 sont des **mesures sur la carte qui porte le service** (GPU 1), pas des extrapolations depuis une taille de fichier.

## Voir aussi

- `docs/genai/genai-services.md` — « Quantification — mesures » et « Politique d'hébergement » (PR #23241)
- `docker-configurations/services/tts-fishaudio/README.md` — installation et API du service
- issue #23415 (le grain), #23252 (parent : l'organe de confrontation doc ↔ quantification)

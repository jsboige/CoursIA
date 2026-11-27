# Paramètres par modèle — table de référence mesurée

Issue d'origine : [#20682](https://github.com/jsboige/CoursIA/issues/20682). Les carnets GenAI
passent des paramètres d'échantillonnage ou de rendu (`temperature`, `top_p`, `top_k`, `style`…)
à des modèles qui les **refusent** (HTTP 400) ou les **ignorent en silence**. Cette table dit,
par modèle utilisé dans les carnets, ce que chaque paramètre devient — **mesuré par un appel
réel, daté, jamais recopié de la documentation**.

La garde consommable vit dans
[`MyIA.AI.Notebooks/GenAI/00-GenAI-Environment/param_guard.py`](../../MyIA.AI.Notebooks/GenAI/00-GenAI-Environment/param_guard.py)
(avec son test), qui lit la même matrice au format machine :
[`param_matrix.json`](../../MyIA.AI.Notebooks/GenAI/00-GenAI-Environment/param_matrix.json).

## Légende des verdicts

| Verdict | Sens exact | Ce qu'il ne dit PAS |
|---|---|---|
| **ACCEPTE** | L'appel HTTP passe (200) avec ce paramètre | Ce n'est pas la preuve d'un effet mesuré sur la sortie |
| **REFUSE** | L'API répond 400 au niveau du paramètre (message cité dans la matrice JSON) | — |
| **IGNORE** | L'appel passe, mais le paramètre est abandonné en route sans effet — preuve croisée : la passerelle répond 200 alors que l'API directe refuse le même paramètre pour le même modèle | L'effet n'est pas nul par API, il est nul par mesure croisée |
| **NON_CONCLUABLE** | La mesure n'a pas pu trancher (accès clé/organisation, modèle retiré, endpoint injoignable) — motif cité | — |

## Famille texte — mesure du 2026-10-26 (lane `myia-po-2027:CoursIA`)

Paramètres sondés : `temperature=0.0` · `top_p=0.9` · `top_k=40` · `frequency_penalty=0.5` ·
`presence_penalty=0.5` · `logprobs=true` · `seed=42` · `max_tokens=16` ·
`max_completion_tokens=80` · `reasoning_effort="low"`.

Appel type (une sonde = un appel) :

```python
POST {base_url}/chat/completions
{"model": "<modele>", "messages": [{"role": "user", "content": "Dis juste: ok."}],
 "<parametre>": "<valeur>"}
```

| Paramètre | `gpt-5-mini`<br>api.openai.com | `gpt-4o-mini`<br>api.openai.com | `openai/gpt-5-mini`<br>openrouter.ai | `meta-llama/llama-3.3-70b-instruct`<br>openrouter.ai | `qwen3.6-35b-a3b`<br>vLLM medium (façade) | `swift-1.5-27b`<br>vLLM cluster + passerelle ¹⁰ |
|---|---|---|---|---|---|---|
| `temperature` | **REFUSE** ¹ | ACCEPTE | **IGNORE** ⁵ | ACCEPTE | ACCEPTE | ACCEPTE ¹⁰ |
| `top_p` | **REFUSE** ² | ACCEPTE | **IGNORE** ⁵ | ACCEPTE | ACCEPTE | ACCEPTE ¹⁰ |
| `top_k` | **REFUSE** ³ | **REFUSE** ⁷ | **IGNORE** ⁵ | ACCEPTE | ACCEPTE | ACCEPTE ¹⁰ |
| `frequency_penalty` | **REFUSE** ² | ACCEPTE | **IGNORE** ⁵ | ACCEPTE | ACCEPTE | ACCEPTE ¹⁰ |
| `presence_penalty` | **REFUSE** ² | ACCEPTE | **IGNORE** ⁵ | ACCEPTE | ACCEPTE | ACCEPTE ¹⁰ |
| `logprobs` | NON_CONCLUABLE ⁴ | ACCEPTE | **REFUSE** ⁶ | ACCEPTE | ACCEPTE | ACCEPTE ¹⁰ |
| `seed` | ACCEPTE | ACCEPTE | ACCEPTE | ACCEPTE | ACCEPTE | ACCEPTE ¹⁰ |
| `max_tokens` | **REFUSE** ⁸ | ACCEPTE | **IGNORE** ⁵ | ACCEPTE | ACCEPTE | ACCEPTE ¹⁰ ¹¹ |
| `max_completion_tokens` | ACCEPTE | ACCEPTE | ACCEPTE | ACCEPTE | ACCEPTE | ACCEPTE ¹⁰ |
| `reasoning_effort` | ACCEPTE | **REFUSE** ⁹ | ACCEPTE | ACCEPTE | ACCEPTE | ACCEPTE ¹⁰ ¹² |

- ¹ `Unsupported value: 'temperature' does not support 0.0 with this model. Only the default (1) value is supported.`
- ² `Unsupported parameter: '<p>' is not supported with this model.`
- ³ `Unknown parameter: 'top_k'. Did you mean 'top_p'?`
- ⁴ `403 You are not allowed to request logprobs from this model` — refus de **compte/organisation**, pas de forme de paramètre : à re-mesurer après vérification org.
- ⁵ La passerelle OpenRouter répond 200, mais l'API directe refuse le même paramètre pour `gpt-5-mini` (mesures ¹²³⁸ du même jour) : le paramètre est abandonné en route, sans effet et sans erreur.
- ⁶ `400 Provider returned error` — refus au niveau passerelle.
- ⁷ `Unrecognized request argument supplied: top_k`.
- ⁸ `Unsupported parameter: 'max_tokens' is not supported with this model. Use 'max_completion_tokens' instead.`
- ⁹ `Unrecognized request argument supplied: reasoning_effort` — le curseur de raisonnement n'existe que sur les modèles de raisonnement.
- ¹⁰ Colonne `swift-1.5-27b` : mesure du **2026-11-25**, lot de dix sondes (une par paramètre), pour le nom demandé `swift-1.5-27b` sur deux endpoints — le vLLM du cluster `http://192.168.0.47:5002/v1` et la passerelle `https://models.myia.io/v1`. Les vingt appels répondent **HTTP 200** : aucun paramètre n'est refusé, les dix verdicts sont ACCEPTE. Détail, routage de clé et effet mesuré : [la section dédiée](#swift-15-27b--mesure-du-2026-11-25-le-modèle-servi-par-le-cluster).
- ¹¹ Effet visible du plafond : à `max_tokens=16`, la génération s'arrête en `finish_reason=length` avec exactement 16 tokens de complétion — le paramètre n'est pas seulement toléré, il borne la sortie.
- ¹² `reasoning_effort="low"` passe de 15 à 45 `prompt_tokens` sur le vLLM du cluster (le serveur insère une consigne de budget de raisonnement dans le prompt), tandis que la passerelle laisse le prompt à 15 tokens : **le même modèle, deux endpoints, deux effets** — c'est ce que la colonne dit, et pas davantage.

**Familles** : la matrice machine porte `gpt-5*` (mesuré sur `gpt-5-mini`) et `gpt-4o*`
(mesuré sur `gpt-4o-mini`) comme entrées explicites — un modèle non mesuré de la famille
hérite du comportement mesuré de son représentant, et la garde le dit dans sa ligne d'avertissement.

**Ce qui n'est plus mesurable en direct** (mesuré le même jour, à re-mesurer via OpenRouter
ou un modèle vivant) :

- `o4-mini` : **déprécié** chez OpenAI (404 deprecation sur `o4-mini` et `o4-mini-2025-04-16`).
  Conséquence immédiate : toute cellule qui l'appelle en direct saute ou échoue — voir l'audit ci-dessous.
  Le mécanisme, et la distinction avec un simple refus d'accès, sont documentés dans
  « Cycle de vie d'un identifiant » plus bas.
- `deepseek/deepseek-r1` : **plus servi par aucun fournisseur OpenRouter**
  (`no provider serves this model anymore`).

## `swift-1.5-27b` — mesure du 2026-11-25 (le modèle servi par le cluster)

Les carnets GenAI de la série Audio et d'autres séries font tous appel à
`llm_model = "swift-1.5-27b"` (`04-6-Audiobook-Pipeline`, `04-1-Educational-Audio-Content`,
`04-5-LiveCoding-LLM-Music`, `03-3-Realtime-Voice-API`) : c'est le modèle que sert le vLLM du
cluster. La matrice ne le couvrait pas — la garde restait donc muette sur ses paramètres,
faute de mesure.

### Les deux endpoints qui servent ce modèle

| Endpoint | Clé qui l'authentifie | `GET /models` |
|---|---|---|
| `http://192.168.0.47:5002/v1` (vLLM du cluster) | `VLLM_API_KEY_MEDIUM` (alias cible `TGWUI_MEDIUM_API_KEY`) | 200 — 2 modèles (`swift-1.5-27b`, `qwen3.6-35b-a3b`) |
| `https://models.myia.io/v1` (passerelle fleet) | `CLAUDISH_PROXY_KEY` | 200 — 36 modèles |

**Connectivité et authentification sont deux observations distinctes.** Le 13 novembre,
la connexion TCP au port 5002 expirait depuis `myia-po-2027` : l'authentification n'était
pas atteinte et la cause du timeout n'a pas été établie. Le 25 novembre, le port était
joignable depuis cette lane ; `VLLM_API_KEY` recevait un 401, tandis que
`VLLM_API_KEY_MEDIUM` recevait 200. Un refus d'authentification avait aussi été observé
le 12 novembre depuis `myia-po-2023` avec `VLLM_API_KEY`. Ces observations ne permettent
pas de déduire la cause du timeout depuis un autre siège.

### Les dix sondes

Pour le nom demandé `swift-1.5-27b`, un lot de dix appels, un par paramètre, sur chaque endpoint (vingt appels au total) :
**HTTP 200 partout**, aucune bannière `Unsupported parameter` — donc dix verdicts **ACCEPTE**
dans la matrice machine. Trois effets ont été relevés au passage :

- `max_tokens=16` → `finish_reason=length`, 16 tokens de complétion : le plafond agit ;
- `temperature=0.0` est accepté — la famille `gpt-5` le refuse ;
- `reasoning_effort="low"` porte le prompt de 15 à 45 tokens sur le vLLM du cluster et le
  laisse à 15 sur la passerelle : même modèle, deux déploiements, deux effets.

### Le nom servi n'est pas le même selon l'endpoint

L'endpoint du cluster sert les **deux noms** pour le même checkpoint (Swift-1.5-Qwen3.8-27B
W4A16-AWQ — voir [#26832](https://github.com/jsboige/CoursIA/issues/26832) et
[`docs/genai/model-mapping-openai.md`](model-mapping-openai.md)) ; l'alias qui l'emporte dépend
de l'endpoint. Mesuré le 2026-11-25T06:02:56Z :

| Endpoint | Nom demandé | `model` renvoyé |
|---|---|---|
| vLLM du cluster `:5002` | `swift-1.5-27b` | `qwen3.6-35b-a3b` |
| vLLM du cluster `:5002` | `qwen3.6-35b-a3b` | `qwen3.6-35b-a3b` |
| passerelle `models.myia.io` | `swift-1.5-27b` | `swift-1.5-27b` |
| passerelle `models.myia.io` | `qwen3.6-35b-a3b` | `swift-1.5-27b` |

Ce tableau décrit les noms renvoyés, pas une mesure des paramètres sous chaque nom. Les dix
sondes ont demandé `swift-1.5-27b` sur chacun des deux endpoints ; leurs verdicts ne sont pas
étendus ici aux appels demandant `qwen3.6-35b-a3b`.

### Ce que cela dit des sept sites `max_tokens` de #24114

Les sept appels du tableau de l'issue ont été rejoués **avec leur forme exacte** (température,
`max_tokens`, et `chat_template_kwargs` pour les quatre appels `llm_client`) :

| Site | Endpoint | Résultat |
|---|---|---|
| `04-6` c.9 (`max_tokens=1000`) | vLLM du cluster | **HTTP 200**, pas de bannière |
| `04-6` c.12 (`max_tokens=1500`) | vLLM du cluster | **HTTP 200**, pas de bannière |
| `04-1` c.9 (`max_tokens=1000`) | vLLM du cluster | **HTTP 200**, pas de bannière |
| `03-3` c.23 (`max_tokens=200`) | vLLM du cluster | **HTTP 200**, pas de bannière |
| `04-5` c.20 / c.33 / c.36 (`max_tokens=2000`) | passerelle fleet | **HTTP 200** ×3, pas de bannière |

Le refus de `max_tokens` est donc **propre à l'API directe `gpt-5.6-luna`** — le cas de
`04-11-Generation-TTS`, corrigé sur `main`. Sur les modèles que sert le cluster, le paramètre
est accepté et il agit : **aucune modification de source n'est justifiée sur ces sept sites**,
ce que l'issue demandait de vérifier avant tout changement.

## Famille image — mesure du 2026-10-26

Appel type : `POST https://api.openai.com/v1/images/generations` avec un seul paramètre sonde
par appel, prompt minimal.

| Paramètre | `gpt-image-1` | `dall-e-3` |
|---|---|---|
| `style` | **REFUSE** (`Unknown parameter: 'style'.`) | **REFUSE** (`Unknown parameter: 'style'.`) ¹⁰ |
| `quality` | NON_CONCLUABLE ¹¹ | NON_CONCLUABLE ¹¹ |
| `size` | NON_CONCLUABLE ¹¹ | (non re-sondé : même cause ¹¹) |
| `response_format` | **REFUSE** (`Unknown parameter: 'response_format'.`) | **REFUSE** (`Unknown parameter: 'response_format'.`) |

- ¹⁰ Le refus est au **niveau de la forme de l'API** (la validation du payload précède la
  résolution du modèle) : ces deux paramètres ne sont plus des champs de
  `/images/generations` pour la clé de mesure.
- ¹¹ `400 The model '<modele>' does not exist` — **accès clé/organisation** au modèle d'image,
  pas un refus de paramètre. La PR [#21340](https://github.com/jsboige/CoursIA/pull/21340)
  (2026-10-19, lane `myia-po-2023:CoursIA-2`) a exécuté `gpt-image-1` avec succès (17/17
  cellules, `image/png` réel) depuis le `.env` du carnet : l'accès dépend de la clé, la
  mesure ci-dessus dit ce que fait la clé partagée `master.env`.

**Moteurs locaux (ComfyUI, Forge)** : pas de paramètre `style`/`quality` homologue — le
réglage vit dans le graphe de workflow (nœuds KSampler, etc.), pas dans un appel REST à
paramètres nommés. Sondes de surface du 2026-10-26 depuis `po-2027` : LAN `192.168.0.47`
(timeout), `comfyui.myia.io` (SSLError), `comfyui-video.myia.io/system_info` (502) — aucune
surface atteinte ce jour-là ; à compléter depuis une machine du stack quand besoin.

## Cycle de vie d'un identifiant — le catalogue ne dit pas si l'appel passe

Un identifiant que le fournisseur annonce n'est **pas** forcément appelable avec notre clé.
Ce n'est pas une supposition : c'est mesuré. Le 2026-10-26, `GET /v1/models` renvoyait une
liste de 140 identifiants où `o4-mini` et `o3-mini` figuraient toujours — et l'appel direct
refusait les deux.

| Identifiant | `POST /v1/chat/completions` | `GET /v1/models` |
|---|---|---|
| `o4-mini` | **404** `model_not_found` — « The model `o4-mini` has been deprecated » | présent |
| `o3-mini` | **404** `model_not_found` — « The model `o3-mini` has been deprecated » | présent |
| `gpt-5` | 200 | présent |
| `gpt-5-mini` | 200 | présent |
| `gpt-5.6-sol` | 200 | présent |

Mesures : [#22707](https://github.com/jsboige/CoursIA/pull/22707) (lane `myia-ai-01:CoursIA-2`)
et [#22605](https://github.com/jsboige/CoursIA/pull/22605) (lane `myia-po-2027:CoursIA`,
mergée le 2026-10-28) — toutes deux du 2026-10-26, clé lue dans le `.env` du dépôt et jamais
affichée.

**La règle : tester l'endpoint du modèle, pas la liste.** Avant d'écrire un identifiant dans
un carnet, envoyer un appel minimal — `POST /v1/chat/completions`, une consigne minimale,
sortie plafonnée — et lire le verdict. `GET /v1/models` est le catalogue de ce que le
fournisseur déclare : il ne dit ni si notre clé atteint le modèle, ni si le modèle a été
retiré. Le catalogue et l'appel sont deux surfaces distinctes, et c'est la seconde qui fait
foi.

**Deux refus qui ne se confondent pas.** Un `404` `model_not_found` « has been deprecated »
annonce un **retrait par le fournisseur** : l'identifiant ne reviendra pas. Un
`400 The model '<modele>' does not exist` annonce un **accès clé/organisation** : le modèle
existe côté fournisseur, c'est notre clé qui n'y accède pas. Le second cas est celui mesuré
sur `gpt-image-1` et `dall-e-3` avec la clé partagée `master.env`, alors que
[#21340](https://github.com/jsboige/CoursIA/pull/21340) exécutait `gpt-image-1` avec succès
depuis le `.env` du carnet.

Un état de cycle de vie est une **mesure d'API**, pas une donnée de documentation : il se
périme comme le reste de la table et se re-mesure par appel. Le mapping courant reste
[`model-mapping-openai.md`](model-mapping-openai.md) ; l'état de cycle de vie des
identifiants se consigne ici, avec sa date de mesure.

## Utiliser la garde dans un carnet

```python
import sys
from pathlib import Path

env_dir = None
for cand in (Path.cwd(), Path.cwd().parent):
    if (cand / "00-GenAI-Environment" / "param_guard.py").exists():
        env_dir = cand / "00-GenAI-Environment"
        break
if env_dir:
    sys.path.insert(0, str(env_dir))
    from param_guard import guard_call

    # Signale a l'ecran chaque parametre refuse ou ignore, retire les refuses.
    params = guard_call("gpt-5-mini", {"temperature": 0.0, "max_completion_tokens": 200})
    # [param_guard] gpt-5-mini refuse 'temperature' (mesure 2026-10-26, ...) -- parametre retire
    reponse = client.chat.completions.create(model="gpt-5-mini", **params)
```

## Re-mesurer

Chaque case date de sa mesure ; une API bouge, la table se périme. Re-mesurer = rejouer un
appel minimal par case (le payload type ci-dessus), consigner verdict + date + `base_url`,
et régénérer `param_matrix.json` — la garde et cette page lisent la même donnée. Les
paramètres de sonde ci-dessus sont volontairement les plus petits qui déclenchent le refus
ou l'acceptation (16 tokens de sortie maximum hors raisonnement).

Re-mesurer l'état de cycle de vie d'un identifiant suit la même exigence : un appel par
identifiant, pas une lecture de `GET /v1/models` — voir « Cycle de vie d'un identifiant »
plus haut.

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

| Paramètre | `gpt-5-mini`<br>api.openai.com | `gpt-4o-mini`<br>api.openai.com | `openai/gpt-5-mini`<br>openrouter.ai | `meta-llama/llama-3.3-70b-instruct`<br>openrouter.ai | `qwen3.6-35b-a3b`<br>vLLM medium (façade) |
|---|---|---|---|---|---|
| `temperature` | **REFUSE** ¹ | ACCEPTE | **IGNORE** ⁵ | ACCEPTE | ACCEPTE |
| `top_p` | **REFUSE** ² | ACCEPTE | **IGNORE** ⁵ | ACCEPTE | ACCEPTE |
| `top_k` | **REFUSE** ³ | **REFUSE** ⁷ | **IGNORE** ⁵ | ACCEPTE | ACCEPTE |
| `frequency_penalty` | **REFUSE** ² | ACCEPTE | **IGNORE** ⁵ | ACCEPTE | ACCEPTE |
| `presence_penalty` | **REFUSE** ² | ACCEPTE | **IGNORE** ⁵ | ACCEPTE | ACCEPTE |
| `logprobs` | NON_CONCLUABLE ⁴ | ACCEPTE | **REFUSE** ⁶ | ACCEPTE | ACCEPTE |
| `seed` | ACCEPTE | ACCEPTE | ACCEPTE | ACCEPTE | ACCEPTE |
| `max_tokens` | **REFUSE** ⁸ | ACCEPTE | **IGNORE** ⁵ | ACCEPTE | ACCEPTE |
| `max_completion_tokens` | ACCEPTE | ACCEPTE | ACCEPTE | ACCEPTE | ACCEPTE |
| `reasoning_effort` | ACCEPTE | **REFUSE** ⁹ | ACCEPTE | ACCEPTE | ACCEPTE |

- ¹ `Unsupported value: 'temperature' does not support 0.0 with this model. Only the default (1) value is supported.`
- ² `Unsupported parameter: '<p>' is not supported with this model.`
- ³ `Unknown parameter: 'top_k'. Did you mean 'top_p'?`
- ⁴ `403 You are not allowed to request logprobs from this model` — refus de **compte/organisation**, pas de forme de paramètre : à re-mesurer après vérification org.
- ⁵ La passerelle OpenRouter répond 200, mais l'API directe refuse le même paramètre pour `gpt-5-mini` (mesures ¹²³⁸ du même jour) : le paramètre est abandonné en route, sans effet et sans erreur.
- ⁶ `400 Provider returned error` — refus au niveau passerelle.
- ⁷ `Unrecognized request argument supplied: top_k`.
- ⁸ `Unsupported parameter: 'max_tokens' is not supported with this model. Use 'max_completion_tokens' instead.`
- ⁹ `Unrecognized request argument supplied: reasoning_effort` — le curseur de raisonnement n'existe que sur les modèles de raisonnement.

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

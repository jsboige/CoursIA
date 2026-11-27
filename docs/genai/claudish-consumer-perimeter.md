# Périmètre des consommateurs claudish — carnets notebooks

**État mesuré au 2026-11-03** par la lane `myia-po-2027:CoursIA` sur `origin/main`, issue #14926. **Dernier addendum : 2026-11-21** (fournée 22b, lane `myia-po-2028:CoursIA` — [ci-dessous](#addendum-du-2026-11-21--22b-migre-et-une-mesure-du-gate-sinverse)).

Ce document répond à la demande du pre-flight du [runbook de flip d'authentification](auth-flip-runbook.md) (l.53) : « **énumérer les consommateurs claudish** ». Jusqu'ici cette énumération était refaite à la main à chaque audit, et elle a dérivé — la liste de huit carnets portée par le corps de #14926 (mesure du 2026-10-06) nomme encore `GameTheory-03c-Le-Joueur-LLM.ipynb` et `GameTheory-28b-Humour-Banc-Dur.ipynb`, **qui n'existent plus sous ces chemins**.

## Instrument

Parse JSON des cellules de code, jamais un `grep` de chaîne : dans un `.ipynb`, les guillemets des littéraux sont échappés, et un `grep` naïf sous-compte massivement — il ne voit qu'une fraction de ce que le parse trouve. Le relevé ci-dessous porte sur les seules cellules `code`, pas sur la prose markdown.

## Le périmètre mesuré

| Carnet | lit `VLLM_API_KEY` | présente `CLAUDISH_PROXY_KEY` | paramètres vLLM natifs | classe |
|---|---|---|---|---|
| `GenAI/SemanticKernel/04-SemanticKernel-Filters-Observability.ipynb` | oui | **oui** | — | **migré** |
| `GameTheory/GameTheory-16e-LLM-Players-Othman-Sandholm-Python.ipynb` | non | **oui** | — | **migré** |
| `GenAI/RAG-et-Memoire-Semantique/09-KernelMemory-Multimodal.ipynb` | oui | non | `chat_template_kwargs` | exception — paramètres ([gate B](#le-gate-de-la-fournée-b-tranché-classe-image-mesure-du-2026-11-26)) |
| `GenAI/Texte/10b_Inference_Mechanics.ipynb` | oui | non | `chat_template_kwargs` | exception — paramètres |
| `GenAI/Texte/10c_Long_Context_Strategies.ipynb` | oui | non | `chat_template_kwargs` | exception — paramètres |
| `GenAI/Texte/10_LocalLlama.ipynb` | oui | non | — | exception — sujet serving |
| `GenAI/_research/e2e_quant_validation.ipynb` | oui | non | — | exception — sujet serving ([gate B](#le-gate-de-la-fournée-b-tranché-classe-image-mesure-du-2026-11-26)) |
| `GenAI/Texte/22b_Profil_Cognitif_CHC.ipynb` | oui (repli) | **oui** | `chat_template_kwargs` (relayé, mesuré 2026-11-21) | **migré** ([addendum 2026-11-21](#addendum-du-2026-11-21--22b-migre-et-une-mesure-du-gate-sinverse)) |

## Les trois classes, et le motif de chacune

**1. Migrés.** `04-SemanticKernel-Filters-Observability` est la forme de référence : une clé dédiée à la façade, **sans repli** sur `OPENAI_API_KEY` (un repli enverrait le credential marchand au mauvais hôte — credential cross-provider interdit), et un commentaire qui dit que le recâblage de l'endpoint impose celui de la clé. Tout consommateur migrable doit prendre cette forme, pas une variante. La colonne « lit `VLLM_API_KEY` » décrit l'état **courant** du code, pas l'historique de migration : `04-SK` garde une occurrence de l'ancienne variable à côté des trois `CLAUDISH_PROXY_KEY`, tandis que `16e-LLM-Players`, migré de bout en bout, ne lit plus que la nouvelle.

**2. Exception — paramètres de serving.** Trois carnets passent `chat_template_kwargs` au moteur vLLM. C'est le **sujet** de ces carnets, pas un détail d'implémentation : `10b_Inference_Mechanics` enseigne le contrôle du gabarit de conversation, `10c_Long_Context_Strategies` la tenue du contexte sous ce gabarit, `09-KernelMemory-Multimodal` l'utilise pour sa propre démonstration. La passerelle claudish ne relaie pas cette sémantique (état mesuré au 2026-10-07 ; l'addendum du 2026-11-21 la mesure **désormais relayée**, `seed` et `logprobs` restant non mesurés) ; router ces carnets à travers elle **viderait la leçon de son objet** tout en laissant des sorties plausibles — exactement le workaround dégradé que [`sota-not-workaround.md`](../../.claude/rules/sota-not-workaround.md) interdit avant même C.2.

`GameTheory-18c-Humour-Banc-Python` passe aussi `chat_template_kwargs`, mais à **OpenRouter** (`OPENROUTER_API_KEY`, zéro occurrence de `VLLM_API_KEY` ou `CLAUDISH_PROXY_KEY`) : il n'appelle ni la pile vLLM ni la passerelle, et n'a donc pas sa place dans ce périmètre. Le motif pédagogique y est le même — le paramètre natif est le sujet — et il ne deviendrait consommateur qu'à la condition d'une migration OpenRouter→pile locale qui n'est pas à l'étude.

**3. Exception — le sujet est le serving.** `10_LocalLlama` et `e2e_quant_validation` parlent du serveur vLLM et de sa quantization. On ne démontre pas une quantization à travers un proxy qui n'expose pas le modèle quantifié. Pour `e2e_quant_validation`, le motif se précise au gate B : son sujet est le serving de **génération d'image**, et la passerelle n'expose ni route `/v1/images/generations` ni modèle de génération d'image.

## Le gate de la fournée A, tranché

Le cadrage du 2026-10-14 pose une décision binaire : **(a)** exception documentée, accès direct au sidebar conservé et motivé, **ou (b)** extension de la passerelle claudish pour relayer `chat_template_kwargs`, `seed` et `logprobs`.

**La branche retenue est (a)**, pour trois raisons qui ne dépendent pas d'une préférence :

1. **(b) n'est pas dans ce dépôt.** Le compose et le code de la passerelle vivent hors CoursIA (`D:\Dev\claudish`) ; une lane de ce dépôt ne modifie pas l'infrastructure d'un autre propriétaire — elle la demande.
2. **(b) serait bâti sur une passe en repli** : la passerelle répond aux appels réels — un `POST /v1/messages` avec la clé courante rend 200 — mais elle les sert aujourd'hui par son modèle de **repli** (`deepseek-flash`), pas par le modèle nominal. Étendre son relais maintenant consacrerait un chemin dégradé ; le préalable est que la passe reprenne son modèle nominal, pas qu'on lui ajoute des paramètres.
3. **Le motif pédagogique est le fond, pas la commodité.** Ces carnets n'évitent pas la passerelle par confort : ils ont besoin des paramètres natifs pour tenir leur propos.

La branche (a) **n'est pas un contournement** : elle déclare le périmètre au lieu de le laisser implicite, ce qui est précisément ce qui manquait pour que l'audit suivant n'ait pas à refaire — et à faire dériver — l'énumération.

## Ce qui reste bloquant, mesuré sur `po-2027`

| Mesure | Résultat | Conséquence |
|---|---|---|
| `GET localhost:3000/v1/models` | `{"object":"list","data":[]}` | **n'est pas un indicateur** : un sidecar relais rend une liste vide par construction (mesure du 2026-11-03) — n'en conclure aucun défaut |
| `POST /v1/messages` avec la clé courante | 200 en 1,04 s, réponse servie par `deepseek-flash` | la passe **fonctionne**, mais en **repli** — c'est précisément ce qui la rend inutilisable pour ces carnets |
| `POST /v1/chat/completions` avec la clé du `.env` local, avant correction | `{"type":"error","error":{"type":"authentication_error","message":"invalid proxy authentication"}}` | clé **inconnue** du sidecar, rapportée comme une requête **sans** clé : la valeur locale était en retard d'une rotation (mesure et correction du 2026-11-03, ci-dessous) |
| `python scripts/secrets/render_envs.py --check` | `[OK] 12/19 target .env on disk, in sync with master.env` | la distribution est en phase — **après** resynchronisation de `master.env` sur la valeur courante |

Conséquence directe : **sur `po-2027`, un appel de modèle s'exécute** — mais par le modèle de **repli** de la passe, jamais par le modèle nominal que ces carnets visent, et sans les paramètres natifs dont ils ont besoin. Ce qui manque n'est donc pas l'accès : c'est l'accès au **bon** modèle. Aucun carnet de ce périmètre n'est ré-exécuté ici, et C.2 interdit de committer une édition de carnet non ré-exécutée — c'est ce qui borne la livraison de #14926 à la décision et au périmètre.

### Ce que la mesure du 2026-11-03 a corrigé

Le raisonnement qui suivait concluait que la divergence siégeait **côté serveur**, dans un dépôt qui n'est pas celui-ci. La mesure l'a démenti, et le chemin de l'erreur vaut d'être gardé : le sidecar rapporte une clé **inconnue** comme une requête **sans clé** (`keyless request … proxy key required`). Cela se lit comme un défaut d'en-tête ou de passerelle, alors que la distribution locale était simplement en retard d'une rotation — et c'est exactement le diagnostic qu'un audit pressé aurait repris tel quel.

Ce qui tient, mesuré : le conteneur `claudish-sidecar` de `po-2027` porte la clé **courante** — il n'a donc pas à être recréé — et c'est `master.env` qui portait la précédente, d'où le refus. La correction est locale et a été faite : `master.env` aligné sur la valeur courante, puis `render_envs.py` pour les `.env` consommateurs (`--check` rend « in sync »).

La règle de redémarrage ne s'applique pas ici : elle vise les services qui recalculent un secret **au démarrage** (ComfyUI-Login, [secrets-management.md](secrets-management.md)). Un sidecar dont l'environnement est déjà correct n'a rien à redémarrer — un redémarrage n'aurait rien changé et aurait coupé la passe.

Le geste correctif de **cette** panne appartient donc à cette lane, et il est fait. Reste ce qui n'est pas à nous : que la passe serve le modèle nominal et relaie les paramètres natifs — cela se demande à son propriétaire.

## Addendum du 2026-11-21 — 22b migre, et une mesure du gate s'inverse

Deux faits nouveaux depuis le 2026-11-03, mesurés depuis `po-2028` (clé du coffre `MyIA-Keys`, empreinte identique à celle mesurée par po-2024) contre `https://models.myia.io/v1` :

1. **`22b_Profil_Cognitif_CHC` entre au périmètre comme migré.** Absent du relevé du 2026-11-03 (absence signalée le 2026-11-20 sur #14926), ce carnet batterie adresse la pile vLLM par sa route `hebergee`. Il gagne le couple canonique `https://models.myia.io/v1` + `CLAUDISH_PROXY_KEY` **en tête de cascade**, les couples directs historiques restant en repli. Ce repli n'est pas un écart à la forme de référence « sans repli » de `04-SK` : celle-ci interdit le repli sur un credential **marchand** (`OPENAI_API_KEY` vers la façade — credential cross-provider), tandis que le repli de 22b est **même-pile** (clé vLLM vers hôte vLLM direct) et que la cascade d'essais successifs est le sujet pédagogique de la cellule.
2. **La passerelle relaie désormais `chat_template_kwargs`.** Mesure : `enable_thinking=False` → `finish=stop`, réponse en 2 tokens à budget 5 ; sans le paramètre, `content=None` (le thinking consomme le budget) ; à budget 512 sans le paramètre, réponse en 37 tokens. Catalogue de 35 modèles, `swift-1.5-27b` servi tel quel (echo exact, pas de repli `deepseek-flash` observé sur ce checkpoint depuis ce siège). **Cela inverse la mesure du 2026-10-07** qui fondait la liste close `chat_template_kwargs, seed, logprobs` de la condition 2.

`seed` et `logprobs` restent **non mesurés** : la condition 2 de réouverture de la fournée A n'est **pas** réunie, et cette fournée (09, 10b, 10c) reste fermée — le motif pédagogique de ces carnets exige les trois sémantiques.

Conséquence pour la validation d'un couple passerelle : sur la façade, `GET /v1/models` est **exempt d'authentification** (proxy-auth). Le carnet juge donc le couple passerelle sur une **completion réelle** (sonde `max_tokens=2` avec le dialecte du carnet), jamais sur le listing — une clé périmée ne peut plus valider la cascade puis échouer en silence dans la batterie.

## Le gate de la fournée B, tranché (classe image, mesure du 2026-11-26)

Le gate de la fournée B attendait depuis le 2026-10-23 un « arbitrage classe image », ouvert par `myia-po-2026:CoursIA-2` et jamais rendu depuis. Il est rendu ici **par mesure**, contre les deux instances de la passerelle claudish, et il **scinde** la fournée : ses deux carnets ne relèvent pas du même service.

**Les mesures** (clé client lue depuis le `.env` du siège ; aucune valeur de secret n'apparaît ci-dessous, et aucune ne doit y apparaître) :

| Mesure | Instance | Résultat |
|---|---|---|
| `GET /v1/models` | `https://models.myia.io/v1` | 200 — catalogue de 36 entrées |
| `GET /v1/models` | `http://localhost:3000/v1` | 200 — catalogue de 5 entrées |
| `POST /v1/images/generations` | les deux instances | **404** — aucune route de génération d'image |
| `POST /v1/chat/completions`, contenu `image_url` en data URI (PNG 8×8 synthétisé en mémoire), modèle `deepseek-v4-flash-vision-exp` | `https://models.myia.io/v1` | 200 — l'image est **lue** : description conforme à l'image (« carré bleu en haut à gauche, le reste en rouge ») |
| idem, **sans** `chat_template_kwargs` | idem | 200 mais `content: null` — le budget de génération est absorbé par le raisonnement, comme mesuré le 2026-11-21 |
| `POST /v1/chat/completions`, modèle `qwen3.6-35b-a3b` | les deux instances | **502** (21 s sur l'instance publique, 42 s sur l'instance locale) — la route vers le serving du cluster ne répond pas |

Les deux catalogues sont **différents** (5 entrées d'un côté, 36 de l'autre) et aucun ne porte de modèle de génération d'image. Un catalogue ne prouve rien de la capacité d'un modèle — seule la completion réelle vaut, comme la règle de validation ci-dessus l'établit.

**Branche 1 — la vision consommée est servie.** La charge utile image traverse la passerelle et un modèle de vision la lit : la classe « image » n'est pas un obstacle de la passerelle. `09-KernelMemory-Multimodal` **consomme** une image (entrée) pour en tirer une description (sortie) ; il n'est donc plus bloqué par la classe image.

**La condition qui reste, et elle est unique.** Ce carnet ne démontre pas un modèle hébergé, il démontre « le vLLM maison du cluster (vision+thinking) » : une migration qui changerait de modèle changerait le propos du carnet et remplacerait une preuve par une autre. La migration fidèle — **même modèle `qwen3.6-35b-a3b`, même serving**, seule la clé change (clé client claudish au lieu de `VLLM_API_KEY`) — suppose que la passerelle serve ce modèle. **Au 2026-11-26, elle répond 502 sur les deux instances.** La condition est donc rejouable en une requête : `POST /v1/chat/completions` avec `qwen3.6-35b-a3b` doit répondre 200. Tant qu'elle ne répond pas, le carnet garde son couple direct, et son exception documentée reste vraie.

**Branche 2 — la génération d'image est hors du périmètre de la passerelle.** `e2e_quant_validation` **produit** des images (`z-image`, `Tongyi-MAI/Z-Image-Turbo` servi par vLLM Omni) et interroge ComfyUI (édition d'image, vidéo). La passerelle n'expose **ni** route `/v1/images/generations` (404 mesuré) **ni** modèle de génération d'image dans ses catalogues. L'exception n'est donc pas un choix de commodité : elle est structurelle, et son motif se précise par rapport à la classe 3 — le sujet est le serving **de génération d'image**, que la passerelle ne relaie pas.

**Ce que cette livraison ne fait pas.** Aucun carnet n'est touché : la branche 1 exige la ré-exécution du carnet sur un siège qui porte le couple `qwen3.6-35b-a3b` servi (C.2), et la branche 2 ne demande aucune édition. Le gate est donc rendu et la fournée B **scindée**, pas fermée.

## Condition de réouverture

La fournée A redevient migrable — en **une seule PR pour les deux carnets**, jamais une PR par carnet — quand les quatre conditions suivantes sont réunies :

1. la passerelle sert les modèles visés **hors repli** — mesuré par un vrai `POST /v1/messages`, jamais par `/v1/models` (une liste vide est le comportement normal d'un sidecar relais) ;
2. elle relaie `chat_template_kwargs`, `seed` et `logprobs` sans les perdre (la liste est close et chiffrée par la mesure du 2026-10-07) ;
3. `render_envs.py --check` rend 0 sur la machine qui exécute — **déjà vérifié sur `po-2027`** au 2026-11-03 ;
4. la valeur serveur de la passerelle correspond à celle que `master.env` distribue — **vérifié sur `po-2027`** au 2026-11-03 ; tout écart se corrige côté distribution locale, sans redémarrage quand le conteneur porte déjà la bonne valeur.

Tant que ces conditions ne sont pas réunies, la classe 2 et la classe 3 ci-dessus restent telles quelles. Le geste utile n'est pas de les migrer, c'est de constater qu'elles n'ont pas bougé.

### Condition de réouverture de la fournée B

La branche « vision consommée » (`09-KernelMemory-Multimodal`) redevient migrable — en **une seule PR pour ce carnet**, comme la fournée A en une PR pour deux — quand les trois conditions suivantes sont réunies :

1. `POST /v1/chat/completions` avec `qwen3.6-35b-a3b` répond 200 sur l'instance que la machine exécutrice utilise — mesuré **502** le 2026-11-26 sur les deux instances ;
2. le couple retenu reste `CLAUDISH_BASE_URL` + `CLAUDISH_PROXY_KEY`, **sans** changement de modèle ni de serving — c'est la clé qui change, pas la preuve ;
3. `render_envs.py --check` rend 0 sur la machine qui exécute.

La branche « image générée » (`e2e_quant_validation`) ne se rouvre pas : elle reste une exception tant que la passerelle n'expose ni route `/v1/images/generations` ni modèle de génération d'image — les deux mesures du 2026-11-26.

## Voir aussi

- [auth-flip-runbook.md](auth-flip-runbook.md) — la procédure de flip dont ce document sert le pre-flight
- [secrets-management.md](secrets-management.md) — `master.env` → `render_envs.py` → `.env` consommateur
- [parametres-par-modele.md](parametres-par-modele.md) — les paramètres que chaque modèle accepte réellement
- #14926 — l'issue porteuse, cadrage réécrit en fournées le 2026-10-14

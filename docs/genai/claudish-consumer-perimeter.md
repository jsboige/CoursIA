# Périmètre des consommateurs claudish — carnets notebooks

**État mesuré au 2026-11-03** par la lane `myia-po-2027:CoursIA` sur `origin/main`, issue #14926.

Ce document répond à la demande du pre-flight du [runbook de flip d'authentification](auth-flip-runbook.md) (l.53) : « **énumérer les consommateurs claudish** ». Jusqu'ici cette énumération était refaite à la main à chaque audit, et elle a dérivé — la liste de huit carnets portée par le corps de #14926 (mesure du 2026-10-06) nomme encore `GameTheory-03c-Le-Joueur-LLM.ipynb` et `GameTheory-28b-Humour-Banc-Dur.ipynb`, **qui n'existent plus sous ces chemins**.

## Instrument

Parse JSON des cellules de code, jamais un `grep` de chaîne : dans un `.ipynb`, les guillemets des littéraux sont échappés, et un `grep` naïf sous-compte massivement — il ne voit qu'une fraction de ce que le parse trouve. Le relevé ci-dessous porte sur les seules cellules `code`, pas sur la prose markdown.

## Le périmètre mesuré

| Carnet | lit `VLLM_API_KEY` | présente `CLAUDISH_PROXY_KEY` | paramètres vLLM natifs | classe |
|---|---|---|---|---|
| `GenAI/SemanticKernel/04-SemanticKernel-Filters-Observability.ipynb` | oui | **oui** | — | **migré** |
| `GameTheory/GameTheory-16e-LLM-Players-Othman-Sandholm-Python.ipynb` | non | **oui** | — | **migré** |
| `GenAI/RAG-et-Memoire-Semantique/09-KernelMemory-Multimodal.ipynb` | oui | non | `chat_template_kwargs` | exception — paramètres |
| `GenAI/Texte/10b_Inference_Mechanics.ipynb` | oui | non | `chat_template_kwargs` | exception — paramètres |
| `GenAI/Texte/10c_Long_Context_Strategies.ipynb` | oui | non | `chat_template_kwargs` | exception — paramètres |
| `GenAI/Texte/10_LocalLlama.ipynb` | oui | non | — | exception — sujet serving |
| `GenAI/_research/e2e_quant_validation.ipynb` | oui | non | — | exception — sujet serving |

## Les trois classes, et le motif de chacune

**1. Migrés.** `04-SemanticKernel-Filters-Observability` est la forme de référence : une clé dédiée à la façade, **sans repli** sur `OPENAI_API_KEY` (un repli enverrait le credential marchand au mauvais hôte — credential cross-provider interdit), et un commentaire qui dit que le recâblage de l'endpoint impose celui de la clé. Tout consommateur migrable doit prendre cette forme, pas une variante. La colonne « lit `VLLM_API_KEY` » décrit l'état **courant** du code, pas l'historique de migration : `04-SK` garde une occurrence de l'ancienne variable à côté des trois `CLAUDISH_PROXY_KEY`, tandis que `16e-LLM-Players`, migré de bout en bout, ne lit plus que la nouvelle.

**2. Exception — paramètres de serving.** Trois carnets passent `chat_template_kwargs` au moteur vLLM. C'est le **sujet** de ces carnets, pas un détail d'implémentation : `10b_Inference_Mechanics` enseigne le contrôle du gabarit de conversation, `10c_Long_Context_Strategies` la tenue du contexte sous ce gabarit, `09-KernelMemory-Multimodal` l'utilise pour sa propre démonstration. La passerelle claudish ne relaie pas cette sémantique ; router ces carnets à travers elle **viderait la leçon de son objet** tout en laissant des sorties plausibles — exactement le workaround dégradé que [`sota-not-workaround.md`](../../.claude/rules/sota-not-workaround.md) interdit avant même C.2.

`GameTheory-18c-Humour-Banc-Python` passe aussi `chat_template_kwargs`, mais à **OpenRouter** (`OPENROUTER_API_KEY`, zéro occurrence de `VLLM_API_KEY` ou `CLAUDISH_PROXY_KEY`) : il n'appelle ni la pile vLLM ni la passerelle, et n'a donc pas sa place dans ce périmètre. Le motif pédagogique y est le même — le paramètre natif est le sujet — et il ne deviendrait consommateur qu'à la condition d'une migration OpenRouter→pile locale qui n'est pas à l'étude.

**3. Exception — le sujet est le serving.** `10_LocalLlama` et `e2e_quant_validation` parlent du serveur vLLM et de sa quantization. On ne démontre pas une quantization à travers un proxy qui n'expose pas le modèle quantifié.

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

## Condition de réouverture

La fournée A redevient migrable — en **une seule PR pour les deux carnets**, jamais une PR par carnet — quand les quatre conditions suivantes sont réunies :

1. la passerelle sert les modèles visés **hors repli** — mesuré par un vrai `POST /v1/messages`, jamais par `/v1/models` (une liste vide est le comportement normal d'un sidecar relais) ;
2. elle relaie `chat_template_kwargs`, `seed` et `logprobs` sans les perdre (la liste est close et chiffrée par la mesure du 2026-10-07) ;
3. `render_envs.py --check` rend 0 sur la machine qui exécute — **déjà vérifié sur `po-2027`** au 2026-11-03 ;
4. la valeur serveur de la passerelle correspond à celle que `master.env` distribue — **vérifié sur `po-2027`** au 2026-11-03 ; tout écart se corrige côté distribution locale, sans redémarrage quand le conteneur porte déjà la bonne valeur.

Tant que ces conditions ne sont pas réunies, la classe 2 et la classe 3 ci-dessus restent telles quelles. Le geste utile n'est pas de les migrer, c'est de constater qu'elles n'ont pas bougé.

## Voir aussi

- [auth-flip-runbook.md](auth-flip-runbook.md) — la procédure de flip dont ce document sert le pre-flight
- [secrets-management.md](secrets-management.md) — `master.env` → `render_envs.py` → `.env` consommateur
- [parametres-par-modele.md](parametres-par-modele.md) — les paramètres que chaque modèle accepte réellement
- #14926 — l'issue porteuse, cadrage réécrit en fournées le 2026-10-14

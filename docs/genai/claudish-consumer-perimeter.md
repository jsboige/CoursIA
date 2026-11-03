# Périmètre des consommateurs claudish — carnets notebooks

**État mesuré au 2026-11-03** par la lane `myia-po-2027:CoursIA` sur `origin/main`, issue #14926.

Ce document répond à la demande du pre-flight du [runbook de flip d'authentification](auth-flip-runbook.md) (l.53) : « **énumérer les consommateurs claudish** ». Jusqu'ici cette énumération était refaite à la main à chaque audit, et elle a dérivé — la liste de huit carnets portée par le corps de #14926 (mesure du 2026-10-06) nomme encore `GameTheory-03c-Le-Joueur-LLM.ipynb` et `GameTheory-28b-Humour-Banc-Dur.ipynb`, **qui n'existent plus sous ces chemins**.

## Instrument

Parse JSON des cellules de code, jamais un `grep` de chaîne : dans un `.ipynb`, les guillemets des littéraux sont échappés, et un `grep` naïf sous-compte massivement (il trouvait 1 fichier là où le parse en trouve 8). Le relevé ci-dessous porte sur les seules cellules `code`, pas sur la prose markdown.

## Le périmètre mesuré

| Carnet | lit `VLLM_API_KEY` | présente `CLAUDISH_PROXY_KEY` | paramètres vLLM natifs | classe |
|---|---|---|---|---|
| `GenAI/SemanticKernel/04-SemanticKernel-Filters-Observability.ipynb` | oui | **oui** | — | **migré** |
| `GameTheory/GameTheory-16e-LLM-Players-Othman-Sandholm-Python.ipynb` | oui | **oui** | — | **migré** |
| `GenAI/RAG-et-Memoire-Semantique/09-KernelMemory-Multimodal.ipynb` | oui | non | `chat_template_kwargs` | exception — paramètres |
| `GenAI/Texte/10b_Inference_Mechanics.ipynb` | oui | non | `chat_template_kwargs` | exception — paramètres |
| `GenAI/Texte/10c_Long_Context_Strategies.ipynb` | oui | non | `chat_template_kwargs` | exception — paramètres |
| `GameTheory/GameTheory-18c-Humour-Banc-Python.ipynb` | oui | non | `chat_template_kwargs` | exception — paramètres |
| `GenAI/Texte/10_LocalLlama.ipynb` | oui | non | — | exception — sujet serving |
| `GenAI/_research/e2e_quant_validation.ipynb` | oui | non | — | exception — sujet serving |

## Les trois classes, et le motif de chacune

**1. Migrés.** `04-SemanticKernel-Filters-Observability` est la forme de référence : une clé dédiée à la façade, **sans repli** sur `OPENAI_API_KEY` (un repli enverrait le credential marchand au mauvais hôte — credential cross-provider interdit), et un commentaire qui dit que le recâblage de l'endpoint impose celui de la clé. Tout consommateur migrable doit prendre cette forme, pas une variante.

**2. Exception — paramètres de serving.** Quatre carnets passent `chat_template_kwargs` au moteur. C'est le **sujet** de ces carnets, pas un détail d'implémentation : `10b_Inference_Mechanics` enseigne le contrôle du gabarit de conversation, `10c_Long_Context_Strategies` la tenue du contexte sous ce gabarit, `09-KernelMemory-Multimodal` et `18c-Humour-Banc` l'utilisent pour leur propre démonstration. La passerelle claudish ne relaie pas cette sémantique ; router ces carnets à travers elle **viderait la leçon de son objet** tout en laissant des sorties plausibles — exactement le workaround dégradé que [`sota-not-workaround.md`](../../.claude/rules/sota-not-workaround.md) interdit avant même C.2.

**3. Exception — le sujet est le serving.** `10_LocalLlama` et `e2e_quant_validation` parlent du serveur vLLM et de sa quantization. On ne démontre pas une quantization à travers un proxy qui n'expose pas le modèle quantifié.

## Le gate de la fournée A, tranché

Le cadrage du 2026-10-14 pose une décision binaire : **(a)** exception documentée, accès direct au sidebar conservé et motivé, **ou (b)** extension de la passerelle claudish pour relayer `chat_template_kwargs`, `seed` et `logprobs`.

**La branche retenue est (a)**, pour trois raisons qui ne dépendent pas d'une préférence :

1. **(b) n'est pas dans ce dépôt.** Le compose et le code de la passerelle vivent hors CoursIA (`D:\Dev\claudish`) ; une lane de ce dépôt ne modifie pas l'infrastructure d'un autre propriétaire — elle la demande.
2. **(b) n'aurait pas d'objet mesurable aujourd'hui** : la passerelle joignable sur `localhost:3000` rend `{"object":"list","data":[]}` sur `/v1/models` — elle ne sert aucun modèle. Étendre son relais ne migrerait rien.
3. **Le motif pédagogique est le fond, pas la commodité.** Ces carnets n'évitent pas la passerelle par confort : ils ont besoin des paramètres natifs pour tenir leur propos.

La branche (a) **n'est pas un contournement** : elle déclare le périmètre au lieu de le laisser implicite, ce qui est précisément ce qui manquait pour que l'audit suivant n'ait pas à refaire — et à faire dériver — l'énumération.

## Ce qui reste bloquant, mesuré sur `po-2027`

| Mesure | Résultat | Conséquence |
|---|---|---|
| `GET localhost:3000/v1/models` | `{"object":"list","data":[]}` | aucun modèle servi par la passerelle |
| `POST /v1/chat/completions` avec la clé du `.env` local | `{"type":"error","error":{"type":"authentication_error","message":"invalid proxy authentication"}}` | la passerelle en cours ne reconnaît pas cette valeur |
| `python scripts/secrets/render_envs.py --check` | `[OK] 12/19 target .env on disk, in sync with master.env` | le `.env` consommateur est **en phase** avec `master.env` — la divergence n'est donc pas côté client |

Conséquence directe : **sur `po-2027`, aucune des deux voies n'exécute un appel de modèle**. Aucun carnet de ce périmètre ne peut donc être ré-exécuté, et C.2 interdit de committer une édition de carnet non ré-exécutée. C'est ce qui borne la livraison de #14926 à la décision et au périmètre, sans toucher aux carnets.

### Ce que la dernière ligne déplace

Elle retire l'explication commode. Le réflexe est de conclure « la clé cliente locale est périmée, c'est l'acceptance 2 qui n'est pas faite sur cette machine ». La mesure dit l'inverse : `master.env` porte la clé, et le `.env` consommateur est **en phase avec elle**. La valeur refusée est donc celle que la distribution a correctement livrée — ce qui place la divergence **entre `master.env` et la passerelle en cours d'exécution**, côté serveur, dans un dépôt qui n'est pas celui-ci.

C'est cohérent avec la mécanique de rotation : changer la valeur serveur impose de **redémarrer le service** (le compose ComfyUI-Login ne régénère son hash qu'au démarrage ; même famille de piège documentée dans [secrets-management.md](secrets-management.md)). Une valeur mise à jour sans redémarrage laisse exactement cette signature — client à jour, serveur qui refuse encore l'ancienne.

Le geste correctif n'appartient donc pas à une lane de ce dépôt : il se demande au propriétaire de la passerelle. L'écrire ici évite qu'un prochain audit referme la boucle sur « acceptance 2 non faite ».

## Condition de réouverture

La fournée A redevient migrable — en **une seule PR pour les deux carnets**, jamais une PR par carnet — quand les trois conditions suivantes sont réunies :

1. la passerelle sert les modèles visés et les expose sur `/v1/models` ;
2. elle relaie `chat_template_kwargs`, `seed` et `logprobs` sans les perdre (la liste est close et chiffrée par la mesure du 2026-10-07) ;
3. `render_envs.py --check` rend 0 sur la machine qui exécute — **déjà vérifié sur `po-2027`** au 2026-11-03 ;
4. la valeur serveur de la passerelle correspond à celle que `master.env` distribue, et le service a été redémarré après la rotation.

Tant que ces conditions ne sont pas réunies, la classe 2 et la classe 3 ci-dessus restent telles quelles. Le geste utile n'est pas de les migrer, c'est de constater qu'elles n'ont pas bougé.

## Voir aussi

- [auth-flip-runbook.md](auth-flip-runbook.md) — la procédure de flip dont ce document sert le pre-flight
- [secrets-management.md](secrets-management.md) — `master.env` → `render_envs.py` → `.env` consommateur
- [parametres-par-modele.md](parametres-par-modele.md) — les paramètres que chaque modèle accepte réellement
- #14926 — l'issue porteuse, cadrage réécrit en fournées le 2026-10-14

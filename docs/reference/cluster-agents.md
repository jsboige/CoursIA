# Cluster CoursIA — machines, lanes, capacités

Référence durable sur la structure du cluster qui porte les grains CoursIA : les machines, les lanes et leurs rôles, les GPU, et les barrières de capacité qui contraignent un dispatch. Les **règles de coordination** vivent dans [CLAUDE.md](../../CLAUDE.md) §A et dans [tricephale-circulation.md](tricephale-circulation.md) ; le **calendrier d'enseignement** dans [teaching-context.md](teaching-context.md).

Ce document décrit ce qui change peu. **Il ne porte pas l'état vivant** : qui tient un GPU, quelle lane tourne, quel modèle anime une lane, quel service est éveillé. Cet état se lit à sa source, jamais ici. Une copie de l'état vivant dans une page de référence se périme en silence, et c'est ce qui était arrivé à la version précédente de cette page.

## Où lire l'état vivant

| Question | Source |
|---|---|
| Qui occupe quel GPU, jusqu'à quand | ledger `gpu-reservation` de `scripts/coordination/debt_ledger.py` (dashboard `CoursIA-gpu-reservation-ledger`, ligne `<machine>#gpu<n>`) |
| Quelles lanes sont actives | `roosync_dashboard(action:"list")`, puis la lecture des clés concernées |
| Quelles machines sont en ligne | `roosync_inventory(type:"machines")` |
| Quelles lanes peuvent émettre un dossier de prévalidation | `QUALIFYING_LANES` dans `scripts/check_adjoint_prevalidation.py` |
| Quel modèle sert réellement le vLLM d'ai-01 | `docker inspect myia_vllm-medium-swift15-27b` (argument `--model`), jamais `/v1/models` |
| Ports, sous-domaines et réveil des services GenAI | [genai-services.md](../genai/genai-services.md) |
| Moteur d'une lane, et donc ce qu'elle voit | la lane elle-même : voir la section « Vision » ci-dessous |

## Machines

La population décrite ici est celle des machines qui portent des grains CoursIA. `myia-web1` et `myia-web2` font partie de la flotte MyIA mais travaillent sur `roo-extensions` ; elles n'apparaissent pas dans `QUALIFYING_LANES` (huit machines en ligne au 2026-10-06, dont ces deux-là).

| Machine | GPU | Ce qu'elle porte pour la flotte |
|---|---|---|
| `myia-ai-01` | 3 × RTX 4090 (24 Go chacune), mesuré le 2026-10-06 | le coordinateur ; le vLLM de la flotte (GPU 0+1) ; le GPU d'expériences (GPU 2) ; la plupart des services partagés (Qdrant, instances Open WebUI des écoles, proxy claudish, sk-agent, NanoClaw). Toute commande à portée machine y touche la flotte entière |
| `myia-po-2023` | RTX 3080 + eGPU RTX 3090 (24 Go) | les services GenAI image, audio et vidéo ([genai-services.md](../genai/genai-services.md)) |
| `myia-po-2024` | RTX 3070 (8 Go) | jeton QuantConnect MCP ; la lane QC isolée |
| `myia-po-2025` | RTX 3080 Ti laptop (16 Go), sous garde thermique | le titulaire de la coordination ; des workspaces hors CoursIA (claudish, maintenance, workspaces d'école) |
| `myia-po-2026` | RTX 3080 | le service d'embedding (port `8004`) ; jeton QuantConnect MCP ; le secrétariat ; Hermes |
| `myia-po-2027` | RTX 4060 laptop (8 Go) | des lanes worker ; hors du LAN d'ai-01 (voir « Réseau ») |

La capacité GPU des machines `po-*` est **déclarée** ; elle se confirme par la lane propriétaire avant toute réservation, pas par cette table.

## Lanes et rôles

Une lane est un couple `machine:workspace`, animé par un seul agent actif à la fois ([lane-claim-protocol.md](../../.claude/rules/lane-claim-protocol.md)). Le rôle et les droits d'une lane s'attachent à la lane : ils ne se déduisent **ni du moteur** qui l'anime, **ni du suffixe** de son workspace.

| Lane | Rôle |
|---|---|
| `myia-ai-01:CoursIA` | coordinateur : merges, fermetures, arbitrages, politique de flotte |
| `myia-po-2025:CoursIA-2` | titulaire : dossiers de prévalidation exact-head, vérifications avant fermeture ; ne merge ni ne ferme |
| `myia-po-2026:CoursIA-3` | secrétariat : attestations tierces, circulation (DM nominatifs, alertes). Il refuse par contrat les dossiers des PRs `DEEP`, qui reviennent au titulaire |
| `myia-ai-01:CoursIA-2` | worker sur la machine du coordinateur ; régisseur des GPU de la flotte depuis le 2026-10-05. Ne merge ni ne ferme |
| `myia-po-2024:CoursIA-3` | lane QuantConnect isolée : déploiement des portefeuilles et maintenance de la partie QC, hors du tapis des workers. Elle partage le dashboard `workspace-CoursIA-3` avec le secrétariat : lire l'auteur (`machineId`) avant d'attribuer un message |
| autres `*:CoursIA` et `*:CoursIA-2` | workers |

Le trio coordinateur, titulaire et secrétaire est décrit, avec la circulation entre ses têtes, dans [tricephale-circulation.md](tricephale-circulation.md).

**Les deux relecteurs du cluster MyIA.** Hermes (`po-2026`, ordonnanceur `hermes-agent`, cycles horaires) et NanoClaw (`ai-01`, workspace `cluster-coordination`, cadence de 30 minutes) relisent les PRs et tiennent une coordination à l'échelle du cluster MyIA, au-delà de CoursIA. Ils signent sous le même compte GitHub, `clusterManager-Myia`, et se distinguent par le préfixe du corps de leur review (`[Hermes]`, `[NanoClaw]`). Ce ne sont pas des lanes au sens du protocole de claim ; leurs réserves se lèvent comme toute réserve (CLAUDE.md §B.0). Harnais et annuaire : [bot-review-harness.md](bot-review-harness.md).

**Workspaces d'école.** Les workspaces des cours (EPITA, EPF, etc.) ont leur propre dashboard. Exception user du 2026-05-16 : le coordinateur peut y envoyer `[INFO]`, `[ASK]` ou `[DIRECTIVE]` par message direct ; il n'y merge pas, n'y committe pas et n'écrit pas sur leur dashboard. Scope par école : [teaching-context.md](teaching-context.md).

**Anti-collision.** Un seul éditeur par notebook ou par série à la fois ; deux sessions sur une même machine (`CoursIA` et `CoursIA-2`) sont deux lanes distinctes, et un worker qui refuse un pivot vers la session voisine a raison.

## D'où vient le grain d'une lane

Il n'y a **aucune table de spécialités** dans cette page, et c'est délibéré. Une table « tel sujet va à telle lane » contredit le tirage sur le pool entier ([proactive-coordination.md](../../.claude/rules/proactive-coordination.md), R5), et la dernière qui figurait ici n'était plus appliquée par aucune lane.

Le grain d'une lane vient du **tapis** (`python scripts/pick_idle_grain.py --belt --lane <machine:workspace>`) ou d'une file composée par le coordinateur. Ce qui contraint une lane, ce sont des **barrières de capacité**, et elles seules :

- **GPU** : la VRAM requise, et la disponibilité au ledger ;
- **vision** : la capacité du modèle qui anime la lane (section suivante) ;
- **réseau** : la joignabilité des endpoints locaux (section « Réseau ») ;
- **jetons de service** : QuantConnect MCP (`po-2024`, `po-2026`), services GenAI de `po-2023`.

Un jeton de service est une capacité **en plus**, jamais un périmètre exclusif : une lane qui le détient prend aussi n'importe quel autre grain.

## Vision

La capacité de voir une image appartient au **modèle**, pas à la machine ni à la lane : une lane change de modèle, et une table par machine se périme au premier changement. La règle et la table des modèles sont dans [model-delegation.md](../../.claude/rules/model-delegation.md). C'est à l'agent de juger s'il voit, sur ce dont il dispose ; s'il ne voit pas, il le dit et rend la partie visuelle du grain.

- **Mécanisme.** Un `Read` sur une image (`.png`, `.webp`, `.jpg`) ou sur une capture (rendu Playwright puis capture, ou Edge headless en `--screenshot` quand le profil Playwright est verrouillé) insère l'image dans le contexte d'un modèle qui voit. `mcp__sk-agent__call_agent` accepte une image en `attachment`, mais un verdict de vision indirecte non corroboré ne vaut pas validation.
- **Sous-agents.** Le moteur derrière `model: "sonnet"` ou `"haiku"` dépend du proxy de la machine qui lance le sous-agent, et il change sans préavis. Mesure du 2026-10-06 sur `ai-01` : un sous-agent `sonnet` ne reçoit pas les images. Le sous-agent peut produire le rendu ; le regard reste à la boucle principale.
- **Un `test -f` prouve l'existence, pas le rendu.** Le défaut à attraper : une figure réduite à des aplats, une image blanche, un placeholder, alors que le vrai outil était invocable. On la régénère, on ne la consacre pas ([sota-not-workaround.md](../../.claude/rules/sota-not-workaround.md)). Cas fondateur : une figure du README `GenAI/Image` réduite à trois aplats colorés, passée au contrôle d'existence et attrapée au premier regard le 2026-07-11, puis régénérée le 2026-07-17.

## GPU d'ai-01

| GPU | Usage |
|---|---|
| 0 et 1 | vLLM `medium` de la flotte : `ukisai/Swift-1.5-Qwen3.8-27b-W4A16-AWQ` (dense 27B), tensor parallel sur les deux cartes, port `5002`. Environ 20 Go occupés par carte, en permanence : ce n'est ni une fuite ni un processus zombie |
| 2 | expériences et entraînements, réservés au ledger avant tout chargement |

- **Piège de l'alias.** Le modèle est servi sous `--served-model-name qwen3.6-35b-a3b`, nom hérité d'un ancien MoE gardé pour la compatibilité des clients. Le nom servi ne dit pas quel modèle tourne.
- **L'ancien alias `mini`** (port `5001`) n'est servi par aucun conteneur au 2026-10-06.
- **GPU 0 et 1** : on n'y charge pas un second modèle pour une expérience. Un modèle trop grand pour 24 Go passe sur le GPU 2, avec une partie des couches déchargée en mémoire CPU.
- **Le modèle servi comme sujet d'expérience.** Le modèle de production peut lui-même être étudié (autoencodeur parcimonieux, lecture d'activations, expérience ICT) quand l'instrument se branche sur le moteur d'inférence sans décharger le modèle. Une courte coupure du service, le temps de redémarrer le moteur avec son instrumentation, est acceptable : elle s'annonce à l'avance sur le dashboard `global`, puisque toute la flotte en dépend. Hors de ce cadre, on ne tue ni ne réinitialise leurs processus : cela couperait le modèle de toute la flotte sans prévenir.
- **GPU 2** : le régisseur (`myia-ai-01:CoursIA-2`) tient la file des expériences (rendez-vous [#1454](https://github.com/jsboige/CoursIA/issues/1454)). Un GPU 2 vide sans raison écrite est une dette du cycle.
- **Désignation du device.** Les variables vont sur la commande elle-même, pas sur une chaîne de commandes qui les perdrait : `CUDA_DEVICE_ORDER=PCI_BUS_ID CUDA_VISIBLE_DEVICES=2 <commande>`. Ensuite, vérifier le placement réel avec `nvidia-smi --query-compute-apps`.
- **Mémoire de la machine.** ai-01 sert la flotte : avant un run lourd, lire le taux d'engagement mémoire juste avant le lancement, pas une valeur lue plus tôt dans le cycle.

## po-2025 — garde thermique

La RTX 3080 Ti laptop de `po-2025` (MSI GE76) a provoqué trois arrêts système en une journée le 2026-04-28, pendant un entraînement LSTM prolongé : TDR, BSOD `0x9F`, puis arrêt thermique à 100 °C. La carte throttle déjà à 50 W vers 89 °C.

Un entraînement GPU non supervisé de plus de 15 minutes y est interdit, sauf avec les trois garde-fous suivants :

- le motif de `MyIA.AI.Notebooks/QuantConnect/shared/gpu_training.py` (`TrainingCheckpoint` et `thermal_check`) ;
- un arrêt automatique à 87 °C ;
- un batch réduit, en précision mixte.

## Réseau

**Règle de routage** (décision [#9976](https://github.com/jsboige/CoursIA/issues/9976), option (a)) : aucun grain qui exige l'inférence locale d'ai-01 n'est dispatché vers une lane hors de son LAN. Ces lanes reçoivent des grains sans inférence, ou à fournisseur externe ([#6949](https://github.com/jsboige/CoursIA/issues/6949)). Une lane qui reçoit un tel grain et mesure un `HTTP 000` le signale comme une erreur de dispatch : elle ne le contourne pas.

| Machine | vLLM d'ai-01 joignable | Mesure |
|---|---|---|
| `po-2023`, `po-2024`, `po-2026` | oui (`401` en quelques millisecondes : vivant, clé requise) | 2026-08-23 et 2026-08-26 |
| `po-2025` | non : LAN physiquement distinct | 2026-08-10 |
| `po-2027` | non : même numérotation /24, mais réseau isolé (Wi-Fi) | 2026-08-25 |

Une adresse dans le même /24 ne prouve pas l'appartenance au même LAN : seule une mesure depuis la machine concernée le prouve. L'endpoint et sa clé se lisent dans le `.env` de chaque machine. Exposition : le port `5002` est publié par Docker Desktop sur toutes les interfaces et n'est protégé que par sa clé ; sur un réseau classé public, il y serait joignable.

**Lire un résultat d'endpoint, sans jamais l'agréger d'une machine à l'autre :**

| Depuis la machine X | Signification | Geste |
|---|---|---|
| `401` en moins de 50 ms | vivant, authentification refusée | vérifier la clé du `.env` de X, pas l'adresse |
| `200` avec clé | vivant et authentifié | — |
| `connection refused` | aucun service n'écoute sur ce port | démarrer le service, vérifier le port |
| `000`, timeout, ping perdu | non joignable **depuis X** | re-tester depuis la machine hôte ; si elle répond `401`, c'est une propriété de routage, pas une panne |

```powershell
# Plage LAN de la machine X, puis sonde courte de l'endpoint
Get-NetIPAddress -AddressFamily IPv4 | Where-Object {$_.IPAddress -notlike '127.*'} | Select-Object IPAddress,InterfaceAlias
curl.exe -s -o NUL -w "%{http_code}`n" --max-time 6 http://<adresse>:<port>/v1/models
```

## Capacités de service

- **QuantConnect MCP** (`quantconnect/mcp-server`, jetons sur `po-2024` et `po-2026`) : au plus 10 appels par minute pour **toute** la flotte ; annoncer un backtest sur le dashboard avant de le lancer. Détail : [quantconnect.md](../qc/quantconnect.md).
- **GenAI image, audio, vidéo** (`po-2023`) : registre des services, ports et sous-domaines dans [genai-services.md](../genai/genai-services.md). Un notebook qui appelle ces services se valide contre eux, pas contre une sortie de substitution.
- **Embedding** (`po-2026`, Qwen3-Embedding-4B AWQ, port `8004`) : consommable depuis le LAN d'ai-01. Son rapatriement aux côtés du vLLM est à l'étude.
- **Lean et Mathlib** : installables sur toutes les machines (CLAUDE.md §F). Sur ai-01, un `lake build` vise une cible, jamais le lake entier.

## Pointeurs

- Circulation entre coordinateur, titulaire et secrétaire : [tricephale-circulation.md](tricephale-circulation.md)
- Délégation à des sous-agents et capacité de vision : [model-delegation.md](../../.claude/rules/model-delegation.md)
- Bots relecteurs : [bot-review-harness.md](bot-review-harness.md)
- Serveurs MCP, cycle de vie et diagnostic : [architecture_mcp_roo.md](architecture_mcp_roo.md)
- Kernels et environnements : [kernels-runtime.md](kernels-runtime.md)
- Services GenAI : [genai-services.md](../genai/genai-services.md)
- QuantConnect : [quantconnect.md](../qc/quantconnect.md)
- Prouveur Lean : [prover_iteration_history.md](../lean/prover_iteration_history.md)

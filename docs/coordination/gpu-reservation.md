# GPU Reservation Ledger — protocole de la flotte

> **Tenancier** : `myia-ai-01:CoursIA-2` (mandat user 2026-09-18, mandat régisseur GPU 2026-10-05).
> **Code source** : `scripts/coordination/debt_ledger.py` (kind `gpu-reservation`, fonction `_summarize_gpu_reservation`).
> **Dashboard dédié** : `CoursIA-gpu-reservation-ledger` (un par kind, jamais partagé).
> **Issue de référence** : [#16737](https://github.com/jsboige/CoursIA/issues/16737).

## Vue d'ensemble

Le ledger `gpu-reservation` catalogue **une entrée par réservation GPU**, cléée par `<machine>#gpu<n>`. Chaque entrée porte **6 champs** (cf. `GPU_RESERVATION_FIELDS` dans `scripts/coordination/debt_ledger.py`) :

| Champ | Type | Description |
|---|---|---|
| `state` | enum | `'held'` (workload en cours), `'released'` (terminal, GPU libre), `'stale'` (`held` passé `expected_end` sans release). |
| `holder` | lane | la lane qui tient le device (ex : `myia-ai-01:CoursIA-2`). |
| `workload` | text | une ligne décrivant ce qui tourne sur le device. |
| `started_at` | ISO-8601 UTC | début de la fenêtre d'usage. |
| `expected_end` | ISO-8601 UTC | fin prévue de la fenêtre ; sert de base à la détection `stale`. |
| `issue` | issue-ref | issue d'exécution servie par cette réservation (`owner/repo#N`), si elle existe. |

## Pourquoi un ledger — pas un README

Le **README documente l'intention**, le **ledger documente l'usage réel**. Une réservation GPU consomme une fenêtre de temps qu'aucune autre lane ne doit chevaucher. Sans ledger, deux lanes peuvent exécuter en parallèle sur la même machine et se neutraliser (saturation mémoire, swap, etc.).

Le dashboard `CoursIA-gpu-reservation-ledger` est la **seule source de vérité** de l'usage GPU réel de la flotte. Les fichiers `*.ledger.json` dans `scripts/coordination/_local/` sont des artefacts locaux (init/spool/reduce) qui n'ont aucune valeur cross-machine.

## Quand poster une observation

**Toute lane** qui lance une expérience GPU poste une observation sur le dashboard dédié avant `nvidia-smi` (ou équivalent). Le geste est **rapide** (1 message), **atomique** (1 observation = 1 fenêtre), et **idempotent** (un re-post remplace l'observation précédente pour la même entité, fenêtre mise à jour).

**Proposition mesurée par `myia-po-2023` le 2026-10-25 — en attente d'arbitrage du coordinateur sur [#16737](https://github.com/jsboige/CoursIA/issues/16737), donc NON en vigueur : le seuil n'est pas la durée, c'est l'annonce.** Un run dont la durée est **annoncée à l'avance** poste un `held` avant son premier appel CUDA et un `released` à la fin, **quelle que soit sa longueur**. Un seuil de 15 min laissait invisibles les runs courts **répétés**, qui occupent le device autant qu'un long — et « machine silencieuse » y devient indiscernable de « machine active » (mesure `myia-po-2023`, 2026-10-25). La règle par l'annonce ne demande aucun jugement sur la durée, ce qui la rend opposable. **Tant que l'arbitrage n'est pas rendu, le seuil des 15 min demeure la règle du protocole.** Restent hors champ les appels d'inférence ponctuels non annoncés, qui ne constituent pas une fenêtre.

Le picker **ne tire plus une expérience GPU** sans qu'une observation existe dans le ledger (cohérence avec [#1454](https://github.com/jsboige/CoursIA/issues/1454) — la file d'expériences GPU).

## Format de l'envelope

L'envelope est un message dashboard d'une ligne, préfixé `[OBS]`, au format JSON. Le body est construit par la sous-commande `append` du `debt_ledger.py` (ou par un script ad-hoc qui passe par `--fields-json`).

**Exemple réel (c.257)** : entité `myia-ai-01#gpu2`, état `released` après un run training :

```json
[OBS] {"schema":"debt-ledger-observation/v1","kind":"gpu-reservation","entity":"myia-ai-01#gpu2","fields":{"state":"released","holder":"myia-ai-01:CoursIA-2","workload":"onset/SAE Qwen3.5-9B-Base (c.247-quater)","started_at":"2026-10-07T16:53:00Z","expected_end":"2026-10-08T00:00:00Z","issue":"jsboige/CoursIA#1454"}}
```

Une observation est **terminale** quand son `state` est `released` ou `stale`. Au-delà, le picker doit incrémenter `observed_at` plutôt que ré-écrire l'historique.

### L'`observation_id` se **calcule**, il ne s'écrit pas

`observation_id` est le **digest du contenu** de l'observation (`observation_id_for()`, `scripts/coordination/debt_ledger.py:439`) ; il exclut lui-même et `message_id` du digest. Le fold **recalcule** le digest et le compare à celui que porte l'enveloppe : s'ils diffèrent, l'observation est **rejetée** avec la raison `observation_id_mismatch` (`debt_ledger.py:830-838`).

Conséquence : **un `observation_id` écrit à la main n'est jamais accepté**. Seul `debt_ledger.py append` en produit un valide et le scelle au moment du postage. Un id forgé n'est pas une erreur de forme : c'est le signal que *le journal n'est pas append-only ici*.

Le rejet est **silencieux** du point de vue des lignes réduites — l'observation disparaît du snapshot sans y laisser de trace, et n'apparaît que dans le champ `rejections`. Mesure du premier fold effectif (2026-10-20, c.2249) : **4 observations rejetées sur 81 exportées**, toutes les quatre avec `observation_id_mismatch`, toutes les quatre écrites à la main par la lane tenancière.

**Règle** : un envelope `[OBS]` posté à la main **ne porte pas** de champ `observation_id`. S'il est présent, il vient de `debt_ledger.py append` (sous-commande `append --fields-json`) — jamais d'un copier-coller d'un autre envelope.

### La seconde cause de rejet : une prose **collée à l'envelope**

Le reducer parse le `content` du message **entier**. Un envelope `[OBS] {…}` suivi d'une phrase d'explication dans le **même** message produit `unparsable_envelope` (« content is not JSON » — l'erreur tombe sur le premier caractère de la prose) : l'observation est rejetée au même titre qu'un id forgé, et l'état qu'elle porte est perdu.

**Règle** : l'envelope est **seule** dans son message. Si un commentaire accompagne l'observation, il va dans un **message distinct** — ou dans le champ `note` de l'observation, qui fait partie du contenu digesté.

### Mesure du fold du 2026-10-22 : le défaut est **cross-lane**

Fold complet (129 messages : 4 archives + intercom vivant, `window kind=full`) : **10 rejets sur 115 observations**, dont 9 `observation_id_mismatch` et 1 `unparsable_envelope`.

La mesure du fold précédent (c.2249) portait sur **4 rejets, tous écrits par la lane tenancière** — un défaut qu'un lane peut corriger seul. Celle-ci change la portée :

| Entité | Rejets | Effet sur l'état foldé |
|---|---:|---|
| `myia-ai-01#gpu2` | 5 (tenancière) | aucun — historique, supersédé par des observations valides |
| `myia-po-2028#gpu0` | 2 | aucun — ligne actuellement `released` |
| `myia-po-2023#gpu1` | 1 | aucun — ligne actuellement `released` |
| `myia-po-2024#gpu0` | **1** | **ligne vivante figée à `held`** alors que la carte est libre |

Le rejet po-2024 est celui qui compte : son `observation_id` (`obs-po2024-gpu0-released-20261022T0319Z`) est un **id lisible, formaté à la main** — il ressemble à un id de l'outil sans en être un. Sa libération est donc invisible au fold, et le ledger continue d'annoncer une réservation active sur un device libre : c'est le pire mode de panne pour un registre de verrouillage, puisqu'il **bloque à tort** au lieu de libérer trop tôt.

Un rejet qui laisse la ligne dans un état **faux** n'est pas rattrapable par le fold seul : la lane détentrice doit **republier** l'observation via `append`, sous son propre nom d'entité. Le tenancier constate et previent (DM à la lane concernée, 2026-10-22) ; il ne forge pas l'observation d'une entité qu'il ne détient pas.

### La clé machine est **canonicalisée** — un seul nom par machine

La clé d'une réservation est `<machine>#gpu<n>`. La partie machine est **normalisée au parsing** par `canonical_machine()` (`scripts/coordination/debt_ledger.py`) : elle est ramenée au nom du **roster de la flotte**, et une machine **hors roster est refusée explicitement** (`entity_mismatch`). Le nom court est déduit mécaniquement du roster (`ai-01` → `myia-ai-01`), les formes sans tiret (`ai01`) sont ajoutées à la main dans `MACHINE_ALIASES`.

Avant cette canonicalisation (implémentation : **PR #21684**), le parseur ne faisait qu'un `strip()` : `ai-01#gpu2` et `myia-ai-01#gpu2` étaient **deux lignes distinctes** — le même GPU physique, compté deux fois, avec deux `holder` possibles et deux fenêtres qui ne se verrouillaient jamais l'une contre l'autre.

Au premier fold effectif (c.2249, 2026-10-20), les deux écritures `ai-01#gpu2` (historique) et `myia-ai-01#gpu2` (ligne vivante) coexistaient — pour un seul device. Les compteurs du fold sont dans le tableau « Premier fold effectif » et dans le snapshot publié.

**Règle** : reprendre le nom de machine du **roster de la flotte** (`myia-ai-01`, `myia-po-2023`, …), c'est-à-dire celui que le CLI rappelle lui-même en exemple (`myia-ai-01#gpu2`). Un raccourci (`ai-01`) reste **accepté** — il est normalisé vers le nom canonique, et l'observation porte l'entité canonique.

**Migration** : la canonicalisation change l'entité, donc le digest de l'observation. Une observation **postée avant** la canonicalisation porte le digest de son entité **brute** ; le fold l'accepte sur ce digest historique et la re-keye vers la clé canonique (elle n'est donc **pas perdue**). Un identifiant qui ne correspond ni au digest canonique ni au digest brut reste **rejeté** (`observation_id_mismatch`) : le fail-closed du journal est intact.

Au fold suivant, les deux lignes `ai-01#gpu2` et `myia-ai-01#gpu2` **convergent vers une seule ligne** `myia-ai-01#gpu2`, dont l'`history` par champ conserve les valeurs supersédées. Mesure sur les observations de production : la convergence vers la clé canonique ne perd aucune observation et n'introduit aucun rejet — avant comme après, le fold consomme le même ensemble.

**Étendre le roster** : ajouter le nom canonique à `FLEET_MACHINES` (`scripts/coordination/debt_ledger.py`). Le nom court (`<nom sans myia->`) est alors déduit automatiquement ; une forme sans tiret s'ajoute à `MACHINE_ALIASES`. Un roster qui ne contient pas la machine **refuse** ses observations — c'est voulu : une faute de frappe ne doit pas créer une ligne fantôme.

## Quand **réduire** (fold)

Le reducer (`python scripts/coordination/debt_ledger.py reduce --ledger gpu-reservation --events <journal>`) agrège les observations en un **snapshot** signé par le tenancier. Fréquence recommandée :

- **Hebdomadaire** (lundi 09:00Z) : fold de la semaine précédente.
- **Événementiel** : fin d'une expérience marquante (release `c.NNN-quater`, PR mergée sur axe GPU).
- **Ad-hoc** : demande du coordinateur (`myia-ai-01:CoursIA`) ou d'un user.

Le snapshot est publié sur le dashboard `CoursIA-gpu-reservation-ledger` avec le préfixe `[SNAPSHOT]`. Le snapshot **ne supprime pas** les observations — il les réduit (fold canonique). Un snapshot + journal export permet à un auditeur de reconstituer l'historique complet.

### L'export doit couvrir **tout** le journal — le dashboard condensé ne suffit pas

`roosync_dashboard(action:"read")` rend le dashboard **après condensation** : au 2026-10-22, `totalMessages: 122` pour 20 messages listés, dont 15 archivés **sans résumé** (circuit breaker LLM ouverte). Réduire sur cette sortie seule ne replie que la queue et perd l'état porté par les messages disparus — c'est l'échec que le contrat « archive-aware » documente, dont la parade est de réassembler les **archives** avec l'intercom vivant.

Les archives RooSync sont des **markdown verbatim** sur GDrive (`$ROOSYNC_SHARED_PATH/dashboards/archive/<clé>-<ts>.md`), pas un export JSON : un bloc par message, avec `### [ts] machine|workspace`, `[msg: id]`, puis le contenu. Le `llmGenerated: false` du frontmatter (fallback de troncature) **n'altère pas le verbatim** — le contenu est celui du message.

`--window-full` déclare que l'export couvre le journal entier ; sans cette déclaration, le reducer refuse une reconstruction à partir de la queue seule (`MISSING_CHECKPOINT`). Déclarer `full` sur un export incomplet est un **mensonge d'instrument** : la sortie paraîtra saine et l'état sera faux.

**Vérifier avant de réduire** : comparer le nombre de blocs `### [ts]` de chaque archive au `messageCount` de son frontmatter, et le total à `totalMessages` du dashboard lu.

## Gardes de sécurité — ce que la lane qui lance DOIT vérifier

Avant `nvidia-smi` (ou tout autre lancement GPU) :

1. **Charge hôte** : `uptime`, `free -g`, `nvidia-smi` — la charge hôte doit rester **< 85 %** sous l'expérience. Au-delà, reporter l'expérience et poster une observation `held` une fois la charge retombée (réservation à venir, pas de geste de lancement).
2. **CUDA devices** : `CUDA_DEVICE_ORDER=PCI_BUS_ID CUDA_VISIBLE_DEVICES=<n>` sur la commande elle-même. Ne pas se fier au seul `CUDA_VISIBLE_DEVICES` (variable d'env du shell sans ordre PCI = risque d'allocation ambigu).
3. **Ledger entry** : poster `[OBS]` (`state: held`) sur `CoursIA-gpu-reservation-ledger` **avant** le geste de lancement (pas après — sinon collision possible). Poster `[OBS]` (`state: released`) à la fin du run, avec `workload` court et `expected_end` réel. **Construire les deux avec `debt_ledger.py append`** : un envelope écrit à la main est rejeté au fold (les deux causes ci-dessus), et une libération rejetée laisse la ligne **`held` sur un device libre**.
4. **GPU 0/1 réservé** : les GPU 0 et 1 de ai-01 portent le vLLM de la flotte et **ne se réservent pas**. Le GPU 2 est le seul slot GPU de cette machine pour les expériences.

## Périmètre du tenancier

Le tenancier (`myia-ai-01:CoursIA-2`) :

- **Lance** les expériences GPU de sa machine (GPU 2 uniquement).
- **Ne lance PAS** sur les GPU 0/1 (vLLM) ni sur les GPU des autres machines (sauf coordination explicite avec leur lane propriétaire).
- **Récupère** le statut GPU d'autres machines (`poset/disponibilité_gpu`, ticket DM `myia-ai-01 → myia-po-2025 → myia-po-2023`).
- **Réduit** le ledger une fois par semaine (lundi 09:00Z) en fold canonique.
- **Coordonne** la file #1454 avec le picker : une expérience GPU ne va jamais sur la flèche sans observation préalable.

## Liaison picker ↔ file #1454

Le picker (`scripts/pick_idle_grain.py`) croise l'urne `delivered` avec un signal **pre-launch** :

1. Avant de tirer un grain `training` ou `genai` marqué **GPU-bound**, le picker vérifie qu'une observation `[OBS]` existe dans le ledger pour l'entité ciblée via la sous-commande `check_pending --entity <m>#gpu<n>`. **L'heuristique « GPU-bound » est fixée** : un candidat est GPU-borne si son genre est `training` ou `genai` — le genre retenu par le picker est celui que l'auteur a déclaré (tag `Grain:`) quand il existe, sinon celui inféré du titre et des labels (`GENRE_RULES`, qui reste « une aide au tri, pas un verdict »). **L'entité ciblée se résout** dans cet ordre : (1) la **ligne dédiée** `GPU: <machine>#gpu<n>` du **corps** du candidat — la seule forme qui distingue une *déclaration* d'une mention en prose ; (2) **une seule** entité `<machine>#gpu<n>` citée en prose dans le corps ; (3) l'option `--gpu-entity` du tirage (répétable) — la cible que la lane qui tire peut offrir. **Deux entités distinctes** dans la même source rendent la cible **ambiguë** : le grain est alors écarté avec le motif `[DEFER gpu-reservation target-ambiguous]` — le picker ne choisit pas à la place de l'auteur. **Aucune cible** n'est pas un device tenu : le grain est alors **servi**, et le fait est nommé dans la sortie du tirage (`[INFO gpu-reservation target-unresolved]`) — la porte n'avait aucun device à protéger, et rien n'a été vérifié.
2. **Pas d'observation `[OBS]`** (`verdict: NO_OBS`) → le picker saute le grain et log `[SKIP gpu-reservation missing]`. La lane worker qui rencontre ce skip doit poster l'observation OU prendre un grain non-GPU.
3. **Observation `held` par une autre lane** (`verdict: HOLD`) → le picker signale `[DEFER gpu-reservation hold]` et passe au suivant.
4. **Observation `held` par ma lane, dans la fenêtre** (`verdict: OK_TO_RUN`) → le picker tire normalement.
5. **Observation `released`** (`verdict: RELEASED`) → le GPU est libre, le picker peut tirer.
6. **Observation `stale`** (`verdict: STALE`) → cas d'erreur, la lane tenancière doit poster un `[OBS]` de réparation.

Le script `scripts/coordination/debt_ledger.py check_pending --entity <m>#gpu<n>` rend le verdict (`OK_TO_RUN`, `NO_OBS`, `HOLD`, `RELEASED`, `STALE`, `UNPOSTED`) en ~50 ms (cache local). **Implémentation 4e livrable : [PR #19855](https://github.com/jsboige/CoursIA/pull/19855)**, merge de la sous-commande et de `evaluate_gpu_pending()` (113/113 tests passent).

### Ce que le picker en fait (c.2431, #22747)

La section ci-dessus était une **promesse du protocole que le code ne tenait pas** : mesuré le 2026-10-27, `git grep -n check_pending scripts/` ne renvoyait que le ledger, ses tests et cette page — **zéro appelant** du côté du picker. Le gate est maintenant câblé :

- **Où** : au moment de **servir** un candidat, sur les deux chemins de tirage — la voie pondérée (`draw_unclaimed`) et le tapis (`belt_pick_with_replacements`, celui que le cycle `/continue` emprunte). Le gate n'est donc consulté que pour une poignée de candidats, jamais pour tout le pool.
- **Doctrine : fail-CLOSED.** Une observation de device tenu est un fait de **contention matérielle** — deux lanes qui lancent sur le même device se marchent dessus (#22456 : le premier essai de `po-2024` n'a pas été vu par la régie). Un gate **illisible** ne rend donc jamais « libre » : il rend `GATE_UNREAD`, et le grain est écarté avec un motif nommé. C'est l'inverse du fail-OPEN des sondes de claim (là, une lecture ratée ne doit pas inventer un blocage).
- **Le verdict est lu dans le JSON, jamais dans le code de sortie** : `NO_OBS` sort 0 et doit pourtant écarter, `STALE` et une erreur d'usage sortent tous deux 2 — le code de sortie ne décide de rien.
- **Le motif est nommé** : un grain écarté est un grain **dit**, pas un grain absent. Marqueurs : `[SKIP gpu-reservation missing]` (aucune observation), `[DEFER gpu-reservation hold]` (device tenu), `[DEFER gpu-reservation stale]`, `[DEFER gpu-reservation unposted]` (spool non drainé), `[DEFER gpu-reservation gate-unreadable]` (gate illisible), `[DEFER gpu-reservation unreadable]` (le transport git n'a pas pu lire le ledger — siège sans remote `gpu-ledger`), `[DEFER gpu-reservation target-ambiguous]` (plusieurs cibles GPU distinctes, aucune ne fait foi). Un grain **servi sans cible déclarée** laisse une trace d'un autre genre : `[INFO gpu-reservation target-unresolved]` — ce n'est pas un écart, c'est l'absence de device à protéger.
- **Déclarer sa cible** : la forme canonique est une **ligne dédiée** dans le **corps de l'issue** :

  ```text
  GPU: myia-ai-01#gpu2
  ```

  Cette ligne **prime** sur toute mention en prose — une mention en prose est un **contexte**, pas une **déclaration** (« po-2024 avait lancé sur `myia-po-2024#gpu0` […] ce grain tourne sur `myia-ai-01#gpu2` »). Si le corps porte **deux** entités distinctes en prose et **aucune** ligne dédiée, la cible est **ambiguë** : le grain est écarté (`[DEFER gpu-reservation target-ambiguous]`). Lever l'ambiguïté n'est pas choisir à la place de l'auteur : c'est écrire la ligne dédiée.
- **Tests** : `scripts/tests/test_pick_idle_grain_gpu_gate.py` couvre les trois cas d'acceptation de #22747 (device libre → proposé, device tenu → écarté avec motif, gate indisponible → écarté avec motif), les deux non-régressions (verdict lu dans le JSON ; un grain non GPU-borne ne consulte jamais le gate) et les deux chemins de tirage.

**Codes de sortie** (promis par la docstring de la sous-commande, `debt_ledger.py:2663`) :

| Verdict | Code | Lecture |
|---|---|---|
| `OK_TO_RUN` | 0 | la fenêtre est à nous, le lancement est permis |
| `NO_OBS` | 0 | aucune observation — le picker **saute** le grain ; ce n'est pas une erreur |
| `RELEASED` | 0 | GPU libre |
| `HOLD` | **1** | la gate refuse : tenu par une autre lane, ou par nous hors fenêtre |
| `STALE` | **2** | `held` dépassé sans release — l'appelant décide (rafraîchir ou bloquer) |
| `UNPOSTED` | **1** | le spool local porte des observations **jamais postées** : le ledger est illisible, pas libre — poster (`flush`) avant de conclure |

Le code 2 est aussi rendu sur un usage invalide (`--entity` absent, ledger ≠ `gpu-reservation`) : là, il signale une **erreur d'appel**, pas un verdict.

`UNPOSTED` prime sur les autres verdicts : il est rendu **avant** la lecture du snapshot, parce qu'un verdict réduit d'un snapshot ne voit pas ce qui n'a jamais voyagé (deux réservations `held` vivantes, quatre-vingt-quatre heures de spool, et un `RELEASED` rendu avec aplomb — #22456).

**Le drainage du spool est en deux temps, et aucun n'est optionnel** : `debt_ledger.py flush` liste (ou `--emit` écrit) le lot à poster — le `content` de chaque appel est l'octet du fichier de spool, sans re-sérialisation — puis `flush --mark-posted <id>...` archive les observations effectivement postées. L'archivage est idempotent (l'`observation_id` est la clé) et tout-ou-rien : un id inconnu refuse le lot entier plutôt que d'archiver la moitié, parce qu'un spool à moitié drainé est précisément l'état qui fait mentir `check_pending`.

## Première observation [OBS] — c.257 (2026-10-08T03:25Z)

**Entité** : `myia-ai-01#gpu2`
**Issued by** : `myia-ai-01:CoursIA-2`
**State** : `held` (observation **pré-run** — relevé de l'état machine avant le prochain job, pas de workload en cours au moment de l'observation)
**Workload** : (vide — pas de workload en cours, c'est un snapshot machine)
**Issue** : `#1454` (file GPU 2)

**Mesures firsthand 2026-10-08T03:25Z** (`nvidia-smi`, `Get-CimInstance Win32_OperatingSystem`) :

| GPU | memory.used (MiB) | memory.free (MiB) | util.gpu % | temperature.gpu |
|---:|---:|---:|---:|---:|
| 0 | 20 890 | 3 249 | 6 | 39°C |
| 1 | 19 892 | 4 247 | 0 | 38°C |
| 2 | **252** | **23 887** | **2** | **31°C** |

| Hôte | Valeur | Seuil |
|---|---|---|
| CPU load moyen | **82 %** | < 85 % (sous le seuil, marge mince) |
| Mémoire libre | **43,1 GB** / 191,8 GB total | > 20 GB libre (OK) |
| Conteneurs running | 49 | (pas de seuil) |

**Verdict** : GPU 2 libre (252 MiB used, charge hote à 82 %). **Pas de lancement de job GPU dans l'immédiat** (charge à 82 % = marge trop mince pour un run training 4-bit QLoRA qui ajoute ~6 GB). Observation `held` (snapshot pré-run) = le prochain job `#1454` peut être scheduler dès que la charge hote descend sous 70 %, et **une nouvelle observation `held` avec `workload` non vide** sera postée au moment du lancement.

**Note de provenance** : ces mesures sont localisées au `myia-ai-01#gpu2`. Les GPU des autres machines ne sont pas couverts par cette observation — leur tenancier publie les leurs.

## Fold inaugural (semaine 2026-09-28 → 2026-10-04)

Le **fold inaugural** du ledger survit en parallèle du chantier de livraison (c.255 premier livrable, c.257 première observation). Aucun snapshot antérieur n'existe (le ledger n'existait pas sous cette forme avant le merge de `debt_ledger.py` kind `gpu-reservation`, c.255 livrable code préexistant par po-2023 #17546).

**Statut du fold inaugural** : **non-applicable**. Les semaines 2026-09-28 → 2026-10-04 sont documentées dans `D:/Runs/ICT-onset-9b-c233/onset_qwen35_9b_base.json` (c.233, c.247-quater) et `D:/Runs/ICT-onset-9b-c246/onset_qwen35_9b_base_seeds23.json` (c.246, seeds 2/3) — ces jobs ont été par rapport à une réservation **hors-ledger** (le ledger n'était pas encore actif). Le fold inaugural commence à partir de c.257 (2026-10-08T03:25Z) et la première fenêtre valide est ouverte pour la prochaine expérience GPU.

## Premier fold effectif (c.2249, 2026-10-20)

Le fold inaugural *calendaire* reste non-applicable (section précédente) : la fenêtre 2026-09-28 → 2026-10-04 n'a aucune observation à réduire. Le **premier fold effectif** a été exécuté le 2026-10-20 (c.2249) sur l'ensemble du journal accumulé depuis c.257.

| Mesure | Valeur |
|---|---|
| Observations exportées | 81 — fenêtre `full`, archive `workspace-CoursIA-gpu-reservation-ledger-2026-10-11T16-28-09.md` |
| Lignes réduites | 3 — 1 vivante, 2 historiques, 0 incomplète, 0 périmée |
| Rejets | 4 — `observation_id_mismatch` (ids écrits à la main, cf. section précédente) |
| Ligne vivante | `myia-ai-01#gpu2` — `held`, `holder myia-ai-01:CoursIA-2`, fenêtre jusqu'à 2026-10-22T08:00Z, issues #20560 + #18395 (EOS #13596) |

Le snapshot est publié sur le dashboard `CoursIA-gpu-reservation-ledger` avec le préfixe `[SNAPSHOT]`, **en version compacte** : le snapshot complet (151 Ko, provenance par champ) dépasse la capacité du dashboard (88 % au 2026-10-20). La forme publiée porte les compteurs, les lignes (champs utiles) et les rejets nommés ; le snapshot complet reste dans l'artefact local du ledger, et un snapshot + journal export permet de reconstituer l'historique complet.

### Planification hebdomadaire (acceptance #3 de #16737)

Chaque snapshot publié est **accompagné du plan de la semaine** : une issue par exécution prévue, avec son état et son ETA. Le plan est la partie *éphémère* du ledger (il change chaque semaine) — il vit sur le dashboard, pas dans ce fichier.

| Issue | Exécution | Machine / GPU | État (2026-10-20) |
|---|---|---|---|
| #20377 | re-exécution papermill end-to-end ICT-25 (GRPO réel) | myia-ai-01 / gpu2 | en vol, ETA 2026-10-21T16:00Z |
| #20560 | bras N @120 steps seed 42 + mesure EOS #13596 (2 artefacts) | myia-ai-01 / gpu2 | chaîne armée, en attente de #20377, ETA 2026-10-22T08:00Z |
| #16760 | G2 — carnet ICT-22c Geometry of Truth, échelle R1-R4 | myia-ai-01 / gpu2 | planifié, derrière la chaîne |
| #20369 | re-exécution DDP/FSDP de 3 carnets DSWA | po-2023 / gpu0-1 | fenêtre demandée par la lane po-2023 |

## Liaison cross-machine — récup statut GPU d'autres lanes (c.258)

Le tenancier de `myia-ai-01#gpu2` a besoin de **récupérer le statut GPU des autres machines** pour deux usages opérationnels :

1. **Routage d'une expérience GPU** : si le GPU 2 de `myia-ai-01` est saturé, le picker peut router l'expérience vers `myia-po-2023#gpu1` ou `myia-po-2024#gpu0` selon leur disponibilité.
2. **Coordination de fenêtre** : deux expériences concurrentes sur deux machines doivent être séquencées pour éviter de saturer l'API GitHub (rate limit GraphQL partagé) ou le réseau de téléchargement de modèles.

### Cartes device mesurées

La table du 2026-10-08 portait six lignes « à confirmer » : elle nommait les machines
sans nommer leurs devices, donc le routage ne pouvait pas s'y appuyer. Elle est
remplacée par des **cartes mesurées sur le siège**, une par device, avec leur date,
leur VRAM réelle et les lanes autorisées à lancer.

| Device | Modèle | VRAM | Lanes autorisées à lancer | Réservable par défaut | Mesure | Source |
|---|---|---|---|---|---|---|
| `myia-ai-01#gpu0` | RTX 4090 | 24 564 MiB | **aucune** — vLLM de la flotte | non | 2026-10-26T07:27Z : 22 636 MiB occupés, 80 % | mesure locale (`nvidia-smi`) |
| `myia-ai-01#gpu1` | RTX 4090 | 24 564 MiB | **aucune** — vLLM de la flotte | non | 2026-10-26T07:27Z : 21 508 MiB occupés, 81 % | mesure locale (`nvidia-smi`) |
| `myia-ai-01#gpu2` | RTX 4090 | 24 564 MiB | `myia-ai-01:CoursIA-2` (seul lanceur) | non (tenu) | 2026-10-26T07:27Z : 24 091 MiB occupés, 100 % — chaîne multi-seed #15293 en cours (`held`) | mesure locale (`nvidia-smi`) |
| `myia-po-2023#gpu0` (`CVD=0`) | RTX 3090 | 24,0 GiB | `myia-po-2023:CoursIA`, autres lanes sur accord | oui | 2026-10-25T14:12Z : 22,8 GiB libres | DM po-2023 |
| `myia-po-2023#gpu1` (`CVD=1`) | RTX 3080 Ti Laptop | 16,0 GiB | idem | oui | 2026-10-25T14:12Z : 14,8 GiB libres | DM po-2023 |
| `myia-po-2025#gpu0` | RTX 3080 Ti Laptop | 16 384 MiB | `myia-po-2025:CoursIA`, `myia-po-2025:CoursIA-2` | oui | 2026-10-25T14:19Z — **seul device exposé** (driver 616.92) | DM po-2025 |
| `myia-po-2027#gpu0` | RTX 4060 Laptop | 8 188 MiB | `myia-po-2027:CoursIA`, `myia-po-2027:CoursIA-2` | oui | 2026-10-25T15:26Z | DM po-2027 |
| `myia-po-2028#gpu0` | RTX 3070 Ti Laptop (cc 8.6) | 8 192 MiB | `myia-po-2028:CoursIA`, `myia-po-2028:CoursIA-2` — **politique posée par la régie**, le siège n'en portait aucune | oui | 2026-10-25T14:40Z : 0 compute app | DM po-2028 |
| `myia-po-2024#gpu0` | RTX 3070 Laptop (cc 8.6), driver 610.88, torch 2.14.1+cu126 | 8 191 MiB | `myia-po-2024:CoursIA` — siège **monolane** worker (reporting CoursIA et CoursIA-2) | oui — aucune réservation permanente | 2026-10-25T15:20Z : 7 128 MiB libres, run papermill en vol (~1 GiB, ETA 17:00Z) ; `device_count = 1` | DM po-2024 |
| `myia-po-2026` | — | — | — | **à mesurer** | carte **non reçue** | silence |

**gpu0/gpu1 de ai-01 portent le vLLM de la flotte** et ne se réservent pas (mêmes slots sont consommés par le serving).

Le relevé d'`ai-01` est **daté et instrumenté** : `2026-10-26T07:27Z` (heure UTC machine,
lue sur l'horloge), `nvidia-smi --query-gpu=index,name,memory.total,memory.used,utilization.gpu`.
Le relevé précédent, non horodaté, portait 22 620 / 21 408 / 15 013 MiB occupés : la
seule variation qui compte est **gpu2**, passé de 15 013 à 24 091 MiB — la chaîne
multi-seed #15293 y tourne, ce que le registre des réservations portait déjà (`held`).
L'occupation de gpu0/gpu1 (vLLM) varie de quelques points de pourcentage d'un relevé
à l'autre ; elle n'est pas un indicateur de disponibilité.

Une carte manquante n'est **pas** une carte vide : `myia-po-2026` n'a pas répondu à la
demande, et rien dans ce registre ne dit qu'elle est libre. Sa ligne se remplit à la
réception, pas par déduction.

**`myia-po-2024` a répondu le 2026-10-25T15:20Z, et sa carte corrige la table
d'origine sur un point de structure** : le siège n'expose **qu'un seul device**
(`device_count = 1`), alors que la table du 2026-10-08 lui prêtait `#gpu0` **et**
`#gpu1`. Un second slot n'a jamais existé — il avait été déduit du nom de la machine,
pas mesuré. C'est la raison d'être de la règle ci-dessus : une ligne « à confirmer »
qui se remplit de mémoire fabrique un device.

Le piège d'inversion `CVD`/`nvidia-smi` ne s'applique pas sur ce siège : avec un seul
device, `CUDA_VISIBLE_DEVICES` non posé et `CVD=0` désignent la même carte.

### Piège d'indexation — mesuré sur `myia-po-2023` le 2026-10-25

**L'indice `CUDA_VISIBLE_DEVICES` et le numéro de ligne `nvidia-smi` peuvent être
inversés.** Sur `myia-po-2023`, `CUDA_VISIBLE_DEVICES=0` désigne la **RTX 3090
(24 GiB)** et `=1` la **3080 Ti Laptop (16 GiB)** — alors que la ligne 0 de
`nvidia-smi` est la 3080 Ti. Une régie qui déduirait le device de l'ordre
`nvidia-smi` enverrait les gros runs sur la carte de 16 GiB, et le run échouerait
en OOM après avoir démarré.

**Règle** : l'identité d'un device se mesure **côté torch**
(`torch.cuda.get_device_name(i)` et `torch.cuda.mem_get_info(i)`), jamais depuis le
numéro de ligne `nvidia-smi`. La carte d'un siège est donc publiée avec son indice
`CVD` **et** le nom du modèle, comme ci-dessus.

Deuxième écart, même mesure : sous WDDM, le driver rapporte **plus** de mémoire
occupée que torch n'en voit. On dimensionne un run sur les chiffres torch, pas sur
ceux de `nvidia-smi`.

### Deux contraintes de siège qui ne sont pas des capacités

- `myia-po-2025#gpu0` est **le seul device** exposé par le pilote de ce siège : une
  réservation y consomme tout le GPU, il n'y a pas de second slot où déborder. Et
  c'est une carte **Laptop** : le budget de temps d'un run n'y est pas comparable à
  celui d'une 4090 de station (fréquence variable sous chauffe).
- Aucun run GPU ne se lance sur un siège pendant sa **fenêtre UAC/Maintenance** :
  les deux se marcheraient dessus (constat po-2025).

### Ce que le registre ne voit pas — mesuré sur le run ODM de `myia-po-2024` (#20386)

Le smoke photogrammétrique ODM du 2026-10-25 (237,6 min, rc=0, 569 images) a été
décrit comme un run « CPU-pur » dans le fil de #20386. **Il ne l'était pas** : la
chaîne embarquait un **COLMAP 4.2.1 CUDA** dans le `tools\` de sa copie de travail,
et l'étape SfM tournait sur le `gpu0` du siège. La répartition exacte GPU/CPU des
237,6 min n'est pas re-mesurée — les logs sont locaux, hors dépôt.

Le registre ne l'a pas vu. Ce n'est pas une déclaration manquante : c'est **ce que
le registre est**. Trois raisons, et elles sont structurelles :

1. **Il enregistre des réservations, pas de l'usage.** Un run local sur le siège de
   sa propre lane ne poste pas de `held` — la carte est à lui par défaut. Un device
   peut donc être chargé sans qu'aucune ligne n'existe.
2. **La consommation venait d'une dépendance de la chaîne, pas du sujet déclaré.**
   Le siège a décrit son run par ce qu'il calculait (photogrammétrie), pas par
   l'outil qui allait tenir la carte (COLMAP CUDA). Personne ne mentait.
3. **Le split CPU/GPU n'était mesuré par personne.** « CPU-pur » était une
   **supposition** présentée comme un fait — la seule chose que la régie pouvait
   objecter, et qu'elle n'a pas objectée à temps.

**Deux conséquences, et la seconde est la seule qui se tienne dans le temps :**

- **« CPU-only » sans mesure est une mesure absente, pas un verdict.** Un run de
  plusieurs heures se déclare avec sa **classe de ressource** (CPU seul / GPU
  probable / GPU certain), pas seulement avec son sujet.
- **Une carte de siège doit nommer les toolchains qui embarquent du CUDA**, pas
  seulement les cartes. `po-2024` porte COLMAP CUDA dans ses `tools\` : c'est une
  capacité de consommation GPU qui n'apparaît nulle part dans `nvidia-smi` avant
  le lancement.

**Limite assumée** : la régie ne voit pas, depuis une autre machine, un run local
démarré sans réservation. Il n'existe aucun canal pour sonder `nvidia-smi` à
distance sur ce cluster. Le registre est donc aveugle par construction à tout run
qui ne réserve pas — et la seule parade est que le siège déclare, ce que cet
échange de DM vient précisément d'établir pour les cinq sièges mesurés.

### Protocole de récupération cross-machine (c.258)

Le tenancier publie sa propre observation `[OBS]` sur le dashboard `CoursIA-gpu-reservation-ledger`. Pour récupérer l'observation d'une autre machine :

1. **DM nominatif** (canal principal) : `roosync_messages send --to myia-po-2023:CoursIA-3 --subject "[gpu-status probe] 2026-10-08T03:55Z" --body "Peux-tu poster un [OBS] rafraîchi pour myia-po-2023#gpu0 et #gpu1 sur le dashboard CoursIA-gpu-reservation-ledger ? Format JSON-LINE sur une ligne. Merci."` — réponse attendue < 5 min en session worker active, < 1 h en cron.
2. **Fallback lecture dashboard** : `roosync_dashboard read --type workspace --section all` puis grep `[OBS]` filtré par entité. Les observations sont tagguées par `entity: "myia-po-2023#gpu0"` dans le JSON, donc matchable.
3. **Cache local** : les observations récentes (< 24 h) sont cachées dans `scripts/coordination/_local/gpu_status_cache.json` pour éviter le ping à chaque décision de routage. Le cache est rafraîchi au prochain DM probe ou à l'expiration du TTL.

### Garde — ne PAS interférer avec le vLLM (c.258)

L'observation `[OBS]` d'un slot gpu0/gpu1 sur ai-01 est **interdite** : ces slots portent le serving de la flotte (LLM endpoint partagé). Le tenancier publie une observation uniquement pour les slots **non-vLLM** (gpu2 sur ai-01, gpu0/gpu1 sur les autres machines selon leur rôle). Une erreur d'aiguillage (lancer un training sur un gpu vLLM) saturerait le serving et bloquerait tous les agents de la flotte.

**Heuristique de discrimination vLLM / training** :
- ai-01 : gpu0/gpu1 = vLLM (à ne **jamais** réserver), gpu2 = training. Seul siège de la flotte dans ce cas à ce jour.
- Tous les autres sièges mesurés (`po-2023`, `po-2024`, `po-2025`, `po-2027`, `po-2028`) exposent leurs devices en **training uniquement**, sans serving : leurs cartes le disent device par device, ce n'est plus une convention. `po-2026` n'a pas encore de carte — l'absence de serving n'y est **pas** établie.

### Trigger de mise à jour

- **Toutes les 6 h** en cron worker (`myia-ai-01:CoursIA-2` active) : DM probe aux tenanciers des autres machines.
- **Sur demande coordinateur** : DM HIGH au tenancier (canal direct).
- **Événement** : nouvelle release d'expérience GPU, ou redirection de job en cours.
- **Carte manquante** : un siège sans carte reste listé comme tel à chaque passage ; il ne se remplit ni par convention ni par déduction. Relance nominative tant que la ligne est vide.

## Liens

- Issue #16737 — Ledger de reservation GPU + planification hebdomadaire des trainings (ai-01 tenancier)
- Issue #1454 — File d'expériences GPU 2
- `scripts/coordination/debt_ledger.py` — kind `gpu-reservation` (fonction `_summarize_gpu_reservation`, ligne 1490 ; `GPU_RESERVATION_FIELDS` ligne 258)
- `scripts/coordination/debt_ledger.py` — sous-commandes `append / reduce / check_pending` (4e livrable : PR #19855)
- `myia-po-2023#gpu1` acceptation initiale (c.247-quater GPU 2 release precedent, seeds 0-3 Qwen3.5-9B-Base)
- Mandat user 2026-09-18 — « les GPU devraient être gérées via le ledger de réservation que tu avais conçu »
- Mandat user 2026-10-05 ~11:33Z — régisseur GPU de la flotte

## Historique des livrables (#16737)

- **1er livrable (c.255)** : protocole initial — format `[OBS]`, garde 85 %, CUDA devices explicites, GPU 2 uniquement, fold hebdo, liaison picker / #1454.
- **2e livrable (c.257)** : 1re observation `[OBS]` + corrections paths + section "Liaison picker ↔ file #1454" + heuristique pre-launch + sous-commande `check_pending --entity`.
- **3e livrable (c.258)** : liaison cross-machine — topologie GPU (ai-01: gpu0/1=vLLM, gpu2=training ; po-* à confirmer), protocole de récupération cross-machine (DM nominatif + dashboard + cache 24h), garde vLLM, trigger de mise à jour.
- **4e livrable (c.260, PR #19855)** : implémentation de la sous-commande `check_pending` + fonction pure `evaluate_gpu_pending()`. **Ce commit (4e livrable doc)** aligne le protocole sur le schéma réel de `debt_ledger.py` (state/holder/workload/started_at/expected_end/issue) et corrige les noms de verdicts (`RELEASED`/`STALE` au lieu de `EXPIRED`).
- **5e livrable (c.2249)** : premier **fold effectif** du ledger (export large, puis réduction ; rejets `observation_id_mismatch` — compteurs dans le tableau « Premier fold effectif ») + les deux règles qui le rendent fiable — `observation_id` **calculé** et jamais écrit à la main, clé machine prise dans le roster de la flotte (`ai-01` et `myia-ai-01` sont deux écritures pour un GPU) — + la planification hebdomadaire publiée avec chaque snapshot.

- **6e livrable (PR #21684)** : canonicalisation de la clé machine au niveau outil (`canonical_machine()`) -- alias vers le nom canonique du roster, machine hors roster refusée, digest historique accepté pour ne perdre aucune observation ; la règle de protocole correspondante est reprise dans la section « La clé machine est canonicalisée ».
- **7e livrable (2026-10-25)** : la topologie du 2026-10-08 (six lignes « à confirmer ») est remplacée par des **cartes device mesurées** — modèle, VRAM réelle, indice `CUDA_VISIBLE_DEVICES`, lanes autorisées, date et source de la mesure, pour quatre sièges (`po-2023` deux devices, `po-2025`, `po-2027`, `po-2028`) plus les trois devices d'ai-01. Deux sièges restent **sans carte** (`po-2024`, `po-2026`) et sont listés comme tels. Deux règles mesurées entrent au protocole : l'indice `CUDA_VISIBLE_DEVICES` peut être **l'inverse** de l'ordre `nvidia-smi` (mesure po-2023, l'identité d'un device se lit côté torch), et un siège sans carte n'est **pas** un siège libre. Le **seuil des 15 min** qui conditionnait l'observation est **proposé** pour être remplacé par « durée annoncée » — un run court répété est indiscernable d'un siège silencieux (proposition mesurée de `myia-po-2023`, **en attente d'arbitrage du coordinateur sur #16737, non appliquée** : le seuil des 15 min reste la règle tant que l'arbitrage n'est pas rendu).

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

Le picker **ne tire plus une expérience GPU** sans qu'une observation existe dans le ledger (cohérence avec [#1454](https://github.com/jsboige/CoursIA/issues/1454) — la file d'expériences GPU).

## Format de l'envelope

L'envelope est un message dashboard d'une ligne, préfixé `[OBS]`, au format JSON. Le body est construit par la sous-commande `append` du `debt_ledger.py` (ou par un script ad-hoc qui passe par `--fields-json`).

**Exemple réel (c.257)** : entité `myia-ai-01#gpu2`, état `released` après un run training :

```json
[OBS] {"schema":"debt-ledger-observation/v1","kind":"gpu-reservation","entity":"myia-ai-01#gpu2","fields":{"state":"released","holder":"myia-ai-01:CoursIA-2","workload":"onset/SAE Qwen3.5-9B-Base (c.247-quater)","started_at":"2026-10-07T16:53:00Z","expected_end":"2026-10-08T00:00:00Z","issue":"jsboige/CoursIA#1454"}}
```

Une observation est **terminale** quand son `state` est `released` ou `stale`. Au-delà, le picker doit incrémenter `observed_at` plutôt que ré-écrire l'historique.

## Quand **réduire** (fold)

Le reducer (`python scripts/coordination/debt_ledger.py reduce --ledger gpu-reservation --events <journal>`) agrège les observations en un **snapshot** signé par le tenancier. Fréquence recommandée :

- **Hebdomadaire** (lundi 09:00Z) : fold de la semaine précédente.
- **Événementiel** : fin d'une expérience marquante (release `c.NNN-quater`, PR mergée sur axe GPU).
- **Ad-hoc** : demande du coordinateur (`myia-ai-01:CoursIA`) ou d'un user.

Le snapshot est publié sur le dashboard `CoursIA-gpu-reservation-ledger` avec le préfixe `[SNAPSHOT]`. Le snapshot **ne supprime pas** les observations — il les réduit (fold canonique). Un snapshot + journal export permet à un auditeur de reconstituer l'historique complet.

## Gardes de sécurité — ce que la lane qui lance DOIT vérifier

Avant `nvidia-smi` (ou tout autre lancement GPU) :

1. **Charge hôte** : `uptime`, `free -g`, `nvidia-smi` — la charge hôte doit rester **< 85 %** sous l'expérience. Au-delà, reporter l'expérience et poster une observation `held` une fois la charge retombée (réservation à venir, pas de geste de lancement).
2. **CUDA devices** : `CUDA_DEVICE_ORDER=PCI_BUS_ID CUDA_VISIBLE_DEVICES=<n>` sur la commande elle-même. Ne pas se fier au seul `CUDA_VISIBLE_DEVICES` (variable d'env du shell sans ordre PCI = risque d'allocation ambigu).
3. **Ledger entry** : poster `[OBS]` (`state: held`) sur `CoursIA-gpu-reservation-ledger` **avant** le geste de lancement (pas après — sinon collision possible). Poster `[OBS]` (`state: released`) à la fin du run, avec `workload` court et `expected_end` réel.
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

1. Avant de tirer un grain `training` ou `genai` marqué **GPU-bound** (heuristique : à définir), le picker vérifie qu'une observation `[OBS]` existe dans le ledger pour l'entité ciblée via la sous-commande `check_pending --entity <m>#gpu<n>`.
2. **Pas d'observation `[OBS]`** (`verdict: NO_OBS`) → le picker saute le grain et log `[SKIP gpu-reservation missing]`. La lane worker qui rencontre ce skip doit poster l'observation OU prendre un grain non-GPU.
3. **Observation `held` par une autre lane** (`verdict: HOLD`) → le picker signale `[DEFER gpu-reservation hold]` et passe au suivant.
4. **Observation `held` par ma lane, dans la fenêtre** (`verdict: OK_TO_RUN`) → le picker tire normalement.
5. **Observation `released`** (`verdict: RELEASED`) → le GPU est libre, le picker peut tirer.
6. **Observation `stale`** (`verdict: STALE`) → cas d'erreur, la lane tenancière doit poster un `[OBS]` de réparation.

Le script `scripts/coordination/debt_ledger.py check_pending --entity <m>#gpu<n>` rend le verdict (`OK_TO_RUN`, `NO_OBS`, `HOLD`, `RELEASED`, `STALE`) en ~50 ms (cache local). **Implémentation 4e livrable : [PR #19855](https://github.com/jsboige/CoursIA/pull/19855)**, merge de la sous-commande et de `evaluate_gpu_pending()` (113/113 tests passent).

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

## Liaison cross-machine — récup statut GPU d'autres lanes (c.258)

Le tenancier de `myia-ai-01#gpu2` a besoin de **récupérer le statut GPU des autres machines** pour deux usages opérationnels :

1. **Routage d'une expérience GPU** : si le GPU 2 de `myia-ai-01` est saturé, le picker peut router l'expérience vers `myia-po-2023#gpu1` ou `myia-po-2024#gpu0` selon leur disponibilité.
2. **Coordination de fenêtre** : deux expériences concurrentes sur deux machines doivent être séquencées pour éviter de saturer l'API GitHub (rate limit GraphQL partagé) ou le réseau de téléchargement de modèles.

### Topologie GPU connue (à 2026-10-08)

| Machine | GPU disponibles | Tenancier (lane) | Statut observation |
|---|---|---|---|
| `myia-ai-01` | gpu0 (vLLM), gpu1 (vLLM), **gpu2** (training) | `myia-ai-01:CoursIA-2` | observation c.257 (252 MiB used, 31°C) |
| `myia-po-2023` | gpu0, gpu1 | `myia-po-2023:CoursIA-3` | (à confirmer — DM `po-2023`) |
| `myia-po-2024` | gpu0, gpu1 | `myia-po-2024:CoursIA-2` | (à confirmer — DM `po-2024`) |
| `myia-po-2025` | (à confirmer — pas de training GPU sur cette machine a priori) | `myia-po-2025:CoursIA-2` (adjoint) | n/a |
| `myia-po-2026` | (à confirmer) | `myia-po-2026:CoursIA-2` | n/a |
| `myia-po-2027` | (à confirmer) | `myia-po-2027:CoursIA-2` | n/a |

**gpu0/gpu1 de ai-01 portent le vLLM de la flotte** et ne se réservent pas (mêmes slots sont consommés par le serving).

### Protocole de récupération cross-machine (c.258)

Le tenancier publie sa propre observation `[OBS]` sur le dashboard `CoursIA-gpu-reservation-ledger`. Pour récupérer l'observation d'une autre machine :

1. **DM nominatif** (canal principal) : `roosync_messages send --to myia-po-2023:CoursIA-3 --subject "[gpu-status probe] 2026-10-08T03:55Z" --body "Peux-tu poster un [OBS] rafraîchi pour myia-po-2023#gpu0 et #gpu1 sur le dashboard CoursIA-gpu-reservation-ledger ? Format JSON-LINE sur une ligne. Merci."` — réponse attendue < 5 min en session worker active, < 1 h en cron.
2. **Fallback lecture dashboard** : `roosync_dashboard read --type workspace --section all` puis grep `[OBS]` filtré par entité. Les observations sont tagguées par `entity: "myia-po-2023#gpu0"` dans le JSON, donc matchable.
3. **Cache local** : les observations récentes (< 24 h) sont cachées dans `scripts/coordination/_local/gpu_status_cache.json` pour éviter le ping à chaque décision de routage. Le cache est rafraîchi au prochain DM probe ou à l'expiration du TTL.

### Garde — ne PAS interférer avec le vLLM (c.258)

L'observation `[OBS]` d'un slot gpu0/gpu1 sur ai-01 est **interdite** : ces slots portent le serving de la flotte (LLM endpoint partagé). Le tenancier publie une observation uniquement pour les slots **non-vLLM** (gpu2 sur ai-01, gpu0/gpu1 sur les autres machines selon leur rôle). Une erreur d'aiguillage (lancer un training sur un gpu vLLM) saturerait le serving et bloquerait tous les agents de la flotte.

**Heuristique de discrimination vLLM / training** :
- ai-01 : gpu0/gpu1 = vLLM (à ne **jamais** réserver), gpu2 = training.
- po-2023/po-2024 : à confirmer par observation de la première `[OBS]`. Par convention, les machines worker `po-*` utilisent leurs gpu0/gpu1 en training (pas de serving), mais cette convention peut évoluer.

### Trigger de mise à jour

- **Toutes les 6 h** en cron worker (`myia-ai-01:CoursIA-2` active) : DM probe aux tenanciers des autres machines.
- **Sur demande coordinateur** : DM HIGH au tenancier (canal direct).
- **Événement** : nouvelle release d'expérience GPU, ou redirection de job en cours.

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
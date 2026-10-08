# GPU Reservation Ledger — protocole de la flotte

> **Tenancier** : `myia-ai-01:CoursIA-2` (mandat user 2026-09-18, mandat régisseur GPU 2026-10-05).
> **Code source** : `scripts/coordination/debt_ledger.py` (kind `gpu-reservation`, fonction `_summarize_gpu_reservation`).
> **Dashboard dédié** : `CoursIA-gpu-reservation-ledger` (un par kind, jamais partagé).
> **Issue de référence** : [#16737](https://github.com/jsboige/CoursIA/issues/16737).

## Vue d'ensemble

Le ledger `gpu-reservation` catalogue **une entrée par réservation GPU**, cléée par `<machine>#gpu<n>`. Chaque entrée porte :

| Champ | Type | Description |
|---|---|---|
| `entity` | string | `<machine>#gpu<n>` (ex : `myia-ai-01#gpu2`, `myia-po-2023#gpu0`). |
| `issued_by` | string | lane qui a posé la réservation (ex : `myia-ai-01:CoursIA-2`). |
| `experiment` | string | issue/PR de l'expérience (ex : `#1454` pour la file GPU 2.0). |
| `window_start` | ISO-8601 | début de la fenêtre d'usage. |
| `window_end` | ISO-8601 | fin de la fenêtre d'usage. |
| `mode` | enum | `'run'` (training SAH/SAE), `'bench'` (microbench), `'hold'` (réservation sèche, ex : maintenance). |
| `load_pct` | float | charge hôte cible à ne pas dépasser (cf. garde 85 %). |
| `cuda_visible` | string | variable d'env CUDA Devices (ex : `CUDA_DEVICE_ORDER=PCI_BUS_ID CUDA_VISIBLE_DEVICES=2`). |
| `notes` | string | annotations libres (cf. ci-dessous). |

## Pourquoi un ledger — pas un README

Le **README documente l'intention**, le **ledger documente l'usage réel**. Une réservation GPU consomme une fenêtre de temps qu'aucune autre lane ne doit chevaucher. Sans ledger, deux lanes peuvent exécuter en parallèle sur la même machine et se neutraliser (saturation mémoire, swap, etc.).

Le dashboard `CoursIA-gpu-reservation-ledger` est la **seule source de vérité** de l'usage GPU réel de la flotte. Les fichiers `*.ledger.json` dans `scripts/coordination/_local/` sont des artefacts locaux (init/spool/reduce) qui n'ont aucune valeur cross-machine.

## Quand poster une observation

**Toute lane** qui lance une expérience GPU poste une observation sur le dashboard dédié avant `nvidia-smi` (ou équivalent). Le geste est **rapide** (1 message), **atomique** (1 observation = 1 fenêtre), et **idempotent** (un re-post remplace l'observation précédente pour la même entité, fenêtre mise à jour).

Le picker **ne tire plus une expérience GPU** sans qu'une observation existe dans le ledger (cohérence avec [#1454](https://github.com/jsboige/CoursIA/issues/1454) — la file d'expériences GPU).

## Format de l'envelope

L'envelope est un message dashboard d'une ligne, préfixé `[OBS]`, au format JSON :

```json
[OBS] {"schema":"debt-ledger-observation/v1","kind":"gpu-reservation","entity":"myia-ai-01#gpu2","issued_by":"myia-ai-01:CoursIA-2","experiment":"#1454","window_start":"2026-10-08T00:00Z","window_end":"2026-10-08T04:00Z","mode":"run","load_pct":85.0,"cuda_visible":"CUDA_DEVICE_ORDER=PCI_BUS_ID CUDA_VISIBLE_DEVICES=2","notes":"onset/SAE Qwen3.5-9B-Base seed 2/3 (c.247-quater)"}
```

Une observation valide toutes les 5000 observations — au-delà, le picker doit incrémenter `issued_at` plutôt que ré-écrire l'historique.

## Quand **réduire** (fold)

Le reducer (`python scripts/coordination/debt_ledger.py reduce --ledger gpu-reservation --events <journal>`) agrège les observations en un **snapshot** signé par le tenancier. Fréquence recommandée :

- **Hebdomadaire** (lundi 09:00Z) : fold de la semaine précédente.
- **Événementiel** : fin d'une expérience marquante (release `c.NNN-quater`, PR mergée sur axe GPU).
- **Ad-hoc** : demande du coordinateur (`myia-ai-01:CoursIA`) ou d'un user.

Le snapshot est publié sur le dashboard `CoursIA-gpu-reservation-ledger` avec le préfixe `[SNAPSHOT]`. Le snapshot **ne supprime pas** les observations — il les réduit (fold canonique). Un snapshot + journal export permet à un auditeur de reconstituer l'historique complet.

## Gardes de sécurité — ce que la lane qui lance DOIT vérifier

Avant `nvidia-smi` (ou tout autre lancement GPU) :

1. **Charge hôte** : `uptime`, `free -g`, `nvidia-smi` — la charge hôte doit rester **< 85 %** sous l'expérience. Au-delà, reporter l'expérience et poster une observation `hold` (réservation à venir).
2. **CUDA devices** : `CUDA_DEVICE_ORDER=PCI_BUS_ID CUDA_VISIBLE_DEVICES=<n>` sur la commande elle-même. Ne pas se fier au seul `CUDA_VISIBLE_DEVICES` (variable d'env du shell sans ordre PCI = risque d'allocation ambigu).
3. **Ledger entry** : poster `[OBS]` sur `CoursIA-gpu-reservation-ledger` **avant** le geste (pas après — sinon collision possible).
4. **GPU 0/1 réservé** : les GPU 0 et 1 portent le vLLM de la flotte et **ne se réservent pas**. Le GPU 2 est le seul slot GPU de cette machine pour les expériences.

## Périmètre du tenancier

Le tenancier (`myia-ai-01:CoursIA-2`) :

- **Lance** les expériences GPU de sa machine (GPU 2 uniquement).
- **Ne lance PAS** sur les GPU 0/1 (vLLM) ni sur les GPU des autres machines (sauf coordination explicite avec leur lane propriétaire).
- **Récupère** le statut GPU d'autres machines (`poset/disponibilité_gpu`, ticket DM `myia-ai-01 → myia-po-2025 → myia-po-2023`).
- **Réduit** le ledger une fois par semaine (lundi 09:00Z) en fold canonique.
- **Coordonne** la file #1454 avec le picker : une expérience GPU ne va jamais sur la flèche sans observation préalable.

## Liaison picker ↔ file #1454

Le picker (`scripts/pick_idle_grain.py`) croise l'urne `delivered` avec un signal **pre-launch** :

1. Avant de tirer un grain `training` ou `genai` marqué **GPU-bound** (heuristique : présence de `cuda_visible`, `experiment` ∈ file #1454), le picker vérifie qu'une observation `[OBS]` existe dans le ledger pour l'entité ciblée.
2. **Pas d'observation `[OBS]`** → le picker saute le grain et log `[SKIP gpu-reservation missing]` dans son diagnostic. La lane worker qui rencontre ce skip doit poster l'observation OU prendre un grain non-GPU.
4. **Observation `hold`** → le picker signale `[DEFER gpu-reservation hold]` et passe au suivant.
3. **Observation `run` valide** (window_start ≤ now ≤ window_end) → le picker tire normalement.

Le script `scripts/coordination/debt_ledger.py check_pending --entity <m>#gpu<n>` rend le verdict (`OK_TO_RUN`, `NO_OBS`, `HOLD`, `EXPIRED`) en ~50 ms (cache local).

## Première observation [OBS] — c.257 (2026-10-08T03:25Z)

**Entité** : `myia-ai-01#gpu2`
**Issued by** : `myia-ai-01:CoursIA-2`
**Mode** : `hold` (aucune expérience en cours — relevé de l'état machine, pas de réservation active)
**Experiment** : `#1454` (file GPU 2, prochain job à scheduler)

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

**Verdict** : GPU 2 libre (252 MiB used, charge hote à 82 %). **Pas de lancement de job GPU dans l'immédiat** (charge à 82 % = marge trop mince pour un run training 4-bit QLoRA qui ajoute ~6 GB). Observation `hold` = le prochain job `#1454` peut être scheduler dès que la charge hote descend sous 70 %.

**Note de provenance** : ces mesures sont localisées au `myia-ai-01#gpu2`. Les GPU des autres machines ne sont pas couverts par cette observation — leur tenancier publie les leurs.

## Fold inaugural (semaine 2026-09-28 → 2026-10-04)

Le **fold inaugural** du ledger survit en parallèle du chantier de livraison (c.255 premier livrable, c.257 première observation). Aucun snapshot antérieur n'existe (le ledger n'existait pas sous cette forme avant le merge de `debt_ledger.py` kind `gpu-reservation`, c.255 livrable code préexistant par po-2023 #17546).

**Statut du fold inaugural** : **non-applicable**. Les semaines 2026-09-28 → 2026-10-04 sont documentées dans `D:/Runs/ICT-onset-9b-c233/onset_qwen35_9b_base.json` (c.233, c.247-quater) et `D:/Runs/ICT-onset-9b-c246/onset_qwen35_9b_base_seeds23.json` (c.246, seeds 2/3) — ces jobs ont été par rapport à une réservation **hors-ledger** (le ledger n'était pas encore actif). Le fold inaugural commence à partir de c.257 (2026-10-08T03:25Z) et la première fenêtre valide est ouverte pour la prochaine expérience GPU.

## Liens

- Issue #16737 — Ledger de reservation GPU + planification hebdomadaire des trainings (ai-01 tenancier)
- Issue #1454 — File d'expériences GPU 2
- `scripts/coordination/debt_ledger.py` — kind `gpu-reservation` (fonction `_summarize_gpu_reservation`, ligne 1490)
- `scripts/coordination/debt_ledger.py` — sous-commandes `append / reduce / check_pending`
- `myia-po-2023#gpu1` acceptation initiale (c.247-quater GPU 2 release precedent, seeds 0-3 Qwen3.5-9B-Base)
- Mandat user 2026-09-18 — « les GPU devraient être gérées via le ledger de réservation que tu avais conçu »
- Mandat user 2026-10-05 ~11:33Z — régisseur GPU de la flotte
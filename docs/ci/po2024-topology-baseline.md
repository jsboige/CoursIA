# Topologie baseline hôte myia-po-2024 — sous-grain #15574

Mesure first-hand 2026-09-15T15:55Z sur `myia-po-2024` (Windows 11 Pro 10.0.26200 / MSI GE76 Raider 11UG). Fournie par `scripts/ci/measure_po2024_topology.py` (cross-platform Windows/Linux/macOS, dépendance standard uniquement).

## Mesures stables (propriétés de la machine)

| Métrique | Valeur | Source instrument |
|---|---|---|
| Hostname | `myia-po-2024` | `platform.node()` |
| OS | Windows 11 (10.0.26200) | `platform.platform()` |
| Fabricant | Micro-Star International Co., Ltd. | `Win32_ComputerSystem.Manufacturer` |
| Modèle | GE76 Raider 11UG | `Win32_ComputerSystem.Model` |
| **CPU modèle** | 11th Gen Intel Core i7-11800H @ 2.30GHz | `Win32_Processor.Name` |
| **Cores physiques** | **8** | `Win32_Processor.NumberOfCores` |
| **Logical processors** | **16** (hyperthreading actif) | `Win32_Processor.NumberOfLogicalProcessors` |
| **RAM totale** | **63.71 GiB** | `Win32_ComputerSystem.TotalPhysicalMemory` |
| **RAM libre** | **7.17 GiB** (88.7 % utilisée) | `Win32_OperatingSystem.FreePhysicalMemory` (KiB → GiB) |
| **Slots RAM** | 2 × 32 GiB DDR4-3200 MHz | `Win32_PhysicalMemory` (×2 instances) |
| Daemon Docker | Docker Desktop / WSL2 kernel 6.6.87.2 | `docker info` |
| **Docker plafonné** | **16 vCPU / 23.47 GiB** | `docker info NCPU/MemTotal` |
| Docker conteneurs running | 0 | `docker info ContainersRunning` |
| Docker conteneurs total | 2 (lean_cli + lean_research, exited) | `docker info Containers` |

## Volatile (instantané — non reproductible)

| Métrique | Valeur au moment de la mesure | Périmé au re-run |
|---|---|---|
| **CPU Load instant** | **76 %** | Oui — instantané |
| **RAM libre** | **7.17 GiB** | Oui — varie selon charge |

Les 2 mesures « instant » (CPU Load, RAM free) **changent à chaque relecture** ; elles documentent un état ponctuel, pas une propriété de la machine. Le champ JSON `cpu_load_instant_pct` est explicitement nommé `instant` pour porter cette volatilité dans la sortie reproductible.

## Complémentarité avec le commentaire ai-01 #5645345667

Le commentaire ai-01 sur #15574 a écrit deux nombres qui restent à mesurer depuis la machine :

> « Le nombre de conteneurs par hôte **physique** et le plafond de
>   jobs concurrents de l'hôte. Ces deux nombres restent à écrire
>   depuis la machine, et je ne les devine pas. »

| Nombre demandé | Mesurable depuis po-2024 OS-localement ? | Statut |
|---|---|---|
| Conteneurs éphémères **par hôte physique** du pool `coursia-ephemeral` | **NON** : les conteneurs self-hosted s'exécutent dans la VM cloud de l'organe Actions — ce ne sont **pas** les conteneurs docker de la machine locale. Côté OS local, on ne voit que les conteneurs **personnels** (lean_cli, lean_research). | **Restant** — outillage exclusif côté console d'administration GitHub org (rôle coordinateur ai-01). |
| Plafond de jobs concurrents de l'hôte | **NON** : paramètre d'enregistrement `self-hosted runner` côté GitHub org, pas paramètre OS | **Restant** — idem. |

**Ce que ce sous-grain livre** : caractéristiques OS-level reproductibles + le **plafond Docker WSL2** = 16 vCPU / 23.47 GiB, qui borne mécaniquement le nombre de jobs CI concurrents **quand un hôte physique accueille le daemon docker par défaut**. Si GitHub Actions monte un conteneur éphémère **dans** WSL2 plutôt que dans une VM dédiée, le plafond mesurable ici est la borne supérieure.

**Ce que ce sous-grain reporte** : les deux nombres API-dépendants que ai-01 a nommés explicitement. Pas de **fabrication** ([G.2](../../CLAUDE.md) métriques honnêtes) : pas de mesure, pas de chiffre dans la sortie JSON.

## Lien avec narrow-cache hostile c.1181-c.1197

La **variance 3-4× mesurée par ai-01** sur `ict-tests.yml` (30 derniers runs, 2,7× médiane sur jambe témoin à code constant) et le **pool narrow-cache hostile sustained 16 cycles** sur cette lane ont **une cause structurelle candidate commune** : saturation de co-résidence sur hôte(s) partagé(s) par 116 workflows déclarant `coursia-linux`. Les mesures ci-dessus donnent à un coordinateur les chiffres manquants pour fermer la branche.

## Reproduction

```bash
python scripts/ci/measure_po2024_topology.py
# → JSON sur stdout, 1 ligne de mesure "Topologie baseline"
```

Pas de dépendance externe. Module standard Python uniquement (cross-platform).

## Périmètre exclu (et pourquoi)

- `scripts/ci/measure_runner_demand.py` (claim myia-po-2025:CoursIA 2026-09-12T13:33:42Z, paths sur les distributions par label/runner — accepté avant merge).
- Pas de modification au pool, au plafond de concurrence, ou aux workflows ; ce sous-grain **ne livre pas** le levier opérationnel, seulement la baseline reproductible depuis l'OS.

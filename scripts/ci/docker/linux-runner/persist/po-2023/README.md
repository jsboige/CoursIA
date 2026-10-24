# Persistance des runners Linux — myia-po-2023

Installe le **2026-10-24** sur la VM WSL `Ubuntu` de MYIA-PO-2023 (Windows 11 Pro,
32 Go, 20 cœurs logiques). Composition demandée par ai-01 : **3 slots docker**,
labels `coursia-ephemeral,coursia-linux`, **pas** de jambe `waiters`, **pas** de
jambe `lean`, pas de `RUNNER_MODE=persistent`.

Ces fichiers sont les **copies de référence** de ce qui tourne réellement dans la
distro. Les originaux vivent dans `/etc/systemd/system/` et `/usr/local/bin/` ;
en cas de divergence, c'est la distro qui fait foi, et l'écart est un défaut à
corriger ici.

## Fichiers

| Fichier | Destination dans la distro |
|---|---|
| `coursia-runner-start.sh` | `/usr/local/bin/coursia-runner-start.sh` (mode 755) |
| `coursia-runner.service` | `/etc/systemd/system/coursia-runner.service` |
| `coursia-ci.slice` | `/etc/systemd/system/coursia-ci.slice` |
| `coursia-socket.conf` | `/etc/systemd/system/docker.service.d/coursia-socket.conf` |
| `coursia-docker-socket.conf` | `/etc/systemd/system/docker.socket.d/coursia-listen.conf` |

Les trois pièces communes à toute la flotte — `persist/daemon.json`,
`persist/hold-runner.ps1`, `persist/launch-runner.sh` — ne sont **pas**
dupliquées ici : ce sont les fichiers du niveau supérieur, sans variante po-2023.

## Deltas contre po-2028 (la référence la plus récente)

| Axe | po-2028 | po-2023 | Pourquoi |
|---|---|---|---|
| Composition | 8 slots × 1536m | **3 slots × 4g** | consigne ai-01 (N = 3) ; classe « Scripts Tests (CPU) » #16643 — 1536m ferait tuer le job par OOM |
| `MemoryHigh` | 12G | **10G** | la VM porte 20 conteneurs GenAI vivants (~16,9 Go résidents) : le reclaim doit commencer 2 Go plus bas, pour que la pression tombe sur la CI et jamais sur les services |
| `MemoryMax` | 14G | **12G** | égal à la somme des caps des 3 slots (3 × 4 Go) ; po-2028 met +2 Go au-dessus |
| `COURSIA_RUNNER_CPU_BUDGET` | (autre dimensionnement) | **10** | moitié des 20 cœurs logiques de la VM, comme demandé par ai-01 ; 3 × 3 vCPU = 9 consommés, 1 vCPU de marge non allouée |
| `COURSIA_RUNNER_BUDGET_GB` | (autre dimensionnement) | **12** | = somme des caps (règle #19802) : plafond d'**admission**, pas un mur |
| Jeton | `GH_RUNNERS_ADMIN_TOKEN` | cascade 4 étages | po-2023 n'a pas ce jeton dans son `master.env` (mesuré le 2026-10-24) — voir ci-dessous |
| `docker.socket` | non traité | **`coursia-docker-socket.conf`** | incident mesuré le 2026-10-24, voir ci-dessous |

## Le jeton — cascade à 4 étages, et pourquoi

`coursia-runner-start.sh` essaie, dans l'ordre : `GH_RUNNERS_ADMIN_TOKEN` (le
jeton dédié de la doctrine flotte), puis `GITHUB_ACCESS_TOKEN`, puis
`GITHUB_TOKEN` dans `master.env`, puis `gh.exe auth token` par interop Windows.

Le jeton dédié est essayé **en premier** pour que la machine se range d'elle-même
dans la doctrine dès qu'il sera provisionné, sans retoucher le wrapper. Les trois
voies ont été mesurées `admin=true` sur `jsboige/CoursIA` le 2026-10-24.

Le jeton n'apparaît jamais dans `argv`, dans un commit, dans une PR ni sur un
dashboard : il est relu à chaque invocation et meurt avec le processus.

## L'incident `docker.socket` (mesuré le 2026-10-24) — la leçon de cette machine

**Ce qui s'est passé.** Le drop-in `docker.service.d/coursia-socket.conf` de
po-2028 vide `Requires=` pour empêcher `docker.service` d'entraîner
`docker.socket` (qui détient `/run/docker.sock`, le socket de Docker Desktop).
Sur po-2023, **ce vidage n'a pas pris** : après déploiement,
`systemctl show docker.service -p Requires` rendait encore
`Requires=system.slice sysinit.target docker.socket`, alors que le vidage
`ExecStart=` du même fichier, lui, fonctionnait parfaitement.

**Conséquence.** Démarrer `docker.service` activait `docker.socket`, qui prenait
`/run/docker.sock` — le socket par défaut de la machine. Docker Desktop a perdu
son point de rendez-vous (`docker info` pendait, `docker ps` rendait une liste
vide), alors que son moteur et ses 20 conteneurs GenAI étaient intacts.

**Réparation.** Un drop-in sur l'unité **socket** elle-même
(`docker.socket.d/coursia-listen.conf`) qui vide `ListenStream` et le repose sur
un chemin neutre, `/run/docker-ci-socket-activation.sock`. Vérification :
`systemctl show docker.socket -p Listen`. Le socket de Desktop a été restauré
par un lien vers son proxy d'hôte (`/mnt/wsl/docker-desktop/shared-sockets/host-services/docker.proxy.sock`),
et les 20 conteneurs ont été revérifiés depuis Windows.

**La règle qui en sort.** Neutraliser la dépendance par un vidage `Requires=`
n'est pas portable : selon la version de systemd et de docker-ce, le vidage peut
être ignoré. Le geste déterministe est de **déplacer le socket**, pas d'espérer
que la dépendance tombe. Les deux drop-ins sont donc livrés ensemble ici.

**Résidu assumé.** Le lien `/run/docker.sock → proxy d'hôte` vit sur tmpfs et ne
survit pas à un redémarrage de la distro. C'est à l'intégration Docker Desktop
de le reprovisionner ; si elle ne le fait pas, le symptôme est un `docker` muet
côté distro uniquement, sans effet sur le démon de CI (qui est sur son socket
privé) ni sur le moteur Desktop.

## Budgets déclarés (postés sur le dashboard avant installation)

| Variable | Valeur | Sens |
|---|---|---|
| `COURSIA_RUNNER_CPU_BUDGET` | 10 | somme des vCPU des familles d'exécution ; refus au démarrage au dépassement |
| `COURSIA_RUNNER_BUDGET_GB` | 12 | somme des caps mémoire ; plafond d'admission |
| `COURSIA_RUNNER_CGROUP_PARENT` | `coursia-ci.slice` | parent cgroup des conteneurs |
| `COURSIA_RUNNER_REQUIRE_CGROUP_BUDGET` | 1 | `assert_ci_slice` refuse de démarrer si la slice manque ou n'a pas `io.max` |
| `COURSIA_RUNNER_CPUS` / `_MEMORY` / `_PIDS` | 3 / 4g / 512 | dimensionnement par slot, classe « Scripts Tests (CPU) » |

`COURSIA_RUNNER_HOST_FREE_FLOOR_GB` est **retiré** de `supervise.sh` (ligne 480) :
il n'est pas disponible comme garde sur cette version.

## Murs de la slice (vérifiés après pose)

```
MemoryHigh=10737418240   (10G)
MemoryMax=12884901888    (12G)
MemorySwapMax=0          (aucun swap : un job qui déborde meurt localement, exit 137 retryable)
IOWeight=50
IOWriteBandwidthMax=/var/lib/docker 209715200
IOReadBandwidthMax=/var/lib/docker  419430400
```

Disque au moment de la pose : `/dev/sdf 1007G, 316G utilisés, 641G libres (34 %)`
— très au-dessus du plancher de 20 % exigé après N slots.

## Persistance — trois étages

1. **systemd dans la distro** : `coursia-runner.service`, `Restart=always`,
   `Requires=`/`BindsTo=docker.service` (fail-closed #15095).
2. **Pont Windows à l'ouverture de session** : `persist/launch-runner.sh`, appelé
   par le raccourci `CoursIA-LinuxRunners.lnk` du dossier Démarrage — **non
   élevé**. La variante « tâche planifiée » exige une fenêtre UAC et reste en
   attente (voir ci-dessous).
3. **Porteur WSL** : `persist/hold-runner.ps1`, qui maintient la distro vivante
   (`systemctl start … && exec sleep infinity`). Obligatoire : WSL récolte la
   distro moins de 3 minutes après la sortie du dernier client, même avec
   systemd en PID 1.

## Rollback (écrit avant l'installation, conservé ici)

```bash
# dans la distro
sudo systemctl disable --now coursia-runner.service
sudo /usr/local/bin/coursia-runner-start.sh stop   # ExecStop gracieux, un job en vol va à son terme
```

État attendu après rollback : les slots passent `offline` au registre, aucun
conteneur `coursia-ci=1` vivant. Le démon docker-ce, la slice et les drop-ins
peuvent rester en place : ils ne consomment rien sans conteneur.

## Reste à faire

- **Tâche planifiée `CoursIA-LinuxRunners`** (variante élevée du pont de session,
  et tâche S4U au démarrage) : assemblage déjà dry-runé, en attente d'une
  **fenêtre UAC annoncée**. Le raccourci du dossier Démarrage couvre le cas
  nominal en attendant.
- **Premier job réel** : l'acceptation se fait **au registre**
  (`gh api repos/jsboige/CoursIA/actions/runners` → slots `online`) **et** par un
  run effectif, jamais par `systemctl is-active`. Le run id est posté sur le
  dashboard.
- **Latence GenAI pendant un job** : les références avant installation sont
  ComfyUI `/system_stats` 200 en 0,068 s et SearXNG 0,136 s. Dégradation
  observée = arrêt du service d'abord, rapport ensuite. Fil-piège : `free`
  sous 2 Go libres pendant un job → arrêt et rapport.

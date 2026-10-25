# Leg coursia-runner de po-2027 (Linux, ephemere)

Slots Docker Linux pour le pool `coursia-linux`, en mode **ephemere** : un job par
enregistrement, puis le conteneur se retire et le superviseur en demarre un neuf.
La machine reste un poste de travail — les caps sont dimensionnes pour que l'hote
prime.

## Manifeste

| Fichier | Role |
|---|---|
| `coursia-runner-start.sh` | Enveloppe du legs : budget CPU/memoire, jeton, `DOCKER_HOST`, gardes, puis `exec supervise.sh` |
| `coursia-ci.slice` | Slice cgroup qui borne l'ensemble (memoire, swap, cpu) |
| `coursia-runner.service` | Unite systemd du superviseur, rattachee a la slice |
| `coursia-socket.conf` | Drop-in de `docker.socket` (socket neutre, cf. piege ci-dessous) |
| `docker.service` | Override complet de l'unite Docker (necessaire sur ce systemd) |
| `install-keepalive-task.ps1` | Tache Windows qui re-arme le porteur toutes les 5 min (self-heal) |

Le pont Windows `persist/launch-runner.sh` et le porteur `hold-runner.ps1` sont
communs a toutes les machines ; seul `install-keepalive-task.ps1` est propre a ce
poste.

## Pourquoi un porteur, et pourquoi il ne suffit pas

WSL reape une distro des que le dernier client sort, **meme** avec systemd en
PID 1, le service actif et les slots online (mesure fondatrice du 2026-09-02,
consignee dans `persist/hold-runner.ps1`). Un reveil one-shot ne tient donc rien :
le porteur est un `wsl.exe` detache qui demarre le service puis dort.

Mesure du 2026-10-24 (cette machine) : ce porteur vit exactement aussi longtemps
que la distro. Un `wsl --shutdown` — ce que fait Docker Desktop a chaque
redemarrage — les tue ensemble.

| Evenement | Heure (CEST) | Effet mesure |
|---|---|---|
| Porteur spawn (pid 38780) | 23:32:22 | slots online |
| `wsl --shutdown` (Docker Desktop) | 23:54:02 | distro et porteur morts ; 4 slots disparus de GitHub |
| Boot suivant, autostart systemd | 23:54:12 | `docker.service` + `coursia-runner.service` actifs |
| Slots de nouveau online | ~23:54:2x | 4/4, sans intervention |

Le redemarrage se rétablit donc seul **cote runner** ; ce qui manquait est le
porteur. Sans lui, la distro est a nouveau reapee des que le dernier client
sort, et les slots disparaissent en silence — le seul symptome est leur absence.

## Installation

1. Fichiers systeme (sous WSL root) : `coursia-ci.slice`, `coursia-runner.service`,
   `coursia-socket.conf`, `docker.service` aux emplacements systemd.
2. Pont et porteur Windows : `persist/launch-runner.sh` +
   `%USERPROFILE%\.coursia-runner\hold-myia-po-2027.ps1`.
3. Tache logon (creee en eleve, une seule fois) : action
   `C:\Program Files\Git\bin\bash.exe -lc "<depot>/persist/launch-runner.sh 4"`.
4. Tache de rattrapage, **non elevee** :

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File install-keepalive-task.ps1          # dry-run
powershell -NoProfile -ExecutionPolicy Bypass -File install-keepalive-task.ps1 -Apply   # ecrit
```

L'appel est idempotent : porteur vivant, `hold-myia-po-2027.ps1` se contente d'un
`systemctl start` one-shot.

## Retrait

```powershell
schtasks /Delete /TN "Coursia-LinuxRunners-Keep" /F   # tache de rattrapage
schtasks /Delete /TN "Coursia-LinuxRunners" /F        # tache logon (en eleve)
```

Puis `supervise.sh stop` **avant** toute extinction : l'arret gracieux laisse le
job en vol se terminer, une extinction brutale le tue.

## Limite connue, a ne pas maquiller

Un `wsl --shutdown` tue les jobs en vol, et GitHub laisse alors le job
`in_progress` jusqu'a detection de la perte du runner. Cas mesure le
2026-10-24 : run `40129334303`, job `120977484412` sur
`myia-po-2027-linux-docker-4`, demarre 21:53:45Z, fige a l'etape 5 a 21:53:53Z,
soit 9 s avant le shutdown de 21:54:02Z (journal evenementiel Windows du
2026-10-24 : NIC de la VM demonte a 21:54:03Z, recree au boot suivant a
21:54:12Z ; Docker Desktop redemarre a 21:54:19Z). Le leg ne peut pas s'en proteger : la
cause est externe (redemarrage de Docker Desktop). Ce qu'il peut faire, et que
la tache de rattrapage fait, est de revenir en ligne sans intervention.

## Deregistration propre

Le mode ephemere se desinscrit seul : apres chaque job, le conteneur ecrit
`Removed .credentials` / `Removed .runner` et rend son jeton d'enregistrement.
Un `supervise.sh stop` arrete les slots sans laisser d'enregistrement orphelin ;
le registre GitHub oscille donc en fonctionnement normal (une entree par slot
present a l'instant de la lecture).

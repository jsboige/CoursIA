# `po-2026/` -- pool de runners `coursia-linux` sans Docker, et sans borne jusqu'au 2026-09-22

Ce sous-repertoire porte la chaine de runners self-hosted de **po-2026**. Elle est
la seule du parc a ne reposer **ni sur Docker, ni sur une unite systemd** : c'est
ce qui la rend invisible dans les documents qui decrivent le parc par ses
conteneurs et ses unites.

| Fichier | Chemin vivant | Etat |
|---|---|---|
| `pool.sh` | `/home/jesse/CoursIA-runners-p0/pool.sh` (WSL Ubuntu) | **deploye et vivant** -- superviseur du pool, 8 slots depuis le 2026-09-22 |
| `run-pool-po2026.sh` | `C:\dev\CoursIA-runners-p0\run-pool-po2026.sh` (hote Windows) | **deploye et vivant** -- lanceur de la tache planifiee, porte la borne CPU/memoire. La premiere forme ecrite le 2026-09-22 ne relancait **rien** (cf. piege du transport ci-dessous) ; la forme livree est verifiee de bout en bout |

**Attention -- la chaine est coupee en deux repertoires.** Mesure du 2026-09-22 :

| Repertoire hote | Contenu |
|---|---|
| `C:\dev\CoursIA-runners-p0\` | **le lanceur seulement** (`run-pool-po2026.sh`) -- c'est le chemin fige dans l'action de la tache planifiee, donc celui qui ne peut pas bouger sans redeployer la tache |
| `D:\Dev\CoursIA-runners-p0\` | **le superviseur seulement** (`pool.sh`) |

Les deux ne sont **pas** une jonction l'un de l'autre : ce sont deux repertoires
distincts, aux contenus disjoints. Chercher `pool.sh` sous `C:\dev\...` ou
`run-pool-po2026.sh` sous `D:\Dev\...` rend un fichier absent -- ce qui, lu vite,
ressemble a « la source n'existe plus ». La copie vivante cote WSL
(`/home/jesse/CoursIA-runners-p0/pool.sh`) est une copie **LF** de la source `D:` ;
les deux ont ete mesurees **byte-identiques** le 2026-09-22 (`sha256:458b6bf3af69...`).

## Architecture mesuree (firsthand sur po-2026, 2026-09-22)

| Element | Valeur mesuree | Oracle |
|---|---|---|
| Distro | Ubuntu 24.04.3 LTS (noble) | `. /etc/os-release` |
| PID 1 de la distro | `systemd` 255 (255.4-1ubuntu8.17) | `ps -p 1 -o comm=` |
| Utilisateur | `jesse`, `$HOME=/home/jesse` | `id -un` |
| Daemon Docker | **absent** -- le binaire `/usr/bin/docker` est installe, `/var/run/docker.sock` n'existe pas | `ls /var/run/docker.sock` |
| Unite systemd du pool | **aucune** -- `systemctl --user list-units 'coursia*'` rend 0 unite | `systemctl --user list-units` |
| Declencheur hote | tache planifiee `CoursIA-LinuxRunners-po2026`, type **a l'ouverture de session**, compte `jsboi` | `schtasks /Query /TN ... /V /FO LIST` |
| Action de la tache | `C:\Program Files\Git\bin\bash.exe -l /c/dev/CoursIA-runners-p0/run-pool-po2026.sh` | idem |
| Labels demandes par un slot | `coursia-ephemeral,coursia-linux` | `pool.sh` |
| Nom d'un slot | `myia-po-2026-wsl-<n>` | `pool.sh` |
| Mode | `--ephemeral` + `run.sh --once` : un slot sert **un** job puis se desenregistre et est re-cree | `pool.sh` |

Le superviseur est un script bash qui boucle : pour chaque slot mort, il reminte un
registration token (`gh.exe api .../registration-token`), extrait le bundle runner
dans `slot-<n>/`, enregistre le runner en ephemeres et lance `run.sh --once`. Un
`flock -n` sur `pool.lock` garantit qu'il n'y en a qu'un.

**Cette architecture n'est pas un choix documente, c'est un etat de fait** : aucun
des fichiers de `persist/` ne decrit po-2026, et aucun document du depot ne
mentionnait que cette machine servait des jobs `coursia-linux`.

## Le defaut livre par la PR du 2026-09-22 : le pool n'etait borne par RIEN

Mesure avant le correctif, sur le superviseur vivant :

```
$ cat /proc/<superviseur>/cgroup
0::/init.scope
```

`/init.scope` est le scope de l'init WSL. Le pool n'etait donc borne ni par une
unite, ni par un scope, ni par un conteneur -- **aucun des quatre leviers** que le
`README.md` parent decrit pour le parc dockerise (`coursia-ci.slice`, la limite par
conteneur, `COURSIA_RUNNER_CPU_BUDGET`, `COURSIA_RUNNER_BUDGET_GB`) n'existe ici :
les trois derniers supposent un daemon Docker, et le premier une unite.

Consequence concrete : avec `POOL_SIZE=8`, huit jobs simultanes pouvaient prendre
les 20 vCPU et la memoire de la VM, famine de la lane interactive incluse. Le
`README.md` parent documente deja ce que coute un cap mal dimensionne (correction 5 :
un cap juge « ~10x le pic mesure » a fait OOM un rendu Quarto) -- ici il n'y avait
pas de cap du tout.

## La borne livree, et pourquoi ce mecanisme

Le mecanisme disponible dans cette distro est un **scope systemd utilisateur** :

```bash
systemd-run --user --scope --unit=coursia-pool-po2026 \
  -p CPUQuota=1400% -p MemoryMax=20G "$HOME/CoursIA-runners-p0/pool.sh"
```

C'est ce que fait `run-pool-po2026.sh`. Trois raisons, chacune mesuree :

1. **Les controleurs n'existent pas a la racine du cgroup v2.** `cat
   /sys/fs/cgroup/cgroup.controllers` rend `cpuset cpu io memory hugetlb pids rdma` :
   la liste est vide de tout fichier de limite a ce niveau, donc ecrire
   `memory.max` a la racine n'est pas un chemin disponible.
2. **systemd tourne en PID 1 dans la distro** (255), donc `systemd-run --user`
   dispose d'un gestionnaire pour creer et borner le scope. Le scope est nomme,
   donc verifiable : `systemctl --user status coursia-pool-po2026.scope`.
3. **Le mecanisme est verifiable par le cgroup du processus.** Mesures du
   2026-09-22 : superviseur nu `0::/init.scope` ; processus dans un scope utilisateur
   nomme `0::/user.slice/user-1000.slice/user@1000.service/app.slice/<nom>.scope`.
   C'est le tell du defaut, et il ne demande aucune hypothese sur la facon dont le
   processus a ete lance.

### Le piege du transport `wsl.exe` -- un `$` dans la commande, et la borne disparait

Premiere ecriture du lanceur, le 2026-09-22 : le script construisait la commande
avec des variables.

```bash
# NE PAS FAIRE -- cette forme ne borne rien et ne relance rien
exec wsl.exe -d Ubuntu -- bash -lc '
set -u
UNIT=coursia-pool-po2026
exec systemd-run --user --scope --unit="$UNIT" -p CPUQuota=1400% -p MemoryMax=20G \
  "$HOME/CoursIA-runners-p0/pool.sh"
'
```

Mesure : la tache planifiee rendait

```
Failed to mangle scope name: Invalid argument
```

`UNIT` etait arrive **vide** cote WSL : Git Bash (MSYS) mange les references `$VAR`
avant que WSL ne les voie. La commande devenait donc `--unit=` (unite sans nom) et
un chemin d'executable vide. Le tell est trompeur -- le message parle de « mangle »,
pas de variable perdue, et rien n'indique que c'est le transport qui a mange le
texte.

Le meme piege frappe **le transport, pas le contenu** : une commande mono-ligne
`wsl.exe -d Ubuntu -- bash -lc 'UNIT=x; echo "[$UNIT]"'` rend `[]` exactement comme
la forme multi-lignes. Ce qui marche est une commande **sans aucun `$`**, chemins
ecrits en clair :

```bash
exec wsl.exe -d Ubuntu -- bash -lc 'systemd-run --user --scope --unit=coursia-pool-po2026 -p CPUQuota=1400% -p MemoryMax=20G /home/jesse/CoursIA-runners-p0/pool.sh'
```

(une seule ligne -- la forme exacte du fichier livre, sans `$` ni continuation de ligne)

**Ce que ca a coute, et pourquoi c'est ecrit ici.** Le defaut n'etait pas seulement
que le pool restait sans borne : la tache planifiee **ne relancait plus le pool du
tout**. Un redemarrage de la machine aurait laisse po-2026 avec **zero** slot
`coursia-linux`, et le message d'erreur n'aurait accuse ni la variable ni le
transport. La verification qui l'attrape est de bout en bout : lancer le script par
son chemin de production et verifier qu'une ligne **du jour** apparait dans
`/home/jesse/CoursIA-runners-p0/pool.log` -- un `systemd-run` qui rend « Running as
unit: ... » ne prouve pas que le superviseur a ete atteint.

### Dimensionnement -- mesure sur cette machine, pas recopie

| Ressource | Mesure po-2026 | Borne posee | Motif |
|---|---|---|---|
| vCPU | `nproc` = 20 (i7-12700H) | `CPUQuota=1400%` = 14 vCPU | 14 pour la CI, 6 laisses a l'interactif |
| Memoire VM | `free -g` : 23 Go vus par WSL | `MemoryMax=20G` | backstop contre la famine de la lane interactive ; le plafond dur reste la memoire de la VM |
| Swap | 32 Go | non borne | hors perimetre de cette PR |

**Le cap annonce a d'abord ete 16 Go, il est livre a 20 Go** -- et l'ecart est
assume, pas silencieux : le pic de la phase de test est **non mesure** sur cette
machine, et le `README.md` parent documente qu'un cap serre sur une extrapolation a
deja produit un OOM reel. Poser 16 Go sur une VM de 23 Go n'aurait rien protege de
plus qu'un plafond a 20 Go, tout en augmentant le risque de tuer un job legitime.

La borne est **au niveau du pool, pas du slot** : c'est une propriete a connaitre,
car elle ne protege pas un slot isole mais l'ensemble `pool + hote`. Un seul job
pathologique peut consommer la part des huit.

## Le piege du verrou -- `kill` du superviseur ne libere pas le pool

Mesure firsthand : apres `kill -TERM <superviseur>`, la relance immediate rend

```
2026-09-22T11:55:00+02:00 pool deja actif (/home/jesse/CoursIA-runners-p0/pool.lock)
```

Le `flock` est pose sur le descripteur 9 avant la boucle, et **les sous-shells de
slot l'heritent**. Tuer le seul superviseur laisse donc le verrou tenu par le slot
encore vivant, et toute relance echoue proprement mais sans effet.

Ce que ca implique pour une procedure de redemarrage :

- **ne pas boucler sur `kill` puis relance** en esperant que ca converge : la
  relance echoue tant que le dernier slot n'a pas termine son job ;
- **attendre la liberation du verrou** en la sondant
  (`flock -n "$HOME/CoursIA-runners-p0/pool.lock" -c true`), puis relancer ;
- **ne pas tuer les slots** pour aller plus vite quand un job est en vol : c'est
  couper un job CI reel. Tuer le superviseur seul est sur -- les slots lui
  survivent et terminent leur job.

## Sequence de deploiement

```bash
# 1. installer le lanceur a SON chemin vivant -- C:, pas D: : c'est le chemin
#    fige dans l'action de la tache planifiee :
install -m 0755 run-pool-po2026.sh /c/dev/CoursIA-runners-p0/run-pool-po2026.sh

# 2. cote WSL, le superviseur (copie LF, PAS de CRLF) -- chemin litteral, sans $ :
wsl.exe -d Ubuntu -- bash -lc 'install -m 0755 /mnt/d/Dev/CoursIA-runners-p0/pool.sh /home/jesse/CoursIA-runners-p0/pool.sh'

# 3. relancer par le chemin de production (la tache planifiee) :
schtasks /Run /TN "CoursIA-LinuxRunners-po2026"

# 4. PREUVE que la relance a atteint le superviseur -- une ligne DU JOUR :
wsl.exe -d Ubuntu -- bash -lc 'grep -a "pool demarre" /home/jesse/CoursIA-runners-p0/pool.log | tail -2'

# 5. PREUVE de la borne -- le cgroup du superviseur (PID pris a l'etape 4) :
wsl.exe -d Ubuntu -- bash -lc 'pgrep -af "^bash /home/jesse/CoursIA-runners-p0/pool.sh"'
wsl.exe -d Ubuntu -- bash -lc 'cat /proc/<PID>/cgroup'

# 6. verifier le nombre de slots en ligne :
gh api repos/jsboige/CoursIA/actions/runners --paginate \
  --jq '.runners[] | select(.name|test("myia-po-2026-wsl-")) | .name'
```

Les etapes 4 et 5 sont les deux oracles. `systemd-run` qui rend « Running as unit »
ne prouve **pas** que le superviseur a ete atteint -- il l'a rendu pendant des
heures alors que `pool.sh` n'etait jamais lance (cf. le piege du transport
ci-dessus). La preuve de la **relance** est une ligne du jour dans `pool.log` ; la
preuve de la **borne** est le cgroup du processus. La liste des unites n'est qu'un
indice : elle rendait 0 unite sur le superviseur nu, et elle rend le scope nomme
seulement tant qu'il est vivant -- deux etats tres differents que la meme sortie
vide confond.

## Ce que cette PR ne tranche pas

- **`#14329` propose de supprimer le superviseur hote plutot que de le blinder**
  (runner non-ephemere en conteneur `--restart unless-stopped`). La borne livree ici
  est de la seconde famille : elle reduit le dommage, elle ne supprime pas le
  maillon. La position de `#14329` reste ouverte, et sur po-2026 elle supposerait
  d'installer un daemon Docker, absent aujourd'hui.
- **`#16646` demande de trancher la conteneurisation du superviseur ou de la refuser
  par ecrit.** Le scope livre ici est une troisieme voie (borner sans conteneuriser) ;
  il apporte une piece au dossier, il ne repond pas a l'issue.
- **Le cap de 20 Go est un backstop, pas un dimensionnement mesure.** Le pic reel
  d'un pool de 8 jobs n'a pas ete echantillonne. Tant qu'il ne l'est pas, ce chiffre
  ne doit pas etre cite comme une mesure.

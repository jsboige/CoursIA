# `persist/` -- copies de reference des fichiers qui vivent HORS du depot

Les fichiers de ce repertoire ne sont **executes par personne ici**. Chacun est la
copie de reference d'un fichier deploye ailleurs : une unite systemd sous
`/etc/systemd/system/`, un wrapper sous `/usr/local/bin/`, une configuration de
daemon sous `/etc/docker/`. Le depot en garde une copie pour qu'ils soient
relisibles, versionnes et discutables en PR -- pas pour qu'ils tournent.

**Consequence directe, et c'est la premiere correction que ce fichier doit :**
modifier un fichier ici ne change rien sur une machine tant que la copie vivante
n'a pas ete remplacee. Un `git pull` ne deploie pas `persist/`.

## Table de correspondance -- quel fichier appartient a quelle machine

| Fichier | Machine | Chemin vivant | Etat |
|---|---|---|---|
| `coursia-runner.service` | **po-2024** | `/etc/systemd/system/coursia-runner.service` | reference |
| `coursia-runner-start.sh` | **po-2024** | `/usr/local/bin/coursia-runner-start.sh` | reference |
| `launch-runner.sh` | po-2024 | lancement manuel d'un slot | reference |
| `hold-runner.ps1` | po-2024 (hote Windows) | tache planifiee | reference |
| `coursia-lean.service` | **po-2024** | `/etc/systemd/system/coursia-lean.service` | reference |
| `coursia-lean-start.sh` | **po-2024** | `/usr/local/bin/coursia-lean-start.sh` | reference |
| `coursia-waiters.service` | ai-01 (execute telle quelle par po-2024, qui la dimensionne par son propre drop-in) | `/etc/systemd/system/coursia-waiters.service` | **reference partagee** -- 12 slots, prefixe par defaut de `supervise.sh`. NE PAS confondre avec `ai-01/coursia-waiters.service` (famille B, deposee le 2026-10-28) : les deux portent le meme nom vivant, sur deux sieges differents |
| `coursia-waiters-start.sh` | **ai-01** | `/usr/local/bin/coursia-waiters-start.sh` | **deploye et vivant** (2026-10-28, arbitrage `ai01-c2721-23037-budget` point 3) -- le wrapper est **PINLE hors arbre de travail** : l'unite vivante l'appelle desormais par `/usr/local/bin`, et non plus par le clone de travail partage `/mnt/d/CoursIA/scripts/ci/docker/linux-runner/persist/coursia-waiters-start.sh`. Un checkout de branche dans `D:\CoursIA` ne change donc plus le code du pool au prochain redemarrage. Les deux copies portent la purge de sentinelle #15163. **Ce que le pin ne couvre pas** : le wrapper est un lanceur mince, il fait `cd $REPO_DIR` puis `exec $SUPERVISE_SH` -- le code du SUPERVISEUR reste lu dans l'arbre de travail partage (le chemin est devenu explicite et surchargeable par `COURSIA_SUPERVISE_SH`) |
| `coursia-ci.slice` | **ai-01** | `/etc/systemd/system/coursia-ci.slice` | **deploye et vivant** -- 7235 octets, documente, et il etait **en avance sur le depot** : c'est le depot qui a ete synchronise depuis le vivant, pas l'inverse (cf. correction 6) |
| `daemon.json` | **ai-01** | `/etc/docker/daemon.json` | **deploye et vivant** -- 155 octets, **byte-identique** a la copie du depot (`sha256:1ef80038e470...`, mesure le 2026-09-08). **Ne se recopie PAS sur un autre daemon** : il ne sert que le daemon `systemd` -- cf. « Le nom plat de `cgroup-parent` » ci-dessous |
| `ai-01/coursia-runner.service` | **ai-01** | `/etc/systemd/system/coursia-runner.service` | **a deployer** (corrige, cf. correction 3) -- **jamais seul**, cf. correction 4 |
| `ai-01/coursia-runner.service.d/10-sizing.conf` | **ai-01** | `/etc/systemd/system/coursia-runner.service.d/10-sizing.conf` | **deploye et vivant** -- necessaire mais **pas suffisant** : il borne la memoire et laisse le CPU au defaut (cf. corrections 4 et 5) |
| `ai-01/coursia-runner-start.sh` | **ai-01** | `/usr/local/bin/coursia-runner-start.sh` | **a deployer** (corrige, cf. correction 3) |
| `ai-01/coursia-waiters.service` | **ai-01** | `/etc/systemd/system/coursia-waiters.service` | **deploye et vivant** (2026-10-28) -- unite PERSISTANTE du pool d'attente PR-gate (label `coursia-waiter`), famille B : 10 slots, prefixe `myia-ai-01-wsl-waiterb`, state dir `/var/lib/coursia-waiters-b`, `enable`d. Remplace l'unite TRANSITOIRE `coursia-waiters-b.service` (memes parametres, releves a l'identique), qui disparaitait au reboot. **Depuis le 2026-10-28**, `ExecStart`/`ExecStop` pointent vers le wrapper PINLE `/usr/local/bin/coursia-waiters-start.sh` (arbitrage `ai01-c2721-23037-budget` point 3) et non plus vers le wrapper du clone de travail partage. Le bandeau « DEPRECATED » qui figurait ici (2026-10-15, #20835) est REFUTE : `pr-gate.yml` l.172 consomme le label depuis #21063 (2026-10-16) |
| `ai-01/coursia-runner.service.d/40-scale-14.conf` | **ai-01** | `/etc/systemd/system/coursia-runner.service.d/40-scale-14.conf` | **deploye et vivant** (2026-10-28) -- drop-in de SCALAGE et de BUDGET (le `10-sizing.conf` porte le dimensionnement : memoire, cap par slot, nombre de slots). `ExecStart` du runner a 14 slots, `COURSIA_RUNNER_BUDGET_GB=80`, et **`COURSIA_RUNNER_CPU_BUDGET=40`** (arbitrage `ai01-c2721-23037-budget` : 32 -> 40, sans couper aucune famille). La mesure qui fonde la decision -- 38 vCPU de demande declaree (14 x 2 + 10 x 1), slice a 32 coeurs, `cpu.stat` a 7 evenements / 2,4 s sur ~25 h -- est ecrite dans le fichier meme et dans la section « Le budget CPU : 32 -> 40 » ci-dessous |
| `ai-01/coursia-waiters.service.d/10-sizing.conf` | **ai-01** | `/etc/systemd/system/coursia-waiters.service.d/10-sizing.conf` | **deploye et vivant** (2026-10-28) -- caps des slots waiters (1 vCPU, 512m, 128 pids, mesures sur le pool transitoire) + budget CPU **arme** a 10 vCPU : la famille waiters n'en declarait aucun, donc `assert_cpu_budget` y etait inactif |
| `po-2026/pool.sh` | **po-2026** | `/home/jesse/CoursIA-runners-p0/pool.sh` (WSL Ubuntu) | **deploye et vivant** -- superviseur du pool, **8 slots** et **borne depuis le 2026-09-22** (cf. `po-2026/README.md`) |
| `po-2026/run-pool-po2026.sh` | **po-2026** (hote Windows) | `C:\dev\CoursIA-runners-p0\run-pool-po2026.sh` | **deploye et vivant** -- lanceur de la tache planifiee, porte la borne CPU/memoire. **Attention : ce fichier vit sous `C:\dev\...`, pas sous `D:\Dev\CoursIA-runners-p0\`** (cf. `po-2026/README.md`) |
| `po-2026/README.md` | -- | -- | **document** : architecture, dimensionnement, piege du verrou |
| `po-2024/coursia-ci.slice` | **po-2024** | `/etc/systemd/system/coursia-ci.slice` | **a deployer** (2026-10-12, arbitrage c2153 : 14G/16G -> **20G/22G**, budget 15 -> **21** apres #20174 -- la composition vive 8x1536 + 6x512 + 1x6144 = 21 504 Mo n'avait pas ete comptee depuis le J+7) -- le mur kernel de cette machine : `MemoryHigh=20G`, `MemoryMax=22G`, `MemorySwapMax=0`. Homonyme de la slice ai-01, valeurs differentes (cf. section `po-2024/`) |
| `po-2024/coursia-waiters.service.d/10-sizing.conf` | **po-2024** | `/etc/systemd/system/coursia-waiters.service.d/10-sizing.conf` | **a deployer** (2026-10-12, arbitrage c2153 : budget 15 -> **21**, meme nombre que les wrappers) -- 12 -> 6 slots waiters pour po-2024 seulement, par drop-in, parce que `coursia-waiters.service` est le fichier d'**ai-01** que les deux machines executent |
| `po-2028/coursia-ci.slice` | **po-2028** | `/etc/systemd/system/coursia-ci.slice` | **deploye et vivant** (2026-10-20) -- mur kernel pour une VM WSL de 31 Go : `MemoryHigh=12G`, `MemoryMax=14G`, `MemorySwapMax=0`, io.max 8:80 rbps=400M/wbps=200M. Homonyme des slices ai-01/po-2024, valeurs differentes |
| `po-2028/coursia-socket.conf` | **po-2028** | `/etc/systemd/system/docker.service.d/coursia-socket.conf` | **deploye et vivant** (2026-10-20) -- PREMIERE copie depotiee du drop-in socket (la doc citait `coursia-socket.conf` sans que persist/ le porte). Differe des deploiements historiques : il VIDE aussi `Requires=docker.socket` -- piege mesure sur po-2028, l'unite stock porte `Requires=docker.socket`, qui recreerait `/var/run/docker.sock` (socket du proxy Docker Desktop) a chaque boot ; et l'arret de docker.socket CASCADE l'arret du service via son `Service=` |
| `po-2028/coursia-runner-start.sh` | **po-2028** | `/usr/local/bin/coursia-runner-start.sh` | **deploye et vivant** (2026-10-20) -- wrapper, 3 slots x (cpus=3, memory=4g, pids=512), BUDGET_GB=12, CPU_BUDGET=9, device bps 40M/80M. DELTA token : pas de master.env sur cette machine -- le token est relu a chaque invocation depuis `gh.exe auth token` cote Windows via interop |
| `po-2028/coursia-runner.service` | **po-2028** | `/etc/systemd/system/coursia-runner.service` | **deploye et vivant** (2026-10-20) -- unite, `start 3`, structure conforme au modele po-2024 (#15095 fail-closed, IOWeight, sentinel) |

Le sous-repertoire `ai-01/` existe parce que les deux machines ont des fichiers
**homonymes et incompatibles**. Les melanger a plat, comme c'etait le cas, revient
a laisser croire qu'il n'y en a qu'un.

Le sous-repertoire `po-2024/` existe pour la meme raison que `ai-01/` : ses deux
fichiers sont homonymes de fichiers d'autres machines, et **incompatibles** avec
eux. `coursia-ci.slice` porte les bornes de la VM de 24 Go de po-2024, la ou la
copie d'ai-01 borne une machine bien plus large ; les confondre ferait deployer
16 Go de plafond dur sur une machine qui en a 24, ou l'inverse. Le drop-in
waiters est l'autre moitie du meme probleme : l'unite `coursia-waiters.service`
appartient a ai-01 et po-2024 l'execute **telle quelle**, donc editer l'unite
pour descendre po-2024 descendrait aussi ai-01 -- le drop-in rend le perimetre
explicite.

Le sous-repertoire `po-2028/` suit la meme regle, avec une addition : il porte
`coursia-socket.conf`, le drop-in `docker.service.d` qui epingle le daemon
docker-ce sur `/var/run/docker-ce.sock`. La doc le citait (section
Persistance) sans que `persist/` n'en garde copie -- le deploiement po-2028 est
l'occasion de combler le trou. Sa copie differe des vivants historiques sur un
point documente dans le fichier meme : le vidage de `Requires=docker.socket`.

Les fichiers po-2024 anterieurs (wrappers `runner-start`, `lean-start`, unites
`runner` et `lean`) restent a la racine de `persist/` : ce sont eux qui ont
etabli la convention « racine = po-2024 » avant que les sous-repertoires
n'existent, et les deplacer serait du churn sans portee. Tout **nouvel** artefact
propre a une machine dont le nom est deja pris ailleurs va dans son
sous-repertoire.

Le sous-repertoire `po-2026/` existe pour une raison differente : cette machine est
la seule du parc dont la chaine de runners ne passe **ni par Docker ni par une unite
systemd**. Ses fichiers ne sont homonymes d'aucun autre, mais la table ci-dessus,
lue comme une description du parc, laissait croire que le parc se resume a des
conteneurs et des unites -- et c'est exactement ce qui a rendu son absence de borne
invisible. Detail, mesures et bornes : `po-2026/README.md`.

## Le contexte d'image epingle -- un vivant sans fichier dans le depot (#16134)

Le motif s'etend au **contexte de build des images runner**. Depuis #16134,
`supervise.sh pin` copie `entrypoint.sh`, `work_cache_health.sh`,
`seed_action_cache.py`, `Dockerfile` et `Dockerfile.lean` du checkout vers un
repertoire epingle (defaut `$STATE_DIR/image-context`, overridable par
`COURSIA_RUNNER_PINNED_CTX`), et le garde de fraicheur compare l'image a CETTE
copie -- plus au checkout vivant. Ce repertoire est un vivant de la meme
classe que la table ci-dessus : il n'a **pas** de copie dans `persist/` (il
n'est pas un fichier unique mais un artefact reconstruit par le gesture), il
vit hors de tout worktree, et seul `pin` le deplace.

Consequence de deploiement, meme nature que la premiere correction de ce
fichier : un `git pull` ne deploye RIEN -- apres un merge qui touche
`entrypoint.sh` ou `work_cache_health.sh`, la sequence est `pin` puis rebuild
depuis l'epingle (le pin publie le diff d'empreintes et la commande exacte).
Tant que l'epingle n'est pas bougee, un checkout de branche ou une edition non
commitee laissent le parc demarrable -- c'est l'acceptance de la tranche (a).
La protection #14801 est conservee : epingle plus recente que l'image = refus
`PERIMEE` au demarrage.

## Les six corrections dues sur #15091 / #15094

Les trois premiers ont ete etablis firsthand sur ai-01 le 2026-09-07, les
trois suivants le 2026-09-08 (lecture des fichiers vivants via
`wsl.exe -d Ubuntu -u root --`). Ils corrigent des choses que
j'avais annoncees ou laissees entendre, et qui etaient fausses.

Les corrections **4, 5 et 6** ont ete ajoutees apres coup et se lisent en fin
de fichier, **apres** la section « Voir aussi ».

### 1. La PR #15094 patche une copie qui ne tourne pas sur ai-01

`persist/coursia-runner.service` et `persist/coursia-runner-start.sh` sont ceux de
**po-2024** : depot sous `/mnt/d/Dev/CoursIA` (migration du 2026-09-17 ; le
defaut etait `/mnt/c/dev/CoursIA` avant, cf. #16578), prefixe
`myia-po-2024-linux-docker`,
et un wrapper qui relaie n'importe quelle sous-commande (`exec "$SUPERVISE" "$@"`).

Les fichiers vivants d'ai-01 sont differents sur les trois points qui comptent :
depot sous `/mnt/d/CoursIA`, prefixe `myia-ai-01-wsl`, et un premier argument qui
est le **nombre de slots**, pas une sous-commande. Un correctif porte sur la copie
a plat ne touche donc pas la machine qui a gele. C'est ce que le sous-repertoire
`ai-01/` rend desormais impossible a confondre.

**Les deux chemins ne different plus que par un segment** (`/mnt/d/Dev/CoursIA`
pour po-2024, `/mnt/d/CoursIA` pour ai-01) : les relire a la lettre avant de
conclure un drift -- une difference d'un seul composant est exactement ce que
l'oeil saute.

### 2. `systemctl start` ignore `disabled` -- une unite desactivee redemarre au boot

J'ai ecrit que la machine etait au repos parce que les deux unites etaient
`inactive` / `disabled`. C'etait incomplet. `disabled` ne dit qu'une chose : que
l'unite n'a pas de lien dans `multi-user.target.wants`. Un `systemctl start`
explicite la demarre quand meme.

Or la tache planifiee Windows **`CoursIA-LinuxRunners-Boot`** fait exactement cela
a chaque demarrage. Une unite desactivee y est donc re-armee sans que rien ne
signale la contradiction. La desactivation seule n'est pas un arret : la tache
planifiee fait partie de l'inventaire a traiter, et elle est le vrai item du lot
UAC (le travail sur le superviseur, lui, n'en demande aucun -- tout se fait sous
WSL root).

### 3. L'arret gracieux d'ai-01 n'a jamais fonctionne, et rendait 0 en le faisant

C'est le defaut le plus consequent des trois, parce qu'il est silencieux.

`coursia-runner.service` sur ai-01 porte un `Environment=` **vide** et un
`ExecStop=` qui appelle `supervise.sh stop` **directement**, sans passer par le
wrapper. Sans `COURSIA_RUNNER_STATE_DIR`, `supervise.sh` retombe sur son defaut,
`$HOME/.coursia-runner` -- soit `/root/.coursia-runner` pour un service systemd.
Et comme `supervise.sh` fait lui-meme `mkdir -p "$STATE_DIR"`, l'arret **cree** ce
repertoire, y pose son sentinel, et affiche son message de succes.

Mesure : le repertoire n'existait pas avant la sonde, il existait apres. Le
superviseur, lui, surveille `/var/lib/coursia-runner/stop`. Il n'a jamais rien vu.

`cmd_stop` rend `0` quoi qu'il arrive -- le script tourne sous `set -uo pipefail`
**sans `-e`**, donc l'echec eventuel du `touch` n'interromprait rien, et le code de
retour de la fonction est celui de son dernier `echo`. Un arret inerte est donc
indiscernable d'un arret reussi, pour systemd comme pour l'operateur.

La suite est mecanique : `systemctl stop` attend, rien ne se passe, puis le
`KillMode=mixed` envoie SIGTERM aux jobs en vol. C'est-a-dire precisement le
« couper net » que le sentinel existe pour eviter, et que le commentaire de
l'unite decrit comme produisant des rouges qui ne veulent rien dire.

La jambe **waiters** ne souffre pas de ce defaut : son wrapper porte une branche
`stop`, et son unite y route son `ExecStop`. `ai-01/coursia-runner-start.sh`
reprend cette forme.

## Ce qui rend l'ordre de grandeur concret

Le diagnostic d'origine parlait de « traffic disque fou et git clones en serie ».
Voici ce qu'un clone complet de ce depot coute, mesure sur ai-01 le 2026-09-07 par
lecture de metadonnees git (aucun clone lance -- la machine sortait de deux gels
d'I/O, et deux autres lanes sondaient le disque au meme moment) :

| Grandeur | Valeur | Comment elle est obtenue |
|---|---|---|
| Objets dans le pack | 241 982 | `git count-objects -v` |
| **Transfere par un clone complet** | **3,70 Gio** | `size-pack` |
| **Ecrit par le checkout** | **1,14 Gio** (10 387 blobs) | somme des tailles de `git ls-tree -r -l HEAD` |
| `.git` sur disque, arbre deja construit | 13 Go | `du -sh` |
| Arbre de travail apres builds | 67 Go | `du -sh` |

Les deux dernieres lignes ne sont **pas** ce qu'un clone ecrit : elles portent les
artefacts de build (`.lake`, caches, sorties). Ce qu'un slot neuf ecrit reellement,
c'est la somme des deux premieres, **environ 4,8 Gio par clone**. Douze slots qui
repartent ensemble ecrivent une cinquantaine de gigaoctets avant d'avoir execute la
premiere ligne de CI -- sans aucun plafond, sur le meme disque que l'interactif.

C'est la raison d'etre des bornes ci-dessous, et la raison pour laquelle elles sont
posees **avant** le redemarrage du parc, pas apres.

## Les quatre bornes, et laquelle borne quoi

Elles ne sont pas redondantes : chacune couvre ce que les autres ne peuvent pas
voir.

| Borne | Ou elle vit | Ce qu'elle borne | Ce qu'elle ne peut pas borner |
|---|---|---|---|
| `coursia-ci.slice` | `/etc/systemd/system/` + `cgroup-parent` du daemon | la **somme** de tous les conteneurs : `CPUQuota=800%`, `MemoryHigh`/`MemoryMax`/`MemorySwapMax`, `IOWriteBandwidthMax` | rien en dessous : elle ne distingue pas un slot glouton d'une famille entiere |
| `--device-write-bps` / `--device-read-bps` | drapeaux passes par `supervise.sh` a chaque `docker run` | **un** conteneur | la somme : 12 conteneurs conformes un a un saturent quand meme le disque |
| `COURSIA_RUNNER_CPU_BUDGET` | verification dans `supervise.sh` au demarrage | la **somme des demandes** de vCPU entre familles, **avant** de lancer quoi que ce soit | l'usage reel : c'est un refus de demarrage, pas un plafond kernel |
| `COURSIA_RUNNER_BUDGET_GB` | **declare par le wrapper de CHAQUE machine** (les trois jambes, meme nombre) | la **somme des memoires** en vol **plus** la demande, toutes familles, avant de lancer un slot | la memoire reellement consommee ensuite, et le page cache de la VM : c'est un refus de demarrage, pas un plafond kernel |

**`COURSIA_RUNNER_BUDGET_GB` est la seule borne de ressource qui n'est PAS inerte
par defaut**, et c'est pour cela qu'elle doit etre ecrite : elle ne peut pas valoir
0 (le garde compare une somme EN VOL a ce budget -- 0 refuserait tous les slots de
toutes les machines), donc son defaut 12 **gouverne**. Tant qu'aucun wrapper ne
l'ecrit, la valeur effective n'existe dans aucun fichier que l'operateur ouvre.
Le superviseur la **signale** desormais a chaque demarrage quand elle manque ; un
avertissement `[budget] AVERTISSEMENT` dans le journal du service veut dire que
cette machine n'a pas declare son budget, pas que quelque chose est casse.


Le budget agrege est applique a **deux endroits distincts**, et la distinction n'est pas
cosmetique. Le **defaut du daemon** (`cgroup-parent` dans `daemon.json`) ne vaut que pour
le daemon qui porte ce fichier -- c'est la seule cible du fichier, objet de la section
suivante. Le **drapeau du superviseur** est ce qui place reellement les conteneurs de la
flotte : `supervise.sh` passe `--cgroup-parent` sur ses deux chemins de lancement, avec le
nom que chaque pilote attend (nom plat sous `systemd`, chemin imbrique sous `cgroupfs`).
Ce qui reste vrai de l'avertissement d'origine : passer ce drapeau sur une machine ou la
slice n'existe pas **cree** un cgroup vide, qui a l'apparence exacte d'un garde et ne borne
rien -- d'ou la neutralisation (`CI_CGROUP_PARENT=""`) quand la slice manque, et le
controle d'appartenance apres demarrage (`EVASION`).

### Le nom plat de `cgroup-parent` n'est correct que sous le pilote `systemd` (#15157)

`daemon.json` porte `"cgroup-parent": "coursia-ci.slice"`. C'est la **bonne valeur pour
la seule cible qu'il sert** : `/etc/docker/daemon.json` alimente le daemon `docker-ce`,
dont le pilote cgroup est `systemd`, qui resout ce nom en slice imbriquee sous
`coursia.slice` -- celle qui porte `MemoryMax`.

**Ce fichier ne se recopie pas sur un autre daemon.** Sous pilote `cgroupfs` -- celui de
Docker Desktop, qui porte les runners de la flotte -- la meme chaine n'est plus un nom de
slice mais un **chemin litteral** : docker **cree** `/sys/fs/cgroup/coursia-ci.slice`
**a plat**, a la racine de l'arbre, **sans aucun plafond**. Ce cgroup porte le meme nom de
feuille que le vrai mur, un niveau au-dessus : un conteneur qui y atterrit fait monter son
`memory.peak`, et le leurre **a l'air cable** tout en ne bornant rien. La valeur correcte
pour un daemon `cgroupfs` est le **chemin imbrique complet**,
`"coursia.slice/coursia-ci.slice"`.

Trois surfaces portent ce sujet, chacune avec son role : **ce paragraphe** est la regle
actionnable (ne pas recopier le fichier, et quelle valeur mettre a la place) ; l'en-tete de
`coursia-ci.slice` (bloc `PIEGE DE RECOPIE`) porte le mecanisme et sa conclusion ; la
**mesure chiffree du 2026-09-08** (`memory.peak`, sous-groupes, `max` sur le leurre) vit
dans le corps de #15157, et nulle part ailleurs dans le depot.

Le `daemon.json` du daemon Docker Desktop, lui, **ne vit pas dans ce depot** : ce sont
`~/.docker/daemon.json` et `settings-store.json` de l'hote. Au 2026-10-23, le leurre plat a
ete retire de la machine -- reproductible par `ls -d /sys/fs/cgroup/coursia-ci.slice`,
attendu **absent** ; la presence d'un `cgroup-parent` par defaut sur ce daemon n'est en
revanche **pas confirmee**. Tant qu'elle ne l'est pas, les conteneurs de la flotte entrent
dans le mur par le drapeau explicite que pose `supervise.sh`, et un conteneur lance a la
main y echappe -- `report_slice_membership()` rend cette evasion **visible** (`EVASION`),
il ne la corrige pas.

**Ce que la recopie produirait n'est pas ce qui a ete observe.** Le leurre plat constate le
2026-09-08 existait alors qu'**aucun** `cgroup-parent` par defaut n'etait pose sur Docker
Desktop : il ne peut donc pas venir d'une recopie de ce fichier, mais d'un
`--cgroup-parent` passe a la main ou d'une configuration anterieure. Le piege decrit
ci-dessus est ce qu'une recopie **creerait** ; l'observation de septembre ne l'illustre
pas, elle en montre seulement le resultat possible.

Mesure du 2026-09-07, trois conteneurs ecrivant en parallele sur `/dev/sde` :

| | Debit cumule |
|---|---|
| sans la slice | 5,4 + 5,9 + 5,6 = **16,9 Go/s** |
| sous la slice (`wbps=209715200`) | 77,6 + 72,0 + 71,5 = **221 Mo/s** |

soit 5,4 % au-dessus des 209,7 Mo/s declares, et un facteur **76**. Le plafond par
conteneur a ete verifie separement : 7,4 Go/s ramenes a 21,2 Mo/s sous un cap de
20 Mio/s, a 1 % pres.

### Resserrer un cap : nommer ce qui a ete mesure, et ce qui ne l'a pas ete (#15202)

Le cap de 1536 Mo par slot avait ete juge « ~10x le pic mesure ». Le pic avait
ete pris sur des jobs ordinaires : le rendu Quarto du site, qui n'en faisait pas
partie, a fini en OOM (`exit 137`) a 1145 carnets sur 1276, et `main` est reste
rouge du 2026-09-07 au 2026-09-08. Le rendu est sorti du pool auto-heberge
(#15203). Le defaut de methode, lui, demeure : la marge n'etait juste que pour
les jobs mesures.

Toute PR qui **abaisse** une borne de ce repertoire (memoire, CPU, budget, nombre
de slots) porte donc dans son body deux listes :

- les jobs dont le pic a ete **mesure** sous la nouvelle valeur, avec la mesure ;
- les jobs **non mesures** qui tournent sur ce pool, nommes un par un.

La seconde liste ne peut pas etre vide par omission. Si elle contient un job
lourd, la PR dit pourquoi le cap le laisse passer, ou elle le sort du pool
d'abord.

## Ce que la conteneurisation du superviseur ne resoudra PAS

Le superviseur lance ses conteneurs a travers le socket du daemon. Une fois
conteneurise, il reste donc **oncle** de ses workers, jamais leur parent : les
conteneurs naissent dans le cgroup du daemon, pas dans le sien. Mettre le
superviseur dans un cgroup borne ne borne que ce que le superviseur ecrit
lui-meme -- ses journaux.

Ce que la conteneurisation apporte reellement : l'isolation de l'environnement du
superviseur, un `--restart on-failure` qui ne depend pas de systemd, et un cgroup
propre pour ses propres ressources. Ce qu'elle demande en echange : monter
`/var/run/docker-ce.sock` dans le conteneur, ce qui est **equivalent a root sur
l'hote**. Les deux moities de ce constat doivent figurer dans la PR qui la porte.

## Deploiement sur ai-01

**Aucun UAC.** WSL root ne passe pas par l'elevation Windows -- tout ce qui suit
s'execute via `wsl.exe -d Ubuntu -u root --`. Les items qui demandent reellement
une fenetre UAC sont les **taches planifiees Windows**, et elles sont annoncees
separement.

Ordre obligatoire -- les bornes d'abord, le parc ensuite. Redemarrer avant de les
poser ferait repartir la file sous le regime non borne qui a gele la machine.

**Regle de lecture de ce bloc : ce qui LIT est vivant, ce qui ECRIT est
commente.** Les `diff` et les `cat` peuvent se copier-coller tels quels -- ce
sont des mesures. Toutes les lignes qui modifient la machine sont commentees a
dessein, et le restent tant que le dimensionnement CPU n'est pas tranche.

**Pourquoi elles sont commentees -- mesure du 2026-09-08 sur ai-01, pas une
hypothese.** Sous le budget en vigueur (`COURSIA_RUNNER_CPU_BUDGET=8`) et avec
les quatre waiters residents (`4 x 1 = 4` vCPU), la famille `start` telle que ce
drop-in la dimensionne demande `4 x 3 = 12` vCPU : `4 + 12 = 16 > 8`, et
`assert_cpu_budget` **refuse le demarrage**. C'est l'etat de la machine a
l'instant ou ces lignes sont ecrites -- `coursia-runner.service` en `failed`,
et la file d'attente sans aucun runner capable de la servir. Deployer ce bloc
tel quel sur un hote neuf y reproduirait le meme verrou. L'arbitrage de
dimensionnement appartient a la lane qui porte le parc ; il n'est pas rendu ici.

```sh
# 1. Le budget agrege, au daemon et au kernel.
#    Les DEUX fichiers sont deja vivants (mesure du 2026-09-08). Diffe AVANT
#    d'installer : la copie vivante de la slice a ete, une journee durant, plus
#    riche que celle du depot -- un install a l'aveugle aurait retire
#    MemoryHigh / MemoryMax / MemorySwapMax de la machine (cf. correction 6).
#
#    ATTENTION sur daemon.json : sa destination est /etc/docker/daemon.json,
#    c'est-a-dire le daemon docker-ce (pilote systemd), et RIEN d'autre. Recopie
#    sur le daemon Docker Desktop (pilote cgroupfs), son "coursia-ci.slice" cree
#    /sys/fs/cgroup/coursia-ci.slice A PLAT, sans plafond -- cf. « Le nom plat de
#    cgroup-parent ».
diff /etc/docker/daemon.json              persist/daemon.json
diff /etc/systemd/system/coursia-ci.slice persist/coursia-ci.slice

# N'installer QUE si le diff est compris et va dans le bon sens :
# install -m 0644 persist/daemon.json          /etc/docker/daemon.json
# install -m 0644 persist/coursia-ci.slice     /etc/systemd/system/coursia-ci.slice

# 2. L'unite corrigee, son wrapper, ET son drop-in -- les trois ensemble.
#    Le drop-in est ce qui porte le dimensionnement : installer l'unite sans lui
#    laisse la famille sur les defauts de supervise.sh (cpus=3, memory=4g), qui
#    ne sont PAS ce que ce depot decrit. La commande omettait le drop-in tandis
#    que la prose disait le contraire ; sur un hote neuf, l'ecart etait muet.
# install -m 0644 persist/ai-01/coursia-runner.service   /etc/systemd/system/coursia-runner.service
# install -m 0755 persist/ai-01/coursia-runner-start.sh  /usr/local/bin/coursia-runner-start.sh
# mkdir -p /etc/systemd/system/coursia-runner.service.d
# install -m 0644 persist/ai-01/coursia-runner.service.d/10-sizing.conf \
#                 /etc/systemd/system/coursia-runner.service.d/10-sizing.conf

# 3. Recharger, puis appliquer.
# systemctl daemon-reload
#
#    Le redemarrage de docker n'est PLUS neutre : docker-ce porte les quatre
#    waiters (mesure du 2026-09-08). `daemon.json` declare `live-restore: true`,
#    qui est fait pour qu'ils survivent -- mais cette survie n'a pas ete
#    verifiee firsthand ici. Tant qu'elle ne l'est pas, cette ligne coupe le
#    seul etage du parc qui fonctionne encore.
# systemctl restart docker.service
# systemctl start coursia-ci.slice

# 4. Verifier que la borne est REELLE avant de rallumer quoi que ce soit.
cat /sys/fs/cgroup/coursia.slice/coursia-ci.slice/io.max
cat /sys/fs/cgroup/coursia.slice/coursia-ci.slice/cpu.max
./scripts/ci/docker/linux-runner/supervise.sh status
```

Le chemin kernel porte **deux** niveaux (`coursia.slice/coursia-ci.slice`) parce
que systemd imbrique automatiquement une slice sous le prefixe de son nom. Chercher
`coursia-ci.slice` a la racine du cgroup ne rend rien, et se lit a tort comme une
slice absente.

Le `restart docker.service` ne vise que **docker-ce** (`unix:///var/run/docker-ce.sock`,
`Name=MyIA-AI-01`). Le socket par defaut est celui du proxy Docker Desktop, qui
porte le reste du parc : il n'est pas touche.

**Ce paragraphe disait autre chose, et c'etait faux au moment de le lire.** Il
affirmait que docker-ce portait **0 conteneur**, donc que le redemarrage etait
sans effet. C'etait vrai le 2026-09-07 ; ca ne l'est plus. Mesure du 2026-09-08 :
docker-ce porte **quatre** conteneurs, `myia-ai-01-linux-waiter-{1..4}`, et rien
d'autre. Le redemarrage n'est donc plus neutre. `daemon.json` declare
`live-restore: true`, qui est fait exactement pour que les conteneurs survivent
a l'arret du daemon -- mais cette survie n'a **pas** ete verifiee firsthand ici,
et l'annoncer comme acquise referait la faute que cette correction repare.
Mesurer d'abord :

```sh
DOCKER_HOST=unix:///var/run/docker-ce.sock docker ps
```

`supervise.sh status` est le controle qui compte : il enumere les familles actives,
lit la slice, et **refuse** de rendre un vert si le budget est exige et absent
(`COURSIA_RUNNER_REQUIRE_CGROUP_BUDGET=1`, arme par le wrapper d'ai-01).

## Le pool d'attente PR-gate (ai-01) -- persistance et inscriptions mortes

**Ce qui etait mesure le 2026-10-28.** La jambe d'attente PR-gate (label
`coursia-waiter`) tournait sur une unite **transitoire**,
`coursia-waiters-b.service`, creee via l'API systemd le 2026-10-27 21:58:58
CET. Une unite transitoire vit sous `/run/systemd/transient/` : elle
**disparait au reboot**, et avec elle le seul fournisseur du label sur ai-01.
Le depot, lui, portait depuis le 2026-10-15 un bandeau **DEPRECATED** qui
affirmait que le label n'avait plus aucun consommateur depuis #17436, et
ordonnait de ne pas redeployer sans le verifier.

**Le consommateur existe.** Mesure sur `origin/main` :
`.github/workflows/pr-gate.yml` l.172 route la jambe same-repo vers
`fromJSON('["self-hosted","coursia-waiter"]')` -- restaure par #21063
(2026-10-16), sonde d'extinction ajoutee par #22183. La verification que le
bandeau exigeait a donc ete faite, et elle est positive.

**Ce qui a ete depose.** `ai-01/coursia-waiters.service` (unite PERSISTANTE) et
`ai-01/coursia-waiters.service.d/10-sizing.conf` (dimensionnement), poses sur
la machine le 2026-10-28 et **identiques octet pour octet** a ces copies. Les
parametres sont ceux de l'unite transitoire, releves a l'identique : meme
`ExecStart` (10 slots), meme state dir (`/var/lib/coursia-waiters-b`), meme
prefixe de noms (`myia-ai-01-wsl-waiterb`), meme budget memoire. Le passage a
la persistance ne change aucun comportement.

**Le `--now` a ete volontairement omis.** L'unite a ete `enable` sans etre
demarree : le pool transitoire portait les jobs en vol, et la bascule se fait au
prochain reboot, sans interruption. Les deux ne peuvent pas cohabiter (famille B
d'un cote, transitoire de l'autre) : le transitoire disparait au reboot.

**Le budget CPU des waiters est desormais arme.** La famille ne declarait
aucun `COURSIA_RUNNER_CPU_BUDGET` : `assert_cpu_budget` sort immediatement
quand le budget vaut 0, donc le garde etait **inactif** pour elle -- un slot de
plus serait passe sans jamais etre refuse. Le drop-in declare 10 vCPU, cale
sur la demande mesuree (10 slots x 1 vCPU).

**Ce que la mesure revele au passage.** L'instrument de dimensionnement
(`ai-01/dryrun-sizing-control.sh`) ne pouvait plus produire de verdict : il
refusait de sous-compter les waiters plutot que de rendre un verdict permissif,
faute d'une unite a lire. L'unite deposee lui rend cette capacite, et le verdict
sorti est : `start 14 x 2 = 28` + `waiters 10 x 1 = 10` = **38 vCPU contre un
budget declare de 32**. Cette composition est anterieure a ce depot -- c'est
celle qui tournait deja. Le noyau, lui, ne borne pas : la slice plafonne a 32
coeurs sur une machine de 32 vCPU, et `cpu.stat` compte 7 evenements de
throttling pour 2,4 s cumulees sur 22 h d'uptime. Les caps DECLARES ne sont
donc pas satures simultanement. L'arbitrage du budget (elever la declaration,
ou redimensionner une famille) appartient a la lane qui porte le parc.

**Les inscriptions mortes ont ete retirees.** Recensement du 2026-10-28 :
39 runners, dont **8 hors ligne et non reproductibles** sur ce siege --
`myia-ai-01-linux-waiter-{4,5}` (prefixe par defaut de `supervise.sh`,
atteignable seulement si une unite appelle le wrapper SANS
`COURSIA_RUNNER_WAITER_NAME_PREFIX`) et `myia-ai-01-wsl-waiter-{1..6}` (prefixe
d'une unite qui n'existe plus). Aucune unite vivante ni aucun fichier d'unite
de ce siege ne declare ces prefixes. Les 8 ont ete supprimees via l'API
`DELETE /repos/jsboige/CoursIA/actions/runners/{id}` ; les 21 runners ai-01
vivants sont restes en ligne. Les inscriptions hors ligne d'autres sieges
(`po-2024-linux-persist-*`, `po-2027-linux-docker-4`) n'ont pas ete touchees :
elles ne sont pas les notres, et les `persistent` doivent revenir avec leur
hote.

```sh
# Le prefixe vivant -- ne declare QUE la famille B :
systemctl show coursia-waiters.service -p Environment --value
```

## Rotation des journaux

Les journaux du superviseur ne tournaient pas : `/var/lib/coursia-runner` pesait
**14 Mo** et `/var/lib/coursia-waiters` 280 Ko, sans rotation d'aucune sorte.

`supervise.sh` porte desormais `COURSIA_RUNNER_LOG_MAX_BYTES`, et c'est **la seule
des nouvelles valeurs qui n'est pas inerte par defaut** : elle vaut **32 Mio**, donc
la rotation s'active partout, po-2024 comprise, des le `git pull`. Les autres bornes
sont vides ou a 0 tant qu'une machine ne les declare pas -- une machine ne se voit
jamais imposer un plafond de ressources qu'elle n'a pas demande. La rotation est
d'une autre nature : elle ne refuse rien, ne ralentit rien, et son absence est ce
qui a laisse un journal grossir sans borne. La laisser inerte aurait demande a
chaque machine de reclamer explicitement de ne pas remplir son disque.

Les journaux des **conteneurs** sont bornes ailleurs, par `daemon.json`
(`log-driver: local`, 10 Mo x 3). Deux mecanismes distincts, ecrits a deux endroits
differents, qui remplissaient chacun le meme disque.

## Maintenance du cache `_work` (#15105)

`actions/checkout` pose `gc.auto = 0` dans le depot du slot : correct pour un
workspace jetable, faux depuis que #14285 rend ce workspace persistant. Chaque
job depose un pack promisor de plus (slot 1 : **264 packs** au diagnostic,
compte croissant sans plafond), et un arret brutal laisse des refs de ZERO
octet qui transforment le gate en loterie -- le slot 7 en portait 1471.

Deux passes vivent dans l'entrypoint du conteneur (avant l'enregistrement du
runner : aucun job en vol ne les paie, et elles tournent sous les bornes d'I/O
du conteneur lui-meme) :

- **Integrite, inconditionnelle** : refs cassees detectees sur le canal stderr
  de `for-each-ref` (rc=0 -- seul le warning nomme la ref), reparees par
  retrait des fichiers vides de `.git/refs` et `.git/logs` UNIQUEMENT (un
  marqueur `.promisor` vide est legitime et vit sous `.git/objects` :
  hors perimetre par construction), et purge du clone si le depot reste muet.
- **Repack, seuille** : `COURSIA_RUNNER_CACHE_PACK_THRESHOLD` (defaut **16**,
  0 = desactive) descend au conteneur ; au-dela, `git repack -ad` consolide
  avec la mesure avant/apres au journal. Non inerte au meme titre que
  `COURSIA_RUNNER_LOG_MAX_BYTES` : son absence est une croissance de disque
  sans borne, pas un plafond qu'une machine n'a pas demande. Sur un clone
  partiel `blob:none`, le repack est sur (mesure sur fixture au filtre
  reellement honore : 5 packs promisor -> 1, marqueur preserve, lazy-fetch et
  fetch incremental intacts).

La garde de fraicheur #14801 lit desormais **deux** scripts embarques
(`entrypoint.sh` ET `work_cache_health.sh` qu'il source) : un correctif merge
mais non rebuild sur l'un ou l'autre est refuse au demarrage du pool.

## Voir aussi

- [`../supervise.sh`](../supervise.sh) -- le superviseur, ses trois pools et ses bornes
- [`../test_supervise_guards.sh`](../test_supervise_guards.sh) -- 20 tests, chaque garde avec son controle negatif
- [`../test_work_cache_health.sh`](../test_work_cache_health.sh) -- sante du cache `_work` sur fixtures git reelles (#15105)
- [`../../../../../docs/ci/self-hosted-runners.md`](../../../../../docs/ci/self-hosted-runners.md) -- vue d'ensemble du parc
- **#15091** -- revision du design du superviseur (traffic disque, isolation)
- **#14385** -- volumes `_work` par slot -- les waiters n'en montent pas, le test 17 le garde
- **#14801** -- fraicheur de l'image, verifiee par empreinte de l'entrypoint
- **#15105** -- integrite et maintenance du cache `_work` persistant

### 4. La copie 8-slots est marquee « a deployer » -- et la deployer seule rallume la panne

Etabli firsthand sur ai-01 le 2026-09-08 (`wsl.exe -d Ubuntu`).

`ai-01/coursia-runner.service` declare `ExecStart=... 8` et **aucun**
`COURSIA_RUNNER_MEMORY`. Or `supervise.sh` l.82 lit
`MEMORY="${COURSIA_RUNNER_MEMORY:-4g}"`. Huit slots sans cap, c'est donc
**8 x 4096 = 32768 Mo** nominal demandes contre un budget de slice de
**12288 Mo** : le garde de budget refuse, `Restart=always` reboucle toutes les
30 s, et le pool ne monte jamais.

Ce que la machine execute reellement n'est pas ce fichier seul, mais ce fichier
**plus un drop-in** qui le corrige :

| | slots | cap par slot | nominal | budget |
|---|---:|---:|---:|---:|
| `coursia-runner.service` seul | 8 | *(defaut 4g)* | 32768 Mo | 12288 Mo -- **refuse** |
| avec `10-sizing.conf` | 4 | 1536 Mo | 6144 Mo | 12288 Mo -- passe |

Le drop-in etait **untracked** jusqu'a #15091 : il vivait sur la machine et
nulle part ailleurs. La table ci-dessus marquait la copie 8-slots « a
deployer » sans mentionner qu'un deuxieme fichier etait indispensable a cote --
un deploiement fidele a la consigne reproduisait donc la panne a l'identique.

C'est la panne qui a impose quatre redemarrages manuels de la machine dans la
meme journee, chacun par une intervention sur site. Les deux fichiers partent
desormais ensemble, ou aucun.

Mesure du fichier vivant au moment de la copie : 762 octets, unite `active`,
`NRestarts=0`, `ExecMainStatus=0`. La strophe operante du fichier tracke est
**byte-identique** au fichier vivant ; seul un en-tete de provenance a ete
ajoute au-dessus, conformement a la convention des autres copies de ce
repertoire.

### 5. Le drop-in borne la memoire et laisse le CPU au defaut -- meme defaut, autre axe

Etabli firsthand sur ai-01 le 2026-09-08 a 14:49Z, **apres** la redaction de la
correction 4 -- et il la contredit en partie. La correction 4 dit que le
drop-in « tient la machine debout ». Mesure du moment :

```
$ systemctl show coursia-runner -p ActiveState -p NRestarts -p Result
ActiveState=failed
NRestarts=4
Result=exit-code
```

Le drop-in etait charge (`DropInPaths=/etc/systemd/system/coursia-runner.service.d/10-sizing.conf`),
`COURSIA_RUNNER_MEMORY=1536m` bien en vigueur, et le service en echec depuis
14:23:40Z. Le journal donne la cause, quatre fois de suite, puis
`Start request repeated too quickly` :

```
ERREUR: budget CPU inter-familles depasse : 16.00 vCPU demandes pour un plafond de 8.
  deja actif : waiters n=4 cpus=1 -> 4.00
  demande    : start n=4 cpus=3 -> 12.00
```

Ce n'est pas la memoire. C'est **le meme defaut que la correction 4, sur l'axe
que la correction 4 ne regarde pas** :

| axe | ce que le drop-in pose | ce que `supervise.sh` applique | resultat |
|---|---|---|---|
| memoire | `COURSIA_RUNNER_MEMORY=1536m` | la valeur posee | 4 x 1536 = 6144 Mo / 12288 -- passe |
| **CPU** | **rien** | **`CPUS="${COURSIA_RUNNER_CPUS:-3}"` (l.81), le defaut** | **4 x 3 = 12, +4 waiters = 16 / 8 -- refuse** |

Le budget CPU vaut 8 (`COURSIA_RUNNER_CPU_BUDGET:-8`, l.101 du wrapper
`coursia-runner-start.sh`) : une clause d'egard pour l'hote, qui reserve 8 des
32 vCPU de la machine a la CI. Elle est **anterieure** a ce travail -- ligne
identique sur `origin/main`, ni introduite ni modifiee par #15188.

**Pourquoi la correction 4 a pu mesurer `active NRestarts=0` le matin et ce
tableau `failed NRestarts=4` l'apres-midi.** J'ai d'abord attribue l'ecart a un
ordre de demarrage entre familles. C'etait une hypothese, et le journal la
refute. Chronologie mesuree (`journalctl -u coursia-runner --since`, heures
locales CEST = UTC+2) :

| heure | evenement |
|---|---|
| 08:33:52, 08:34:43, 09:29:41 | `demarrage de 4 slot(s) ; caps : cpus=3 memory=1536m` -- **succes**, et **aucune** ligne de budget CPU |
| **09:47:21** | **mtime de `/usr/local/bin/coursia-runner-start.sh`** -- le wrapper portant `COURSIA_RUNNER_CPU_BUDGET:-8` est ecrit sur la machine |
| 16:11:53 | premier `ERREUR: budget CPU inter-familles depasse : 16.00 / 8` |
| 16:24:11 | `Start request repeated too quickly` -> `failed` |

L'ordre de boot est d'ailleurs refute une seconde fois, par arithmetique seule :
la famille `start` demande **4 x 3 = 12 vCPU a elle seule**, contre un plafond de
8. Elle echoue meme en partant **la premiere, avec zero waiter actif**. Aucun
ordre de demarrage ne la fait passer -- c'est ce qui rend l'hypothese non pas
seulement non prouvee, mais fausse. (Le journal du 2026-09-08 a 16:11:53 montre
la sequence complete : les waiters obtiennent leurs 4 vCPU, la famille `start`
demande les 12 restants, total 16, refus.)

Le mecanisme n'est donc pas l'ordre de boot, c'est **l'armement d'un garde
au-dessus d'une sur-souscription pre-existante**. `assert_cpu_budget()` sort
immediatement quand le budget vaut 0 (l.422, `[ "${CPU_BUDGET:-0}" = "0" ] &&
return 0`) et n'imprime alors **rien**. Avant 09:47 le garde n'existait pas sur
la machine : les 16 vCPU etaient **declares et acceptes** sans un mot. La ligne
de succes du garde (l.444, `budget CPU inter-familles : N / M vCPU`) est
**absente de tout le journal disponible** (depuis le 2026-09-02) -- la famille
`start` n'a jamais franchi ce garde une seule fois.

**Ce que « sans un mot » ne veut PAS dire -- et je l'avais d'abord ecrit trop
fort.** Declaration n'est pas consommation, et il y a **deux** bornes, pas une :
la table « Les quatre bornes » ci-dessus le dit deja de `COURSIA_RUNNER_CPU_BUDGET`
-- « c'est un refus de demarrage, pas un plafond kernel ». Le plafond kernel,
lui, c'est `coursia-ci.slice` (`CPUQuota=800%`, soit `cpu.max 800000 100000`),
et il etait **arme et actif tout du long** : mesure du 2026-09-08, la slice
existe, ses controleurs sont poses, et le pid d'un waiter s'y trouve bien. La
machine porte par ailleurs `nproc = 32` : **8 est le budget consenti a la CI,
pas la taille du processeur**.

Autrement dit, la famille aurait **demande** 16 vCPU et le noyau lui en aurait
**servi 8**, avec throttling. Retirer le garde a supprime le **refus lisible**,
pas le plafond. La sur-souscription reste un vrai defaut -- elle etrangle en
silence au lieu de refuser franchement -- mais elle n'a jamais laissee la CI
consommer 16 vCPU, et l'ecrire ainsi surevaluait la gravite.

Deux consequences qu'il faut ecrire clairement :

1. **La sur-souscription CPU est anterieure a la panne et elle est de moi.**
   4 slots x 3 vCPU + 4 waiters = **16 vCPU declares** depuis le matin (le
   noyau en servait 8 : cf. l'encadre ci-dessus). Ce n'est pas le garde qui a
   casse le parc, c'est le garde qui a rendu visible ce que le drop-in
   demandait deja.
2. **Le garde lui-meme vient de #15103**, la PR precedente de ce meme chantier
   (`COURSIA_RUNNER_CPU_BUDGET` n'apparait dans le depot qu'au commit
   `93c05cf10`). Les deux moities du defaut sont donc dans mon propre travail :
   une PR a pose la sur-souscription, la suivante a arme le declencheur
   au-dessus, et aucune des deux n'a confronte les deux chiffres.

**Ce que ce README ne tranche pas.** Budget 8 moins 4 de waiters laisse 4 vCPU.
Trois configurations passent le garde (`>` strict, donc 8 est admis) :

| slots | `COURSIA_RUNNER_CPUS` | famille `start` | total avec waiters |
|---:|---:|---:|---:|
| 4 | 1 | 4 | 8 -- passe |
| 2 | 2 | 4 | 8 -- passe |
| 1 | 3 *(defaut)* | 3 | 7 -- passe |

Le choix demande une mesure, pas une extrapolation : un job reel a ete mesure a
**129 % CPU**, donc `cpus=1` l'etranglerait -- exactement la « perte » que le
mandat user demande d'eviter. Et les extrapolations de ce parc ont deja eu tort
une fois : le cap de 1536 Mo, juge « ~10x le pic mesure », a fait OOM un rendu
Quarto. Le dimensionnement CPU est donc laisse **ouvert et nomme**, pas devine
ici.

**Portee de cette correction** : elle ne change aucun dimensionnement et ne
touche pas au fichier vivant. Elle retire une affirmation fausse -- « le
drop-in tient la machine debout » -- et la remplace par ce qui est mesure : le
drop-in ferme la porte memoire, la porte CPU est restee ouverte, et le pool est
tombe par la.

### 6. Le depot allait ecraser la borne memoire de la machine

C'est la correction la plus grave de la liste, et elle ne porte pas sur une PR
anterieure : elle porte sur **ce fichier-ci**, tel qu'il etait redige il y a une
heure.

Les deux premieres lignes de la table de correspondance disaient que
`coursia-ci.slice` et `daemon.json` restaient **a deployer** -- la slice vivante
y etait decrite comme « une version ad-hoc de 283 octets, sans documentation »,
et `daemon.json` comme un fichier qui « n'existe pas encore ». Mesure firsthand
du 2026-09-08 :

| Fichier vivant | Octets | Etat reel |
|---|---:|---|
| `/etc/docker/daemon.json` | 155 | present, **byte-identique** a `persist/daemon.json` |
| `/etc/systemd/system/coursia-ci.slice` | 7235 | present, documente, **plus riche** que la copie du depot |

La copie du depot faisait **4057 octets** et ne portait qu'un
`MemoryAccounting=yes` -- l'axe memoire declare, mais aucune borne. La copie
vivante porte la borne elle-meme :

```
MemoryAccounting=yes
MemoryHigh=12G
MemoryMax=16G
MemorySwapMax=16G
```

**Ce que l'erreur aurait produit.** L'etape 1 du bloc de deploiement ci-dessus
disait `install -m 0644 persist/coursia-ci.slice /etc/systemd/system/coursia-ci.slice`,
sans condition. Executee telle quelle, elle aurait remplace la copie vivante par
celle du depot, donc **retire les trois directives memoire** de la machine. Un
document ecrit pour poser des bornes aurait ete l'instrument qui les enleve --
et la panne qu'il documente est precisement une panne memoire.

**Ce qui a ete fait.** `persist/coursia-ci.slice` a ete synchronise **depuis le
vivant** : le depot en etait un sous-ensemble strict (`git diff --numstat` rend
`56 0` -- cinquante-six lignes ajoutees, zero retiree). L'etape 1 du bloc de
deploiement est passee d'un `install` inconditionnel a un `diff` prealable, et
toutes ses lignes mutantes sont desormais commentees. Restent **deux ecarts
assumes**, tous deux dans des commentaires, tous deux cote depot :

1. **une ligne neutralisee** parce qu'elle nommait une personne privee ; le fait
   technique qu'elle portait -- quatre redemarrages manuels sur site dans la
   meme journee -- est conserve ;
2. **une qualification ajoutee** au bloc « POURQUOI 12 / 16 ET PAS PLUS ». La
   copie vivante presente les ~81 Go d'ecart hote (flotte CI armee vs desarmee)
   comme « l'empreinte de cette slice ». C'est un avant/apres a deux cellules,
   sans controle sur les ~48 autres conteneurs ni sur la workstation : il rend
   un **majorant observe**, pas une empreinte causale mesuree. La copie du depot
   le dit ; la copie vivante, elle, ne l'a pas encore -- l'ecrire ici est la
   seule chose que cette PR peut faire sans toucher la machine.

Ces deux ecarts vont dans le sens depot -> vivant : c'est au prochain `install`
delibere de les propager, jamais a un `install` a l'aveugle.

**La lecon.** « Le depot est la reference » est une **convention**, pas une
mesure. Ce fichier s'ouvre en appelant ses fichiers des *copies de reference* de
fichiers vivants, ce qui laisse entendre que la copie fait autorite. Elle ne la
fait pas : la derive va dans les deux sens, et c'est le fichier vivant qui tient
la machine debout pendant que la copie dort dans le depot. Avant tout `install`
vers un chemin vivant, la regle est donc : **`diff` d'abord, et lire le diff**.

## Le budget CPU : 32 -> 40 vCPU, et le temoin qui le surveille (2026-10-28)

**L'arbitrage** `ai01-c2721-23037-budget` (coordinateur `myia-ai-01:CoursIA`) :
porter la declaration de budget CPU de **32 a 40 vCPU**, sans couper aucune
famille, a deux conditions -- (1) ecrire ici la mesure qui fonde la decision,
(2) ajouter un **temoin de throttling** dans `ai-01/dryrun-sizing-control.sh`.
Point 3 de l'arbitrage : epingler une copie du wrapper **hors arbre de travail**
(`/usr/local/bin`), dans la meme PR.

### La mesure

Relevee sur ai-01 (WSL Ubuntu) le 2026-10-28 ~02:40Z :

| quoi | valeur | ou |
|---|---|---|
| demande DECLAREE | `start 14 x 2 = 28` + `waiters 10 x 1 = 10` = **38 vCPU** | `COURSIA_RUNNER_CPU_BUDGET` du drop-in `40-scale-14.conf` (32) et du drop-in waiters (10) |
| slice | `cpu.max = 3200000 100000` -> **32 coeurs** ; hote `nproc = 32` | `/sys/fs/cgroup/coursia.slice/coursia-ci.slice/cpu.max` |
| noyau | `nr_throttled 7`, `throttled_usec 2 417 700` (**2,42 s** cumulees) | `cpu.stat` de la slice |
| slots individuels | un conteneur a **3 688 evenements / 856 s** de throttling | `cpu.stat` des `docker-*.scope` de la slice |

Lecture : la contrainte qui mordait etait le **cap par slot**, pas le plafond
agrege. Le plafond agrege n'a pas mordu -- 2,42 s en ~25 h. C'est ce qui rend
tenable une declaration de 38 vCPU sur une slice de 32 coeurs : une declaration
de caps n'est pas une reservation de CPU.

**Une limite de la ligne « slots individuels »** : le compteur d'un conteneur
est RECREE quand le slot est recycle (le superviseur remplace le conteneur a
chaque job). Le conteneur qui portait les 856 s a ete remplace dans la
demi-heure qui a suivi la releve -- le temoin 4bis, rejoue apres, ne voyait
plus que 1,51 s au maximum. Le temoin **durable** est celui de la slice, dont
le cgroup n'est pas recree ; le par-slot sert a SITUER la contrainte, pas a la
mesurer dans la duree.

### Ce que la declaration change, et ce qu'elle ne change pas

- Elle **ne donne pas un CPU de plus** a la machine : la slice plafonne a 32
  coeurs, l'hote en a 32.
- Elle **ne change pas l'arithmetique du garde vivant** : depuis #15574
  (arbitrage du 2026-10-01), la famille `waiters` est **exclue** de la somme --
  un waiter est oisif la quasi-totalite du temps, son cap `--cpus` est un
  PLAFOND, pas une reservation. La somme du garde reste 28 vCPU, contre un
  plafond qui passe de 32 a 40 : toujours franchi.
- Elle change une chose de **verifiable** : l'**instrument** de dimensionnement,
  qui compte les waiters, rendait un `REFUSE` permanent (38 > 32) sur une
  composition qui tourne depuis deux semaines et que le noyau dessert sans
  peine. Le verdict permanent etait un fait de l'instrument, pas un etat de la
  machine.

### Le temoin (section 4bis de `ai-01/dryrun-sizing-control.sh`)

Le seul instrument qui dise si une declaration de budget est realiste est le
**throttling mesure** : `nr_throttled` et `throttled_usec` de la slice. Le
temoin lit ces deux compteurs et alerte au-dela de **60 s cumulees par 24 h**
(seuil de l'arbitrage, surchargeable par `COURSIA_DRYRUN_THROTTLE_BUDGET_SPD`).

La **fenetre** est le point delicat : l'age de la slice n'est pas lisible
(cgroup v2 n'expose aucune date de creation ; et sur cette machine
`/proc/uptime` et `journalctl --list-boots` ne concordent pas -- ecart de 22 min
mesure le 2026-10-28, a cause des « Clock change detected » du WSL). Deux bornes
sont donc employees :

- `W_LO = nr_periods x periode` -- duree pendant laquelle la slice a ete
  **comptee**. Une slice ne peut etre comptee que dans des periodes ecoulees,
  donc `W_LO <= age reel` : borne **inferieure** ;
- `W_HI = uptime de l'hote` -- la slice est nee apres le boot, donc
  `age reel <= W_HI` : borne **superieure**.

Ce que cela autorise, et ce que cela n'autorise pas :

- `passe` exige `T <= allocation(W_LO)`. L'age reel etant `>= W_LO`, son
  allocation est `>=` : le PASS est **sound**.
- `ALERTE CERTAINE` : `T > allocation(W_HI)` -- meme la borne la plus generouse
  est depassee, l'alerte est etablie.
- Entre les deux, l'alerte est **incertaine**, et le dit : une alerte qui
  pretend etre certaine quand elle ne l'est pas reproduirait exactement le
  defaut que ce script combat depuis son premier jour.

Trois etats, jamais confondus : `passe` ; `ALERTE CERTAINE` / `ALERTE
INCERTAINE` (sortie **3**, distincte de la sortie 1 qui est le `REFUS` du
garde -- ici c'est la **mesure** du noyau qui parle, pas le garde) ; et
`INDETERMINE` / `INDISPONIBLE` quand l'instrument manque. Un `cpu.stat` absent
ou un `nr_periods` illisible ne rendent **ni** « passe » **ni** alerte : une
panne d'instrument ne se confond pas avec une absence de throttling.

Les sept cas du temoin sont exerces dans `ai-01/test-dryrun-sizing-control.sh`
(section L) : cumul faible, depassement de la borne superieure, depassement
entre les deux bornes, seuil abaisse (controle negatif du seuil reellement
lu), `cpu.stat` absent, `nr_periods` illisible.

### Le pin du wrapper

`ai-01/coursia-waiters.service` appelle desormais
`/usr/local/bin/coursia-waiters-start.sh` au lieu du wrapper du **clone de
travail partage** (`/mnt/d/CoursIA/scripts/ci/docker/linux-runner/persist/coursia-waiters-start.sh`).
Un checkout de branche dans `D:\CoursIA` ne change plus le code du pool a son
prochain redemarrage, et des sessions concurrentes ne partagent plus un arbre
dont le contenu n'etait pas identifie.

**Ce que le pin ne couvre pas**, a lire avant de le prendre pour un correctif
complet : le wrapper est un lanceur mince. Il fait `cd $REPO_DIR` puis `exec
$SUPERVISE_SH waiters "$ARG"`. Le code du **superviseur** reste donc lu dans
l'arbre de travail partage. Le pin fixe l'ENTREE du pool ; il ne fige pas le
corps du superviseur. Le chemin du superviseur est devenu explicite et
surchargeable (`COURSIA_SUPERVISE_SH`), pour que l'epinglage complet soit un
geste de configuration et non une modification du wrapper -- mais le geste
lui-meme (epingler `supervise.sh` ET sa fermeture de dependances, image de
runner comprise) n'est pas fait, et n'est pas mesure.

### Reproduire la mesure

```bash
# cote WSL d'ai-01
cat /sys/fs/cgroup/coursia.slice/coursia-ci.slice/cpu.max
grep -E 'nr_throttled|throttled_usec|nr_periods' \
     /sys/fs/cgroup/coursia.slice/coursia-ci.slice/cpu.stat
systemctl show coursia-runner.service -p Environment --value | tr ' ' '\n' | grep CPU_BUDGET
# l'instrument complet (verdict + temoin + bundle de preuve) :
bash /mnt/d/CoursIA/scripts/ci/docker/linux-runner/persist/ai-01/dryrun-sizing-control.sh \
     --slots 14 --cpus 2 --ack-one-slot
```

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
| `coursia-waiters.service` | **ai-01** | `/etc/systemd/system/coursia-waiters.service` | reference |
| `coursia-waiters-start.sh` | **ai-01** | `/usr/local/bin/coursia-waiters-start.sh` | reference |
| `coursia-ci.slice` | **ai-01** | `/etc/systemd/system/coursia-ci.slice` | **a deployer** (une version ad-hoc de 283 octets, sans documentation, occupe la place) |
| `daemon.json` | **ai-01** | `/etc/docker/daemon.json` | **a deployer** (le fichier n'existe pas encore) |
| `ai-01/coursia-runner.service` | **ai-01** | `/etc/systemd/system/coursia-runner.service` | **a deployer** (corrige, cf. correction 3) |
| `ai-01/coursia-runner-start.sh` | **ai-01** | `/usr/local/bin/coursia-runner-start.sh` | **a deployer** (corrige, cf. correction 3) |

Le sous-repertoire `ai-01/` existe parce que les deux machines ont des fichiers
**homonymes et incompatibles**. Les melanger a plat, comme c'etait le cas, revient
a laisser croire qu'il n'y en a qu'un.

## Les trois corrections dues sur #15091 / #15094

Ces trois points ont ete etablis firsthand sur ai-01 le 2026-09-07 (lecture des
fichiers vivants via `wsl.exe -d Ubuntu -u root --`). Ils corrigent des choses que
j'avais annoncees ou laissees entendre, et qui etaient fausses.

### 1. La PR #15094 patche une copie qui ne tourne pas sur ai-01

`persist/coursia-runner.service` et `persist/coursia-runner-start.sh` sont ceux de
**po-2024** : depot sous `/mnt/c/dev/CoursIA`, prefixe `myia-po-2024-linux-docker`,
et un wrapper qui relaie n'importe quelle sous-commande (`exec "$SUPERVISE" "$@"`).

Les fichiers vivants d'ai-01 sont differents sur les trois points qui comptent :
depot sous `/mnt/d/CoursIA`, prefixe `myia-ai-01-wsl`, et un premier argument qui
est le **nombre de slots**, pas une sous-commande. Un correctif porte sur la copie
a plat ne touche donc pas la machine qui a gele. C'est ce que le sous-repertoire
`ai-01/` rend desormais impossible a confondre.

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

## Les trois bornes, et laquelle borne quoi

Elles ne sont pas redondantes : chacune couvre ce que les autres ne peuvent pas
voir.

| Borne | Ou elle vit | Ce qu'elle borne | Ce qu'elle ne peut pas borner |
|---|---|---|---|
| `coursia-ci.slice` | `/etc/systemd/system/` + `cgroup-parent` du daemon | la **somme** de tous les conteneurs : `CPUQuota=800%`, `IOWriteBandwidthMax` | rien en dessous : elle ne distingue pas un slot glouton d'une famille entiere |
| `--device-write-bps` / `--device-read-bps` | drapeaux passes par `supervise.sh` a chaque `docker run` | **un** conteneur | la somme : 12 conteneurs conformes un a un saturent quand meme le disque |
| `COURSIA_RUNNER_CPU_BUDGET` | verification dans `supervise.sh` au demarrage | la **somme des demandes** de vCPU entre familles, **avant** de lancer quoi que ce soit | l'usage reel : c'est un refus de demarrage, pas un plafond kernel |

Le budget agrege est **applique par defaut du daemon** (`cgroup-parent` dans
`daemon.json`), pas par un drapeau du superviseur -- et le superviseur le
**verifie** plutot que de le re-imposer. La distinction n'est pas cosmetique :
passer `--cgroup-parent` sur une machine ou la slice n'existe pas **cree** un
cgroup vide, qui a l'apparence exacte d'un garde et ne borne rien.

Mesure du 2026-09-07, trois conteneurs ecrivant en parallele sur `/dev/sde` :

| | Debit cumule |
|---|---|
| sans la slice | 5,4 + 5,9 + 5,6 = **16,9 Go/s** |
| sous la slice (`wbps=209715200`) | 77,6 + 72,0 + 71,5 = **221 Mo/s** |

soit 5,4 % au-dessus des 209,7 Mo/s declares, et un facteur **76**. Le plafond par
conteneur a ete verifie separement : 7,4 Go/s ramenes a 21,2 Mo/s sous un cap de
20 Mio/s, a 1 % pres.

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

```sh
# 1. Le budget agrege, au daemon et au kernel.
install -m 0644 persist/daemon.json          /etc/docker/daemon.json
install -m 0644 persist/coursia-ci.slice     /etc/systemd/system/coursia-ci.slice

# 2. L'unite corrigee et son wrapper.
install -m 0644 persist/ai-01/coursia-runner.service   /etc/systemd/system/coursia-runner.service
install -m 0755 persist/ai-01/coursia-runner-start.sh  /usr/local/bin/coursia-runner-start.sh

# 3. Recharger, puis appliquer.
systemctl daemon-reload
systemctl restart docker.service          # docker-ce : 0 conteneur, redemarrage sans effet sur le parc
systemctl start coursia-ci.slice

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
pid 253, `Name=MyIA-AI-01`), qui portait **0 conteneur** a la mesure. Le socket par
defaut est celui du proxy Docker Desktop (pid 10179), qui portait les 48 conteneurs
du parc : il n'est pas touche.

`supervise.sh status` est le controle qui compte : il enumere les familles actives,
lit la slice, et **refuse** de rendre un vert si le budget est exige et absent
(`COURSIA_RUNNER_REQUIRE_CGROUP_BUDGET=1`, arme par le wrapper d'ai-01).

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

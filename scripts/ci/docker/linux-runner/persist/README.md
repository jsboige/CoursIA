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
| `coursia-waiters.service` | **ai-01** | `/etc/systemd/system/coursia-waiters.service` | reference |
| `coursia-waiters-start.sh` | **ai-01** | `/usr/local/bin/coursia-waiters-start.sh` | reference |
| `coursia-ci.slice` | **ai-01** | `/etc/systemd/system/coursia-ci.slice` | **deploye et vivant** -- 7235 octets, documente, et il etait **en avance sur le depot** : c'est le depot qui a ete synchronise depuis le vivant, pas l'inverse (cf. correction 6) |
| `daemon.json` | **ai-01** | `/etc/docker/daemon.json` | **deploye et vivant** -- 155 octets, **byte-identique** a la copie du depot (`sha256:1ef80038e470...`, mesure le 2026-09-08) |
| `ai-01/coursia-runner.service` | **ai-01** | `/etc/systemd/system/coursia-runner.service` | **a deployer** (corrige, cf. correction 3) -- **jamais seul**, cf. correction 4 |
| `ai-01/coursia-runner.service.d/10-sizing.conf` | **ai-01** | `/etc/systemd/system/coursia-runner.service.d/10-sizing.conf` | **deploye et vivant** -- necessaire mais **pas suffisant** : il borne la memoire et laisse le CPU au defaut (cf. corrections 4 et 5) |
| `ai-01/coursia-runner-start.sh` | **ai-01** | `/usr/local/bin/coursia-runner-start.sh` | **a deployer** (corrige, cf. correction 3) |

Le sous-repertoire `ai-01/` existe parce que les deux machines ont des fichiers
**homonymes et incompatibles**. Les melanger a plat, comme c'etait le cas, revient
a laisser croire qu'il n'y en a qu'un.

## Les six corrections dues sur #15091 / #15094

Les trois premiers ont ete etablis firsthand sur ai-01 le 2026-09-07, les
trois suivants le 2026-09-08 (lecture des fichiers vivants via
`wsl.exe -d Ubuntu -u root --`). Ils corrigent des choses que
j'avais annoncees ou laissees entendre, et qui etaient fausses.

Les corrections **4, 5 et 6** ont ete ajoutees apres coup et se lisent en fin
de fichier, **apres** la section « Voir aussi ».

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
#    Les DEUX fichiers sont deja vivants (mesure du 2026-09-08). Diffe AVANT
#    d'installer : la copie vivante de la slice a ete, une journee durant, plus
#    riche que celle du depot -- un install a l'aveugle aurait retire
#    MemoryHigh / MemoryMax / MemorySwapMax de la machine (cf. correction 6).
diff /etc/docker/daemon.json              persist/daemon.json
diff /etc/systemd/system/coursia-ci.slice persist/coursia-ci.slice

# N'installer QUE si le diff est compris et va dans le bon sens :
# install -m 0644 persist/daemon.json          /etc/docker/daemon.json
# install -m 0644 persist/coursia-ci.slice     /etc/systemd/system/coursia-ci.slice

# 2. L'unite corrigee et son wrapper.
install -m 0644 persist/ai-01/coursia-runner.service   /etc/systemd/system/coursia-runner.service
install -m 0755 persist/ai-01/coursia-runner-start.sh  /usr/local/bin/coursia-runner-start.sh

# 3. Recharger, puis appliquer.
systemctl daemon-reload
systemctl restart docker.service          # docker-ce porte les 4 waiters : ce redemarrage n'est PLUS neutre, cf. ci-dessous
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

## Voir aussi

- [`../supervise.sh`](../supervise.sh) -- le superviseur, ses trois pools et ses bornes
- [`../test_supervise_guards.sh`](../test_supervise_guards.sh) -- 18 tests, chaque garde avec son controle negatif
- [`../../../../../docs/ci/self-hosted-runners.md`](../../../../../docs/ci/self-hosted-runners.md) -- vue d'ensemble du parc
- **#15091** -- revision du design du superviseur (traffic disque, isolation)
- **#14385** -- volumes `_work` par slot -- les waiters n'en montent pas, le test 17 le garde
- **#14801** -- fraicheur de l'image, verifiee par empreinte de l'entrypoint

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
la table « Les trois bornes » ci-dessus le dit deja de `COURSIA_RUNNER_CPU_BUDGET`
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
deploiement est passee d'un `install` inconditionnel a un `diff` prealable. Le
seul ecart restant entre les deux copies est **une ligne de commentaire**,
neutralisee cote depot parce qu'elle nommait une personne privee ; le fait
technique qu'elle portait -- quatre redemarrages manuels sur site dans la meme
journee -- est conserve.

**La lecon.** « Le depot est la reference » est une **convention**, pas une
mesure. Ce fichier s'ouvre en appelant ses fichiers des *copies de reference* de
fichiers vivants, ce qui laisse entendre que la copie fait autorite. Elle ne la
fait pas : la derive va dans les deux sens, et c'est le fichier vivant qui tient
la machine debout pendant que la copie dort dans le depot. Avant tout `install`
vers un chemin vivant, la regle est donc : **`diff` d'abord, et lire le diff**.

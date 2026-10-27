# Débit de requêtes UDP des runners — mesure (#22937 volet 5.1)

> **Organe** : `scripts/ci/check_dns_rate.py`
> **Tests** : `scripts/tests/test_dns_rate.py` (déterministes, sans Docker)
> **Issues** : [#22937](https://github.com/jsboige/CoursIA/issues/22937) volet 5, Maintenance#196
> **Objectif de fermeture** : débit DNS vers `api.github.com` **inférieur à 1 requête par seconde**

## Invocation exacte

Depuis Windows, l'organe tourne **dans la distribution Ubuntu** : c'est la seule voie où le moteur Docker des runners et leur `/proc/net/snmp` sont joignables.

```bash
wsl -d Ubuntu -- python3 /mnt/d/CoursIA/scripts/ci/check_dns_rate.py --window 15
wsl -d Ubuntu -- python3 /mnt/d/CoursIA/scripts/ci/check_dns_rate.py --window 60 --json
wsl -d Ubuntu -- python3 /mnt/d/CoursIA/scripts/ci/check_dns_rate.py --dry-run
```

Depuis un shell déjà dans WSL (ou en CI Linux) :

```bash
./scripts/ci/check_dns_rate.py --window 60
```

Le chemin `/mnt/d/CoursIA` est celui du clone principal sur `ai-01`. Depuis un worktree, utiliser son propre chemin (`/mnt/d/CoursIA-<suffixe>`). Depuis Git Bash (MSYS), passer la commande à `bash -lc` plutôt qu'en argument direct : MSYS réécrit les arguments de forme `/mnt/...` en chemins Windows et le fichier devient introuvable. Aucune dépendance externe : bibliothèque standard uniquement.

## Ce que l'organe mesure

Les runners d'`ai-01` sont des **conteneurs Docker dans WSL2** (14 slots `myia-ai-01-wsl-1..14`, image `coursia-linux-runner:2.338.0`), pas des processus Windows. Chaque conteneur a son propre network namespace, donc son propre `/proc/net/snmp`. L'organe relève la colonne `Udp: ... OutDatagrams` **dans chaque conteneur** (`docker exec <slot> cat /proc/net/snmp`), échantillonne ce compteur à intervalle régulier (1 s par défaut), et somme les deltas.

Deux nombres en sortie, parce qu'une moyenne masque une rafale :

| Champ | Sens |
|---|---|
| `average_qps` | datagrammes cumulés / durée réelle de la fenêtre |
| `burst_qps` | maximum du débit sur une fenêtre **glissante de 5 s** |

La fenêtre glissante retient, pour chaque échantillon, l'intervalle dont la durée est la plus proche de 5 s ; la durée réellement utilisée est publiée (`burst_span_s`). Une rafale n'est évaluée qu'une fois 5 s d'historique accumulées : sur une fenêtre plus courte, `burst_qps` vaut `null` et le verdict ne porte que sur la moyenne — un zéro serait un chiffre fabriqué.

Un compteur qui recule n'est pas un débit négatif : c'est un conteneur recréé (le nom est réutilisé, le compteur repart de 0). Ces événements sont listés dans `resets` avec leur nature (`recycle` quand l'ID du conteneur a changé, `reset` quand seul le compteur a reculé) et l'intervalle concerné ne contribue pas au débit.

## Ce que l'organe NE mesure pas

`Udp.OutDatagrams` compte **tout** l'UDP sortant, pas les seules requêtes DNS. C'est donc un **majorant** du débit DNS, et un **substitut** à la mesure directe des requêtes vers `api.github.com` — jamais cette mesure. Ce que l'organe ne voit pas, et qu'il ne comble pas par un zéro :

- **le DNS côté Windows** : `Get-DnsClientCache` rend 0 entrée alors qu'un enregistrement valide existe (TTL 49 mesuré) et `wslservice` ne porte aucune connexion :443 établie — toute mesure côté Windows est aveugle, et c'est pourquoi l'organe tourne dans WSL ;
- **l'attribution au processus `wslservice`** ;
- **les requêtes vers `api.github.com` elles-mêmes** : on lit un compteur agrégé par network namespace, on n'inspecte pas les paquets ;
- **les jobs déjà terminés** : seuls comptent les conteneurs vivants pendant la fenêtre. Un conteneur recréé repart de zéro.

Le DNS du conteneur passe par le proxy WSL (`nameserver 10.255.255.254`) et l'image ne porte ni `nscd` ni `systemd-resolved` : sans cache DNS applicatif, le débit UDP suit d'assez près le débit de résolution. Un pic UDP d'une autre nature serait compté comme du DNS — c'est le prix de la seule voie qui répond sans root.

## Verdicts et codes de retour

Alignés sur les autres organes du dépôt (`gh_queue_health.py` : 0/1/2).

| Statut | Condition | Code |
|---|---|---|
| `OK` | moyenne < seuil **et** rafale < seuil de rafale | 0 |
| `WARN` | un des deux seuils atteint | 1 |
| `RED` | le rapport au seuil atteint 5x (moyenne ou rafale) | 1 |
| `UNREADABLE` | rien n'a pu être mesuré | 2 |

`UNREADABLE` couvre quatre causes, toutes nommées dans la sortie : socket du moteur absent, `docker ps` en échec, zéro conteneur de runner alors que des slots sont attendus, et aucun compteur lisible. **Un zéro non mesuré n'est jamais un `OK`.**

## Le piège des deux moteurs Docker

`ai-01` porte deux moteurs : le contexte `default` (`/var/run/docker.sock`, Docker Desktop) et le dockerd natif (`unix:///var/run/docker-ce.sock`), qui héberge les runners. Un `docker ps` sur le mauvais moteur rend **zéro** conteneur runner : un organe qui lirait ce zéro comme « 0 requête/s » afficherait un vert total sur une mesure jamais faite. L'organe épingle donc explicitement le socket natif, et en diagnostic seulement, sonde le moteur par défaut pour nommer la mauvaise pince (« 0 ici, 14 là-bas »).

Mesure du 2026-10-27 : `--docker-host unix:///var/run/docker.sock` rend `UNREADABLE` (code 2) et le message nomme les 14 slots attendus ; `--docker-host unix:///var/run/pas-de-socket.sock` rend `UNREADABLE` sur le `docker ps` en échec.

## Protocole de référence (Maintenance#196)

1. `--dry-run` : état du moteur épinglé et liste des slots vus.
2. `--window 60` (défaut) en régime normal ; poster la sortie (ou le JSON) telle quelle avec la mesure.
3. Une fenêtre de moins de 5 s ne prouve rien de la rafale : `burst_qps` sera `null`, et le verdict ne portera que sur la moyenne.
4. Le chiffre à comparer à « 1 requête/s » est `average_qps`, en sachant qu'il **majore** le DNS. `burst_qps` répond à l'autre question : le backoff et le jitter de `supervise.sh` dispersent-ils les rafales (le chiffre « 12 slots → ~48 appels `registration-token`/minute » de son en-tête est de cette famille) ?

## Mesures du 2026-10-27 (référence)

Parc : 14 conteneurs `myia-ai-01-wsl-1..14` sur `unix:///var/run/docker-ce.sock`.

| Fenêtre | Échantillons | Datagrammes | Moyenne | Rafale | Verdict |
|---|---|---|---|---|---|
| 15 s | 16 (pas 1,00 s) | 2 | 0,13 q/s | 0,39 q/s sur 5,07 s | `OK` |
| 6 s | 7 (pas 1,01 s) | 28 | 4,62 q/s | 5,13 q/s sur 5,07 s | `WARN` |
| 15 s | 16 (pas 1,00 s) | 26 | 1,74 q/s | 3,24 q/s sur 4,94 s | `WARN` (1 recyclage du slot 4) |

Les trois mesures sont prises à quelques minutes d'intervalle : le débit n'est pas un état stable, il suit l'activité des jobs. Une mesure unique ne conclut donc rien sur la conformité au seuil — c'est la série dans le temps qui le fera. Mesure fondatrice du volet (rapportée dans #22937, pas reproduite ici) : 11 slots au repos → delta 0 ; 2 slots occupés → ~78 datagrammes en 20 s (~3,9/s).

Un conteneur recréé entre deux fenêtres remet son compteur à zéro : c'est la cause des `resets` signalés, jamais un débit négatif.

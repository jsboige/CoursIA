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
python3 scripts/ci/check_dns_rate.py --window 60
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

Codes alignés sur les autres organes du dépôt (`gh_queue_health.py` : 0/1/2), plus `3` pour la non-applicabilité, qui n'est pas une panne.

| Statut | Condition | Code |
|---|---|---|
| `OK` | moyenne < seuil **et** rafale < seuil de rafale, **sans réserve** | 0 |
| `WARN` | un des deux seuils atteint, **ou** une réserve (couverture, pool) | 1 |
| `RED` | le rapport au seuil atteint 5x (moyenne ou rafale) | 1 |
| `UNREADABLE` | rien n'a pu être mesuré (fenêtre non lue comprise) | 2 |
| `NOT_APPLICABLE` | le parc de runners n'est pas attendu sur cette machine | 3 |
| `WIRED` (`--dry-run` seulement) | le câblage est vu, **aucune** mesure n'a eu lieu | 0 |

`UNREADABLE` couvre quatre causes, toutes nommées dans la sortie : socket du moteur absent (prédicat testé en premier, car un socket absent fait aussi échouer `docker ps`), `docker ps` en échec, zéro conteneur de runner **listé** alors que des slots sont attendus, et des conteneurs listés dont **aucun** compteur n'a pu être lu. Les deux derniers se distinguent par le champ qui les fonde : `found_slots` vient du **listing** (`docker ps`), pas des compteurs lus — les confondre nommait « mauvais moteur Docker » une cause qui était un `docker exec` en échec. **Un zéro non mesuré n'est jamais un `OK`.**

### Deux réserves qui interdisent un `OK`

Elles **s'ajoutent** au calcul des deux seuils et ne peuvent que durcir le verdict (`effective_verdict`), jamais l'adoucir.

| Réserve | Seuil | Effet | Trace |
|---|---|---|---|
| **Couverture** | un slot lu sur **plus de la moitié** des échantillons (seuil strict : 50 % pile passe) | aucun slot au-dessus → `UNREADABLE` ; une partie seulement → verdict au moins `WARN` | `coverage.by_slot`, `coverage.degraded`, champ `reserves` |
| **Pool incomplet** | un slot attendu n'est pas au listing | verdict au moins `WARN` | `slots_expected_missing`, `pool_complete`, champ `reserves` |

Sans la première, un `docker exec` qui répond au premier échantillon puis échoue sur les quinze suivants laissait `MEASURED`, une moyenne de 0,0 q/s et un `OK` à code 0 : une fenêtre non lue rendait un vert parfaitement faux. Sans la seconde, une somme portant sur 2 slots vivants sur 14 était comparée telle quelle à l'objectif de 1 q/s de la flotte entière.

### Quelle machine fait quoi

| Machine | Parc | Comportement |
|---|---|---|
| `ai-01` | 14 slots `myia-ai-01-wsl-1..14` | mesure nominale ; `UNREADABLE` si le parc est absent (c'est une panne réelle) |
| toute autre | aucun parc déclaré | `NOT_APPLICABLE` (code 3) : un parc qui n'existe pas là n'est **pas** une panne |
| toute autre, avec `--name-prefix` **et** `--expected-slots` | déclaré par l'opérateur | mesure nominale, `UNREADABLE` si zéro slot listé |

Les deux défauts (`myia-ai-01-wsl`, 14 slots) sont propres à `ai-01` : ils ne s'appliquent qu'à la machine dont le nom normalisé vaut `myia-ai-01` (le nom vu depuis WSL est `MyIA-AI-01`, normalisé en minuscules). Déclarer un parc (`--name-prefix` ou `--expected-slots`, ou `COURSIA_RUNNER_NAME_PREFIX` / `COURSIA_RUNNER_EXPECTED_SLOTS`) lève la non-applicabilité sur n'importe quelle machine.

## Le piège des deux moteurs Docker

`ai-01` porte deux moteurs : le contexte `default` (`/var/run/docker.sock`, Docker Desktop) et le dockerd natif (`unix:///var/run/docker-ce.sock`), qui héberge les runners. Un `docker ps` sur le mauvais moteur rend **zéro** conteneur runner : un organe qui lirait ce zéro comme « 0 requête/s » afficherait un vert total sur une mesure jamais faite. L'organe épingle donc explicitement le socket natif, et en diagnostic seulement, sonde le moteur par défaut pour nommer la mauvaise pince (« 0 ici, 14 là-bas »).

Mesure du 2026-10-27 : `--docker-host unix:///var/run/docker.sock` rend `UNREADABLE` (code 2) et le message nomme les 14 slots attendus (« 0 conteneur de runner alors que 14 slot(s) sont attendus ») ; `--docker-host unix:///var/run/pas-de-socket.sock` rend `UNREADABLE` (code 2) avec le motif « socket du moteur natif absent » — le socket est testé **avant** l'échec de `docker ps`, sinon la cause nommée serait l'échec de listing au lieu de la cause racine.

## Protocole de référence (Maintenance#196)

1. `--dry-run` : état du moteur épinglé et liste des slots vus. Le statut rendu est `WIRED` — c'est un diagnostic de câblage, il ne dit rien du débit.
2. `--window 60` (défaut) en régime normal.
3. **Toute mesure publiée porte son artefact** : la ligne de commande exacte, l'horodatage UTC (relevé par `date -u` dans la même commande), et la sortie `--json` (au moins un extrait des champs de tête). Un débit sans sa commande n'est pas une mesure, c'est un chiffre nu.
4. Une fenêtre de moins de 5 s ne prouve rien de la rafale : `burst_qps` sera `null`, et le verdict ne portera que sur la moyenne.
5. Le chiffre à comparer à « 1 requête/s » est `average_qps`, en sachant qu'il **majore** le DNS. `burst_qps` répond à l'autre question : le backoff et le jitter de `supervise.sh` dispersent-ils les rafales (le chiffre « 12 slots → ~48 appels `registration-token`/minute » de son en-tête est de cette famille) ?
6. Lire les réserves avant de conclure : un `WARN` peut venir d'une couverture dégradée ou d'un pool incomplet, pas du débit. Les champs `reserves`, `coverage.degraded` et `slots_expected_missing` disent lequel.

## Mesures du 2026-10-27 (artefact)

Parc : 14 conteneurs `myia-ai-01-wsl-1..14` sur `unix:///var/run/docker-ce.sock`. Les mesures ci-dessous ont été **lancées sur `ai-01`**, dans WSL, aux horodatages UTC affichés (relevés par `date -u` dans la même commande que la mesure).

### Commandes exactes

```bash
date -u +%Y-%m-%dT%H:%M:%SZ
python3 /mnt/d/CoursIA-22937c/scripts/ci/check_dns_rate.py --dry-run --json
python3 /mnt/d/CoursIA-22937c/scripts/ci/check_dns_rate.py --window 15 --json
python3 /mnt/d/CoursIA-22937c/scripts/ci/check_dns_rate.py --window 6 --json
```

Le chemin `/mnt/d/CoursIA-22937c` est celui du worktree de la PR ; sur le clone principal, `/mnt/d/CoursIA`.

### Relevés

| Mesure | UTC | Statut | Échantillons | Datagrammes | Moyenne | Rafale | Verdict |
|---|---|---|---|---|---|---|---|
| `--dry-run` | 2026-10-27T13:30:19Z | `WIRED` | — | — | — | — | aucun (14 slots vus, 0 mesuré) |
| 15 s | 2026-10-27T13:30:23Z | `MEASURED` | 16 (pas 0,998 s) | 0 | 0,00 q/s | 0,00 q/s sur 4,99 s | `OK` |
| 6 s | 2026-10-27T13:30:44Z | `MEASURED` | 7 (pas 0,986 s) | 0 | 0,00 q/s | 0,00 q/s sur 4,87 s | `OK` |
| 15 s | 2026-10-27T13:32:28Z | `MEASURED` | 16 (pas 1,010 s) | 0 | 0,00 q/s | 0,00 q/s sur 5,13 s | `WARN` (pool incomplet : `myia-ai-01-wsl-10` absent) |

La dernière ligne est le cas qui justifie la réserve de pool : le slot 10 était en cours de recréation pendant la fenêtre, et il est revenu dans `docker ps` juste après. La somme porte donc sur 13 slots vivants ; l'organe ne rend pas `OK`, il rend `WARN` et nomme le slot manquant. Sans cette réserve, cette fenêtre aurait été un `OK` muet.

### Extrait de la sortie `--json` (fenêtre de 15 s, 2026-10-27T13:32:28Z)

Projection des champs de tête, produite par le filtre ci-dessous appliqué à la sortie de l'organe. Les 13 entrées de `coverage.by_slot` sont toutes à `{"missing": 0, "fraction": 0.0}` (les slots vus ont tous été lus à chaque échantillon) ; `slots` et `slots_seen` listent les 13 noms vus :

```bash
python3 scripts/ci/check_dns_rate.py --window 15 --json | python3 -c "import json,sys; p=json.load(sys.stdin); print(json.dumps({k:p[k] for k in ('status','verdict','average_qps','burst_qps','burst_span_s','window_s','elapsed_s','sample_count','sample_period_s','datagrams_total','expected_slots','slots_expected_missing','pool_complete','reserves','machine')}, indent=2, ensure_ascii=False))"
```

```json
{
  "status": "MEASURED",
  "verdict": "WARN",
  "average_qps": 0.0,
  "burst_qps": 0.0,
  "burst_span_s": 5.129769815499458,
  "window_s": 15.0,
  "elapsed_s": 15.154634643498866,
  "sample_count": 16,
  "sample_period_s": 1.0103089762332578,
  "datagrams_total": 0,
  "expected_slots": 14,
  "slots_expected_missing": [
    "myia-ai-01-wsl-10"
  ],
  "pool_complete": false,
  "reserves": [
    "pool incomplet : 1 slot(s) attendu(s) et non vu(s) sur 14 -- la somme porte sur les 13 slot(s) vivants, pas sur la flotte entiere"
  ],
  "machine": "myia-ai-01"
}
```

Par comparaison, la fenêtre de 15 s de 13:30:23Z porte `"verdict": "OK"`, `"pool_complete": true`, `"slots_expected_missing": []` et `"reserves": []`.

### Série antérieure (rapportée, non reproduite ici)

Trois fenêtres avaient été rapportées à la rédaction du volet : 15 s / 16 échantillons / 2 datagrammes → 0,13 q/s et 0,39 q/s de rafale sur 5,07 s (`OK`) ; 6 s / 7 échantillons / 28 datagrammes → 4,62 q/s et 5,13 q/s sur 5,07 s (`WARN`) ; 15 s / 16 échantillons / 26 datagrammes → 1,74 q/s et 3,24 q/s sur 4,94 s (`WARN`, 1 recyclage du slot 4). Leur sortie machine n'a pas été conservée : elles restent **rapportées**, pas vérifiables, et ne sont donc pas la référence de ce document. Mesure fondatrice du volet (rapportée dans #22937, non reproduite ici non plus) : 11 slots au repos → delta 0 ; 2 slots occupés → ~78 datagrammes en 20 s (~3,9/s).

Le débit n'est pas un état stable : il suit l'activité des jobs, et les fenêtres ci-dessus tombent à 0 datagramme parce que le parc était au repos. Une mesure unique ne conclut donc rien sur la conformité au seuil — c'est la série dans le temps qui le fera, et chaque point doit porter sa commande et son horodatage.

Un conteneur recréé entre deux fenêtres remet son compteur à zéro : c'est la cause des `resets` signalés, jamais un débit négatif. Un conteneur recréé **pendant** une fenêtre peut aussi manquer au listing sur toute la fenêtre, et c'est alors la réserve de pool qui parle.

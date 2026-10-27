#!/usr/bin/env python3
"""Organe de mesure du debit de requetes UDP des conteneurs de runners (#22937, volet 5.1).

CE QUE CE SCRIPT EXISTE POUR MESURER
------------------------------------
L'objectif de fermeture du volet 5 de #22937 (et de Maintenance#196) est un
debit DNS vers `api.github.com` **inferieur a 1 requete par seconde**. Aucun
organe du depot ne mesurait ce debit : ce fichier est le premier, et il commence
par dire ce qu'il mesure VRAIMENT.

Le parc de runners ephemeres d'ai-01 est un ensemble de conteneurs Docker dans
WSL2 (14 slots `myia-ai-01-wsl-1..14`, image `coursia-linux-runner:2.338.0`),
pas des processus Windows. Chacun porte son propre network namespace, donc son
propre `/proc/net/snmp`. On releve la colonne `Udp: ... OutDatagrams` DANS
chaque conteneur, on l'echantillonne periodiquement, et on somme les deltas des
14 slots.

CE QUE CE COMPTEUR EST -- ET CE QU'IL N'EST PAS
-----------------------------------------------
`Udp.OutDatagrams` compte **tout** l'UDP sortant du conteneur, pas les seules
requetes DNS. C'est donc un **MAJORANT** du debit DNS, et un **substitut** a la
mesure directe des requetes vers `api.github.com` -- jamais cette mesure. Un
reseau sain affiche un debit UDP proche du debit DNS (l'agent runner ne fait
que du HTTPS et de la resolution, et le DNS du conteneur passe par le proxy WSL
`nameserver 10.255.255.254`, sans `nscd` ni `systemd-resolved` dans l'image :
pas de cache DNS applicatif). Mais un pic UDP d'une autre nature serait compte
comme du DNS : c'est le prix de la seule voie qui repond sans root, et c'est
ecrit dans la sortie, pas seulement ici.

CE QUE L'ORGANE NE MESURE PAS (dit explicitement, jamais comble par un zero)
---------------------------------------------------------------------------
  - le DNS cote Windows : `Get-DnsClientCache` rend 0 entree alors qu'un
    enregistrement valide existe (TTL 49 mesure) et `wslservice` ne porte
    aucune connexion :443 etipee -- toute mesure cote Windows est AVEUGLE ;
  - l'attribution au processus `wslservice` ;
  - les requetes vers `api.github.com` elles-memes : on ne lit pas les
    paquets, on lit un compteur agregе par network namespace ;
  - les jobs deja termines : seuls comptent les conteneurs vivants pendant la
    fenetre. Un conteneur recree repart de zero.

LE PIEGE DES DEUX MOTEURS DOCKER -- ET POURQUOI LA DEFAITE EST UN ROUGE
----------------------------------------------------------------------
ai-01 porte DEUX moteurs : le contexte `default` (`/var/run/docker.sock`,
Docker Desktop) et le dockerd natif (`unix:///var/run/docker-ce.sock`), qui est
celui des runners. Un `docker ps` naif sur le mauvais moteur rend ZERO conteneur
runner -- et un organe qui lirait ce zero comme « 0 requete par seconde »
afficherait un vert total sur une mesure jamais faite. C'est le defaut que ce
script existe pour rendre impossible :

  - le moteur est epingle explicitement (`DOCKER_HOST=unix:///var/run/docker-ce.sock`) ;
  - socket absent, `docker ps` en echec, zero conteneur de runner alors que des
    slots sont attendus, ou aucun compteur lisible : verdict `UNREADABLE`,
    code retour 2, et le motif est ecrit -- JAMAIS `OK` ;
  - en diagnostic seulement (le verdict ne change pas), l'organe sonde le
    moteur par defaut et rapporte combien de slots il y voit : « 0 ici, 14
    la-bas » nomme la mauvaise pince au lieu de la laisser deviner.

METHODE DE MESURE
-----------------
Par echantillon : un `docker ps` (noms + IDs) puis un `docker exec <slot> cat
/proc/net/snmp` par slot vivant. Pourquoi un seul point final ne suffit pas :
une moyenne sur la fenetre masque une rafale. Le compteur est donc releve a
intervalle regulier (1 s par defaut), et l'organe restitue DEUX nombres :

  - `average_qps` : datagrammes cumules / duree reelle de la fenetre ;
  - `burst_qps`   : maximum du debit sur une fenetre glissante de 5 s.

La fenetre glissante retient, pour chaque echantillon, l'intervalle dont la
duree est la PLUS PROCHE de 5 s (et non le plus court disponible) : choisir le
plus court sur-reporterait des micro-intervalles de 1 s, choisir le plus long
diluerait la rafale. La duree effectivement utilisee est publiee (`burst_span_s`)
pour que le lecteur sache a quoi se rapporte le chiffre. Une rafale n'est
evaluee qu'une fois 5 s d'historique accumulees ; sur une fenetre plus courte,
`burst_qps` vaut `null` et le verdict ne porte que sur la moyenne -- un zero
serait ici un chiffre fabrique.

Un compteur qui RECULE n'est pas un debit negatif : c'est un conteneur recree
(le nom est reutilise, le compteur repart de 0). Ces evenements sont listes dans
`resets` avec leur nature (`recycle` quand l'ID du conteneur a change, `reset`
quand seul le compteur a recule), et l'intervalle qui les contient ne contribue
PAS au debit (il est incomplet par construction). Le biais est donc une
sous-estimation declaree, jamais un chiffre invente.

Le cout d'un echantillon est un `docker exec` par slot vivant (~30-80 ms
chacun) : a 14 slots, un tour coute ~1-2 s et l'intervalle effectif derive. Les
horodatages sont pris au MILIEU de chaque tour et le debit est calcule sur les
durees reelles, donc la mesure reste exacte ; seule la granularite
d'observation de la rafale est celle du tour. Ce cout est publie (`sample_period_s`).

VERDICT ET CODES DE RETOUR
--------------------------
Alignes sur les autres organes du depot (`gh_queue_health.py` : 0/1/2) :

  - `OK`          : moyenne < seuil ET rafale < seuil de rafale ............ 0
  - `WARN`        : un des deux seuils atteint .............................. 1
  - `RED`         : le rapport au seuil atteint 5x (moyenne ou rafale) ...... 1
  - `UNREADABLE`  : rien n'a pu etre mesure (moteur, socket, slots, exec) ... 2

INVOCATION
----------
Depuis Windows, l'organe tourne DANS la distrib Ubuntu (c'est la seule voie ou
docker et `/proc/net/snmp` des conteneurs sont joignables) :

    wsl -d Ubuntu -- python3 /mnt/d/CoursIA/scripts/ci/check_dns_rate.py --window 15
    wsl -d Ubuntu -- python3 /mnt/d/CoursIA/scripts/ci/check_dns_rate.py --window 60 --json
    wsl -d Ubuntu -- python3 /mnt/d/CoursIA/scripts/ci/check_dns_rate.py --dry-run

Depuis un shell deja dans WSL, ou en CI Linux :

    ./scripts/ci/check_dns_rate.py --window 60

Le chemin `/mnt/d/CoursIA` est celui du clone principal sur ai-01 ; depuis un
worktree, remplacer par son propre chemin (`/mnt/d/CoursIA-<suffixe>`).
Depuis Git Bash (MSYS), passer la commande a `bash -lc` plutot qu'en argument
direct : MSYS reecrit les arguments de forme `/mnt/...` en chemins Windows et
le fichier devient introuvable (`wsl -d Ubuntu -- bash -lc 'python3 ...'`).
Aucune dependance externe : bibliotheque standard uniquement (le depot interdit
`requests` dans ses organes).

PROTOCOLE DE REFERENCE (Maintenance#196)
----------------------------------------
1. `--dry-run` d'abord : etat du moteur epingle et liste des slots vus.
2. `--window 60` (defaut) en regime normal, a poster tel quel avec son JSON.
3. Une mesure sous 5 s ne prouve rien de la rafale : `burst_qps` sera `null`.
4. Le chiffre a comparer a « 1 requete/s » est `average_qps`, en sachant qu'il
   MAJORE le DNS. `burst_qps` repond a l'autre question (le backoff et le
   jitter de `supervise.sh` dispersent-ils les rafales ?).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from dataclasses import dataclass, field

DEFAULT_DOCKER_HOST = "unix:///var/run/docker-ce.sock"
# Chemin du socket du moteur NATIF, distinct de DOCKER_HOST pour deux raisons :
# l'existence du fichier se lit sans docker, et l'URL peut etre surchargee
# (tcp://) alors que le diagnostic de socket reste pertinent sur unix://.
DEFAULT_SOCKET_PATH = "/var/run/docker-ce.sock"
# Prefixe de nom des slots sur ai-01 (persist/ai-01/coursia-runner-start.sh).
# Le predicat est STRICT -- `<prefixe>-<numero>` --, comme running_family_mb de
# supervise.sh : `<prefixe>-backup` ou `<prefixe>-4x` ne sont pas des slots.
DEFAULT_NAME_PREFIX = "myia-ai-01-wsl"
# Parc mesure le 2026-10-27 : 14 slots. Sert UNIQUEMENT au predicat
# « zero conteneur alors que des slots sont attendus » -> UNREADABLE.
DEFAULT_EXPECTED_SLOTS = 14
DEFAULT_WINDOW_S = 60.0
DEFAULT_INTERVAL_S = 1.0
DEFAULT_THRESHOLD_QPS = 1.0
DEFAULT_BURST_THRESHOLD_QPS = 10.0
BURST_WINDOW_S = 5.0
DEFAULT_SNMP_PATH = "/proc/net/snmp"
# Au-dela de 5x le seuil, ce n'est plus une derive a surveiller : c'est l'etat
# qui a motive le volet 5.
RED_FACTOR = 5.0

EXIT_OK = 0
EXIT_WARN = 1
EXIT_UNREADABLE = 2

STATUS_OK = "OK"
STATUS_WARN = "WARN"
STATUS_RED = "RED"
STATUS_UNREADABLE = "UNREADABLE"


# ---------------------------------------------------------------------------
# Parsing du compteur
# ---------------------------------------------------------------------------

def parse_snmp_udp_out_datagrams(text: str) -> int | None:
    """Extrait `Udp.OutDatagrams` d'un `/proc/net/snmp`.

    Le fichier porte une ligne d'en-tetes puis une ligne de valeurs, par
    protocole (`Ip:`, `Icmp:`, `Udp:`, `UdpLite:`...). La colonne est reperee
    PAR SON NOM dans l'en-tete, jamais par une position supposee : le noyau a
    deja insere des colonnes (`IgnoredMulti`, `MemErrors`) et en insera
    d'autres, et une lecture positionnelle se decalerait en silence. La
    position historique (colonne 5, index 4) ne sert que de repli quand
    l'en-tete ne nomme pas la colonne -- cas d'un noyau qui renommerait.

    Rend `None` quand la valeur est absente ou non entiere : l'appelant compte
    alors l'echantillon comme illisible, il ne fabrique pas un zero.
    """
    header: list[str] | None = None
    for line in text.splitlines():
        # `UdpLite:` ne commence pas par `Udp:` -- pas de confusion possible.
        if not line.startswith("Udp:"):
            continue
        cells = line.split()[1:]
        if header is None:
            header = cells
            continue
        if "OutDatagrams" in header:
            idx = header.index("OutDatagrams")
        else:
            idx = 4
        if idx >= len(cells):
            return None
        try:
            return int(cells[idx])
        except ValueError:
            return None
    return None


# ---------------------------------------------------------------------------
# Modele de mesure et calculs purs (testables sans Docker)
# ---------------------------------------------------------------------------

@dataclass
class Sample:
    """Un releve : horodatage (s depuis le debut) et compteurs par slot.

    `ids` est optionnel -- les tests synthetiques n'en ont pas besoin. Quand il
    est present, un changement d'ID distingue un conteneur RECREE d'un compteur
    qui recule, et les deux sont nommes differemment dans `resets`.
    """

    t: float
    counters: dict[str, int] = field(default_factory=dict)
    ids: dict[str, str] = field(default_factory=dict)


@dataclass
class Reset:
    """Compteur non monotone : conteneur recree ou compteur remis a zero."""

    slot: str
    t: float
    before: int
    after: int
    kind: str  # "recycle" (ID change) | "reset" (meme conteneur)


@dataclass
class Measurement:
    times: list[float] = field(default_factory=list)
    totals: list[float] = field(default_factory=list)
    resets: list[Reset] = field(default_factory=list)
    average_qps: float = 0.0
    burst_qps: float | None = None
    burst_start: float | None = None
    burst_end: float | None = None
    slots: list[str] = field(default_factory=list)
    missing_samples: dict[str, int] = field(default_factory=dict)
    datagrams_total: int = 0
    # Nombre maximal de compteurs lus sur UN echantillon -- ce que la mesure a
    # effectivement pu voir (0 = rien, et alors il n'y a pas de mesure).
    counters_read: int = 0

    @property
    def elapsed_s(self) -> float:
        return (self.times[-1] - self.times[0]) if len(self.times) >= 2 else 0.0

    @property
    def burst_span_s(self) -> float | None:
        if self.burst_start is None or self.burst_end is None:
            return None
        return self.burst_end - self.burst_start

    @property
    def sufficient(self) -> bool:
        """Deux points au moins : sans cela il n'y a pas de debit, donc pas de mesure."""
        return len(self.times) >= 2 and self.elapsed_s > 0


def _closest_span(times: list[float], i: int, window_s: float) -> int:
    """Indice `j < i` dont la duree `times[i] - times[j]` est la plus proche de `window_s`.

    Le critere « le plus proche » est le moins biaise des trois candidats
    naturels -- le plus court sur-reporterait des micro-intervalles d'un seul
    pas d'echantillonnage, le plus long diluerait la rafale dans une duree qui
    n'a pas ete demandee. Le cout est quadratique en nombre d'echantillons, ce
    qui est sans consequence sur les fenetres visees (dizaines de points).
    """
    j = 0
    while j + 1 < i and (abs(times[i] - times[j + 1] - window_s)
                         <= abs(times[i] - times[j] - window_s)):
        j += 1
    return j


def fold_samples(samples: list[Sample], *, burst_window_s: float = BURST_WINDOW_S) -> Measurement:
    """Passe des compteurs cumules aux deux debits, en tolerant le recyclage.

    Le cumul adjuste (`totals`) ne fait que croitre : chaque intervalle ajoute
    `max(0, delta)`, et un intervalle qui contient un recul de compteur ajoute 0
    en etant NOMME dans `resets`. C'est ce qui rend le debit non negatif par
    construction, sans jamais moyenner un conteneur recree dans le debit d'un
    autre.

    Un slot absent d'un echantillon ne contribue pas a l'intervalle concerne (il
    n'y a rien a soustraire) : l'absence est comptee dans `missing_samples`,
    jamais comblee par un zero.
    """
    m = Measurement()
    if not samples:
        return m
    m.times = [s.t for s in samples]
    m.slots = sorted({slot for s in samples for slot in s.counters}, key=slot_sort_key)

    prev_counter: dict[str, int] = {}
    prev_id: dict[str, str] = {}
    adjusted = 0.0
    for s in samples:
        for slot in m.slots:
            if slot not in s.counters:
                m.missing_samples[slot] = m.missing_samples.get(slot, 0) + 1
                continue
            cur = s.counters[slot]
            cur_id = s.ids.get(slot, "")
            old = prev_counter.get(slot)
            old_id = prev_id.get(slot, "")
            if old is None:
                prev_counter[slot] = cur
                prev_id[slot] = cur_id
                continue
            if cur_id and old_id and cur_id != old_id:
                # Nouveau conteneur, nouveau network namespace : son compteur
                # n'a aucun rapport avec le precedent.
                m.resets.append(Reset(slot, s.t, old, cur, "recycle"))
                prev_counter[slot] = cur
                prev_id[slot] = cur_id
                continue
            if cur < old:
                m.resets.append(Reset(slot, s.t, old, cur, "reset"))
                prev_counter[slot] = cur
                prev_id[slot] = cur_id
                continue
            adjusted += cur - old
            prev_counter[slot] = cur
            prev_id[slot] = cur_id
        m.totals.append(adjusted)

    m.datagrams_total = int(adjusted)
    elapsed = m.elapsed_s
    if elapsed > 0:
        m.average_qps = adjusted / elapsed

    # Rafale : uniquement quand l'historique couvre la fenetre demandee. Avant,
    # le meilleur intervalle disponible est un prefixe plus court que 5 s, et
    # l'appeler « rafale sur 5 s » serait un chiffre faux.
    if elapsed >= burst_window_s:
        for i in range(1, len(m.times)):
            if m.times[i] - m.times[0] < burst_window_s:
                continue
            j = _closest_span(m.times, i, burst_window_s)
            span = m.times[i] - m.times[j]
            if span <= 0:
                continue
            rate = (m.totals[i] - m.totals[j]) / span
            if m.burst_qps is None or rate > m.burst_qps:
                m.burst_qps = rate
                m.burst_start = m.times[j]
                m.burst_end = m.times[i]
    return m


def verdict(average_qps: float, burst_qps: float | None,
            threshold_qps: float, burst_threshold_qps: float,
            red_factor: float = RED_FACTOR) -> str:
    """`OK` / `WARN` / `RED` a partir des deux debits et des deux seuils.

    `burst_qps = None` (fenetre trop courte) : la jambe rafale est ABSENTE, pas
    satisfaite -- le verdict ne porte alors que sur la moyenne, et l'appelant
    doit le dire.
    """
    ratio_avg = average_qps / threshold_qps if threshold_qps > 0 else 0.0
    ratio_burst = 0.0
    if burst_qps is not None and burst_threshold_qps > 0:
        ratio_burst = burst_qps / burst_threshold_qps
    if max(ratio_avg, ratio_burst) >= red_factor:
        return STATUS_RED
    if average_qps >= threshold_qps or (burst_qps is not None and burst_qps >= burst_threshold_qps):
        return STATUS_WARN
    return STATUS_OK


def decide_status(*, read_error: str | None, socket_present: bool | None,
                  found_slots: int, expected_slots: int,
                  counters_read: int) -> tuple[str, str]:
    """Separe « je n'ai pas mesure » de « j'ai mesure et c'est calme ».

    C'est la fonction qui ferme le piege principal de l'organe : sans elle, un
    `docker ps` sur le mauvais moteur rendrait zero slot, zero datagramme, et un
    `OK` parfaitement faux.

    Rend `(statut, motif)` ; motif est vide quand la mesure a eu lieu.
    """
    if read_error:
        return STATUS_UNREADABLE, read_error
    if socket_present is False:
        return STATUS_UNREADABLE, (
            "socket du moteur natif absent -- le dockerd des runners ne repond "
            "pas sur ce chemin, et un zero ne serait pas une mesure")
    if found_slots == 0 and expected_slots > 0:
        return STATUS_UNREADABLE, (
            f"0 conteneur de runner alors que {expected_slots} slot(s) sont "
            f"attendus -- mauvais moteur Docker (piege des deux moteurs), pool "
            f"arrete, ou prefixe de nom errone ; ce n'est PAS « 0 requete/s »")
    if counters_read == 0:
        return STATUS_UNREADABLE, (
            "aucun compteur Udp.OutDatagrams n'a pu etre lu -- la mesure n'a "
            "pas eu lieu")
    return "MEASURED", ""


# ---------------------------------------------------------------------------
# Acces Docker (seule couche non pure)
# ---------------------------------------------------------------------------

_SLOT_OK = re.compile(r"^(?P<prefix>.+)-(?P<index>\d+)$")


def slot_sort_key(name: str) -> tuple[str, int, str]:
    """Tri NUMERIQUE des slots : `-2` avant `-10`, jamais l'ordre alphabetique."""
    match = _SLOT_OK.match(name)
    if match is None:
        return (name, 0, name)
    return (match.group("prefix"), int(match.group("index")), name)


def is_slot_name(name: str, prefix: str) -> bool:
    """Vrai ssi le nom est EXACTEMENT `<prefixe>-<numero>`.

    Predicat strict, sur le modele de `running_family_mb` de supervise.sh : un
    filtre `docker ps --filter name=` est un match de SOUS-CHAINE, qui
    compterait `<prefixe>-backup` ou `<prefixe>-4x` comme des slots.
    """
    if not prefix or not name.startswith(prefix + "-"):
        return False
    rest = name[len(prefix) + 1:]
    return rest.isdigit()


def docker_env(docker_host: str | None) -> dict[str, str]:
    """Environnement enfant, avec le moteur EPINGLE (ou explicitement defaut).

    `docker_host=None` RETIRE `DOCKER_HOST` herite : sans cela, une machine qui
    exporte le socket natif dans son shell ferait croire au diagnostic « moteur
    par defaut » qu'il regarde Docker Desktop alors qu'il regarde deja le bon.
    """
    env = dict(os.environ)
    if docker_host:
        env["DOCKER_HOST"] = docker_host
    else:
        env.pop("DOCKER_HOST", None)
    return env


def run_cmd(cmd: list[str], docker_host: str | None,
            timeout_s: float = 15.0) -> tuple[int | None, str, str]:
    """Execute une commande docker ; `rc=None` signifie « non invoquable »."""
    try:
        proc = subprocess.run(
            cmd, capture_output=True, text=True, encoding="utf-8",
            errors="replace", timeout=timeout_s, check=False,
            env=docker_env(docker_host),
        )
    except FileNotFoundError:
        return None, "", "docker introuvable dans le PATH"
    except subprocess.TimeoutExpired:
        return None, "", f"delai depasse ({timeout_s:.0f} s) : {' '.join(cmd)}"
    except OSError as exc:  # pragma: no cover -- defensif
        return None, "", f"invoquer docker a echoue : {exc}"
    return proc.returncode, proc.stdout, proc.stderr


def list_slots(docker_host: str | None, prefix: str,
               run=run_cmd) -> tuple[dict[str, str], str | None]:
    """Conteneurs de runner vivants -> `{nom: id}`, plus un motif d'echec eventuel.

    `run` est injectable : les tests exercent le chemin « moteur absent » avec
    un faux executeur, sans Docker ni machine.
    """
    code, out, err = run(["docker", "ps", "--format", "{{.Names}}\t{{.ID}}"],
                         docker_host)
    if code is None:
        return {}, err or "docker n'a pas pu etre invoque"
    if code != 0:
        return {}, (f"docker ps a echoue (rc={code}) : "
                    f"{(err or out).strip()[:300] or 'sans message'}")
    slots: dict[str, str] = {}
    for line in out.splitlines():
        parts = line.split("\t")
        name = parts[0].strip()
        if not name or not is_slot_name(name, prefix):
            continue
        slots[name] = parts[1].strip() if len(parts) > 1 else ""
    return slots, None


def read_udp_out_datagrams(slot: str, docker_host: str | None,
                           snmp_path: str = DEFAULT_SNMP_PATH,
                           run=run_cmd) -> tuple[int | None, str]:
    """Compteur UDP sortant DU CONTENEUR (son network namespace), ou motif d'echec."""
    code, out, err = run(["docker", "exec", slot, "cat", snmp_path], docker_host)
    if code is None:
        return None, err or "docker exec non invocable"
    if code != 0:
        return None, (f"docker exec a echoue (rc={code}) : "
                      f"{(err or out).strip()[:200] or 'sans message'}")
    value = parse_snmp_udp_out_datagrams(out)
    if value is None:
        return None, f"Udp.OutDatagrams illisible dans {snmp_path}"
    return value, ""


def count_slots_on_default_engine(prefix: str, run=run_cmd) -> int | None:
    """Diagnostic : combien de slots le moteur PAR DEFAUT voit.

    Ne change jamais le verdict. Sert a nommer la mauvaise pince : « 0 sur le
    moteur natif, 14 sur le moteur par defaut » designe le piege des deux
    moteurs d'ai-01 sans que le lecteur ait a le deviner.
    """
    slots, err = list_slots(None, prefix, run=run)
    if err:
        return None
    return len(slots)


def measure(docker_host: str | None, prefix: str, window_s: float, interval_s: float,
            snmp_path: str = DEFAULT_SNMP_PATH, run=run_cmd,
            sleep=time.sleep, clock=time.monotonic) -> tuple[Measurement, str, str]:
    """Echantillonne les compteurs pendant `window_s`.

    Rend `(mesure, erreur_de_listing, note_par_slot)` :

      - un echec de LISTING arrete la mesure et remonte en tete : sans listing,
        on ne sait pas quels conteneurs existent, donc la suite serait une
        mesure sur un perimetre inconnu ;
      - un echec de `docker exec` sur UN slot est compte pour ce slot et la
        mesure continue (les autres slots restent mesurables) ; le premier motif
        remonte en NOTE, pour le diagnostic, jamais comme verdict -- si aucun
        compteur n'a ete lu, `counters_read` vaut 0 et c'est ce fait-la qui
        conclut UNREADABLE.
    """
    samples: list[Sample] = []
    slot_note = ""
    t0 = clock()
    while True:
        started = clock() - t0
        slots, err = list_slots(docker_host, prefix, run=run)
        if err:
            return fold_samples(samples), err, slot_note
        counters: dict[str, int] = {}
        ids: dict[str, str] = {}
        for name in sorted(slots, key=slot_sort_key):
            value, why = read_udp_out_datagrams(name, docker_host, snmp_path, run=run)
            if value is None:
                if not slot_note:
                    slot_note = f"{name} : {why}"
                continue
            counters[name] = value
            ids[name] = slots[name]
        # Horodatage au MILIEU du tour : les compteurs ne sont pas lus au meme
        # instant, et dater le releve au debut surestimerait chaque intervalle
        # du cout du tour.
        finished = clock() - t0
        samples.append(Sample((started + finished) / 2.0, counters, ids))
        if finished >= window_s:
            break
        target = min(started + interval_s, window_s)
        wait = target - finished
        if wait > 0:
            sleep(wait)

    measurement = fold_samples(samples)
    measurement.counters_read = max((len(s.counters) for s in samples), default=0)
    return measurement, "", slot_note


def socket_present_for(docker_host: str | None) -> bool | None:
    """Existence du socket du moteur epingle, sans appeler docker.

    `None` quand l'endpoint n'est pas un socket unix (tcp://) : la question ne
    se pose alors pas. Un `False` est un fait mesure (le fichier n'existe pas),
    pas une hypothese.
    """
    if not docker_host or not docker_host.startswith("unix://"):
        return None
    path = docker_host[len("unix://"):] or DEFAULT_SOCKET_PATH
    return os.path.exists(path)


# ---------------------------------------------------------------------------
# Rendu
# ---------------------------------------------------------------------------

def build_payload(*, status: str, reason: str, m: Measurement, args,
                  found_slots: dict[str, str], prefix: str,
                  window_s: float, sample_period_s: float | None,
                  diagnostics: dict[str, object]) -> dict:
    return {
        "status": status,
        "reason": reason,
        "verdict": verdict(m.average_qps, m.burst_qps,
                           args.threshold, args.max_burst_threshold)
        if status == "MEASURED" else None,
        "average_qps": m.average_qps,
        "burst_qps": m.burst_qps,
        "burst_span_s": m.burst_span_s,
        "burst_window_s": BURST_WINDOW_S,
        "threshold_qps": args.threshold,
        "burst_threshold_qps": args.max_burst_threshold,
        "window_s": window_s,
        "elapsed_s": m.elapsed_s,
        "sample_count": len(m.times),
        "sample_period_s": sample_period_s,
        "datagrams_total": m.datagrams_total,
        "slots": m.slots,
        "slots_seen": sorted(found_slots, key=slot_sort_key),
        "expected_slots": args.expected_slots,
        "name_prefix": prefix,
        "docker_host": args.docker_host,
        "resets": [
            {"slot": r.slot, "t_s": round(r.t, 3), "before": r.before,
             "after": r.after, "kind": r.kind}
            for r in m.resets
        ],
        "missing_samples": m.missing_samples,
        "counts_all_udp": True,
        "measures": "Udp.OutDatagrams des conteneurs de runners (majorant du DNS)",
        "does_not_measure": [
            "le DNS cote Windows (instrument aveugle, mesure 2026-10-27)",
            "l'attribution au processus wslservice",
            "les requetes vers api.github.com elles-memes (compteur agrege par netns)",
        ],
        "diagnostics": diagnostics,
    }


def render_text(payload: dict, *, dry_run: bool = False) -> list[str]:
    tag = "[dns-rate]"
    lines: list[str] = []
    status = payload["status"]
    lines.append(f"{tag} compteurs UDP des conteneurs de runners -- MAJORANT du "
                 f"DNS (tout UDP sortant), pas la mesure des requetes vers "
                 f"api.github.com")
    if dry_run:
        lines.append(f"{tag} moteur epingle : {payload['docker_host']} ; "
                     f"{len(payload['slots_present'])} slot(s) vu(s) "
                     f"(prefixe {payload['name_prefix']}, "
                     f"{payload['expected_slots']} attendu(s)) : "
                     f"{', '.join(payload['slots_present']) or 'aucun'}")
        for name, value in payload["diagnostics"].items():
            lines.append(f"{tag} diagnostic {name} : {value}")
        if status != "MEASURED":
            lines.append(f"::error::{tag} {status}: {payload['reason']}")
        return lines
    lines.append(f"{tag} moteur: {payload['docker_host']} ; "
                 f"{len(payload['slots_seen'])} slot(s) vu(s) pendant la fenetre "
                 f"(prefixe {payload['name_prefix']})")
    if payload["sample_count"]:
        period = payload["sample_period_s"]
        period_txt = f"{period:.2f} s" if period is not None else "inconnu"
        lines.append(f"{tag} fenetre: {payload['elapsed_s']:.1f} s, "
                     f"{payload['sample_count']} echantillon(s), "
                     f"pas ~{period_txt}")
    if status != "MEASURED":
        lines.append(f"::error::{tag} {status}: {payload['reason']}")
        for name, value in payload["diagnostics"].items():
            lines.append(f"{tag} diagnostic {name} : {value}")
        return lines
    burst = payload["burst_qps"]
    if burst is None:
        lines.append(f"{tag} rafale: NON OBSERVABLE (moins de "
                     f"{BURST_WINDOW_S:.0f} s d'historique) -- le verdict ne "
                     f"porte que sur la moyenne")
    else:
        lines.append(f"{tag} rafale max: {burst:.2f} q/s sur "
                     f"{payload['burst_span_s']:.2f} s (seuil "
                     f"{payload['burst_threshold_qps']:.2f})")
    lines.append(f"{tag} debit moyen: {payload['average_qps']:.2f} q/s "
                 f"(seuil {payload['threshold_qps']:.2f}) ; "
                 f"{payload['datagrams_total']} datagramme(s) cumules")
    if payload["resets"]:
        kinds = {}
        for r in payload["resets"]:
            kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1
        detail = ", ".join(f"{k}={v}" for k, v in sorted(kinds.items()))
        lines.append(f"{tag} {len(payload['resets'])} compteur(s) non monotone(s) "
                     f"({detail}) -- intervalles concernes exclus du debit, "
                     f"jamais moyennes")
    if payload["missing_samples"]:
        detail = ", ".join(f"{k}:{v}" for k, v in sorted(payload["missing_samples"].items()))
        lines.append(f"{tag} echantillons absents par slot (conteneur recycle ou "
                     f"arrete) : {detail}")
    if payload["verdict"] in (STATUS_WARN, STATUS_RED):
        burst_txt = ("non observable" if burst is None else f"{burst:.2f} q/s")
        lines.append(f"::warning::{tag} {payload['verdict']} : debit UDP moyen "
                     f"{payload['average_qps']:.2f} q/s (seuil "
                     f"{payload['threshold_qps']:.2f}) et rafale {burst_txt} "
                     f"(seuil {payload['burst_threshold_qps']:.2f}) -- objectif "
                     f"de fermeture #22937 volet 5 : moyenne < 1 q/s")
    else:
        lines.append(f"{tag} verdict: {payload['verdict']}")
    for name, value in payload["diagnostics"].items():
        lines.append(f"{tag} diagnostic {name} : {value}")
    return lines


# ---------------------------------------------------------------------------
# Entree
# ---------------------------------------------------------------------------

def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description="Mesure le debit de requetes UDP des conteneurs de runners "
                    "(majorant du DNS) -- #22937 volet 5.1 / Maintenance#196.",
        epilog="Depuis Windows : wsl -d Ubuntu -- python3 "
               "/mnt/d/CoursIA/scripts/ci/check_dns_rate.py --window 15")
    ap.add_argument("--window", type=float,
                    default=float(os.environ.get("DNS_RATE_WINDOW", DEFAULT_WINDOW_S)),
                    help=f"duree de la mesure, en secondes (defaut "
                         f"{DEFAULT_WINDOW_S:.0f}) ; sous "
                         f"{BURST_WINDOW_S:.0f} s la rafale n'est pas observable")
    ap.add_argument("--interval", type=float,
                    default=float(os.environ.get("DNS_RATE_INTERVAL", DEFAULT_INTERVAL_S)),
                    help=f"intervalle d'echantillonnage vise, en secondes "
                         f"(defaut {DEFAULT_INTERVAL_S:.0f}) ; le cout d'un tour "
                         f"(un docker exec par slot) peut l'allonger")
    ap.add_argument("--threshold", type=float,
                    default=float(os.environ.get("DNS_RATE_THRESHOLD", DEFAULT_THRESHOLD_QPS)),
                    help=f"seuil du debit MOYEN, en requetes/s (defaut "
                         f"{DEFAULT_THRESHOLD_QPS:.2f})")
    ap.add_argument("--max-burst-threshold", type=float,
                    default=float(os.environ.get("DNS_RATE_BURST_THRESHOLD",
                                                 DEFAULT_BURST_THRESHOLD_QPS)),
                    help=f"seuil du maximum glissant sur {BURST_WINDOW_S:.0f} s, "
                         f"en requetes/s (defaut {DEFAULT_BURST_THRESHOLD_QPS:.2f})")
    ap.add_argument("--docker-host", default=os.environ.get("DNS_RATE_DOCKER_HOST",
                                                            DEFAULT_DOCKER_HOST),
                    help="endpoint DOCKER_HOST du moteur NATIF (defaut "
                         f"{DEFAULT_DOCKER_HOST}) ; c'est ce pin qui evite le "
                         f"piege des deux moteurs")
    ap.add_argument("--name-prefix", default=os.environ.get("COURSIA_RUNNER_NAME_PREFIX",
                                                            DEFAULT_NAME_PREFIX),
                    help=f"prefixe de nom des slots (defaut {DEFAULT_NAME_PREFIX})")
    ap.add_argument("--expected-slots", type=int,
                    default=int(os.environ.get("COURSIA_RUNNER_EXPECTED_SLOTS",
                                               DEFAULT_EXPECTED_SLOTS)),
                    help=f"slots attendus sur cette machine (defaut "
                         f"{DEFAULT_EXPECTED_SLOTS}) ; 0 conteneur vu alors que "
                         f"ce nombre est > 0 vaut UNREADABLE, jamais OK")
    ap.add_argument("--snmp-path", default=DEFAULT_SNMP_PATH,
                    help=f"chemin du compteur DANS le conteneur (defaut "
                         f"{DEFAULT_SNMP_PATH})")
    ap.add_argument("--dry-run", action="store_true",
                    help="liste le moteur et les slots vus, sans mesurer")
    ap.add_argument("--json", action="store_true", help="sortie JSON du verdict")
    return ap.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)

    if args.dry_run:
        slots, err = list_slots(args.docker_host, args.name_prefix)
        status, reason = decide_status(
            read_error=err, socket_present=None,
            found_slots=len(slots), expected_slots=args.expected_slots,
            counters_read=1 if slots else 0,
        )
        diagnostics = {}
        if not slots:
            diagnostics["moteur par defaut"] = (
                f"{count_slots_on_default_engine(args.name_prefix)} slot(s) vu(s)")
        payload = {
            "status": "MEASURED" if status == "MEASURED" else status,
            "reason": reason,
            "docker_host": args.docker_host,
            "name_prefix": args.name_prefix,
            "expected_slots": args.expected_slots,
            "slots_present": sorted(slots, key=slot_sort_key),
            "diagnostics": diagnostics,
        }
        if args.json:
            print(json.dumps(payload, ensure_ascii=False, indent=2))
        else:
            for line in render_text(payload, dry_run=True):
                print(line)
        return EXIT_OK if payload["status"] == "MEASURED" else EXIT_UNREADABLE

    started = time.monotonic()
    m, listing_error, slot_note = measure(
        args.docker_host, args.name_prefix, args.window, args.interval,
        snmp_path=args.snmp_path,
    )
    elapsed_wall = time.monotonic() - started
    sample_period = m.elapsed_s / (len(m.times) - 1) if len(m.times) >= 2 else None

    # Les trois predicats de non-mesure, dans l'ordre ou ils rendent le verdict
    # le plus utile : moteur injoignable, mauvais moteur (0 slot pour N
    # attendus), aucun compteur lisible. Le dernier couvre aussi la fenetre
    # trop courte pour calculer un debit.
    status, status_reason = decide_status(
        read_error=listing_error or None,
        socket_present=socket_present_for(args.docker_host),
        found_slots=len(m.slots),
        expected_slots=args.expected_slots,
        counters_read=m.counters_read,
    )
    if status == "MEASURED" and not m.sufficient:
        status, status_reason = STATUS_UNREADABLE, (
            "moins de deux echantillons exploitables -- un debit ne se calcule "
            "pas sur un point unique (fenetre trop courte, ou tours trop lents)")

    diagnostics: dict[str, object] = {}
    if slot_note:
        diagnostics["compteur par slot"] = slot_note
    if status != "MEASURED":
        diagnostics["moteur par defaut"] = (
            f"{count_slots_on_default_engine(args.name_prefix)} slot(s) vu(s) "
            f"(moteur epingle : {len(m.slots)} slot(s))")
        if sample_period:
            diagnostics["duree du tour"] = f"{sample_period:.2f} s"

    found = {slot: "" for slot in m.slots}
    payload = build_payload(
        status=status, reason=status_reason, m=m, args=args, found_slots=found,
        prefix=args.name_prefix, window_s=args.window,
        sample_period_s=sample_period, diagnostics=diagnostics,
    )
    payload["wall_s"] = elapsed_wall
    payload["expected_slots"] = args.expected_slots

    if args.json:
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        for line in render_text(payload):
            print(line)

    if status != "MEASURED":
        return EXIT_UNREADABLE
    return EXIT_OK if payload["verdict"] == STATUS_OK else EXIT_WARN


if __name__ == "__main__":
    sys.exit(main())

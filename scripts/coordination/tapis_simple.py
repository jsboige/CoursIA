"""Tapis simple : servir les issues ouvertes par ordre de dernier grain.

Demande du mainteneur (28/11) : les issues sont servies en commencant par les
plus vieilles qui n'ont pas recu de grain recent, et une issue qui vient d'en
recevoir un repart en queue. Les cas chauds (PR etudiantes, fer a battre) ne
passent pas par ici : le coordinateur les place a la main dans ses files.

Une seule regle d'ordre. La cle d'une issue est la date de son dernier grain,
ou sa date de creation si elle n'en a jamais recu. Le tri est croissant. Il n'y
a ni seuil, ni fenetre, ni quota.

Ce qui compte comme grain (et renvoie en queue) :

- un commentaire dont la premiere ligne commence par ``[CLAIMED]``,
  ``[CLAIMED-AMEND]`` ou ``[DELIVERED]`` ;
- le drapeau manuel ``tapis_simple.py servi N...`` ;
- un tirage enregistre par ``belt_queues.py record`` (fichiers ``draw-*.json``).

Deux exclusions seulement, portees par des labels : ``candidate-delivered``
(l'urne de cloture, rendue a part pour le coordinateur, l'adjoint et le
secretaire) et ``pause``. Les EPIC restent dans l'ordre, marques
``conteneur`` et rendus dans une liste a part : leur tour venu, le
coordinateur leur decoupe une issue fille.

Cout reseau : une liste en bloc des issues ouvertes, puis la lecture des fils
de la seule tete de file, par lots GraphQL. Une lecture reste valable tant que
l'issue n'a pas bouge (``updatedAt``).

Usage ::

    python scripts/coordination/tapis_simple.py tirer [--n 60] [--conteneurs 10] [--json]
    python scripts/coordination/tapis_simple.py servi N [N ...] [--lane L] [--note T]

Sorties : 0 tirage rendu ; 1 lecture en bloc impossible ; 2 usage.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from collections.abc import Callable, Iterable
from datetime import datetime, timedelta, timezone
from pathlib import Path

DEPOT = "jsboige/CoursIA"
LABELS_URNE = {"candidate-delivered"}
LABELS_PAUSE = {"pause"}
MARQUEURS = ("[CLAIMED]", "[CLAIMED-AMEND]", "[DELIVERED]")
CONTENEUR_RE = re.compile(r"\b(EPIC|Epic|epic|umbrella|Umbrella|Tracker|parapluie)\b")
LOT = 25
COMMENTAIRES_LUS = 30

LireFils = Callable[[list[int]], "dict[int, list[dict]] | None"]


def maintenant_iso() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def store_dir() -> Path:
    if os.environ.get("TAPIS_SIMPLE_DIR"):
        return Path(os.environ["TAPIS_SIMPLE_DIR"])
    base = os.environ.get("LOCALAPPDATA") or str(Path.home() / ".local" / "share")
    return Path(base) / "CoursIA" / "tapis_simple"


def draws_dir() -> Path:
    if os.environ.get("BELT_QUEUES_DIR"):
        return Path(os.environ["BELT_QUEUES_DIR"])
    base = os.environ.get("LOCALAPPDATA") or str(Path.home() / ".local" / "share")
    return Path(base) / "CoursIA" / "belt_queues"


# --- le registre des grains servis (drapeau manuel et tirages) ---------------

def lire_registre(dossier: Path) -> dict[int, str]:
    """Derniere date de service connue par issue, drapeau manuel compris."""
    dernier: dict[int, str] = {}
    chemin = dossier / "registre.jsonl"
    if chemin.is_file():
        for ligne in chemin.read_text(encoding="utf-8").splitlines():
            try:
                e = json.loads(ligne)
                n, quand = int(e["issue"]), str(e["quand"])
            except (ValueError, KeyError, TypeError):
                continue
            if quand > dernier.get(n, ""):
                dernier[n] = quand
    return dernier


def lire_tirages(dossier: Path) -> dict[int, str]:
    """Issues placees dans une file par ``belt_queues.py record`` : un grain servi."""
    dernier: dict[int, str] = {}
    for f in sorted(dossier.glob("draw-*.json")):
        try:
            d = json.loads(f.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            continue
        quand = str(d.get("assigned_at") or "")
        for lane in (d.get("lanes") or {}).values():
            for g in lane.get("queue") or []:
                try:
                    n = int(g["number"])
                except (KeyError, TypeError, ValueError):
                    continue
                if quand > dernier.get(n, ""):
                    dernier[n] = quand
    return dernier


def marquer_servi(dossier: Path, numeros: Iterable[int], lane: str = "", note: str = "",
                  quand: str | None = None) -> int:
    dossier.mkdir(parents=True, exist_ok=True)
    quand = quand or maintenant_iso()
    lignes = [json.dumps({"issue": int(n), "quand": quand, "source": "servi",
                          "lane": lane, "note": note}, ensure_ascii=False) for n in numeros]
    with (dossier / "registre.jsonl").open("a", encoding="utf-8") as fh:
        for ligne in lignes:
            fh.write(ligne + "\n")
    return len(lignes)


# --- le cache des fils lus ---------------------------------------------------

def lire_cache(dossier: Path) -> dict[int, dict]:
    chemin = dossier / "fils.json"
    if not chemin.is_file():
        return {}
    try:
        brut = json.loads(chemin.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}
    return {int(k): v for k, v in brut.items()}


def ecrire_cache(dossier: Path, cache: dict[int, dict]) -> None:
    dossier.mkdir(parents=True, exist_ok=True)
    tmp = dossier / "fils.json.tmp"
    tmp.write_text(json.dumps({str(k): v for k, v in sorted(cache.items())},
                              ensure_ascii=False, indent=0), encoding="utf-8")
    tmp.replace(dossier / "fils.json")


def dernier_marqueur(commentaires: list[dict]) -> str | None:
    """Date du dernier commentaire dont la premiere ligne porte un marqueur de grain."""
    dates = [c.get("createdAt") or "" for c in commentaires
             if (c.get("body") or "").lstrip().startswith(MARQUEURS)]
    dates = [d for d in dates if d]
    return max(dates) if dates else None


# --- l'ordre -----------------------------------------------------------------

def est_conteneur(issue: dict) -> bool:
    labels = {lab.lower() for lab in issue.get("labels_noms", [])}
    return "epic" in labels or bool(CONTENEUR_RE.search(issue.get("title") or ""))


JAMAIS = "2099-12-31"
BANDES = {0: "echue", 1: "a-trier", 2: "queue", 3: "a-trier"}
PART_TRI = 0.25


def plus_jours(iso: str, jours: int) -> str:
    d = datetime.strptime(iso[:10], "%Y-%m-%d") + timedelta(days=int(jours))
    return d.strftime("%Y-%m-%dT00:00:00Z")


def echeance(decision: dict | None, dernier: str | None) -> str | None:
    """Date explicite du prochain tirage, ou ``None`` si aucune decision n'est vivante.

    Une date ``prochain`` vaut tant que l'issue n'a pas ete servie depuis : servie
    a la date ou apres, la decision est consommee. Une ``cadence`` (jours) prend
    alors le relais : prochain tirage = dernier grain + cadence.
    """
    if not decision:
        return None
    prochain = decision.get("prochain")
    if prochain:
        p = str(prochain)[:10] + "T00:00:00Z"
        if not dernier or dernier < p:
            return p
    cadence = decision.get("cadence")
    if cadence and dernier:
        return plus_jours(dernier, int(cadence))
    return None


def ordonner(issues: list[dict], connus: dict[int, str], cache: dict[int, dict],
             lire_fils: LireFils, n: int, max_lectures: int = 200,
             n_conteneurs: int = 10, decisions: dict[int, dict] | None = None,
             maintenant: str | None = None,
             part_tri: float = PART_TRI) -> tuple[list[dict], list[dict], int, int]:
    """Rend les ``n`` premiers grains, les ``n_conteneurs`` premiers conteneurs, le
    nombre de fils lus et le nombre d'issues en attente de leur date.

    Trois bandes, une seule cle dans chacune (decision mandataire du 28/11) :

    0. **echue** : une decision explicite (date ou cadence) est arrivee a terme ;
       la plus en retard d'abord ;
    1. **a-trier** : jamais servie et sans decision ; la plus ancienne d'abord.
       Son premier grain est le triage, qui pose la decision. Cette bande prend
       au plus ``part_tri`` des grains d'un tirage : un afflux d'issues neuves
       n'affame pas la queue ;
    2. **queue** : servie sans decision vivante ; la derniere intervention la plus
       ancienne d'abord.

    Une decision a echeance future retient l'issue jusqu'a sa date (``attente``).

    Un EPIC recoit rarement un claim direct : il est rendu a part, au
    coordinateur, qui lui decoupe une fille quand son tour vient.

    Le rang connu d'une issue non lue est une borne basse : lire son fil ne peut
    que la faire reculer (une intervention plus recente consomme une decision ou
    deplace la cle). On ne sert donc une issue qu'une fois qu'aucune issue non
    lue ne la precede ; sinon on lit d'abord, par lots, les non lues de tete. Le
    budget de lectures epuise, la suite est servie dans l'ordre connu, avec
    ``fil_lu: False``.
    """
    decisions = decisions or {}
    maintenant = maintenant or maintenant_iso()
    par_num = {it["number"]: it for it in issues}

    def lu(num: int) -> bool:
        c = cache.get(num)
        return bool(c) and c.get("lu_le", "") >= (par_num[num].get("updatedAt") or "")

    def dernier(num: int) -> tuple[str | None, str]:
        sources = []
        if connus.get(num):
            sources.append((connus[num], "servi"))
        c = cache.get(num) or {}
        if c.get("dernier_grain"):
            sources.append((c["dernier_grain"], "fil"))
        return max(sources) if sources else (None, "")

    quota_tri = max(1, int(n * part_tri))
    tri_servis = [0]

    def rang(num: int) -> tuple[int, str, str]:
        date, source = dernier(num)
        e = echeance(decisions.get(num), date)
        if e is not None:
            return (0, e, "decision") if e <= maintenant else (9, e, "decision")
        if date is None:
            bande = 1 if tri_servis[0] < quota_tri else 3
            return (bande, par_num[num].get("createdAt") or "", "creation")
        return (2, date, source)

    en_attente = [m for m in par_num if rang(m)[0] == 9]
    restants = [m for m in par_num if m not in set(en_attente)]
    servis: list[dict] = []
    conteneurs: list[dict] = []
    lectures = 0
    while restants and (len(servis) < n or len(conteneurs) < n_conteneurs):
        restants.sort(key=lambda m: (rang(m)[:2], m))
        tete = restants[0]
        if lu(tete) or lectures >= max_lectures:
            restants.pop(0)
            bande, date, source = rang(tete)
            if bande == 9:  # la lecture a revele une decision a echeance future
                en_attente.append(tete)
                continue
            it = par_num[tete]
            d = decisions.get(tete) or {}
            entree = {"numero": tete, "titre": it.get("title") or "",
                      "bande": BANDES[bande], "cle": date, "source_cle": source,
                      "conteneur": est_conteneur(it), "fil_lu": lu(tete),
                      "cadence": d.get("cadence"), "restants": d.get("restants"),
                      "labels": it.get("labels_noms", [])}
            cible, borne = (conteneurs, n_conteneurs) if entree["conteneur"] else (servis, n)
            if len(cible) < borne:
                cible.append(entree)
                if bande in (1, 3) and not entree["conteneur"]:
                    tri_servis[0] += 1
            continue
        a_lire = [m for m in restants if not lu(m)][:min(LOT, max_lectures - lectures)]
        fils = lire_fils(a_lire)
        if fils is None:  # lecture en panne : la suite est servie, honnetement non lue
            lectures = max_lectures
            continue
        lectures += len(a_lire)
        for m in a_lire:
            cache[m] = {"lu_le": par_num[m].get("updatedAt") or maintenant_iso(),
                        "dernier_grain": dernier_marqueur(fils.get(m, []))}
    return servis, conteneurs, lectures, len(en_attente)


# --- lectures GitHub ---------------------------------------------------------

def _gh(argv: list[str], timeout: int = 180) -> str:
    return subprocess.run(["gh", *argv], capture_output=True, text=True, encoding="utf-8",
                          timeout=timeout, check=True).stdout


def lister_issues() -> list[dict]:
    brut = _gh(["issue", "list", "-R", DEPOT, "--state", "open", "--limit", "5000",
                "--json", "number,title,labels,createdAt,updatedAt"])
    issues = json.loads(brut)
    for it in issues:
        it["labels_noms"] = [lab.get("name", "") for lab in it.get("labels") or []]
    return issues


def lire_fils_gh(numeros: list[int]) -> dict[int, list[dict]] | None:
    """Les derniers commentaires de chaque issue, en un appel ; ``None`` si la lecture echoue."""
    if not numeros:
        return {}
    proprio, nom = DEPOT.split("/")
    champs = " ".join(
        f"i{n}: issue(number: {n}) {{ comments(last: {COMMENTAIRES_LUS}) "
        f"{{ nodes {{ createdAt body }} }} }}" for n in numeros)
    requete = f'query {{ repository(owner: "{proprio}", name: "{nom}") {{ {champs} }} }}'
    try:
        data = json.loads(_gh(["api", "graphql", "-f", f"query={requete}"]))
    except (subprocess.SubprocessError, OSError, ValueError):
        return None
    repo = (data.get("data") or {}).get("repository") or {}
    return {n: ((repo.get(f"i{n}") or {}).get("comments") or {}).get("nodes") or []
            for n in numeros}


# --- les decisions explicites (champs d'un GitHub Project) -------------------
#
# Chaque issue peut porter, dans un Project dedie, trois champs :
#   - « Prochain tirage » (date) : l'issue n'est pas servie avant ; a terme elle
#     passe en tete (bande echue) ;
#   - « Cadence (j) » (nombre) : apres chaque grain, prochain tirage = dernier
#     grain + cadence ;
#   - « Grains restants » (nombre) : prevision, informative.
# Sans decision, une issue servie repart en queue. Les champs sont poses a
# l'APPROVE par le coordinateur (ou par le mainteneur dans le tableau).
#
# Garde (consigne mainteneur du 28/11) : une cadence ou une date a moins de
# CADENCE_MIN jours n'est acceptee qu'avec ``--consolidation``. Les cas chauds ne
# passent pas par le tapis : le coordinateur les place a la main dans ses files.

CHAMP_PROCHAIN = "Prochain tirage"
CHAMP_CADENCE = "Cadence (j)"
CHAMP_RESTANTS = "Grains restants"
CADENCE_MIN = 7
VIEILLE_JOURS = 14


def projet_cible() -> tuple[str, int] | None:
    """Le Project des decisions, ``proprietaire/numero`` (env ``TAPIS_PROJET`` ou ``projet.txt``)."""
    v = os.environ.get("TAPIS_PROJET", "")
    if not v:
        f = store_dir() / "projet.txt"
        v = f.read_text(encoding="utf-8").strip() if f.is_file() else ""
    proprio, _, num = v.partition("/")
    try:
        return (proprio, int(num)) if proprio else None
    except ValueError:
        return None


def _graphql(requete: str, variables: dict) -> dict:
    argv = ["api", "graphql", "-f", f"query={requete}"]
    for k, v in variables.items():
        if v is not None:
            argv += ["-F" if isinstance(v, (int, float)) else "-f", f"{k}={v}"]
    data = json.loads(_gh(argv))
    if data.get("errors"):
        raise ValueError(data["errors"][0].get("message", "graphql"))
    return data.get("data") or {}


_Q_ITEMS = """query($o:String!,$n:Int!,$a:String){ user(login:$o){ projectV2(number:$n){
 items(first:100, after:$a){ pageInfo{ hasNextPage endCursor } nodes{
  content{ ... on Issue{ number repository{ nameWithOwner } } }
  fieldValues(first:20){ nodes{
   ... on ProjectV2ItemFieldDateValue{ date field{ ... on ProjectV2FieldCommon{ name } } }
   ... on ProjectV2ItemFieldNumberValue{ number field{ ... on ProjectV2FieldCommon{ name } } }
 } } } } } } }"""


def decisions_des_items(noeuds: list[dict]) -> dict[int, dict]:
    """Les decisions par issue du depot, depuis les noeuds ``items`` du Project."""
    cles = {CHAMP_PROCHAIN: "prochain", CHAMP_CADENCE: "cadence", CHAMP_RESTANTS: "restants"}
    out: dict[int, dict] = {}
    for nd in noeuds:
        c = nd.get("content") or {}
        if (c.get("repository") or {}).get("nameWithOwner") != DEPOT or "number" not in c:
            continue
        d: dict = {}
        for fv in (nd.get("fieldValues") or {}).get("nodes") or []:
            cle = cles.get((fv.get("field") or {}).get("name", ""))
            if cle == "prochain" and fv.get("date"):
                d[cle] = fv["date"]
            elif cle and fv.get("number") is not None:
                d[cle] = int(fv["number"])
        if d:
            out[int(c["number"])] = d
    return out


def lire_decisions_gh(proprio: str, numero: int) -> dict[int, dict] | None:
    noeuds: list[dict] = []
    curseur = None
    try:
        while True:
            d = _graphql(_Q_ITEMS, {"o": proprio, "n": numero, "a": curseur})
            items = (((d.get("user") or {}).get("projectV2") or {}).get("items")) or {}
            noeuds += items.get("nodes") or []
            info = items.get("pageInfo") or {}
            if not info.get("hasNextPage"):
                break
            curseur = info.get("endCursor")
    except (subprocess.SubprocessError, OSError, ValueError):
        return None
    return decisions_des_items(noeuds)


def verifier_decision(prochain: str | None, cadence: int | None, consolidation: bool,
                      aujourd_hui: str) -> str | None:
    """Rend le motif du refus, ou ``None`` : rien sous CADENCE_MIN jours sans ``--consolidation``."""
    if consolidation:
        return None
    if cadence is not None and 0 < cadence < CADENCE_MIN:
        return (f"cadence {cadence} j < {CADENCE_MIN} j : reservee aux issues de "
                "consolidation (--consolidation) ; un cas chaud va dans une file manuelle")
    if prochain and prochain != JAMAIS and prochain < plus_jours(aujourd_hui, CADENCE_MIN)[:10]:
        return (f"prochain tirage {prochain} a moins de {CADENCE_MIN} j : reserve a la "
                "consolidation (--consolidation) ; un cas chaud va dans une file manuelle")
    return None


_M_CLEAR = """mutation($p:ID!,$i:ID!,$f:ID!){ clearProjectV2ItemFieldValue(
 input:{projectId:$p,itemId:$i,fieldId:$f}){ projectV2Item{ id } } }"""
_M_DATE = """mutation($p:ID!,$i:ID!,$f:ID!,$v:Date!){ updateProjectV2ItemFieldValue(
 input:{projectId:$p,itemId:$i,fieldId:$f,value:{date:$v}}){ projectV2Item{ id } } }"""
_M_NOMBRE = """mutation($p:ID!,$i:ID!,$f:ID!,$v:Float!){ updateProjectV2ItemFieldValue(
 input:{projectId:$p,itemId:$i,fieldId:$f,value:{number:$v}}){ projectV2Item{ id } } }"""


def planifier_gh(proprio: str, numero: int, issues: list[int], prochain: str | None,
                 effacer_prochain: bool, cadence: int | None, restants: int | None) -> None:
    meta = _graphql("""query($o:String!,$n:Int!){ user(login:$o){ projectV2(number:$n){ id
      fields(first:50){ nodes{ ... on ProjectV2Field{ id name } } } } } }""",
                    {"o": proprio, "n": numero})
    projet = (meta.get("user") or {}).get("projectV2") or {}
    champs = {f.get("name"): f.get("id")
              for f in (projet.get("fields") or {}).get("nodes") or [] if f}
    manquants = [c for c in (CHAMP_PROCHAIN, CHAMP_CADENCE, CHAMP_RESTANTS) if c not in champs]
    if manquants:
        raise ValueError(f"champs absents du Project : {manquants}")
    pid = projet["id"]
    depot_proprio, depot_nom = DEPOT.split("/")
    for num in issues:
        iid = _graphql("""query($o:String!,$r:String!,$n:Int!){ repository(owner:$o,name:$r){
          issue(number:$n){ id } } }""", {"o": depot_proprio, "r": depot_nom, "n": num})
        contenu = iid["repository"]["issue"]["id"]
        item = _graphql("""mutation($p:ID!,$c:ID!){ addProjectV2ItemById(
          input:{projectId:$p, contentId:$c}){ item{ id } } }""",
                        {"p": pid, "c": contenu})["addProjectV2ItemById"]["item"]["id"]
        base = {"p": pid, "i": item}
        if effacer_prochain:
            _graphql(_M_CLEAR, {**base, "f": champs[CHAMP_PROCHAIN]})
        elif prochain:
            _graphql(_M_DATE, {**base, "f": champs[CHAMP_PROCHAIN], "v": prochain})
        if cadence == 0:
            _graphql(_M_CLEAR, {**base, "f": champs[CHAMP_CADENCE]})
        elif cadence is not None:
            _graphql(_M_NOMBRE, {**base, "f": champs[CHAMP_CADENCE], "v": int(cadence)})
        if restants is not None:
            _graphql(_M_NOMBRE, {**base, "f": champs[CHAMP_RESTANTS], "v": int(restants)})


def creer_projet_gh(proprio: str, titre: str) -> int:
    oid = _graphql("query($o:String!){ user(login:$o){ id } }", {"o": proprio})["user"]["id"]
    p = _graphql("""mutation($o:ID!,$t:String!){ createProjectV2(input:{ownerId:$o,title:$t}){
      projectV2{ id number } } }""", {"o": oid, "t": titre})["createProjectV2"]["projectV2"]
    for nom, genre in ((CHAMP_PROCHAIN, "DATE"), (CHAMP_CADENCE, "NUMBER"),
                       (CHAMP_RESTANTS, "NUMBER")):
        _graphql("mutation($p:ID!,$n:String!){ createProjectV2Field(input:{projectId:$p,"
                 f"dataType:{genre},name:$n}}){{ projectV2Field{{ ... on ProjectV2Field{{ id }} }} }} }}",
                 {"p": p["id"], "n": nom})
    return int(p["number"])


# --- couverture : toutes les issues sont-elles visitees ? -------------------

def couverture(issues: list[dict], connus: dict[int, str], cache: dict[int, dict],
               decisions: dict[int, dict], maintenant: str) -> dict:
    """Mesure ce que le mainteneur demande de surveiller : aucune issue oubliee."""
    limite = plus_jours(maintenant, -VIEILLE_JOURS)
    jamais, vieilles, plus_vieille = 0, 0, None
    for it in issues:
        num = it["number"]
        dates = [d for d in (connus.get(num), (cache.get(num) or {}).get("dernier_grain")) if d]
        dernier = max(dates) if dates else None
        ref = dernier or it.get("createdAt") or ""
        if dernier is None:
            jamais += 1
        if ref < limite:
            vieilles += 1
        if plus_vieille is None or ref < plus_vieille[1]:
            plus_vieille = (num, ref)
    courtes = sorted(n for n, d in decisions.items()
                     if d.get("cadence") and d["cadence"] < CADENCE_MIN)
    return {"jamais_servies": jamais, "non_vues_depuis_14j": vieilles,
            "plus_vieille": ({"numero": plus_vieille[0], "depuis": plus_vieille[1]}
                             if plus_vieille else None),
            "decisions": len(decisions), "cadences_sous_7j": courtes}


# --- commandes ---------------------------------------------------------------

def tirer(n: int, issues: list[dict], dossier: Path, tirages: Path,
          lire_fils: LireFils, max_lectures: int, n_conteneurs: int = 10,
          decisions: dict[int, dict] | None = None, etat_decisions: str = "aucune",
          maintenant: str | None = None) -> dict:
    maintenant = maintenant or maintenant_iso()
    decisions = decisions or {}
    urne = [it for it in issues if LABELS_URNE & set(it["labels_noms"])]
    pause = [it for it in issues if LABELS_PAUSE & set(it["labels_noms"])
             and not LABELS_URNE & set(it["labels_noms"])]
    exclus = {it["number"] for it in urne + pause}
    connus = lire_tirages(tirages)
    for num, quand in lire_registre(dossier).items():
        if quand > connus.get(num, ""):
            connus[num] = quand
    cache = lire_cache(dossier)
    servables = [it for it in issues if it["number"] not in exclus]
    servis, conteneurs, lectures, attente = ordonner(
        servables, connus, cache, lire_fils, n, max_lectures, n_conteneurs,
        decisions, maintenant)
    ecrire_cache(dossier, cache)
    urne.sort(key=lambda it: it.get("updatedAt") or "")
    return {"tapis": "simple", "maintenant": maintenant, "ouvertes": len(issues),
            "urne": len(urne), "pause": len(pause), "fils_lus": lectures,
            "en_attente": attente, "decisions": etat_decisions,
            "couverture": couverture(servables, connus, cache, decisions, maintenant),
            "grains": servis, "conteneurs": conteneurs,
            "urne_plus_vieilles": [{"numero": it["number"], "titre": it.get("title") or ""}
                                   for it in urne[:20]]}


def texte(r: dict) -> str:
    c = r["couverture"]
    pv = c["plus_vieille"] or {}
    lignes = [(f"Tapis simple, {r['maintenant']} : {r['ouvertes']} issues ouvertes, "
               f"{r['urne']} dans l'urne, {r['pause']} en pause, {r['en_attente']} en attente "
               f"de leur date, {r['fils_lus']} fils lus ; decisions : {r['decisions']}."),
              (f"Couverture : {c['jamais_servies']} jamais servies, "
               f"{c['non_vues_depuis_14j']} non vues depuis 14 j, "
               f"plus vieille #{pv.get('numero')} ({str(pv.get('depuis'))[:10]}), "
               f"cadences sous 7 j : {c['cadences_sous_7j'] or 'aucune'}."),
              ""]
    for titre, liste in (("Grains (files des workers)", r["grains"]),
                         ("Conteneurs a decouper (coordinateur)", r["conteneurs"])):
        lignes.append(titre + " :")
        for i, g in enumerate(liste, 1):
            lu = "" if g["fil_lu"] else " (fil non lu)"
            lignes.append(f"{i:3d}. #{g['numero']} {g['bande']} {g['cle'][:10]} "
                          f"({g['source_cle']}){lu} {g['titre'][:90]}")
        lignes.append("")
    return "\n".join(lignes)


def _date_decision(args: argparse.Namespace) -> tuple[str | None, bool]:
    if args.jamais:
        return JAMAIS, False
    if args.queue:
        return None, True
    if args.le:
        return args.le, False
    if args.dans is not None:
        return plus_jours(maintenant_iso(), args.dans)[:10], False
    return None, False


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sous = p.add_subparsers(dest="cmd", required=True)
    t = sous.add_parser("tirer", help="rendre la tete de file")
    t.add_argument("--n", type=int, default=60)
    t.add_argument("--conteneurs", type=int, default=10, help="EPIC rendus a part")
    t.add_argument("--max-lectures", type=int, default=300)
    t.add_argument("--json", action="store_true")
    s = sous.add_parser("servi", help="drapeau manuel : ces issues ont recu un grain")
    s.add_argument("numeros", nargs="+", type=int)
    s.add_argument("--lane", default="")
    s.add_argument("--note", default="")
    pl = sous.add_parser("planifier", help="poser la decision de prochain tirage")
    pl.add_argument("numeros", nargs="+", type=int)
    quand = pl.add_mutually_exclusive_group()
    quand.add_argument("--dans", type=int, help="jours avant le prochain tirage")
    quand.add_argument("--le", help="date AAAA-MM-JJ du prochain tirage")
    quand.add_argument("--jamais", action="store_true", help="retenir l'issue indefiniment")
    quand.add_argument("--queue", action="store_true", help="effacer la date : retour en queue")
    pl.add_argument("--cadence", type=int, help="jours entre deux tirages (0 efface)")
    pl.add_argument("--restants", type=int, help="grains restants prevus")
    pl.add_argument("--consolidation", action="store_true",
                    help="autorise moins de 7 j (issues de consolidation seulement)")
    cp = sous.add_parser("creer-projet", help="creer le Project des decisions et ses champs")
    cp.add_argument("--owner", default=DEPOT.split("/")[0])
    cp.add_argument("--titre", default="CoursIA -- Tapis")
    args = p.parse_args(argv)

    if args.cmd == "servi":
        k = marquer_servi(store_dir(), args.numeros, args.lane, args.note)
        print(f"{k} issue(s) marquee(s) servie(s) : elles repartent en queue.")
        return 0
    if args.cmd == "creer-projet":
        try:
            num = creer_projet_gh(args.owner, args.titre)
        except (subprocess.SubprocessError, OSError, ValueError, KeyError) as exc:
            print(f"creation impossible (scope `project` requis) : {exc}", file=sys.stderr)
            return 1
        store_dir().mkdir(parents=True, exist_ok=True)
        (store_dir() / "projet.txt").write_text(f"{args.owner}/{num}\n", encoding="utf-8")
        print(f"Project {args.owner}/{num} cree avec ses trois champs.")
        return 0
    if args.cmd == "planifier":
        cible = projet_cible()
        if cible is None:
            print("aucun Project configure : `creer-projet` d'abord (scope `project`)",
                  file=sys.stderr)
            return 1
        prochain, effacer = _date_decision(args)
        motif = verifier_decision(prochain, args.cadence, args.consolidation, maintenant_iso())
        if motif:
            print(f"refuse : {motif}", file=sys.stderr)
            return 2
        try:
            planifier_gh(cible[0], cible[1], args.numeros, prochain, effacer,
                         args.cadence, args.restants)
        except (subprocess.SubprocessError, OSError, ValueError, KeyError) as exc:
            print(f"ecriture impossible : {exc}", file=sys.stderr)
            return 1
        print(f"{len(args.numeros)} decision(s) posee(s) dans {cible[0]}/{cible[1]}.")
        return 0
    try:
        issues = lister_issues()
    except (subprocess.SubprocessError, OSError, ValueError) as exc:
        print(f"lecture en bloc impossible : {exc}", file=sys.stderr)
        return 1
    cible = projet_cible()
    decisions: dict[int, dict] | None = {}
    etat = "aucun Project configure"
    if cible:
        decisions = lire_decisions_gh(*cible)
        etat = (f"{cible[0]}/{cible[1]}" if decisions is not None
                else f"{cible[0]}/{cible[1]} ILLISIBLE (tirage degrade, sans decisions)")
    r = tirer(args.n, issues, store_dir(), draws_dir(), lire_fils_gh, args.max_lectures,
              args.conteneurs, decisions or {}, etat)
    print(json.dumps(r, ensure_ascii=False, indent=1) if args.json else texte(r))
    return 0


if __name__ == "__main__":
    sys.exit(main())

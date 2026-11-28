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
from datetime import datetime, timezone
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


def ordonner(issues: list[dict], connus: dict[int, str], cache: dict[int, dict],
             lire_fils: LireFils, n: int, max_lectures: int = 200,
             n_conteneurs: int = 10) -> tuple[list[dict], list[dict], int]:
    """Rend les ``n`` premiers grains et les ``n_conteneurs`` premiers conteneurs
    par cle croissante, puis le nombre de fils lus.

    Un EPIC recoit rarement un claim direct : le travail se fait sur ses filles.
    Il tient donc souvent la tete de file. On le sert a part, au coordinateur,
    qui lui decoupe une fille quand son tour vient ; les grains vont aux workers.

    La cle connue d'une issue non lue est une borne basse : lire son fil ne peut
    que la faire reculer. On ne sert donc une issue qu'une fois qu'aucune issue
    non lue ne la precede ; sinon on lit d'abord, par lots, les non lues de tete.
    Le budget de lectures epuise, la suite est servie dans l'ordre connu, avec
    ``fil_lu: False``.
    """
    par_num = {it["number"]: it for it in issues}

    def lu(num: int) -> bool:
        c = cache.get(num)
        return bool(c) and c.get("lu_le", "") >= (par_num[num].get("updatedAt") or "")

    def cle(num: int) -> tuple[str, str]:
        it = par_num[num]
        sources = [(it.get("createdAt") or "", "creation")]
        if connus.get(num):
            sources.append((connus[num], "servi"))
        c = cache.get(num) or {}
        if c.get("dernier_grain"):
            sources.append((c["dernier_grain"], "fil"))
        return max(sources)

    restants = list(par_num)
    servis: list[dict] = []
    conteneurs: list[dict] = []
    lectures = 0
    while restants and (len(servis) < n or len(conteneurs) < n_conteneurs):
        restants.sort(key=lambda m: (cle(m)[0], m))
        tete = restants[0]
        if lu(tete) or lectures >= max_lectures:
            restants.pop(0)
            date, source = cle(tete)
            it = par_num[tete]
            entree = {"numero": tete, "titre": it.get("title") or "",
                      "cle": date, "source_cle": source,
                      "conteneur": est_conteneur(it), "fil_lu": lu(tete),
                      "labels": it.get("labels_noms", [])}
            cible, borne = (conteneurs, n_conteneurs) if entree["conteneur"] else (servis, n)
            if len(cible) < borne:
                cible.append(entree)
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
    return servis, conteneurs, lectures


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


# --- commandes ---------------------------------------------------------------

def tirer(n: int, issues: list[dict], dossier: Path, tirages: Path,
          lire_fils: LireFils, max_lectures: int, n_conteneurs: int = 10) -> dict:
    urne = [it for it in issues if LABELS_URNE & set(it["labels_noms"])]
    pause = [it for it in issues if LABELS_PAUSE & set(it["labels_noms"])
             and not LABELS_URNE & set(it["labels_noms"])]
    exclus = {it["number"] for it in urne + pause}
    connus = lire_tirages(tirages)
    for num, quand in lire_registre(dossier).items():
        if quand > connus.get(num, ""):
            connus[num] = quand
    cache = lire_cache(dossier)
    servis, conteneurs, lectures = ordonner(
        [it for it in issues if it["number"] not in exclus],
        connus, cache, lire_fils, n, max_lectures, n_conteneurs)
    ecrire_cache(dossier, cache)
    urne.sort(key=lambda it: it.get("updatedAt") or "")
    return {"tapis": "simple", "maintenant": maintenant_iso(), "ouvertes": len(issues),
            "urne": len(urne), "pause": len(pause), "fils_lus": lectures,
            "grains": servis, "conteneurs": conteneurs,
            "urne_plus_vieilles": [{"numero": it["number"], "titre": it.get("title") or ""}
                                   for it in urne[:20]]}


def texte(r: dict) -> str:
    lignes = [(f"Tapis simple, {r['maintenant']} : {r['ouvertes']} issues ouvertes, "
               f"{r['urne']} dans l'urne, {r['pause']} en pause, {r['fils_lus']} fils lus."),
              ""]
    for titre, liste in (("Grains (files des workers)", r["grains"]),
                         ("Conteneurs a decouper (coordinateur)", r["conteneurs"])):
        lignes.append(titre + " :")
        for i, g in enumerate(liste, 1):
            lu = "" if g["fil_lu"] else " (fil non lu)"
            lignes.append(f"{i:3d}. #{g['numero']} {g['cle'][:10]} ({g['source_cle']}){lu} "
                          f"{g['titre'][:90]}")
        lignes.append("")
    return "\n".join(lignes)


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
    args = p.parse_args(argv)

    if args.cmd == "servi":
        k = marquer_servi(store_dir(), args.numeros, args.lane, args.note)
        print(f"{k} issue(s) marquee(s) servie(s) : elles repartent en queue.")
        return 0
    try:
        issues = lister_issues()
    except (subprocess.SubprocessError, OSError, ValueError) as exc:
        print(f"lecture en bloc impossible : {exc}", file=sys.stderr)
        return 1
    r = tirer(args.n, issues, store_dir(), draws_dir(), lire_fils_gh, args.max_lectures,
              args.conteneurs)
    print(json.dumps(r, ensure_ascii=False, indent=1) if args.json else texte(r))
    return 0


if __name__ == "__main__":
    sys.exit(main())

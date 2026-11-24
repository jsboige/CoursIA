#!/usr/bin/env python3
"""Le balayage de la SUSPICION de livraison (#28114, dispatch `c0035b`).

Le coordinateur (24/11) : « les issues livrees sont encore servies ; "le
chemin cible est sur main" ne doit que **soupconner** une livraison, jamais
la conclure ; le grain passe a l'urne avec un label candidat ».

Ce que fait cet organe, et rien de plus :

1. il lit le **pool ouvert** (un appel `gh`) ;
2. il lit ce que `origin/main` a fait des chemins que chaque issue nomme
   (**un** appel git pour tout le balayage) ;
3. quand un chemin cible a bouge sur `main` **apres** que l'issue s'est
   tuee, il pose le marqueur `[INFO] suspicion-livraison` dans le fil et le
   label `candidate-delivered` -- le grain part a l'URNE ;
4. il ne clot **rien**, il ne retire **rien**, il ne decide de **rien**.

La decision de cloture reste au coordinateur et a l'adjoint, qui lisent
les criteres de l'issue (G.9). La marque de la suspicion est une **donnee**
lue par le poseur de label (`candidate_delivered.py`) et par le tapis : le
signal ne se repaye pas a chaque tirage.

Le balayage est **local** (il lui faut l'historique) : le poseur de label
tourne en CI sur un sparse-checkout sans historique, il lit le marqueur
pose ici.

Usage :

    python scripts/coordination/tapis_livraison.py            # rapport seul
    python scripts/coordination/tapis_livraison.py --apply    # pose marqueur + label
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

RACINE = Path(__file__).resolve().parents[2]
if str(RACINE / "scripts") not in sys.path:
    sys.path.insert(0, str(RACINE / "scripts"))

import candidate_delivered_chemins as chemins  # noqa: E402
import issue_containers  # noqa: E402
from candidate_delivered import is_epic  # noqa: E402

#: Le label de l'urne de cloture (la source unique est `tapis_labels`).
LABEL = "candidate-delivered"

#: Le prefixe du marqueur de la suspicion (la forme exacte est dans
#: `candidate_delivered_chemins.SUSPICION_MARKER_RE`).
MARQUEUR = "[INFO] suspicion-livraison"

#: Le maximum de chemins cites dans le marqueur (le fil reste lisible).
MAX_CITES = 4

_REF_RE = re.compile(r"#(\d+)")


def _gh_json(args: list[str]) -> object:
    """Un appel `gh` qui rend du JSON (ou `None` si la reponse est vide)."""
    proc = subprocess.run(["gh", *args], capture_output=True, text=True,
                          check=False, encoding="utf-8", errors="replace")
    if proc.returncode != 0:
        return None
    try:
        return json.loads(proc.stdout or "null")
    except json.JSONDecodeError:
        return None


def pool(repo: str, limit: int) -> list[dict]:
    """Le pool ouvert, avec titre, corps, labels et date de creation."""
    data = _gh_json(["issue", "list", "--repo", repo, "--state", "open",
                     "--limit", str(limit), "--json",
                     "number,title,body,labels,createdAt"])
    return data if isinstance(data, list) else []


def prs_ouverts(repo: str, limit: int = 300) -> set[int]:
    """Les numeros d'issue cites par une PR ouverte (le travail en cours)."""
    data = _gh_json(["pr", "list", "--repo", repo, "--state", "open",
                     "--limit", str(limit), "--json", "number,title,body"])
    cites: set[int] = set()
    for pr in data if isinstance(data, list) else []:
        texte = f"{pr.get('title') or ''}\n{pr.get('body') or ''}"
        cites.update(int(n) for n in _REF_RE.findall(texte))
    return cites


def fil(repo: str, number: int) -> list[dict]:
    """Les commentaires de l'issue (dates + corps)."""
    data = _gh_json(["api", f"repos/{repo}/issues/{number}/comments",
                     "--paginate", "--jq",
                     "[.[] | {created_at: .created_at, body: .body}]"])
    return data if isinstance(data, list) else []


def corps_marqueur(suspects: list[dict]) -> str:
    """Le corps du marqueur : les chemins, et le fait que ce n'est pas une preuve."""
    cites = ", ".join(f"`{s['chemin']}` ({s['statut']}, {s['date'][:10]} -- "
                      f"{s['sujet'][:60]})" for s in suspects[:MAX_CITES])
    reste = len(suspects) - MAX_CITES
    if reste > 0:
        cites += f" (+{reste} autre(s))"
    return (
        f"{MARQUEUR} -- chemin(s) cible(s) sur `main`, touche(s) apres le "
        f"dernier mouvement de l'issue : {cites}\n\n"
        f"Ce n'est **pas** une preuve de livraison : aucun grain de "
        f"travail n'a ete constate sur cette issue. C'est un indice "
        f"suffisant pour que le grain cesse d'etre servi comme neuf : il "
        f"passe a l'urne (label `{LABEL}`), et la decision de cloture "
        f"revient au coordinateur et a l'adjoint, qui confrontent le chemin "
        f"aux criteres de l'issue.\n\n"
        f"Source : `scripts/coordination/tapis_livraison.py` (comparaison du "
        f"chemin cible au contenu de `origin/main`)."
    )


def poster(repo: str, number: int, corps: str) -> None:
    subprocess.run(["gh", "issue", "comment", str(number), "--repo", repo,
                    "--body", corps], capture_output=True, text=True, check=False,
                   encoding="utf-8", errors="replace")


def poser_label(repo: str, number: int) -> None:
    subprocess.run(["gh", "issue", "edit", str(number), "--repo", repo,
                    "--add-label", LABEL], capture_output=True, text=True,
                   check=False, encoding="utf-8", errors="replace")


def suspecter(issue: dict, touches: dict, commentaires: list[dict]) -> list[dict]:
    """Les chemins cibles de l'issue qui bougent sur `main` apres son silence,
    par un commit qui cite l'issue."""
    texte = f"{issue.get('title') or ''}\n{issue.get('body') or ''}"
    noms = chemins.nommes(texte)
    if not noms:
        return []
    dernier = max((c.get("created_at") or "" for c in commentaires), default="")
    return chemins.suspects(noms, touches, issue.get("createdAt"), dernier or None,
                            numero=int(issue.get("number") or 0))


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo", default="jsboige/CoursIA")
    ap.add_argument("--limit", type=int, default=600,
                    help="taille du pool lu (defaut 600)")
    ap.add_argument("--depot", default=str(RACINE),
                    help="le depot ou lire `origin/main`")
    ap.add_argument("--apply", action="store_true",
                    help="poser le marqueur et le label (defaut : rapport seul)")
    args = ap.parse_args(argv)

    touches = chemins.touches_main(args.depot)
    if not touches:
        print("[tapis-livraison] `origin/main` illisible (depot, historique ou "
              "ref absents) : aucune suspicion, l'organe sort sans rien poser.")
        return 0

    issues = pool(args.repo, args.limit)
    cites_prs = prs_ouverts(args.repo)
    print(f"[tapis-livraison] repo={args.repo} pool={len(issues)} "
          f"chemins sur main={len(touches)} mode="
          f"{'apply' if args.apply else 'rapport'}")

    poses: list[int] = []
    for issue in issues:
        numero = int(issue.get("number") or 0)
        labels = [l.get("name", "") for l in (issue.get("labels") or [])]
        if LABEL in labels:
            continue
        if numero in cites_prs:
            continue  # une PR ouverte cite l'issue : le travail est en cours
        # Les parapluies et les conteneurs ne sont pas des grains : ils
        # nomment beaucoup de chemins, et les soupconner les viderait du
        # pool. Meme predicat que le poseur de label (`is_epic`,
        # `issue_containers.looks_container`) : la decision ne peut pas
        # diverger entre les deux organes.
        if is_epic(issue.get("title") or "", labels):
            continue
        if issue_containers.looks_container(issue.get("title") or "", labels,
                                            issue.get("body") or ""):
            continue
        commentaires: list[dict] = []
        suspects = suspecter(issue, touches, commentaires)
        if not suspects:
            continue
        # Le fil n'est lu que pour les candidats : le cout du balayage ne
        # depend pas du pool, mais du nombre de soupcons.
        commentaires = fil(args.repo, numero)
        if chemins.suspicion_dans_le_fil([c.get("body") or "" for c in commentaires]):
            continue  # la suspicion est deja posee
        suspects = suspecter(issue, touches, commentaires)
        if not suspects:
            continue
        corps = corps_marqueur(suspects)
        if args.apply:
            poster(args.repo, numero, corps)
            poser_label(args.repo, numero)
        poses.append(numero)
        detail = ", ".join(f"{s['chemin']} ({s['date'][:10]})" for s in suspects[:2])
        print(f"  #{numero:<6} SUSPECT  {detail}")

    print(f"[tapis-livraison] {len(poses)} grain(s) doute(s) "
          f"{'poses' if args.apply else 'signales'} "
          f"({'marqueur + label' if args.apply else 'rien n a ete pose'})")
    return 0


if __name__ == "__main__":
    sys.exit(main())

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
4. il ne clot **rien**, il ne retire **rien**, il ne decide de **rien** ;
5. la voie d'ecriture (`--apply`) applique le **VETO HUMAIN** : si une
   personne a retire le label candidat, le balayage ne le repose pas (sa
   pose deviendrait le dernier evenement humain, et effacerait le veto du
   classificateur). Une LECTURE INCOMPLETE du fil ou des evenements vaut
   veto aussi : rien n'est pose sur une lecture incomplete (reserve du
   coordinateur du 25/11 sur #28454) ;
6. une lecture INCOMPLETE du **pool** (issues ouvertes ou PRs ouvertes)
   vaut de meme refus de la voie d'ecriture : ce qui est en cours est
   INCONNU, pas absent, et la voie `--apply` rend `2` sans rien ecrire
   (reserve du coordinateur du 26/11 sur #28454).

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
import re
import subprocess
import sys
from pathlib import Path

RACINE = Path(__file__).resolve().parents[2]
if str(RACINE / "scripts") not in sys.path:
    sys.path.insert(0, str(RACINE / "scripts"))

import candidate_delivered_chemins as chemins  # noqa: E402
import issue_containers  # noqa: E402
from candidate_delivered import (  # noqa: E402
    human_retraction,
    is_epic,
    parse_label_events,
    parse_pages,
)

#: Le label de l'urne de cloture (la source unique est `tapis_labels`).
LABEL = "candidate-delivered"

#: Le prefixe du marqueur de la suspicion (la forme exacte est dans
#: `candidate_delivered_chemins.SUSPICION_MARKER_RE`).
MARQUEUR = "[INFO] suspicion-livraison"

#: Le maximum de chemins cites dans le marqueur (le fil reste lisible).
MAX_CITES = 4

_REF_RE = re.compile(r"#(\d+)")


def _gh_json(args: list[str]) -> object:
    """Un appel `gh` qui rend du JSON (ou `None` si la reponse est illisible).

    La sortie peut contenir PLUSIEURS documents JSON : `gh api --paginate`
    imprime un document PAR PAGE. Les pages sont aplatis par
    `candidate_delivered.parse_pages` -- sans quoi un fil ou une timeline de
    deux pages se lisait comme une lecture ratee, alors que GitHub avait
    repondu correctement (reserve du coordinateur du 26/11 sur #28454).
    """
    proc = subprocess.run(["gh", *args], capture_output=True, text=True,
                          check=False, encoding="utf-8", errors="replace")
    if proc.returncode != 0:
        return None
    return parse_pages(proc.stdout or "")


def pool(repo: str, limit: int) -> list[dict] | None:
    """Le pool ouvert, avec titre, corps, labels et date de creation.

    `None` = LECTURE INCOMPLETE (appel rate, reponse illisible) : le pool est
    alors INCONNU, pas vide. Une lecture incomplete ne se lit pas comme «
    aucune issue ouverte » -- ce serait un zero fabriqué.
    """
    data = _gh_json(["issue", "list", "--repo", repo, "--state", "open",
                     "--limit", str(limit), "--json",
                     "number,title,body,labels,createdAt"])
    if not isinstance(data, list):
        return None
    if len(data) >= limit:
        # Plafond atteint : la lecture est probablement complete, mais on ne
        # peut pas le distinguer d'une page coupee -- donc inconcluante.
        return None
    return data


def prs_ouverts(repo: str, limit: int = 300) -> set[int] | None:
    """Les numeros d'issue cites par une PR ouverte (le travail en cours).

    `None` = LECTURE INCOMPLETE (appel rate, reponse illisible, ou plafond
    atteint) : le pool des PRs ouvertes est alors INCONNU, pas vide. Une
    lecture incomplete ne peut pas se lire comme « aucune PR ouverte » --
    ce serait soupconner une issue dont le travail est en cours. En mode
    `--apply`, la voie d'ecriture refuse sur une lecture incomplete
    (reserve du coordinateur du 26/11 sur #28454).
    """
    data = _gh_json(["pr", "list", "--repo", repo, "--state", "open",
                     "--limit", str(limit), "--json", "number,title,body"])
    if not isinstance(data, list):
        return None
    if len(data) >= limit:
        return None
    cites: set[int] = set()
    for pr in data:
        texte = f"{pr.get('title') or ''}\n{pr.get('body') or ''}"
        cites.update(int(n) for n in _REF_RE.findall(texte))
    return cites


def fil(repo: str, number: int) -> list[dict] | None:
    """Les commentaires de l'issue (dates + corps).

    `None` = la LECTURE est INCOMPLETE (appel rate) : le balayage ne pose
    alors rien (fail-CLOSED, reserve du coordinateur du 25/11 sur #28454).
    """
    data = _gh_json(["api", f"repos/{repo}/issues/{number}/comments",
                     "--paginate", "--jq",
                     "[.[] | {created_at: .created_at, body: .body}]"])
    return data if isinstance(data, list) else None


def evenements(repo: str, number: int) -> list[dict] | None:
    """Les evenements du LABEL candidat sur cette issue.

    `None` = la LECTURE est INCOMPLETE (timeline illisible) : le balayage ne
    pose alors rien. Un issue sans evenement rend une liste VIDE, pas `None`
    (les deux se distinguent, et la distinction porte la decision).
    """
    data = _gh_json(["api", f"repos/{repo}/issues/{number}/timeline",
                     "--paginate"])
    if not isinstance(data, list):
        return None
    return parse_label_events(data, LABEL)


def veto_humain(repo: str, number: int) -> str | None:
    """Le veto humain sur le label candidat, ou `None` s'il n'y en a pas.

    Une personne a retire le label : le balayage ne peut pas le reposer, sous
    le login partage (reserve du coordinateur du 25/11 sur #28454). La
    LECTURE INCOMPLETE des evenements vaut aussi veto : on ne pose rien sur
    une lecture incomplete.
    """
    lus = evenements(repo, number)
    if lus is None:
        return "LECTURE INCOMPLETE des evenements"
    if human_retraction(lus) is not None:
        return "RETRAIT HUMAIN du label (veto)"
    return None


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
    if touches is None:
        print("[tapis-livraison] LECTURE INCOMPLETE : `origin/main` illisible ; "
              "mouvements INCONNUS, aucune ecriture.")
        return 2 if args.apply else 0
    if not touches:
        print("[tapis-livraison] `origin/main` lu : aucun mouvement dans la fenetre ; "
              "aucune suspicion ni ecriture.")
        return 0

    issues = pool(args.repo, args.limit)
    cites_prs = prs_ouverts(args.repo)

    # Une LECTURE INCOMPLETE n'est pas un zero. Le pool des issues ouvertes
    # et le pool des PRs ouvertes sont les DEUX lectures qui disent ce qui est
    # en cours : les confondre avec un pool vide ferait soupconner une issue
    # dont le travail est en cours (fail-OPEN), et ecrire sur une lecture
    # incomplete est un fail-OPEN de la meme famille. En `--apply`, la voie
    # d'ecriture REFUSE (reserve du coordinateur du 26/11 sur #28454).
    lectures_incompletes = []
    if issues is None:
        lectures_incompletes.append("pool des issues ouvertes")
    if cites_prs is None:
        lectures_incompletes.append("pool des PRs ouvertes")
    if lectures_incompletes:
        detail = ", ".join(lectures_incompletes)
        if args.apply:
            print(f"[tapis-livraison] LECTURE INCOMPLETE ({detail}) : la voie "
                  f"--apply n'ecrit rien sur une lecture incomplete. "
                  f"Ce qui est en cours est INCONNU, pas absent.")
            return 2
        print(f"[tapis-livraison] LECTURE INCOMPLETE ({detail}) : le rapport "
              f"est produit, mais il peut soupconner une issue dont le "
              f"travail est en cours (ce qui est en cours est INCONNU).")
        issues = issues or []
        cites_prs = cites_prs or set()

    print(f"[tapis-livraison] repo={args.repo} pool={len(issues)} "
          f"chemins sur main={len(touches)} mode="
          f"{'apply' if args.apply else 'rapport'}")

    poses: list[int] = []
    refuses: list[int] = []
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
        lus = fil(args.repo, numero)
        if lus is None:
            # LECTURE INCOMPLETE : rien n'est pose (fail-CLOSED).
            refuses.append(numero)
            print(f"  #{numero:<6} LECTURE INCOMPLETE (fil) -- rien n'est pose")
            continue
        commentaires = lus
        if chemins.suspicion_dans_le_fil([c.get("body") or "" for c in commentaires]):
            continue  # la suspicion est deja posee
        suspects = suspecter(issue, touches, commentaires)
        if not suspects:
            continue
        if args.apply:
            # Le VETO HUMAIN prime sur le balayage : une personne a retire le
            # label candidat, le balayage ne le repose pas (il poserait sous
            # le login partage, et sa pose deviendrait le dernier evenement
            # humain, effacant le veto). Une lecture incomplete vaut veto
            # aussi : on ne pose rien sur une lecture incomplete.
            veto = veto_humain(args.repo, numero)
            if veto is not None:
                refuses.append(numero)
                print(f"  #{numero:<6} {veto} -- rien n'est pose")
                continue
            corps = corps_marqueur(suspects)
            poster(args.repo, numero, corps)
            poser_label(args.repo, numero)
        poses.append(numero)
        detail = ", ".join(f"{s['chemin']} ({s['date'][:10]})" for s in suspects[:2])
        print(f"  #{numero:<6} SUSPECT  {detail}")

    print(f"[tapis-livraison] {len(poses)} grain(s) doute(s) "
          f"{'poses' if args.apply else 'signales'} "
          f"({'marqueur + label' if args.apply else 'rien n a ete pose'})"
          + (f" ; {len(refuses)} refuse(s) (veto humain ou lecture incomplete)"
             if refuses else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())

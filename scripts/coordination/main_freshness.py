#!/usr/bin/env python3
"""Garde de fraicheur du tirage : un main local a jour, des organes a leur version d'origin/main.

Pourquoi cet organe existe
--------------------------
Mesures du 2026-11-14 (mandat mainteneur : « les doubles, les peremptions,
doivent donner lieu a des reparations d'organes qui n'ont pas su prevenir les
collisions ») :

* une lane a tire le tapis sur un clone dont le `main` local avait 605
  commits de retard sur `origin/main`, et en a conclu « sature, tout est
  livre » -- faux : ce qui est livre se lit sur `origin/main` ;
* une autre lane a vu le picker l'avertir que son script differait
  d'`origin/main` ([PICKER PERIME], #25522) et a continue : un
  avertissement n'arrete personne.

La garde REFUSE, elle n'avertit pas. Avant de rendre des grains, l'organe de
tirage mesure l'ecart entre le `main` local et `origin/main` (`git fetch
origin main`, puis `git rev-list --count main..origin/main`) et refuse :

* si l'ecart n'est pas nul -- remede : `git pull --ff-only` ;
* si l'un des modules du tirage differe de sa version sur `origin/main` --
  la mesure compare l'arbre de travail au `origin/main` fraichement fetche,
  quel que soit le nom de la branche courante ;
* si la mesure est impossible (fetch hs, ref illisible) -- une mesure ratee
  ne se publie jamais comme un vert.

Le clone qui n'est pas sur `main` se mesure quand meme : les references
candidates sont `refs/heads/main` quand elle existe (un worktree partage les
refs du depot) puis `HEAD`, l'ecart retenu est le plus petit des deux, et le
verdict nomme la reference qui l'a donne. Un worktree cree depuis un
`origin/main` frais passe donc, meme si le `main` partage du clone principal
est en retard : le tirage ne lit qu'`origin/main`, et ce qu'il execute est
deja verifie par la divergence des organes.

`--allow-stale` passe outre, explicitement : le depassement est dit dans la
sortie JSON (`outre_passe: true`). C'est la voie de la lane qui developpe
l'organe de tirage lui-meme, pas une echappatoire silencieuse.

Le refus n'imprime PAS la commande de repli vers l'ancien picker : il ferait
rejouer le meme incident sous un organe qui, lui, se contente d'avertir. Le
remede est la mise a jour du clone.

Usage
-----
    python scripts/coordination/main_freshness.py [--repo <depot>] [--allow-stale] [--json]

Codes de sortie du standalone : 0 = frais (ou outre-passe) ; 1 = refus.
Cable dans tapis_rapide.py en tete du point d'entree : le refus s'y rend par
le code de sortie 4 (distinct du 3 « lecture incomplete », qui pointe le
repli -- ici le repli serait le contournement).
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from collections.abc import Callable
from pathlib import Path

#: Les modules qui DECIDENT le tirage. Une divergence avec origin/main fait
#: servir des grains sous un contrat perime : c'est l'incident po-2028 du
#: 14/11 -- l'avertissement du picker a ete lu, puis ignore. Une lane qui
#: developpe ces fichiers passe par --allow-stale, en le sachant.
ORGANES = (
    "scripts/coordination/tapis_rapide.py",
    "scripts/coordination/tapis_marqueurs.py",
    "scripts/coordination/tapis_sature.py",
    "scripts/coordination/gh_bulk.py",
    # La LECTURE elle-meme : le conteneur, l'echec qui interdit de servir a
    # moitie, et la mise a plat d'une issue -- dont le `comments_total`
    # INCONNU, qui decide si la fenetre est prouvee complete.
    "scripts/coordination/gh_lecture.py",
    "scripts/coordination/gh_recherche.py",
    "scripts/coordination/frozen_campaigns.py",
    "scripts/coordination/main_freshness.py",
    # Le CHEMIN DU TIRAGE (bascule #27225) : le classement, ses deux
    # priorites, la rotation, la qualification sur fil complet et la relecture
    # de service -- tous modifient le grain servi, donc tous doivent
    # correspondre a origin/main pour que le tirage soit recevable.
    "scripts/coordination/gh_selection.py",
    "scripts/coordination/gh_issues.py",
    "scripts/coordination/gh_snapshot.py",
    "scripts/coordination/tapis_universel.py",
    "scripts/coordination/tapis_avantages.py",
    "scripts/coordination/tapis_leger.py",
    "scripts/coordination/tapis_qualification.py",
    "scripts/coordination/tapis_fil_complet.py",
    "scripts/coordination/tapis_prise_en_charge.py",
    "scripts/coordination/tapis_reverif.py",
    "scripts/coordination/tapis_fenetre.py",
    "scripts/coordination/tapis_origami.py",
)

FETCH_TIMEOUT_S = 120

#: Runner injectable : argv + timeout -> (rc, stdout, stderr), tous strippes.
Run = Callable[[list[str], int], tuple[int, str, str]]


def run_defaut(argv: list[str], timeout: int) -> tuple[int, str, str]:
    """Lance une commande bornee ; rend (rc, stdout, stderr) stripes."""
    try:
        out = subprocess.run(argv, capture_output=True, text=True, encoding="utf-8",
                             errors="replace", timeout=timeout, check=False)
    except subprocess.TimeoutExpired:
        return 124, "", f"timeout apres {timeout} s : {' '.join(argv[:4])}"
    except OSError as exc:
        return 127, "", f"commande introuvable : {exc}"
    return out.returncode, out.stdout.strip(), out.stderr.strip()


def _premiere_ligne(err: str) -> str:
    """Premiere ligne d'un stderr git, bornee : c'est elle qui nomme la panne."""
    return err.splitlines()[0][:160] if err else "(sans message)"


def mesurer(depot: str | Path, organes: tuple[str, ...] = ORGANES,
            run: Run = run_defaut) -> dict:
    """La mesure brute : ecart main..origin/main et organes divergents.

    Rend un dict toujours serialisable. `cause` non nul = mesure impossible :
    l'appelant refuse, il ne_vert JAMAIS une mesure qu'il n'a pas pu prendre
    (meme doctrine que session_hygiene.check_fetch).
    """
    depot = Path(depot)
    m: dict = {"depot": str(depot), "branche": None, "ref_mesure": None,
               "ecart": None, "organes_divergents": [], "cause": None}
    git = ["git", "-C", str(depot)]

    rc, _, err = run([*git, "fetch", "-q", "origin", "main"], FETCH_TIMEOUT_S)
    if rc != 0:
        m["cause"] = (f"git fetch origin main a echoue (rc={rc}, {_premiere_ligne(err)}) : "
                      "la fraicheur ne peut pas etre mesuree")
        return m

    rc, out, _ = run([*git, "rev-parse", "--abbrev-ref", "HEAD"], 30)
    if rc == 0:
        m["branche"] = out or "(detache)"

    # References candidates : le main LOCAL (un worktree partage les refs du
    # depot, la branche courante n'y change rien) PUIS le HEAD qui execute.
    # Le tirage ne lit qu'origin/main ; ce qu'il execute est couvert par
    # ORGANE_DIVERGENT. Un worktree cree depuis un origin/main frais est donc
    # a jour meme quand le main partage du clone principal est en retard :
    # retenir le plus petit ecart, et nommer la reference qui l'a donne
    # (mesure du 15/11 : une lane refusee a 381 commits depuis un worktree
    # frais, sans pouvoir toucher le checkout partage).
    rc, out, _ = run([*git, "rev-parse", "--verify", "-q", "refs/heads/main"], 30)
    candidates = (["refs/heads/main"] if rc == 0 and out else []) + ["HEAD"]
    meilleur: tuple[int, str] | None = None
    for ref in candidates:
        rc, out, err = run([*git, "rev-list", "--count", f"{ref}..origin/main"], 60)
        if rc != 0 or not out.strip().isdigit():
            m["ref_mesure"] = ref
            m["cause"] = (f"rev-list --count {ref}..origin/main illisible "
                          f"(rc={rc}, {_premiere_ligne(err) or out[:80]})")
            return m
        ecart = int(out.strip())
        if meilleur is None or ecart < meilleur[0]:
            meilleur = (ecart, ref)
        if ecart == 0:
            break
    m["ecart"], m["ref_mesure"] = meilleur

    rc, out, err = run([*git, "diff", "--name-only", "origin/main", "--", *organes], 60)
    if rc != 0:
        m["cause"] = (f"diff origin/main -- <organes du tirage> illisible "
                      f"(rc={rc}, {_premiere_ligne(err)})")
        return m
    m["organes_divergents"] = [l.strip() for l in out.splitlines() if l.strip()]
    return m


def garder(depot: str | Path, allow_stale: bool = False,
           organes: tuple[str, ...] = ORGANES, run: Run | None = None) -> dict:
    """Le verdict de garde : `refuse` arrete le tirage, `raisons` nomment le remede.

    `outre_passe` est vrai seulement quand un refus a eu lieu ET que
    `allow_stale` l'a explicitement leve : le depassement se lit dans la
    sortie JSON, il ne se prend pas en silence.
    """
    if run is None:
        # Sous pytest, la garde ne touche ni reseau ni depot reel : les tests
        # qui la veulent lui injectent un `run` ou posent MAIN_FRESHNESS_FORCE
        # (memes coutures que le journal de tirage de pick_idle_grain.py).
        if "PYTEST_CURRENT_TEST" in os.environ and not os.environ.get("MAIN_FRESHNESS_FORCE"):
            return {"ok": True, "refuse": False, "outre_passe": False,
                    "raisons": [], "passe": "pytest"}
        run = run_defaut
    m = mesurer(depot, organes=organes, run=run)
    raisons: list[dict] = []
    if m["cause"]:
        raisons.append({"code": "MESURE_IMPOSSIBLE", "motif": m["cause"],
                        "remede": "retablir le fetch (reseau, credential) puis relancer"})
    else:
        if m["ecart"]:
            remede = ("git pull --ff-only" if m["branche"] == "main" else
                      "revenir sur main puis `git pull --ff-only` ; un worktree se "
                      "recree depuis un origin/main a jour")
            raisons.append({"code": "MAIN_PERIME",
                            "motif": (f"le main local est en retard de {m['ecart']} "
                                      "commit(s) sur origin/main"),
                            "remede": remede})
        if m["organes_divergents"]:
            raisons.append({"code": "ORGANE_DIVERGENT",
                            "motif": ("module(s) du tirage differents d'origin/main : "
                                      + ", ".join(m["organes_divergents"])),
                            "remede": ("remettre ces fichiers a leur version d'origin/main "
                                       "puis rejouer le tirage")})
    return {**m, "ok": not raisons, "allow_stale": bool(allow_stale),
            "refuse": bool(raisons and not allow_stale),
            "outre_passe": bool(raisons and allow_stale),
            "raisons": raisons}


def garder_et_dire(depot: str | Path, allow_stale: bool = False) -> dict:
    """La garde et son rendu pour le tapis : le verdict tel quel, imprime.

    Le refus va sur ses deux canaux -- chaque raison sur stderr avec son
    remede, le verdict complet en JSON sur stdout -- et l'appelant (le point
    d'entree du tapis) rend le code 4, distinct du 3 « lecture incomplete » ;
    aucun des deux ne renvoie au tapis lourd (#26926). Un
    outrepasse `--allow-stale` se dit sur stderr : il ne se prend pas en
    silence. Le tapis attache ensuite le verdict au rapport JSON (`fraicheur`).
    """
    v = garder(depot, allow_stale=allow_stale)
    if v["refuse"]:
        for r in v["raisons"]:
            print(f"TIRAGE REFUSE [{r['code']}] : {r['motif']} -- remede : {r['remede']}",
                  file=sys.stderr)
        sys.stdout.buffer.write((json.dumps(v, ensure_ascii=False, indent=1)
                                 + "\n").encode("utf-8"))
    if v.get("outre_passe"):
        print("TIRAGE SUR UN ETAT PERIME (--allow-stale) : "
              + " ; ".join(r["motif"] for r in v["raisons"]), file=sys.stderr)
    return v


def _texte(v: dict) -> str:
    if v.get("passe") == "pytest":
        return "garde inactive sous pytest (MAIN_FRESHNESS_FORCE pour la forcer)"
    lignes = [f"fraicheur -- depot {v.get('depot')} -- branche {v.get('branche')} "
              + f"-- reference mesuree {v.get('ref_mesure')}"]
    if v.get("cause"):
        lignes.append(f"MESURE IMPOSSIBLE : {v['cause']}")
    if v.get("ecart") is not None:
        lignes.append(f"ecart main..origin/main : {v['ecart']} commit(s)")
    for r in v.get("raisons") or []:
        lignes.append(f"[{r['code']}] {r['motif']}")
        lignes.append(f"  remede : {r['remede']}")
    if v.get("outre_passe"):
        lignes.append("OUTRE-PASSE par --allow-stale : le tirage rend des grains "
                      + "sur un etat perime, en connaissance de cause.")
    if v.get("ok") and not v.get("raisons"):
        lignes.append("OK : clone frais, organes conformes a origin/main.")
    return "\n".join(lignes)


def main(argv: list[str] | None = None) -> int:
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="replace")
    ap = argparse.ArgumentParser(
        description="Garde de fraicheur du tirage : refuse sur un main local "
                    "en retard ou un organe divergent d'origin/main.")
    ap.add_argument("--repo", default=".", help="depot a mesurer (defaut : cwd)")
    ap.add_argument("--allow-stale", action="store_true",
                    help="outre-passer le refus, explicitement (dit dans le JSON)")
    ap.add_argument("--json", action="store_true", help="sortie structuree")
    args = ap.parse_args(argv)
    v = garder(Path(args.repo), allow_stale=args.allow_stale)
    out = json.dumps(v, ensure_ascii=False, indent=1) if args.json else _texte(v)
    sys.stdout.buffer.write((out + "\n").encode("utf-8"))
    return 1 if v["refuse"] else 0


if __name__ == "__main__":
    sys.exit(main())

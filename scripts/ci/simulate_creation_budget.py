#!/usr/bin/env python3
"""Simulation du budget de creation (#23174) — replay d'une semaine.

L'issue impose une simulation AVANT tout merge : « replay de la semaine
21-28/10 dans le body (ce que le budget aurait servi/écarté, combien de
carnets neufs auraient démarré, ce que la garde de provenance aurait
signalé) + contrôle négatif : aucune issue de `consolidation` ou de
correction ne peut être écarté ».

Ce script rejoue une fenetre et rend trois choses :

  1. **Le rejeu du compteur.** Jour par jour, le compteur de carnets neufs
     demarres sur 7 jours glissants est comparé au budget. La simulation
     ne laisse pas monter le compteur au-dela du budget : un carnet neuf
     ecarte ne demarre pas. Le resultat est le nombre de carnets neufs
     qui auraient demarre SOUS le regime, et ceux qui n'auraient pas.

  2. **Le controle negatif.** Les grains ecartees par la porte sont
     listes, et le script verifie qu'aucune d'eux n'est une issue de
     consolidation ni de correction : une porte qui ecarterait un grain de
     reparation viderait le tapis de son travail. Le controle est
     MECANIQUE (le veto l'emporte), et son resultat est affiche pour etre
     relu.

  3. **La garde de provenance.** Combien de PRs ajoutant un carnet neuf
     auraient ete signalees par la garde (issue servie de plus de 48 h, ou
     issue jamais servie par un tirage) — avec le detail par tranche
     d'age.

Usage :

    python scripts/ci/simulate_creation_budget.py \\
        --since 2026-10-21 --until 2026-10-28
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import pathlib
import re
import subprocess
import sys

SCRIPTS_DIR = pathlib.Path(__file__).resolve().parent.parent
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

import creation_budget as cb  # noqa: E402

REPO = "jsboige/CoursIA"
DEFAULT_REF = "origin/main"

# L'age minimal d'une issue servie, en heures, sous lequel la garde de
# provenance signale la PR (issue #23174 : « creee au moins 48 h avant la PR »).
PROVENANCE_HOURS = 48

# Les formes de reference d'une issue servie dans le body d'une PR.
_SERVED_RE = re.compile(
    r"(?i)\b(?:closes|see|part of|fixes|refs)\s+#(\d+)")


def _run(cmd: list[str], timeout: int = 300) -> str:
    out = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8",
                         timeout=timeout, check=False)
    if out.returncode != 0:
        raise RuntimeError(f"{cmd[0]} a echoue : {(out.stderr or '').strip()[:300]}")
    return out.stdout


def new_notebooks_by_day(repo_root: str, ref: str, since: dt.datetime,
                         until: dt.datetime) -> dict[str, int]:
    """Les `.ipynb` AJOUTES sur `ref`, jour par jour (date de commit)."""
    out = _run(["git", "-C", repo_root, "log", "--diff-filter=A",
                "--name-only", "--date=format:%Y-%m-%d",
                "--pretty=format:%ad", f"--since={since:%Y-%m-%d}",
                f"--until={until:%Y-%m-%d}", ref, "--", "*.ipynb"])
    par_jour: dict[str, int] = {}
    jour = None
    vus: set[str] = set()
    for line in out.splitlines():
        line = line.strip()
        if not line:
            continue
        if re.fullmatch(r"\d{4}-\d{2}-\d{2}", line):
            jour = line
            continue
        if jour and line.endswith(".ipynb") and line not in vus:
            vus.add(line)
            par_jour[jour] = par_jour.get(jour, 0) + 1
    return par_jour


def replay(par_jour: dict[str, int], budget: int, jours: list[str],
           fenetre: int = 7) -> dict:
    """Le rejeu du compteur, jour par jour.

    Le compteur porte sur une fenetre glissante de `fenetre` jours. Un
    carnet neuf ecarte ne demarre pas : le compteur simule ne monte donc
    jamais au-dela du budget tant que la fenetre n'a pas turné.
    """
    servis = 0
    simules: dict[str, int] = {}
    ecartes: dict[str, int] = {}
    serie_servis: list[int] = []
    for i, j in enumerate(jours):
        n = par_jour.get(j, 0)
        # compteur des `fenetre - 1` jours precedents (la fenetre glissante
        # comprend le jour courant, qui n'est pas encore servi)
        avant = sum(serie_servis[max(0, i - fenetre + 1):i])
        place = max(0, budget - avant)
        s = min(n, place)
        servis += s
        ecartes[j] = n - s
        simules[j] = s
        serie_servis.append(s)
    return {
        "par_jour": {j: {"nouveaux": par_jour.get(j, 0),
                         "servis": simules.get(j, 0),
                         "ecartes": ecartes.get(j, 0)} for j in jours},
        "carnets_neufs_servis": servis,
        "carnets_neufs_ecartes": sum(ecartes.values()),
        "carnets_neufs_reels": sum(par_jour.get(j, 0) for j in jours),
    }


def controle_negatif(pool: list[dict], catalog: cb.NotebookCatalog) -> dict:
    """Le controle negatif : aucune issue de consolidation ou de correction
    n'est ecartee par la porte.

    Le veto est deja dans le code (`_RE_REPAIR`) ; ce controle le MESURE sur
    le pool reel et affiche la liste des ecartees, pour qu'un lecteur puisse
    la relire ligne a ligne.
    """
    index = cb.build_children_index(pool)
    ecartees = []
    for it in pool:
        verdict, why = cb.classify_grain(it, catalog, pool, index)
        if verdict == cb.VERDICT_CREATION:
            ecartees.append({"number": it["number"], "title": it.get("title"),
                             "labels": cb.labels_of(it), "motif": why})
    coupables = [e for e in ecartees
                  if cb._RE_REPAIR.search(e["title"] or "")
                  or "consolidation" in e["labels"]]
    return {
        "ecartees": ecartees,
        "nombre_ecartees": len(ecartees),
        "coupables": coupables,
        "verdict": "OK" if not coupables else "ECHEC",
    }


def garde_provenance(since: dt.datetime, until: dt.datetime) -> dict:
    """Ce que la garde de provenance aurait signale.

    Une PR qui ajoute un carnet neuf est signalee si l'issue servie a ete
    creee depuis MOINS de 48 h, ou si aucune issue n'est servie. Le second
    cas est signale a part : il n'est pas un Age, c'est une absence de
    service — et c'est elle que le tirage du tapis (draw_id) couvre.
    """
    lo = since.strftime("%Y-%m-%d")
    hi = until.strftime("%Y-%m-%d")
    prs = json.loads(_run(["gh", "pr", "list", "--repo", REPO, "--state", "all",
                           "--search", f"created:{lo}..{hi}", "--limit", "1000",
                           "--json", "number,author,createdAt,body,files"]))
    fleet = [p for p in prs
             if (p.get("author") or {}).get("login", "").startswith(("jsboige", "myia-"))]
    # Seules les PRs qui AJOUTENT un carnet neuf comptent. Le listing
    # `gh pr list --json files` ne donne pas le statut ; c'est l'API des
    # fichiers de la PR qui porte `status` (`added` / `renamed` / ...).
    # Un carnet MODIFIE n'est pas un carnet neuf : le compter comme tel
    # gonflerait le denominateur de la mesure (constate : 507 PRs au lieu
    # de 126 sur la meme fenetre).
    avec_carnet = []
    for p in fleet:
        if not any((f.get("path") or "").endswith(".ipynb")
                   for f in (p.get("files") or [])):
            continue
        try:
            fichiers = json.loads(_run(["gh", "api",
                                        f"repos/{REPO}/pulls/{p['number']}/files"]))
        except Exception:  # noqa: BLE001 - fichiers illisibles = PR non mesuree
            continue
        ajoutes = [f.get("filename") for f in fichiers
                   if (f.get("filename") or "").endswith(".ipynb")
                   and f.get("status") == "added"
                   and not (f.get("filename") or "").endswith("_en.ipynb")]
        if ajoutes:
            avec_carnet.append((p, ajoutes))

    ages = {"moins_48h": 0, "plus_48h": 0, "sans_issue_servie": 0}
    sans_issue = 0
    prs_ajoutees = 0
    for p, _fichiers in avec_carnet:
        prs_ajoutees += 1
        m = _SERVED_RE.search(p.get("body") or "")
        if not m:
            ages["sans_issue_servie"] += 1
            sans_issue += 1
            continue
        num = int(m.group(1))
        try:
            issue = json.loads(_run(["gh", "issue", "view", str(num), "--repo", REPO,
                                     "--json", "createdAt"]))
        except Exception:  # noqa: BLE001 - issue illisible = age non mesure
            continue
        created = dt.datetime.fromisoformat(
            issue["createdAt"])
        age_h = (dt.datetime.fromisoformat(p["createdAt"])
                 - created).total_seconds() / 3600.0
        if age_h < PROVENANCE_HOURS:
            ages["moins_48h"] += 1
        else:
            ages["plus_48h"] += 1
    signalees = ages["moins_48h"] + ages["sans_issue_servie"]
    return {
        "prs_flotte_avec_carnet_neuf": prs_ajoutees,
        "signalees": signalees,
        "detail": ages,
        "seuil_heures": PROVENANCE_HOURS,
    }


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Simulation du budget de creation")
    ap.add_argument("--since", default="2026-10-21")
    ap.add_argument("--until", default="2026-10-28")
    ap.add_argument("--repo-root", default=".")
    ap.add_argument("--ref", default=DEFAULT_REF)
    ap.add_argument("--budget", type=int, default=None,
                    help="forcer le budget (defaut : derive de la mesure)")
    ap.add_argument("--json", default=None, help="ecrire le rapport JSON ici")
    ap.add_argument("--skip-provenance", action="store_true",
                    help="ne pas lire les PRs (mesure lente, ~1 req/PR)")
    args = ap.parse_args(argv)

    since = dt.datetime.fromisoformat(args.since).replace(tzinfo=dt.UTC)
    until = dt.datetime.fromisoformat(args.until).replace(tzinfo=dt.UTC)

    catalog = cb.NotebookCatalog.from_repo(args.repo_root, args.ref)
    par_jour = new_notebooks_by_day(args.repo_root, args.ref, since, until)

    budget = args.budget
    if budget is None:
        import creation_budget_counter as counter
        pool = counter.open_pool()
        livres = counter.closed_issues(since, until)
        budget, preuve = cb.derive_budget(pool, livres, catalog)
    else:
        pool = []
        preuve = {}

    jours = []
    jour = since
    while jour <= until:
        jours.append(jour.strftime("%Y-%m-%d"))
        jour += dt.timedelta(days=1)

    r = replay(par_jour, budget, jours)
    r["budget"] = budget
    r["preuve_budget"] = preuve

    import creation_budget_counter as counter
    r["controle_negatif"] = controle_negatif(counter.open_pool(), catalog)

    if not args.skip_provenance:
        r["garde_provenance"] = garde_provenance(since, until)

    print(f"fenetre {args.since} -> {args.until} | budget {budget}")
    for j in jours:
        d = r["par_jour"][j]
        print(f"  {j}  nouveaux {d['nouveaux']:>3}  servis {d['servis']:>3}  "
              f"ecartes {d['ecartes']:>3}")
    print(f"carnets neufs reels {r['carnets_neufs_reels']} -> servis sous le "
          f"regime {r['carnets_neufs_servis']} "
          f"(ecartes {r['carnets_neufs_ecartes']})")
    cn = r["controle_negatif"]
    print(f"controle negatif : {cn['nombre_ecartees']} grain(s) de creation "
          f"ecarte(s) sur le pool, {len(cn['coupables'])} consolidation/"
          f"correction -> {cn['verdict']}")
    if "garde_provenance" in r:
        gp = r["garde_provenance"]
        print(f"garde de provenance : {gp['signalees']} PR(s) signalee(s) sur "
              f"{gp['prs_flotte_avec_carnet_neuf']} PR(s) de flotte ajoutant un "
              f"carnet neuf (detail {gp['detail']})")

    if args.json:
        pathlib.Path(args.json).write_text(
            json.dumps(r, ensure_ascii=False, indent=2, default=str) + "\n",
            encoding="utf-8")
    return 0 if cn["verdict"] == "OK" else 1


if __name__ == "__main__":
    raise SystemExit(main())

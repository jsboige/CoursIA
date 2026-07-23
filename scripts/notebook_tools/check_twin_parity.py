#!/usr/bin/env python3
"""Detecte la derive des jumeaux Python/C# depuis le registre de parite (#8057).

Pourquoi cet outil existe
-------------------------
La campagne de **jumeaux Python/C#** est devenue structurante (Search/CSP,
ML.NET + pendants Python, SemanticWeb, Planners, Z3/SMT : des dizaines de
paires). Une **parite de surface** peut masquer une derive silencieuse : un
notebook evolue (fix, enrichissement, re-exec) tandis que son jumeau reste a
l'etat anterieur, et les deux implimentations derivent separement sans que
personne ne re-audite la parite. Aujourd'hui la parite est **declarative**
(des notes eparses dans des READMEs) ; ce outil la rend **auditable**.

Le registre `twin_pairs.yaml` (a cote de ce script) decrit chaque paire :
le chemin des deux notebooks, le `parity_level` (surface | semantic |
native-both), le `last_audit` (date, auteur, et le **git blob SHA** de chaque
notebook au moment de l'audit) et les `known_differences` documentees.

Comment ca marche
-----------------
Pour chaque paire du registre, on :
  1. lit le **git blob SHA courant** de chaque notebook via `git ls-tree HEAD`
     (le contenu versionne, pas le working tree — reproductible) ;
  2. compare le SHA courant au `last_audit.{python,csharp}_sha` enregistre ;
  3. **DRIFT** si l'un des deux a change depuis le dernier audit -> la paire
     doit etre re-auditee (un cote a evolue, la parite n'est plus garantie) ;
  4. **MISSING** si le chemin n'existe pas dans git (typo, deplacement, jumeau
     non cree) ;
  5. **OK** sinon (les deux cotes sont au SHA audite, parite tenue).

Le bouclage d'audit : apres avoir re-audite une paire firsthand, on rebaseline
avec `--update` qui reecrit les SHAs courants comme nouvelle reference.

Cet outil lit seulement par defaut (git ls-tree). Le mode `--update` ecrit le
registre (curated YAML, pas un notebook -> pas de souci de re-exec C.2).

Usage
-----
    # verifier toutes les paires vs le registre
    python check_twin_parity.py
    # exit 1 si drift/missing (CI-ready)
    python check_twin_parity.py --check
    # restreindre a une famille
    python check_twin_parity.py --family SMT/Z3-API
    # rebaseline apres audit firsthand (ecrit les SHAs courants)
    python check_twin_parity.py --update
    # sortie machine
    python check_twin_parity.py --json

Exit codes
----------
    0 -- toutes les paires OK (ou mode non --check)
    1 -- un ou plusieurs DRIFT / MISSING (--check seulement)
    2 -- erreur (registre illisible, pas un depot git)

Voir aussi
----------
- twin_pairs.yaml (registre curated, a cote de ce script)
- Issue #8057 (metadonnee de parite des jumeaux Python/C#)
- Issue #4208 (parent : open-courseware fiabilise/publie)
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

try:
    import yaml
except ImportError:  # pragma: no cover
    yaml = None

DEFAULT_REGISTRY = Path(__file__).resolve().parent / "twin_pairs.yaml"


def _git_blob_sha(repo_root: Path, rel_path: str) -> str | None:
    """Git blob SHA d'un fichier versionne a HEAD (None si absent)."""
    r = subprocess.run(
        ["git", "ls-tree", "HEAD", "--", rel_path],
        capture_output=True, text=True, cwd=str(repo_root),
    )
    if r.returncode != 0 or not r.stdout.strip():
        return None
    # format : "<mode> <type> <blob_sha>\t<path>"
    parts = r.stdout.split()
    if len(parts) >= 3:
        return parts[2]
    return None


def _repo_root() -> Path:
    r = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True, text=True,
    )
    if r.returncode != 0:
        raise SystemExit("Erreur : pas un depot git (impossible de trouver la racine).")
    return Path(r.stdout.strip())


def load_registry(path: Path) -> list:
    if path is None or not path.exists():
        raise SystemExit(f"Erreur : registre introuvable : {path}")
    if yaml is None:
        raise SystemExit("Erreur : PyYAML requis (pip install pyyaml).")
    data = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(data, list):
        raise SystemExit("Erreur : le registre doit etre une liste de paires.")
    return data


def check_pair(repo_root: Path, pair: dict) -> dict:
    """Verifie une paire. Retourne {name, python, csharp, status, details}.

    status in {OK, DRIFT, MISSING}. details = liste de chaines explicatives.
    """
    name = pair.get("name", "?")
    py = pair["python"]
    cs = pair["csharp"]
    audit = pair.get("last_audit", {}) or {}
    rec_py = audit.get("python_sha")
    rec_cs = audit.get("csharp_sha")

    cur_py = _git_blob_sha(repo_root, py)
    cur_cs = _git_blob_sha(repo_root, cs)

    details = []
    status = "OK"

    if cur_py is None:
        details.append(f"Python MANQUANT dans git : {py}")
        status = "MISSING"
    if cur_cs is None:
        details.append(f"C# MANQUANT dans git : {cs}")
        status = "MISSING"

    if status == "OK":
        py_drift = (rec_py is not None and cur_py != rec_py)
        cs_drift = (rec_cs is not None and cur_cs != rec_cs)
        no_baseline = (rec_py is None or rec_cs is None)
        if py_drift:
            details.append(f"Python a drift : {rec_py[:8]} -> {cur_py[:8]}")
        if cs_drift:
            details.append(f"C# a drift : {rec_cs[:8]} -> {cur_cs[:8]}")
        if no_baseline:
            details.append("Pas de last_audit_sha enregistre (--update requis)")
        if py_drift or cs_drift or no_baseline:
            status = "DRIFT"

    return {
        "name": name,
        "family": pair.get("family", "?"),
        "python": py,
        "csharp": cs,
        "parity_level": pair.get("parity_level", "?"),
        "status": status,
        "current_python_sha": cur_py,
        "current_csharp_sha": cur_cs,
        "recorded_python_sha": rec_py,
        "recorded_csharp_sha": rec_cs,
        "last_audit_date": audit.get("date"),
        "last_audit_by": audit.get("by"),
        "details": details,
    }


def update_pair(repo_root: Path, pair: dict) -> tuple[dict, str | None]:
    """Rebaseline une paire : enregistre les SHAs courants comme nouvelle ref.

    Retourne (last_audit_dict mis a jour, sha_utilise_pour_python ou None si missing).
    """
    py = pair["python"]
    cs = pair["csharp"]
    cur_py = _git_blob_sha(repo_root, py)
    cur_cs = _git_blob_sha(repo_root, cs)
    today = pair.get("last_audit", {}).get("date")  # conserve si deja la
    by = pair.get("last_audit", {}).get("by", "manual")
    audit = {
        "date": today,
        "by": by,
        "python_sha": cur_py,
        "csharp_sha": cur_cs,
    }
    return audit, cur_py


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    p.add_argument("--registry", default=str(DEFAULT_REGISTRY),
                   help=f"Chemin du registre YAML (defaut: {DEFAULT_REGISTRY.name})")
    p.add_argument("--family", default=None,
                   help="Restreindre a une famille (ex. SMT/Z3-API)")
    p.add_argument("--check", action="store_true",
                   help="Exit 1 si DRIFT/MISSING detecte (CI-ready)")
    p.add_argument("--update", action="store_true",
                   help="Rebaseline : ecrit les SHAs courants comme nouveau last_audit "
                        "(a lancer APRES une audit firsthand d'une paire)")
    p.add_argument("--json", action="store_true", help="Sortie machine JSON")
    args = p.parse_args(argv)

    repo_root = _repo_root()
    reg_path = Path(args.registry)
    pairs = load_registry(reg_path)

    if args.family:
        pairs = [pp for pp in pairs if pp.get("family") == args.family]
        if not pairs:
            print(f"Aucune paire pour la famille '{args.family}'.", file=sys.stderr)

    if args.update:
        # rebaseline toutes les paires (ou filtrees par --family)
        updated = 0
        for pp in pairs:
            audit, cur_py = update_pair(repo_root, pp)
            if cur_py is not None:
                pp["last_audit"] = audit
                updated += 1
        # re-ecrit le registre entier (conserve l'ordre + les autres paires)
        if yaml is None:
            raise SystemExit("Erreur : PyYAML requis pour --update.")
        reg_path.write_text(
            yaml.safe_dump(pairs, sort_keys=False, allow_unicode=True, width=100),
            encoding="utf-8",
        )
        msg = f"Registre rebaseline : {updated} paire(s) mise(s) a jour -> {reg_path}"
        print(msg)
        return 0

    results = [check_pair(repo_root, pp) for pp in pairs]
    n_ok = sum(1 for r in results if r["status"] == "OK")
    n_drift = sum(1 for r in results if r["status"] == "DRIFT")
    n_missing = sum(1 for r in results if r["status"] == "MISSING")

    if args.json:
        out = {
            "registry": str(reg_path),
            "total": len(results),
            "ok": n_ok,
            "drift": n_drift,
            "missing": n_missing,
            "pairs": results,
        }
        print(json.dumps(out, ensure_ascii=False, indent=2))
    else:
        for r in results:
            tag = {"OK": "OK", "DRIFT": "DRIFT", "MISSING": "MISSING"}[r["status"]]
            print(f"[{tag}] {r['name']} ({r['family']}, {r['parity_level']})")
            if r["status"] != "OK":
                for d in r["details"]:
                    print(f"       - {d}")
        print(f"\nTotal : {len(results)} paire(s) | OK={n_ok} DRIFT={n_drift} MISSING={n_missing}")

    if args.check and (n_drift > 0 or n_missing > 0):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())

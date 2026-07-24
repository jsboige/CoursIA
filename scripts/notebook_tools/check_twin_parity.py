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
    # exit 1 si drift/missing (CI-ready, mode historique fleet-wide)
    python check_twin_parity.py --check
    # restreindre a une famille
    python check_twin_parity.py --family SMT/Z3-API
    # rebaseline apres audit firsthand (ecrit les SHAs courants)
    python check_twin_parity.py --update
    # sortie machine
    python check_twin_parity.py --json
    # mode per-pair : ne FAIL que sur le drift INTRODUIT par la PR en cours
    # (paire OK au base-ref mais DRIFT au HEAD). Necessite --base <ref>.
    # Compare le registre+blobs au base-ref (avant la PR) vs au HEAD (apres la PR).
    # Le drift pre-existant (deja present au base-ref) n'est PAS comptabilise ici
    # -- il releve d'une PR de rebaseline dediee (cf #8264 batch precedent).
    python check_twin_parity.py --check --per-pair --base origin/main
    python check_twin_parity.py --check --per-pair --base HEAD~1

Exit codes
----------
    0 -- toutes les paires OK (ou mode non --check), ou zero nouveau drift en --per-pair
    1 -- un ou plusieurs DRIFT / MISSING (mode --check fleet-wide)
         OU nouveau(s) DRIFT introduit(s) par la PR (mode --check --per-pair)
    2 -- erreur (registre illisible, pas un depot git)

Voir aussi
----------
- twin_pairs.yaml (registre curated, a cote de ce script)
- Issue #8057 (metadonnee de parite des jumeaux Python/C#)
- Issue #8264 (batch rebaseline precedent -- pattern DRIFT pre-existant)
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


def _git_blob_sha(repo_root: Path, rel_path: str, git_ref: str = "HEAD") -> str | None:
    """Git blob SHA d'un fichier versionne a `git_ref` (defaut: HEAD, None si absent).

    Accepte un ref arbitraire (HEAD, origin/main, HEAD~1, <sha>, ...) -- permet de
    lire l'etat du depot a un instant donne sans modifier le working tree.
    """
    r = subprocess.run(
        ["git", "ls-tree", git_ref, "--", rel_path],
        capture_output=True, text=True, cwd=str(repo_root),
    )
    if r.returncode != 0 or not r.stdout.strip():
        return None
    # format : "<mode> <type> <blob_sha>\t<path>"
    parts = r.stdout.split()
    if len(parts) >= 3:
        return parts[2]
    return None


def _git_show_file(repo_root: Path, git_ref: str, rel_path: str) -> str | None:
    """Contenu d'un fichier versionne a `git_ref` (None si absent).

    Utilise `git show <ref>:<path>` (mode stream), evite de checkout le working tree.
    Necessaire pour lire le registre YAML au base-ref sans polluer le workspace CI.
    """
    r = subprocess.run(
        ["git", "show", f"{git_ref}:{rel_path}"],
        capture_output=True, cwd=str(repo_root),
    )
    if r.returncode != 0:
        return None
    return r.stdout.decode("utf-8", errors="replace")


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


def check_pair(repo_root: Path, pair: dict, git_ref: str = "HEAD") -> dict:
    """Verifie une paire. Retourne {name, python, csharp, status, details}.

    status in {OK, DRIFT, MISSING}. details = liste de chaines explicatives.
    `git_ref` permet de checker a un instant arbitraire (HEAD, origin/main, <sha>...).
    """
    name = pair.get("name", "?")
    py = pair["python"]
    cs = pair["csharp"]
    audit = pair.get("last_audit", {}) or {}
    rec_py = audit.get("python_sha")
    rec_cs = audit.get("csharp_sha")

    cur_py = _git_blob_sha(repo_root, py, git_ref)
    cur_cs = _git_blob_sha(repo_root, cs, git_ref)

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
    p.add_argument("--per-pair", action="store_true",
                   help="Mode per-pair : compare HEAD vs --base <ref>. Ne FAIL que "
                        "le drift INTRODUIT par la PR, jamais le drift pre-existant.")
    p.add_argument("--base", default=None,
                   help="Ref git de base pour le mode --per-pair (ex. origin/main, HEAD~1).")
    args = p.parse_args(argv)

    # Cross-validation : --per-pair <-> --base
    if args.per_pair and not args.base:
        p.error("--per-pair necessite --base <ref>")
    if args.base and not args.per_pair:
        p.error("--base necessite --per-pair")
    if args.update and (args.per_pair or args.base):
        p.error("--update est incompatible avec --per-pair/--base")

    repo_root = _repo_root()
    reg_path = Path(args.registry)

    # --- Mode --per-pair : comparaison HEAD vs base-ref ---
    if args.per_pair:
        # Charge le registre a HEAD (working tree) et au base-ref (git show)
        pairs_head = load_registry(reg_path)
        # reg_path peut etre absolu ou relatif -- on prend toujours le path
        # relatif au repo_root pour `git show <ref>:<relpath>`.
        # IMPORTANT : on normalise en forward-slashes (git sur Windows
        # refuse les backslashes dans `<ref>:<path>`).
        try:
            reg_rel = reg_path.resolve().relative_to(repo_root).as_posix()
        except ValueError:
            # reg_path n'est pas sous repo_root : on tente quand meme avec son nom
            reg_rel = Path(reg_path.name).as_posix()
        reg_text_base = _git_show_file(repo_root, args.base, reg_rel)
        if reg_text_base is None:
            raise SystemExit(f"Impossible de lire le registre au base-ref '{args.base}' : {reg_rel}")
        if yaml is None:
            raise SystemExit("PyYAML requis pour --per-pair.")
        data_base = yaml.safe_load(reg_text_base)
        if not isinstance(data_base, list):
            raise SystemExit("Le registre au base-ref n'est pas une liste.")
        pairs_base = data_base
        # Index par nom (au cas ou l'ordre ou les ajouts/suppressions different)
        base_by_name = {pp.get("name", "?"): pp for pp in pairs_base}

        if args.family:
            pairs_head = [pp for pp in pairs_head if pp.get("family") == args.family]
            if not pairs_head:
                print(f"Aucune paire pour la famille '{args.family}'.", file=sys.stderr)

        results = []
        for pp in pairs_head:
            name = pp.get("name", "?")
            head_state = check_pair(repo_root, pp, git_ref="HEAD")
            base_pp = base_by_name.get(name)
            if base_pp is None:
                # Paire ajoutee par la PR -> si elle n'est PAS OK au HEAD, c'est du drift introduit
                base_status = "MISSING"
                base_details = [f"Paire '{name}' absente du registre au base-ref '{args.base}' (ajoutee par la PR)"]
            else:
                base_check = check_pair(repo_root, base_pp, git_ref=args.base)
                base_status = base_check["status"]
                base_details = base_check["details"]

            head_status = head_state["status"]
            # Classification per-pair
            if base_status == "OK" and head_status == "OK":
                verdict = "OK"
            elif base_status == "OK" and head_status in ("DRIFT", "MISSING"):
                verdict = "DRIFT_INTRODUCED"
            elif base_status in ("DRIFT", "MISSING") and head_status == "OK":
                verdict = "DRIFT_RESOLVED"
            else:
                verdict = "DRIFT_PRE_EXISTING"

            results.append({
                "name": name,
                "family": pp.get("family", "?"),
                "parity_level": pp.get("parity_level", "?"),
                "base_ref": args.base,
                "base_status": base_status,
                "head_status": head_status,
                "verdict": verdict,
                "base_details": base_details,
                "head_details": head_state["details"],
            })

        n_ok = sum(1 for r in results if r["verdict"] == "OK")
        n_introduced = sum(1 for r in results if r["verdict"] == "DRIFT_INTRODUCED")
        n_resolved = sum(1 for r in results if r["verdict"] == "DRIFT_RESOLVED")
        n_pre_existing = sum(1 for r in results if r["verdict"] == "DRIFT_PRE_EXISTING")

        if args.json:
            out = {
                "mode": "per_pair",
                "registry": str(reg_path),
                "base_ref": args.base,
                "total": len(results),
                "ok": n_ok,
                "drift_introduced": n_introduced,
                "drift_resolved": n_resolved,
                "drift_pre_existing": n_pre_existing,
                "pairs": results,
            }
            print(json.dumps(out, ensure_ascii=False, indent=2))
        else:
            tag_map = {
                "OK": "OK",
                "DRIFT_INTRODUCED": "DRIFT-INTRO",
                "DRIFT_RESOLVED": "DRIFT-FIXED",
                "DRIFT_PRE_EXISTING": "DRIFT-PRE",
            }
            for r in results:
                tag = tag_map[r["verdict"]]
                print(f"[{tag}] {r['name']} ({r['family']}, {r['parity_level']}) "
                      f"base={r['base_status']} head={r['head_status']}")
                if r["verdict"] != "OK":
                    for d in r["head_details"]:
                        print(f"       HEAD: {d}")
            print(f"\nTotal : {len(results)} paire(s) | "
                  f"OK={n_ok} INTRO={n_introduced} FIXED={n_resolved} PRE={n_pre_existing}")

        if args.check and n_introduced > 0:
            return 1
        return 0

    # --- Mode historique (fleet-wide) ---
    pairs = load_registry(reg_path)

    if args.family:
        pairs = [pp for pp in pairs if pp.get("family") == args.family]
        if not pairs:
            print(f"Aucune paire pour la famille '{args.family}'.", file=sys.stderr)

    if args.update:
        # IMPORTANT : --update DOIT TOUJOURS reecrire TOUTES les paires du
        # registre (meme avec --family), sinon on DETRUIT les paires des
        # autres familles en re-ecrivant le YAML filtre. On ne met a jour
        # que les paires qui matchent le filtre (ou toutes si pas de filtre).
        all_pairs = load_registry(reg_path)
        target = (
            [pp for pp in all_pairs if pp.get("family") == args.family]
            if args.family else all_pairs
        )
        if args.family and not target:
            print(f"Aucune paire pour la famille '{args.family}'.", file=sys.stderr)
        updated = 0
        for pp in target:
            audit, cur_py = update_pair(repo_root, pp)
            if cur_py is not None:
                pp["last_audit"] = audit
                updated += 1
        # re-ecrit le registre ENTIER (conserve l'ordre + les autres paires)
        if yaml is None:
            raise SystemExit("Erreur : PyYAML requis pour --update.")
        reg_path.write_text(
            yaml.safe_dump(all_pairs, sort_keys=False, allow_unicode=True, width=100),
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

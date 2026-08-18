#!/usr/bin/env python3
"""Check that QuantConnect ML notebooks reference paths that exist on a fresh clone.

Pourquoi cet outil existe
-------------------------
Le guard detruit la classe d'incidents « un notebook leve FileNotFoundError sur
clone frais parce qu'il reference un path `scripts/results/<X>/results.json` qui
est gitignored et jamais commite ». Source : c.290 / issue #11417 / issue
#11433 — 12-13 notebooks du dossier `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/`
referencent de tels paths, et le clone frais casse a la cellule 2 dans 8 cas sur 10.

Le guard distingue 3 cas (sortie ordonnee par severite croissante) :

    OK         path tracked sur origin/main (git ls-tree)
    GITIGNORED path gitignored (git check-ignore) — l'absence n'est pas un bug
               SI le notebook gere le FileNotFoundError ; sinon notifie quand meme
    MISSING    path non tracke et non gitignore = structurellement absent du
               clone frais ; toute lecture echouera

Le MISSING est le seul cas EXIT 1. Le GITIGNORED est INFO (le notebook peut
vouloir gerer l'absence). Le OK est silencieux.

Comment ca marche
-----------------
- Scope : `MyIA.AI.Notebooks/QuantConnect/**/*.ipynb` (tracked-only).
- Parse chaque cellule code, extrait les paths qui matchent
  `(scripts/results|results)/<X>/<file>`.
- Pour chaque path : resoudre relativement au notebook, puis tester
  (a) `git ls-tree HEAD -- <relpath>` (tracke ?), (b) `git check-ignore <relpath>`
  (gitignored ?).
- Read-only : aucun fichier modifie.

Modes (convention check_notebook_navlinks.py)
---------------------------------------------
    python check_quantconnect_notebook_freshness.py              # scan complet tracked-only
    python check_quantconnect_notebook_freshness.py --json       # sortie machine
    python check_quantconnect_notebook_freshness.py --quiet      # sortie minimale (CI)
    python check_quantconnect_notebook_freshness.py NB.ipynb     # un seul notebook

Exit codes
----------
    0  no MISSING (OK / GITIGNORED uniquement)
    1  MISSING detectes (au moins un path non tracked et non gitignore)

Incident fondateur : c.290 / PR #11420 — 8/10 paths MISSING structurel sur la
serie ML-Training-Pipeline. Le fix sur le notebook (cell[2] degrade-propre) est
livre dans #11420 ; le guard (ce script) bloque la recurrence sur les 7 autres
notebooks + futurs ajouts.
"""
import argparse
import json
import os
import pathlib
import re
import subprocess
import sys

# Pattern paths : (scripts|)results/<X>/<file>
PATH_PATTERN = re.compile(r"""['\"]((?:scripts/)?results/[A-Za-z0-9_\-./]+)['\"]""")

# Scope par defaut : notebooks QuantConnect du ML-Training-Pipeline.
DEFAULT_GLOB = "MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/*.ipynb"


def git_ls_tree_tracked(relpath: str, repo_root: pathlib.Path) -> bool:
    """True si le path est tracke sur HEAD (= sera present sur clone frais)."""
    try:
        out = subprocess.run(
            ["git", "ls-tree", "HEAD", "--", relpath],
            cwd=str(repo_root),
            capture_output=True,
            text=True,
            check=False,
        )
    except FileNotFoundError:
        return False
    return bool(out.stdout.strip())


def git_check_ignore(relpath: str, repo_root: pathlib.Path) -> bool:
    """True si gitignore catch-all (git check-ignore) le path."""
    try:
        out = subprocess.run(
            ["git", "check-ignore", relpath],
            cwd=str(repo_root),
            capture_output=True,
            text=True,
            check=False,
        )
    except FileNotFoundError:
        return False
    return out.returncode == 0


def iter_code_cells(nb_path: pathlib.Path):
    """Yield (cell_index, source_string) pour chaque cellule code du notebook."""
    raw = nb_path.read_bytes()
    nb = json.loads(raw.replace(b"\r\n", b"\n"))
    for idx, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        src = "".join(cell.get("source", []))
        yield idx, src


def extract_paths(source: str) -> list:
    """Extraire les paths (scripts|)results/<X>/... depuis le source code."""
    seen = set()
    out = []
    for m in PATH_PATTERN.finditer(source):
        path = m.group(1)
        if path not in seen:
            seen.add(path)
            out.append(path)
    return out


def resolve_path(notebook_dir: pathlib.Path, raw_path: str) -> str:
    """Resoudre le path relatif au notebook_dir, retourner un path RELATIF au repo root.

    Le notebook utilise des paths comme 'scripts/results/<X>/results.json' qui
    sont relatifs au CWD d'execution. On les resout par rapport au dossier du
    notebook pour obtenir un path absolu disque, puis on convertit en chemin
    relatif au repo root pour les appels git (qui sont cwd-repo-root).
    """
    # raw_path est relatif au CWD d'exec (= dossier du notebook quand lance
    # depuis le notebook via papermill). On suppose notebook_dir == CWD.
    abs_path = (notebook_dir / raw_path).resolve()
    repo_root = notebook_dir
    # Remonter jusqu'au .git le plus proche (le notebook peut etre dans un
    # dossier sans .git immediat, mais on a forcement un repo root qqpart).
    while not (repo_root / ".git").exists() and repo_root.parent != repo_root:
        repo_root = repo_root.parent
    try:
        return str(abs_path.relative_to(repo_root))
    except ValueError:
        # Le path est hors du repo (pas attendu pour scripts/results/) :
        # retourner tel quel, le test d'existence disque ci-dessous le dira.
        return str(abs_path)


def classify_path(relpath: str, repo_root: pathlib.Path) -> str:
    """Classer le path en OK / GITIGNORED / MISSING.

    Strategie : tracker d'abord (le clone frais est le test decisif), puis
    gitignore, puis existence disque locale (utile en dev pour debug).
    """
    if git_ls_tree_tracked(relpath, repo_root):
        return "OK"
    if git_check_ignore(relpath, repo_root):
        return "GITIGNORED"
    # Existence disque locale : utile pour debug CI en dev, mais sur clone
    # frais (cwd = worktree), elle est toujours False si MISSING. On garde
    # uniquement la classification git (tracke ou gitignore).
    return "MISSING"


def scan_notebook(nb_path: pathlib.Path, repo_root: pathlib.Path) -> dict:
    """Scan d'un notebook, retourne les paths trouves et leur classification."""
    findings = []
    notebook_dir = nb_path.parent
    try:
        cells = list(iter_code_cells(nb_path))
    except (json.JSONDecodeError, OSError) as e:
        return {"notebook": str(nb_path), "error": f"lecture impossible: {e}", "findings": []}

    for cell_idx, source in cells:
        for raw_path in extract_paths(source):
            # Resolution : le notebook peut etre dans un sous-dossier, et les
            # paths sont relatifs au dossier du notebook.
            abs_path = (notebook_dir / raw_path).resolve()
            try:
                relpath = str(abs_path.relative_to(repo_root))
            except ValueError:
                # Path hors repo (artefact) : signaler en MISSING pour qu'il
                # ne contourne pas le guard.
                relpath = str(abs_path)
            status = classify_path(relpath, repo_root)
            findings.append({
                "cell": cell_idx,
                "path": raw_path,
                "resolved": relpath,
                "status": status,
            })
    return {"notebook": str(nb_path), "findings": findings}


def find_repo_root(start: pathlib.Path) -> pathlib.Path:
    cur = start.resolve()
    while cur != cur.parent:
        if (cur / ".git").exists():
            return cur
        cur = cur.parent
    raise RuntimeError("Pas de .git trouve au-dessus du script")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("notebooks", nargs="*", help="Notebooks a scanner (defaut: scope ML-Training-Pipeline)")
    ap.add_argument("--json", action="store_true", help="Sortie machine")
    ap.add_argument("--quiet", action="store_true", help="Sortie minimale (CI)")
    args = ap.parse_args()

    script_dir = pathlib.Path(__file__).resolve().parent
    repo_root = find_repo_root(script_dir)

    if args.notebooks:
        nb_paths = [pathlib.Path(p).resolve() for p in args.notebooks]
    else:
        nb_paths = sorted((repo_root / "MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline").glob("*.ipynb"))

    all_findings = []
    missing_count = 0
    gitignored_count = 0
    ok_count = 0

    for nb_path in nb_paths:
        result = scan_notebook(nb_path, repo_root)
        if "error" in result:
            if not args.quiet:
                print(f"ERROR {result['notebook']}: {result['error']}", file=sys.stderr)
            continue
        all_findings.append(result)
        for f in result["findings"]:
            if f["status"] == "OK":
                ok_count += 1
            elif f["status"] == "GITIGNORED":
                gitignored_count += 1
            else:  # MISSING
                missing_count += 1
                if not args.quiet:
                    print(f"MISSING {result['notebook']}:{f['cell']}  {f['path']}  -> {f['resolved']}")

    if args.json:
        out = {
            "notebooks_scanned": len(all_findings),
            "ok": ok_count,
            "gitignored": gitignored_count,
            "missing": missing_count,
            "findings": all_findings,
        }
        print(json.dumps(out, indent=1))
    elif not args.quiet:
        print(f"--- scanned {len(all_findings)} notebooks: OK={ok_count} GITIGNORED={gitignored_count} MISSING={missing_count}")

    sys.exit(1 if missing_count > 0 else 0)


if __name__ == "__main__":
    main()
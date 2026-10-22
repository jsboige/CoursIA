#!/usr/bin/env python3
"""Etat pre-build d'un lake Lean — empreinte deterministe, marquage, resolution.

Pourquoi cet outil existe
-------------------------
Le carnet `Lean-13-Kochen-Specker.ipynb` execute `lake build Conway` dans sa
cellule 24. Sur le lac `conway_lean` (3043 modules) le build complet coute
~8 h 51 en sequentiel et depasse 15 min en parallele : mesure sur deux sieges
independants, voie 1 et voie 3 refutees (#21410). Le build ne peut donc pas
vivre dans l'execution du carnet — il doit exister un **etat pre-build** que la
cellule consomme.

La difficulte n'est pas de construire le lac, c'est de savoir **si l'etat
present correspond aux sources presentes**. Un `.lake/build` present mais
construit sur d'autres sources rend un `lake build` rapide qui recompile
silencieusement des modules, ou fait passer un etat perime pour un etat
courant : c'est exactement le mensonge que `check_mathlib_cache.py` documente
pour les junctions. Cet organe ne devine rien, il compare une empreinte.

Contrat
-------
1. `fingerprint` — sha256 deterministe de ce qui definit le lac pour Lake :
   `lean-toolchain`, `lakefile.lean` (ou `lakefile.toml`), `lake-manifest.json`,
   et tous les `*.lean` du projet hors `.lake/` et `.git/` — chemin relatif
   posix trie puis octets. Deux checkouts identiques ont la meme empreinte.
2. `stamp` — ecrit `.lake/prebuilt-stamp.json` apres un build **reussi**
   (l'appelant est le build hors carnet : operateur, CI, script de siege).
   Refuse de marquer quand aucun build n'est present : jamais de stamp sur du
   vide.
3. `status` — compare l'empreinte du stamp a l'empreinte courante :
   `PREBUILT` / `STALE` / `UNSTAMPED` / `ABSENT`.
4. `resolve` — cherche sous des racines donnees un AUTRE checkout du meme lac
   dont l'empreinte est egale et l'etat `PREBUILT` ; rend son chemin. C'est la
   consommation : un worktree neuf consomme le clone deja buildé au lieu de
   rebuilder des heures.

Usage
-----
    py scripts/lean/lean_prebuilt.py status --project <lake>
    py scripts/lean/lean_prebuilt.py fingerprint --project <lake> --json
    py scripts/lean/lean_prebuilt.py stamp --project <lake> --module Conway
    py scripts/lean/lean_prebuilt.py resolve --project <lake> --search <racine> [--search <racine>]

Codes de sortie : `status` et `resolve` sortent 0 sur `PREBUILT` / lac trouve,
1 sinon — utilisables comme garde. `stamp` sort 1 quand il n'y a rien a
marquer. `--json` sort le verdict machine sur stdout.

Perimetre : tranche 1 de la voie 2 de #21410 (l'etat et sa preuve). La
consommation par la cellule 24 du carnet est la tranche 2 ; cet organe
n'execute aucun build et ne modifie aucun carnet.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from datetime import datetime, timezone
from pathlib import Path

STAMP_SCHEMA = "lean-prebuilt-stamp/1"
STAMP_NAME = "prebuilt-stamp.json"

# `.lake` contient build/ et packages/ (Mathlib, batteries…) : ce sont des
# dependances, pas du contenu du lac. `.git` n'existe pas dans un worktree
# normal mais peut apparaitre dans une copie de sauvegarde.
SKIP_PARTS = {".lake", ".git", "node_modules", ".claude"}

STATUS_PREBUILT = "PREBUILT"
STATUS_STALE = "STALE"
STATUS_UNSTAMPED = "UNSTAMPED"
STATUS_ABSENT = "ABSENT"


# ---------------------------------------------------------------------------
# Empreinte
# ---------------------------------------------------------------------------

def _iter_lake_files(project: Path):
    """Fichiers qui definissent le lac, tries par chemin relatif posix.

    Les manifestes sont inclus meme absents : `fingerprint` ne lit que ce qui
    existe, l'absence est donc implicite. Le tri rend l'empreinte independante
    de l'ordre du systeme de fichiers.
    """
    entries: list[tuple[str, Path]] = []
    fixed = ("lean-toolchain", "lakefile.lean", "lakefile.toml", "lake-manifest.json")
    for name in fixed:
        path = project / name
        if path.is_file():
            entries.append((name, path))

    for dirpath, dirnames, filenames in os.walk(project, followlinks=False):
        dirnames[:] = sorted(d for d in dirnames if d not in SKIP_PARTS)
        for filename in sorted(filenames):
            if not filename.endswith(".lean"):
                continue
            path = Path(dirpath) / filename
            rel = path.relative_to(project).as_posix()
            if rel in fixed:
                continue  # lakefile.lean deja compte, sans doublon
            entries.append((rel, path))

    entries.sort(key=lambda item: item[0])
    return entries


def compute_fingerprint(project: Path) -> dict:
    """Empreinte sha256 du lac — voir le contrat du module."""
    project = Path(project).resolve()
    if not project.is_dir():
        raise FileNotFoundError(f"projet introuvable : {project}")

    hasher = hashlib.sha256()
    files = _iter_lake_files(project)
    total_bytes = 0
    for rel, path in files:
        data = path.read_bytes()
        total_bytes += len(data)
        hasher.update(rel.encode("utf-8"))
        hasher.update(b"\0")
        hasher.update(str(len(data)).encode("ascii"))
        hasher.update(b"\0")
        hasher.update(data)
        hasher.update(b"\0")

    toolchain_path = project / "lean-toolchain"
    toolchain = (
        toolchain_path.read_text(encoding="utf-8", errors="replace").strip()
        if toolchain_path.is_file() else ""
    )

    return {
        "fingerprint": hasher.hexdigest(),
        "files": len(files),
        # `lakefile.lean` est un fichier de definition, pas une source du lac :
        # il est deja hashe, mais ne compte pas dans le denombrement des sources.
        "sources": sum(
            1 for rel, _ in files
            if rel.endswith(".lean") and rel != "lakefile.lean"
        ),
        "bytes": total_bytes,
        "toolchain": toolchain,
        "project": str(project),
    }


# ---------------------------------------------------------------------------
# Etat
# ---------------------------------------------------------------------------

def build_present(project: Path) -> bool:
    """Un build existe-t-il ? `.lake/build` non vide, pas seulement un dossier."""
    build_dir = Path(project) / ".lake" / "build"
    if not build_dir.is_dir():
        return False
    for _dirpath, _dirnames, filenames in os.walk(build_dir, followlinks=False):
        if filenames:
            return True
    return False


def read_stamp(project: Path) -> dict | None:
    path = Path(project) / ".lake" / STAMP_NAME
    if not path.is_file():
        return None
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    if not isinstance(data, dict) or not isinstance(data.get("fingerprint"), str):
        return None
    return data


def stamp_project(project: Path, module: str | None = None) -> dict:
    """Marque un build present. Leve ValueError s'il n'y a rien a marquer."""
    project = Path(project).resolve()
    if not build_present(project):
        raise ValueError(
            f"aucun build present sous {project / '.lake' / 'build'} — "
            "stamp refuse de marquer du vide"
        )

    fp = compute_fingerprint(project)
    stamp = {
        "schema": STAMP_SCHEMA,
        "fingerprint": fp["fingerprint"],
        "toolchain": fp["toolchain"],
        "sources": fp["sources"],
        "files": fp["files"],
        "module": module or "",
        "stamped_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
    }
    stamp_path = project / ".lake" / STAMP_NAME
    stamp_path.parent.mkdir(parents=True, exist_ok=True)
    stamp_path.write_text(
        json.dumps(stamp, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    return {"status": STATUS_PREBUILT, "stamp": stamp, "path": str(stamp_path)}


def project_status(project: Path) -> dict:
    """Verdict d'etat d'un lac, sans executer de build."""
    project = Path(project).resolve()
    if not project.is_dir():
        return {"status": STATUS_ABSENT, "reason": "projet introuvable",
                "project": str(project)}
    if not build_present(project):
        return {"status": STATUS_ABSENT, "reason": "aucun .lake/build",
                "project": str(project)}

    fp = compute_fingerprint(project)
    stamp = read_stamp(project)
    if stamp is None:
        return {"status": STATUS_UNSTAMPED,
                "reason": "build present sans stamp lisible",
                "project": str(project), "fingerprint": fp["fingerprint"]}

    if stamp["fingerprint"] != fp["fingerprint"]:
        return {
            "status": STATUS_STALE,
            "reason": "sources ou toolchain modifiees depuis le build",
            "project": str(project),
            "fingerprint": fp["fingerprint"],
            "stamp_fingerprint": stamp["fingerprint"],
        }

    return {
        "status": STATUS_PREBUILT,
        "project": str(project),
        "fingerprint": fp["fingerprint"],
        "toolchain": fp["toolchain"],
        "stamped_at": stamp.get("stamped_at", ""),
        "module": stamp.get("module", ""),
    }


# ---------------------------------------------------------------------------
# Resolution inter-checkouts
# ---------------------------------------------------------------------------

def find_lakes(root: Path) -> list[Path]:
    """Lacs sous une racine (lakefile present), hors `.lake`/`.git`."""
    lakes: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(root, followlinks=False):
        dirnames[:] = sorted(d for d in dirnames if d not in SKIP_PARTS)
        if "lakefile.lean" in filenames or "lakefile.toml" in filenames:
            lakes.append(Path(dirpath))
    return sorted(lakes)


def resolve_prebuilt(project: Path, search_roots: list[Path]) -> dict:
    """Cherche un checkout equivalent deja `PREBUILT`.

    L'egalite d'empreinte est la condition : un clone dont les sources, le
    manifeste ou la toolchain different n'est PAS une reponse, meme s'il est
    buildé. L'ordre de preference est le projet demande lui-meme, puis les
    racines dans l'ordre recu, puis l'ordre alphabetique.
    """
    project = Path(project).resolve()
    target_name = project.name
    requested = compute_fingerprint(project)
    checked: list[dict] = []
    seen: set[str] = set()

    candidates: list[Path] = [project]
    for root in search_roots:
        root = Path(root).resolve()
        if not root.is_dir():
            checked.append({"path": str(root), "status": "MISSING_ROOT"})
            continue
        for lake in find_lakes(root):
            if lake.name == target_name:
                candidates.append(lake)

    for candidate in candidates:
        key = str(candidate.resolve()).lower()
        if key in seen:
            continue
        seen.add(key)
        try:
            candidate_fp = compute_fingerprint(candidate)
        except OSError as exc:
            checked.append({"path": str(candidate), "status": "UNREADABLE",
                            "reason": str(exc)})
            continue
        if candidate_fp["fingerprint"] != requested["fingerprint"]:
            checked.append({"path": str(candidate), "status": "FINGERPRINT_MISMATCH",
                            "fingerprint": candidate_fp["fingerprint"]})
            continue
        verdict = project_status(candidate)
        checked.append({"path": str(candidate), "status": verdict["status"]})
        if verdict["status"] == STATUS_PREBUILT:
            return {
                "status": STATUS_PREBUILT,
                "path": str(candidate.resolve()),
                "requested": str(project),
                "fingerprint": requested["fingerprint"],
                "toolchain": requested["toolchain"],
                "checked": checked,
            }

    return {
        "status": STATUS_ABSENT,
        "requested": str(project),
        "fingerprint": requested["fingerprint"],
        "checked": checked,
    }


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _emit(payload: dict, as_json: bool, human: str) -> None:
    if as_json:
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        print(human)


def _status_human(payload: dict) -> str:
    status = payload["status"]
    if status == STATUS_PREBUILT:
        # `status` porte `project`, `resolve` porte `path` : meme verdict, deux
        # vocabulaires — on affiche celui qui est present.
        located = payload.get("path") or payload.get("project", "")
        return (f"PREBUILT  {located}\n"
                f"  empreinte  {payload['fingerprint']}\n"
                f"  toolchain  {payload.get('toolchain', '')}\n"
                f"  marque     {payload.get('stamped_at', '')}"
                + (f" (module {payload['module']})" if payload.get("module") else ""))
    lines = [f"{status}  {payload.get('project') or payload.get('requested', '')}"]
    if payload.get("reason"):
        lines.append(f"  raison     {payload['reason']}")
    if payload.get("stamp_fingerprint"):
        lines.append(f"  stamp      {payload['stamp_fingerprint']}")
        lines.append(f"  courant    {payload.get('fingerprint', '')}")
    if payload.get("checked"):
        lines.append("  candidats :")
        for item in payload["checked"]:
            lines.append(f"    - {item['status']:20s} {item['path']}")
    return "\n".join(lines)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Etat pre-build d'un lake Lean : empreinte, marquage, resolution."
    )
    sub = parser.add_subparsers(dest="command", required=True)

    def add_common(p: argparse.ArgumentParser) -> None:
        p.add_argument("--project", required=True, type=Path,
                       help="repertoire du lac (lakefile.lean)")
        p.add_argument("--json", action="store_true", help="sortie JSON")

    p_fp = sub.add_parser("fingerprint", help="empreinte deterministe du lac")
    add_common(p_fp)

    p_st = sub.add_parser("stamp", help="marquer un build reussi")
    add_common(p_st)
    p_st.add_argument("--module", default=None,
                      help="module verifie par le build (ex. Conway)")

    p_status = sub.add_parser("status", help="etat du lac (PREBUILT/STALE/...)")
    add_common(p_status)

    p_resolve = sub.add_parser(
        "resolve", help="trouver un checkout equivalent deja PREBUILT")
    add_common(p_resolve)
    p_resolve.add_argument("--search", action="append", default=[], type=Path,
                           help="racine a parcourir (repetable)")

    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)

    if args.command == "fingerprint":
        try:
            payload = compute_fingerprint(args.project)
        except FileNotFoundError as exc:
            print(f"ERREUR {exc}", file=sys.stderr)
            return 1
        human = "\n".join([
            f"empreinte  {payload['fingerprint']}",
            f"projet     {payload['project']}",
            f"toolchain  {payload['toolchain']}",
            f"fichiers   {payload['files']} dont {payload['sources']} sources Lean",
            f"octets     {payload['bytes']}",
        ])
        _emit(payload, args.json, human)
        return 0

    if args.command == "stamp":
        try:
            payload = stamp_project(args.project, module=args.module)
        except (ValueError, FileNotFoundError) as exc:
            print(f"STAMP_REFUSED  {exc}", file=sys.stderr)
            return 1
        human = (f"PREBUILT  {payload['path']}\n"
                 f"  empreinte  {payload['stamp']['fingerprint']}\n"
                 f"  sources    {payload['stamp']['sources']}")
        _emit(payload, args.json, human)
        return 0

    if args.command == "status":
        payload = project_status(args.project)
        _emit(payload, args.json, _status_human(payload))
        return 0 if payload["status"] == STATUS_PREBUILT else 1

    if args.command == "resolve":
        try:
            payload = resolve_prebuilt(args.project, args.search)
        except FileNotFoundError as exc:
            print(f"ERREUR {exc}", file=sys.stderr)
            return 1
        _emit(payload, args.json, _status_human(payload))
        return 0 if payload["status"] == STATUS_PREBUILT else 1

    return 2  # unreachable avec argparse required=True


if __name__ == "__main__":
    raise SystemExit(main())
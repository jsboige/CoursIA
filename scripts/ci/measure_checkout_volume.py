#!/usr/bin/env python3
"""Mesure hors-ligne du volume de checkout et du contrat miroir d'un hote de runners.

Deux modes, tous deux en lecture seule et sans reseau :

- mode clone (defaut) : mesure, sur un clone local, du poids qu'un job
  telemetry doit telecharger pour un checkout, puis derive le tableau
  avant/apres des octets recus par job (regime `fetch-depth: 0` sans filtre
  contre regime `fetch-depth: 0` + `filter: blob:none`, puis contre un
  checkout limite aux chemins d'outillage).
- mode miroir (`--mirror`) : mesure l'etat d'un miroir bare d'hote (taille,
  nombre de refs, fraicheur, `gc.auto`, alternates) et, si `--gitconfig` est
  fourni, verifie que le miroir est reellement branche sur les checkouts
  (une section `url.<miroir>.insteadOf`).

Contexte : issue #26383 (roo-extensions#4376, volet CoursIA). Les criteres
"tableau avant/apres des octets recus par job" et "tableau hote par hote"
n'etaient mesures par aucun outil du depot ; ils etaient donc rediges a la
main, sans etat verifie.

Usage :
    python scripts/ci/measure_checkout_volume.py --path .
    python scripts/ci/measure_checkout_volume.py --mirror /home/<user>/.../objects-mirror.git \
        --gitconfig /home/<user>/.gitconfig --json
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

BIG_BLOB_DEFAULT_MIB = 5.0
MIB = 1024 * 1024
GIB = 1024 * MIB

# Chemins d'outillage : ce qu'un garde CI materialise reellement (scripts de
# validation, workflows, documentation referencee, configuration du harnais).
OUTILLAGE_PATHS = ("scripts/", ".github/", "docs/", ".claude/", "docker-configurations/")


def _git(repo: Path, *args: str) -> str:
    proc = subprocess.run(
        ["git", "-c", "safe.directory=*", "-C", str(repo), *args],
        capture_output=True,
        text=True,
        check=False,
        encoding="utf-8",
        errors="replace",
    )
    if proc.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} a echoue : {proc.stderr.strip()}")
    return proc.stdout


def _parse_human_size(text: str) -> int:
    """Convertit la taille humaine de `git count-objects -vH` en octets."""
    text = text.strip()
    if not text or text.lower() == "none":
        return 0
    units = {"kib": 1024, "mib": MIB, "gib": GIB, "tib": 1024 * GIB}
    parts = text.split()
    try:
        value = float(parts[0])
    except (IndexError, ValueError):
        return 0
    if len(parts) > 1 and parts[1].lower() in units:
        value *= units[parts[1].lower()]
    return int(value)


def history_breakdown(repo: Path) -> dict[str, int]:
    """Repartition (nombre, octets disque) des objets du depot, par type.

    C'est le contenu du pack : c'est ce qu'un fetch d'historique complet
    transfere, et la soustraction des blobs donne exactement le poids d'un
    fetch `filter: blob:none`.
    """
    out = _git(repo, "cat-file", "--batch-all-objects", "--batch-check=%(objecttype) %(objectsize:disk)")
    stats: dict[str, list[int]] = {}
    for line in out.splitlines():
        parts = line.split()
        if len(parts) != 2:
            continue
        otype, size = parts[0], parts[1]
        try:
            bucket = stats.setdefault(otype, [0, 0])
            bucket[0] += 1
            bucket[1] += int(size)
        except ValueError:
            continue
    return {otype: {"objects": values[0], "bytes": values[1]} for otype, values in stats.items()}


def head_blobs(repo: Path) -> list[tuple[str, int, int]]:
    """Blobs materialises par un checkout de HEAD : (chemin, octets, octets disque).

    `octets` est la taille decompressee (ce que le checkout ecrit sur le disque
    de travail) ; `octets disque` est la taille stockee (ce que le reseau
    transfere). Les deux sont distincts : les carnets a sorties embarquees
    compressent mal, les blobs de zeros compressent trop bien.
    """
    out = _git(repo, "ls-tree", "-r", "HEAD")
    paths: dict[str, str] = {}
    for line in out.splitlines():
        meta, _, path = line.partition("\t")
        parts = meta.split()
        if len(parts) != 3 or parts[1] != "blob":
            continue
        paths[parts[2]] = path
    if not paths:
        return []

    payload = "\n".join(paths) + "\n"
    proc = subprocess.run(
        ["git", "-c", "safe.directory=*", "-C", str(repo), "cat-file",
         "--batch-check=%(objectname) %(objectsize) %(objectsize:disk)"],
        input=payload,
        capture_output=True,
        text=True,
        check=False,
        encoding="utf-8",
        errors="replace",
    )
    if proc.returncode != 0:
        raise RuntimeError(f"cat-file --batch-check a echoue : {proc.stderr.strip()}")

    rows: list[tuple[str, int, int]] = []
    for line in proc.stdout.splitlines():
        parts = line.split()
        if len(parts) != 3:
            continue
        sha, size, disk = parts
        if sha not in paths:
            continue
        try:
            rows.append((paths[sha], int(size), int(disk)))
        except ValueError:
            continue
    return rows


def _top_level(path: str) -> str:
    head = path.split("/", 1)[0]
    return head if "/" in path else "(racine)"


def measure_clone(repo: Path, big_blob_mib: float = BIG_BLOB_DEFAULT_MIB) -> dict[str, Any]:
    """Mesure le poids d'un checkout et derive le tableau avant/apres."""
    head = _git(repo, "rev-parse", "HEAD").strip()
    breakdown = history_breakdown(repo)
    blobs = head_blobs(repo)

    big_limit = int(big_blob_mib * MIB)
    big = sorted(
        [(path, size) for path, size, _disk in blobs if size >= big_limit],
        key=lambda item: item[1],
        reverse=True,
    )

    by_dir: dict[str, dict[str, int]] = {}
    for path, size, disk in blobs:
        bucket = by_dir.setdefault(_top_level(path), {"files": 0, "bytes": 0, "disk_bytes": 0})
        bucket["files"] += 1
        bucket["bytes"] += size
        bucket["disk_bytes"] += disk

    outillage_bytes = sum(disk for path, _size, disk in blobs if path.startswith(OUTILLAGE_PATHS))

    history_bytes = sum(entry["bytes"] for entry in breakdown.values())
    blob_bytes = breakdown.get("blob", {}).get("bytes", 0)
    sans_blobs_bytes = history_bytes - blob_bytes
    head_blobs_disk = sum(disk for _path, _size, disk in blobs)
    head_blobs_size = sum(size for _path, size, _disk in blobs)

    return {
        "repo": str(repo),
        "head": head,
        "history": {
            "total_bytes": history_bytes,
            "by_type": breakdown,
        },
        "head_blobs": {
            "files": len(blobs),
            "bytes": head_blobs_size,
            "disk_bytes": head_blobs_disk,
            "by_top_dir": dict(sorted(by_dir.items(), key=lambda kv: kv[1]["disk_bytes"], reverse=True)),
        },
        "big_blobs": {
            "threshold_mib": big_blob_mib,
            "count": len(big),
            "bytes": sum(size for _path, size in big),
            "top": [{"path": path, "bytes": size} for path, size in big[:10]],
        },
        "before_after": {
            "avant_octets_par_job": history_bytes,
            "avant_libelle": "historique complet (fetch-depth: 0 sans filtre)",
            "apres_blob_none_octets": sans_blobs_bytes + head_blobs_disk,
            "apres_blob_none_libelle": "historique sans blobs (filter: blob:none) + blobs de HEAD telecharges",
            "apres_outillage_octets": sans_blobs_bytes + outillage_bytes,
            "apres_outillage_libelle": "historique sans blobs + seuls les chemins d'outillage materialises",
            "delta_blob_none_octets": history_bytes - (sans_blobs_bytes + head_blobs_disk),
            "delta_outillage_octets": history_bytes - (sans_blobs_bytes + outillage_bytes),
            "part_reelle_blobs_octets": head_blobs_size,
            "outillage_paths": list(OUTILLAGE_PATHS),
            "outillage_octets": outillage_bytes,
        },
    }


def measure_mirror(mirror: Path, gitconfig: Path | None = None) -> dict[str, Any]:
    """Mesure l'etat d'un miroir bare et son branchement eventuel sur les checkouts."""
    if not (mirror / "objects").is_dir():
        raise RuntimeError(f"{mirror} n'est pas un depot git bare (objects/ absent)")

    breakdown = history_breakdown(mirror)
    pack_bytes = sum(entry["bytes"] for entry in breakdown.values())

    refs = [line for line in _git(mirror, "for-each-ref", "--format=%(refname)").splitlines() if line]
    backup_refs = [ref for ref in refs if ref.startswith("refs/backup/")]

    config = _git(mirror, "config", "--list")
    gc_auto = None
    for line in config.splitlines():
        if line.startswith("gc.auto="):
            gc_auto = line.split("=", 1)[1]

    alternates_path = mirror / "objects" / "info" / "alternates"
    alternates = alternates_path.read_text(encoding="utf-8", errors="replace").strip() if alternates_path.is_file() else None

    pack_dir = mirror / "objects" / "pack"
    newest_pack = None
    newest_pack_mtime = None
    if pack_dir.is_dir():
        packs = [p for p in pack_dir.glob("*.pack") if p.is_file()]
        if packs:
            newest_pack = max(packs, key=lambda p: p.stat().st_mtime)
            newest_pack_mtime = newest_pack.stat().st_mtime

    wiring_evidence: list[str] = []
    wired = None
    if gitconfig is not None:
        if gitconfig.is_file():
            text = gitconfig.read_text(encoding="utf-8", errors="replace")
            for line in text.splitlines():
                stripped = line.strip()
                if "insteadof" in stripped.lower():
                    wiring_evidence.append(stripped)
        wired = bool(wiring_evidence)

    return {
        "mirror": str(mirror),
        "pack_bytes": pack_bytes,
        "by_type": breakdown,
        "refs": len(refs),
        "backup_refs": len(backup_refs),
        "gc_auto": gc_auto,
        "alternates": alternates,
        "newest_pack": str(newest_pack) if newest_pack else None,
        "newest_pack_mtime": newest_pack_mtime,
        "gitconfig": str(gitconfig) if gitconfig else None,
        "wired_instead_of": wired,
        "wiring_evidence": wiring_evidence,
    }


def _fmt_bytes(value: int) -> str:
    if value >= GIB:
        return f"{value / GIB:.2f} GiB"
    if value >= MIB:
        return f"{value / MIB:.1f} MiB"
    if value >= 1024:
        return f"{value / 1024:.1f} KiB"
    return f"{value} o"


def _pct(part: int, whole: int) -> str:
    if whole <= 0:
        return "-"
    return f"{100.0 * part / whole:.1f} %"


def render_clone(report: dict[str, Any]) -> str:
    ba = report["before_after"]
    head = report["head_blobs"]
    lines = [
        f"Depot   : {report['repo']}",
        f"HEAD    : {report['head']}",
        "",
        "Octets recus par job (mesure locale, hors-ligne)",
        f"  avant  (historique complet, sans filtre)          : {_fmt_bytes(ba['avant_octets_par_job'])}",
        f"  apres  (filter: blob:none + blobs de HEAD)         : {_fmt_bytes(ba['apres_blob_none_octets'])}"
        f"  (-{_pct(ba['delta_blob_none_octets'], ba['avant_octets_par_job'])})",
        f"  apres  (filter: blob:none + chemins d'outillage)    : {_fmt_bytes(ba['apres_outillage_octets'])}"
        f"  (-{_pct(ba['delta_outillage_octets'], ba['avant_octets_par_job'])})",
        f"  part reelle (blobs materialises par le checkout)   : {_fmt_bytes(ba['part_reelle_blobs_octets'])}",
        f"  chemins d'outillage materialises                   : {_fmt_bytes(ba['outillage_octets'])}",
        "",
        "Poids de HEAD par repertoire de premier niveau (octets transferes)",
        f"  {len(head['by_top_dir'])} repertoires, {_fmt_bytes(head['disk_bytes'])} au total",
    ]
    for name, entry in list(head["by_top_dir"].items())[:10]:
        lines.append(
            f"    {_fmt_bytes(entry['disk_bytes']):>10}  ({_pct(entry['disk_bytes'], head['disk_bytes']):>6})  {name}"
        )
    lines += [
        "",
        "Blobs volumineux dans HEAD",
        f"  seuil {report['big_blobs']['threshold_mib']} MiB : {report['big_blobs']['count']} blobs, "
        f"{_fmt_bytes(report['big_blobs']['bytes'])}",
    ]
    for item in report["big_blobs"]["top"]:
        lines.append(f"    {_fmt_bytes(item['bytes']):>10}  {item['path']}")
    return "\n".join(lines)


def render_mirror(report: dict[str, Any]) -> str:
    lines = [
        f"Miroir  : {report['mirror']}",
        f"Taille  : {_fmt_bytes(report['pack_bytes'])}",
        f"Refs    : {report['refs']} (dont {report['backup_refs']} refs/backup/)",
        f"gc.auto : {report['gc_auto'] if report['gc_auto'] is not None else 'absent (defaut git)'}",
        f"Alternates : {report['alternates'] if report['alternates'] else 'aucun'}",
        f"Pack le plus recent : {report['newest_pack']}",
        f"Branche sur les checkouts (insteadOf) : {report['wired_instead_of']}",
    ]
    for item in report["wiring_evidence"]:
        lines.append(f"    {item}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--path", default=".", help="clone local a mesurer (mode clone)")
    parser.add_argument("--mirror", default=None, help="miroir bare a mesurer (mode miroir)")
    parser.add_argument("--gitconfig", default=None, help="fichier gitconfig a inspecter (mode miroir)")
    parser.add_argument("--big-blob-mib", type=float, default=BIG_BLOB_DEFAULT_MIB)
    parser.add_argument("--json", action="store_true", help="sortie JSON")
    args = parser.parse_args(argv)

    try:
        if args.mirror:
            report = measure_mirror(Path(args.mirror), Path(args.gitconfig) if args.gitconfig else None)
            rendered = render_mirror(report)
        else:
            report = measure_clone(Path(args.path).resolve(), args.big_blob_mib)
            rendered = render_clone(report)
    except (RuntimeError, OSError) as exc:
        print(f"ERREUR : {exc}", file=sys.stderr)
        return 1

    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    else:
        print(rendered)
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Scan + backfill des archives RooSync sans resume LLM (#8889).

**Contexte (issue #8889)** :

Quand l'auto-condensation d'un dashboard RooSync ne peut pas joindre le LLM
de resume (vLLM localhost:5002), elle degrade en **truncation fallback** : les
messages sont archives verbatim, mais **sans resume**. Le dashboard vivant
garde alors un stub pour cette fenetre, et **rien ne repasse jamais** derriere
pour combler quand le LLM revient. Mesure : ~11.6% des archives (537/4615)
n'ont jamais recu de resume.

**Aucune perte de contenu** : les archives sont verbatim sur disque, le
format est `archive/workspace-<name>-<ISO>-fallback.md` avec frontmatter
`llmGenerated: false` + `fallbackTruncation: true`. Le probleme est
**lisibilite** du canal principal, pas integrite.

**Scope de cet outil** :

- `--list` : imprime un tableau (date, dashboard, taille, nb messages) pour
  toutes les archives fallback detectees
- `--report` : statistiques agregees par dashboard + export JSON
- `--backfill <path>` : marque une archive pour backfill manuel (sans appel
  LLM — pose juste un tag `markForBackfill: true` dans le frontmatter, le
  backfill reel reste a la charge d'un operateur humain ou d'un script
  dedie branchant vLLM)

**Hors scope** : rejouer la condensation LLM elle-meme (instrument RooSync
proprietaire), toucher au dashboard vivant, modifier le format d'archive
existant. Cet outil est **un detecteur + un marqueur**, pas un moteur de
resume.

**Tell c.974 strict § SOTA** : l'outil s'appuie sur le format verbatim
existant (pas de workaround degrade), aucune reinvention du frontmatter,
lecture regex stricte. Le verdict de fallback (`llmGenerated: false` ET
`fallbackTruncation: true`) est implemente tel que documente dans le body
de #8889.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Iterable, Iterator

# --- Frontmatter parsing ------------------------------------------------------

# Le frontmatter RooSync est un mini-header YAML-like au debut du fichier
# archive. Exemple verbatim (cf #8889 body) :
#
# ---
# messageCount: 8
# llmGenerated: false
# fallbackTruncation: true
# ---
FRONTMATTER_RE = re.compile(
    r"^---\s*\n(?P<body>.*?)\n---\s*\n",
    re.DOTALL | re.MULTILINE,
)


@dataclass(frozen=True)
class ArchiveFrontmatter:
    """Frontmatter parse d'une archive RooSync."""
    message_count: int | None = None
    llm_generated: bool | None = None
    fallback_truncation: bool | None = None
    raw: dict[str, str] = field(default_factory=dict)


def parse_frontmatter(text: str) -> ArchiveFrontmatter:
    """Parse le frontmatter YAML-like. Tolerance : champs manquants = None."""
    match = FRONTMATTER_RE.match(text)
    if not match:
        return ArchiveFrontmatter(raw={})
    raw: dict[str, str] = {}
    for line in match.group("body").splitlines():
        line = line.strip()
        if not line or ":" not in line:
            continue
        key, _, value = line.partition(":")
        raw[key.strip()] = value.strip()

    def _int(key: str) -> int | None:
        v = raw.get(key)
        if v is None:
            return None
        try:
            return int(v)
        except ValueError:
            return None

    def _bool(key: str) -> bool | None:
        v = raw.get(key)
        if v is None:
            return None
        return v.strip().lower() == "true"

    return ArchiveFrontmatter(
        message_count=_int("messageCount"),
        llm_generated=_bool("llmGenerated"),
        fallback_truncation=_bool("fallbackTruncation"),
        raw=raw,
    )


# --- Detection des archives fallback ------------------------------------------

# Pattern de nommage documente dans #8889 : workspace-<name>-<ISO>-fallback.md
# Variante : peut contenir un workspace-prefix 'workspace-' ou pas.
FILENAME_FALLBACK_RE = re.compile(
    r"(?P<workspace>workspace-[A-Za-z0-9_-]+|[A-Za-z0-9_-]+)"
    r"-(?P<iso>\d{4}-\d{2}-\d{2}T\d{2}-\d{2}-\d{2})"
    r"-fallback\.md$",
)


@dataclass(frozen=True)
class ArchiveInfo:
    """Info extraite d'une archive fallback detectee."""
    path: Path
    workspace: str
    iso: str
    size_bytes: int
    message_count: int | None
    frontmatter: ArchiveFrontmatter


def is_fallback_archive(path: Path) -> bool:
    """Vrai si le nom de fichier matche le pattern documented fallback."""
    return bool(FILENAME_FALLBACK_RE.search(path.name))


def iter_archives(root: Path) -> Iterator[Path]:
    """Iterateur sur tous les fichiers *.md sous root."""
    return root.rglob("*.md")


def detect_fallback_archives(root: Path) -> list[ArchiveInfo]:
    """Detecte toutes les archives fallback sous root, avec frontmatter parse.

    Une archive est consideree "fallback reelle" si ET seulement si :
    - Le nom matche FILENAME_FALLBACK_RE
    - Le frontmatter porte `llmGenerated: false` ET `fallbackTruncation: true`
    """
    results: list[ArchiveInfo] = []
    if not root.exists():
        return results
    for path in iter_archives(root):
        if not is_fallback_archive(path):
            continue
        match = FILENAME_FALLBACK_RE.search(path.name)
        if not match:
            continue
        workspace = match.group("workspace")
        iso = match.group("iso")
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        fm = parse_frontmatter(text)
        if fm.llm_generated is False and fm.fallback_truncation is True:
            results.append(ArchiveInfo(
                path=path,
                workspace=workspace,
                iso=iso,
                size_bytes=path.stat().st_size,
                message_count=fm.message_count,
                frontmatter=fm,
            ))
    return results


# --- Modes : list / report / backfill ----------------------------------------

def cmd_list(archives: list[ArchiveInfo]) -> int:
    """Imprime un tableau : date, dashboard, taille, nb messages."""
    if not archives:
        print("[list] aucune archive fallback detectee.")
        return 0
    # Tri par date ISO descendante (plus recentes d'abord)
    archives_sorted = sorted(archives, key=lambda a: a.iso, reverse=True)
    print(f"{'ISO':<22} {'Workspace':<32} {'Messages':>8} {'Size (o)':>10}  Path")
    print("-" * 110)
    total_size = 0
    total_messages = 0
    for a in archives_sorted:
        msg = a.message_count if a.message_count is not None else "?"
        print(f"{a.iso:<22} {a.workspace:<32} {msg:>8} {a.size_bytes:>10}  {a.path}")
        total_size += a.size_bytes
        if a.message_count is not None:
            total_messages += a.message_count
    print("-" * 110)
    print(f"TOTAL : {len(archives)} archives, {total_messages} messages, {total_size} octets")
    return 0


def cmd_report(archives: list[ArchiveInfo], output_dir: Path) -> int:
    """Statistiques agregees par dashboard + export JSON."""
    if not archives:
        print("[report] aucune archive fallback a agreger.")
        return 0
    by_workspace: dict[str, list[ArchiveInfo]] = {}
    for a in archives:
        by_workspace.setdefault(a.workspace, []).append(a)

    summary = {
        "total_archives": len(archives),
        "total_size_bytes": sum(a.size_bytes for a in archives),
        "total_messages": sum(a.message_count or 0 for a in archives),
        "workspaces": {},
    }
    for ws, items in sorted(by_workspace.items()):
        summary["workspaces"][ws] = {
            "archive_count": len(items),
            "size_bytes": sum(a.size_bytes for a in items),
            "messages": sum(a.message_count or 0 for a in items),
            "oldest": min((a.iso for a in items), default=None),
            "newest": max((a.iso for a in items), default=None),
        }

    output_dir.mkdir(parents=True, exist_ok=True)
    json_path = output_dir / "roosync_archive_backfill_report.json"
    json_path.write_text(
        json.dumps(summary, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )
    print(f"[report] {len(archives)} archives, {len(by_workspace)} dashboards")
    print(f"[report] JSON ecrit : {json_path}")
    # Top dashboards par volume
    top = sorted(by_workspace.items(), key=lambda kv: -len(kv[1]))[:5]
    for ws, items in top:
        print(f"  - {ws}: {len(items)} archives")
    return 0


def cmd_backfill(target: Path, archives: list[ArchiveInfo]) -> int:
    """Marque l'archive cible pour backfill manuel (ajoute markForBackfill: true)."""
    target_resolved = target.resolve()
    matches = [a for a in archives if a.path.resolve() == target_resolved]
    if not matches:
        print(f"[backfill] ERREUR : {target} n'est pas une archive fallback detectee.")
        print(f"[backfill] Indication : relancer avec --list pour voir les chemins.")
        return 1
    info = matches[0]
    text = info.path.read_text(encoding="utf-8", errors="replace")
    if "markForBackfill:" in text:
        print(f"[backfill] DEJA MARQUEE : {info.path}")
        return 0
    # Insertion juste apres le frontmatter fermant (---) : ajoute markForBackfill: true
    new_text = FRONTMATTER_RE.sub(
        lambda m: m.group(0)[:-1] + "markForBackfill: true\n---\n",
        text,
        count=1,
    )
    if new_text == text:
        print(f"[backfill] ERREUR : frontmatter absent ou mal forme dans {info.path}")
        return 1
    info.path.write_text(new_text, encoding="utf-8")
    print(f"[backfill] MARQUEE : {info.path}")
    return 0


# --- Main ---------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(
        description="Detection + marquage des archives RooSync sans resume LLM (#8889)",
    )
    parser.add_argument("--root", type=Path, required=True,
                        help="Racine de scan (typiquement $ROOSYNC_SHARED_PATH/dashboards/archive)")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--list", action="store_true",
                       help="Lister toutes les archives fallback detectees")
    group.add_argument("--report", action="store_true",
                       help="Statistiques agregees par dashboard + JSON")
    group.add_argument("--backfill", type=Path, metavar="ARCHIVE_PATH",
                       help="Marquer une archive precise pour backfill manuel")
    parser.add_argument("--output-dir", type=Path,
                        default=Path("scripts/results/roosync_archive_backfill"),
                        help="Repertoire de sortie pour les rapports JSON")
    args = parser.parse_args()

    archives = detect_fallback_archives(args.root)
    print(f"[scan] root={args.root} : {len(archives)} archives fallback detectees")

    if args.list:
        return cmd_list(archives)
    if args.report:
        return cmd_report(archives, args.output_dir)
    if args.backfill:
        return cmd_backfill(args.backfill, archives)
    return 1  # unreachable (mutually_exclusive_group required)


if __name__ == "__main__":
    sys.exit(main())

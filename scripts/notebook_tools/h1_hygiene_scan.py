#!/usr/bin/env python3
"""Advisory H1 hygiene scanner (#11840).

Reports notebooks whose first markdown heading (H1) would be altered by
catalog sanitization — inline markdown (**bold**, `code`), emojis, or the
redundant "Notebook:" prefix. Advisory only (exit 0): new-notebook hygiene
signal, never a merge blocker. The catalog itself is sanitized at generation
(sanitize_title, generate_catalog.py), so this scan is forward-looking: it
flags the SOURCE notebooks so authors can write clean H1s going forward.
"""

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from generate_catalog import _EMOJI_RE, _MARKDOWN_EMPHASIS_RE, _NOTEBOOK_PREFIX_RE  # noqa: E402


def first_heading(nb_path: Path) -> str | None:
    try:
        nb = json.loads(nb_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    for cell in nb.get("cells", []):
        if cell.get("cell_type") == "markdown":
            src = "".join(cell.get("source", []))
            for line in src.split("\n"):
                line = line.strip()
                if line.startswith("#"):
                    return line.lstrip("#").strip()
    return None


def classify_defects(title: str) -> list[str]:
    defects = []
    if _MARKDOWN_EMPHASIS_RE.search(title):
        defects.append("inline-markdown")
    if _EMOJI_RE.search(title):
        defects.append("emoji")
    if _NOTEBOOK_PREFIX_RE.match(title):
        defects.append("notebook-prefix")
    return defects


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("targets", nargs="+", help="notebook files to scan")
    ap.add_argument("--json", action="store_true", help="machine-readable output")
    args = ap.parse_args()

    findings = []
    for target in args.targets:
        p = Path(target)
        title = first_heading(p)
        if title is None:
            continue
        defects = classify_defects(title)
        if defects:
            findings.append({"path": target, "title": title, "defects": defects})

    if args.json:
        print(json.dumps(findings, ensure_ascii=False, indent=1))
    else:
        for f in findings:
            print(f"{f['path']}: {','.join(f['defects'])} — {f['title']}")
        print(f"scan complete: {len(findings)} notebook(s) with H1 hygiene defects")

    if findings:
        # Advisory: report, but never fail the workflow.
        print("::warning::H1 hygiene advisory (non-blocking, #11840): "
              f"{len(findings)} notebook(s) carry inline markdown/emoji/'Notebook:' prefix in H1. "
              "The catalog sanitizes these at generation; consider cleaning the source heading.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

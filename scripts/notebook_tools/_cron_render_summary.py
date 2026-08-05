#!/usr/bin/env python3
"""Helper appele par .github/workflows/twin-parity-cron.yml (step
'Publish job summary') pour rendre le rapport markdown du cron twin-parity.

Externalise le Python du workflow pour eviter le YAML/Bash quoting croise
(f-string `f\"{r['name']}\"` dans un `run: |` block casse yaml.safe_load).

Lit : twin_parity_cron.json (genere par check_twin_parity.py --ci-strict --json).
Sortie : un rapport markdown sur stdout (que GitHub Actions capture dans
         $GITHUB_STEP_SUMMARY).

Usage :
    python scripts/notebook_tools/_cron_render_summary.py \
        <path/to/twin_parity_cron.json>
"""
from __future__ import annotations

import json
import sys


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        sys.stderr.write(
            "Usage: _cron_render_summary.py <twin_parity_cron.json>\n"
        )
        return 2
    path = argv[1]
    try:
        with open(path, encoding="utf-8") as f:
            d = json.load(f)
    except (OSError, json.JSONDecodeError) as e:
        sys.stderr.write(f"_cron_render_summary: cannot read {path}: {e}\n")
        return 1

    ci = d.get("ci_strict", {}) or {}
    total = d.get("total", 0)
    pairs = d.get("pairs", []) or []

    out = []
    out.append(f"## Twin parity CI-strict -- {total} paires")
    out.append("")
    out.append("| Categorie | Count |")
    out.append("|---|---|")
    for k, v in ci.items():
        out.append(f"| `{k}` | {v} |")
    out.append("")

    touched_pairs = [r for r in pairs if r.get("status") != "OK"]
    if touched_pairs:
        out.append(f"### {len(touched_pairs)} paire(s) touchee(s)")
        for r in touched_pairs:
            name = r.get("name", "?")
            family = r.get("family", "?")
            parity = r.get("parity_level", "?")
            status = r.get("status", "?")
            out.append(f"- **{name}** ({family}, {parity}) -- {status}")
            for det in r.get("details", []) or []:
                out.append(f"    - {det}")
    out.append("")

    sys.stdout.write("\n".join(out))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
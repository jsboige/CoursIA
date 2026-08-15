#!/usr/bin/env python3
"""Helper appele par .github/workflows/twin-parity-cron.yml pour extraire
la liste des paires touchees par le drift, dans un format affichable
par `::error title=...::...`.

Externalise le Python du workflow pour eviter le YAML/Bash quoting croise
(f-string `f\"{r['name']}\"` dans un `run: |` block casse yaml.safe_load).

Lit : twin_parity_cron.json (genere par check_twin_parity.py --ci-strict --json).
Sortie : une ligne par paire touchee (`name (family, parity_level)`),
         ou `<none>` si aucune.

Usage :
    python scripts/notebook_tools/_cron_extract_drift.py \
        <path/to/twin_parity_cron.json>
"""
from __future__ import annotations

import json
import sys


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        sys.stderr.write(
            "Usage: _cron_extract_drift.py <twin_parity_cron.json>\n"
        )
        return 2
    path = argv[1]
    try:
        with open(path, encoding="utf-8") as f:
            d = json.load(f)
    except (OSError, json.JSONDecodeError) as e:
        sys.stderr.write(f"_cron_extract_drift: cannot read {path}: {e}\n")
        return 1

    touched = []
    for r in d.get("pairs", []) or []:
        if r.get("status") != "OK":
            name = r.get("name", "?")
            family = r.get("family", "?")
            parity = r.get("parity_level", "?")
            touched.append(f"{name} ({family}, {parity})")

    sys.stdout.write("\n".join(touched) if touched else "<none>")
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
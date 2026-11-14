#!/usr/bin/env python3
"""Rejoue la garde Lean de `merge_ready` sur des PRs donnees (#24989).

Pourquoi un organe de rejeu
---------------------------
La garde `lean:no-local-build-attestation` est une **mesure** : elle doit
sortir `lean:no-local-build-attestation` sur une PR qui touche du Lean et
n'en porte pas. Sans rejeu, la garde n'est qu'un code presume correct ; avec
un rejeu, sa.sortie est un fait. Ce script appelle la **fonction de garde
elle-meme** (`merge_ready.lean_build_attestation_reason`) -- il ne la
reimplementait pas, donc un rejeu vert prouve le code de la garde, pas une
copie de la garde.

Il ne fait **aucun merge** : il appelle la fonction de garde, qui rend un
motif de skip ou None, et rien d'autre.

Usage
-----
    python scripts/coordination/replay_lean_guard.py 24277 24428 ...
    python scripts/coordination/replay_lean_guard.py --json 24277
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPTS_DIR = HERE.parent
for _shared in (SCRIPTS_DIR, HERE):
    if str(_shared) not in sys.path:
        sys.path.insert(0, str(_shared))

import merge_ready as mr  # noqa: E402


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("prs", type=int, nargs="+", help="numeros de PR")
    ap.add_argument("--repo", default=mr.REPO)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args(argv)

    runner = mr.SubprocessRunner()
    try:
        token = mr.resolve_token(runner)
    except mr.CannotRunError as exc:
        print("replay_lean_guard : jeton indisponible -- {}".format(exc), file=sys.stderr)
        return 2
    gh_env = {**os.environ, "GH_TOKEN": token}

    rows = []
    for pr in args.prs:
        view = mr.fetch_pr_view(runner, pr, gh_env)
        head = str(view.get("headRefOid") or "")
        reason = mr.lean_build_attestation_reason(view, head, runner, gh_env)
        lean_files = mr.lean_build_attestation.lean_paths(
            str((row or {}).get("path") or "") for row in (view.get("files") or [])
        )
        rows.append(
            {
                "pr": pr,
                "head": head,
                "lean_files": len(lean_files),
                "reason": reason,
            }
        )

    if args.json:
        json.dump(rows, sys.stdout, ensure_ascii=False, indent=1)
        sys.stdout.write("\n")
    else:
        for row in rows:
            print(
                "#{pr}: {reason} ({n} fichier(s) Lean)".format(
                    pr=row["pr"],
                    reason=row["reason"] or "passe",
                    n=row["lean_files"],
                )
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

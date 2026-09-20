#!/usr/bin/env python3
"""Garde anti-drift du dispatcher matriciel Lean (#13751).

Le manifeste ``scripts/lean/ci_lakes.json`` est la source unique des lakes
migres vers la matrice ; le ``on.paths`` de
``.github/workflows/lean-ci-matrix.yml`` est l'UNION des chemins de
declenchement. Ces deux surfaces derivent si on les maintient a la main :
un lake ajoute au manifeste sans chemin dans l'union serait un lake que
PLUS AUCUN declencheur ne voit (CI silencieusement morte -- exactement le
defaut que le self-cover de #8712 ferme pour les fichiers du gate).

Ce garde verifie, fail-CLOSED (exit 1) :

  1. chaque chemin ``paths`` de chaque lake du manifeste figure dans les
     DEUX blocs (``push`` et ``pull_request``) du dispatcher ;
  2. chaque self-cover du dispatcher existe bien sur le disque (chemin
     mort = garde muette) ;
  3. aucun lake du manifeste ne garde son dispatcher historique
     ``lean-<lake>.yml`` : les deux declencheurs ensemble produiraient un
     DOUBLE build du meme lake sur la meme PR.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_MANIFEST = REPO_ROOT / "scripts" / "lean" / "ci_lakes.json"
DEFAULT_WORKFLOW = (REPO_ROOT / ".github" / "workflows" /
                    "lean-ci-matrix.yml")


def workflow_paths(doc: dict, event: str) -> set[str]:
    trig = doc.get("on") or doc.get(True)
    return set(trig.get(event, {}).get("paths", []))


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    ap.add_argument("--workflow", type=Path, default=DEFAULT_WORKFLOW)
    ap.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    args = ap.parse_args(argv)

    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    doc = yaml.safe_load(args.workflow.read_text(encoding="utf-8"))
    push = workflow_paths(doc, "push")
    pr = workflow_paths(doc, "pull_request")

    errors: list[str] = []
    for lake in manifest["lakes"]:
        for p in lake["paths"]:
            for event, surface in (("push", push), ("pull_request", pr)):
                if p not in surface:
                    errors.append(
                        f"lake {lake['lake']}: chemin {p!r} absent du "
                        f"on.paths[{event}] de {args.workflow.name} -- la "
                        f"CI de ce lake ne se declenche plus")
        legacy = args.repo_root / ".github" / "workflows" / f"lean-{lake['lake']}.yml"
        if legacy.exists():
            errors.append(
                f"lake {lake['lake']}: le dispatcher historique "
                f"{legacy.name} existe encore ALORS que le lake est au "
                f"manifeste -- double declencheur = double build")

    for p in sorted(push | pr):
        if p.startswith((".github/", "scripts/")) and not (args.repo_root / p).exists():
            errors.append(
                f"self-cover {p!r} du dispatcher n'existe pas sur le disque")

    if errors:
        for e in errors:
            print(f"LAKE-MATRIX DRIFT: {e}", file=sys.stderr)
        return 1
    n = len(manifest["lakes"])
    print(f"lake-matrix OK : {n} lake(s) couvert(s), union push/pr "
          f"coherente avec le manifeste, aucun double declencheur")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Organe de pin de version des runners Linux self-hosted (#15201).

Le compromis accepte (#15182) porte un cout cache : `--disableupdate` fige
la version du runner a celle de l'image. Le rebuild etant manuel, l'ecart
entre la version epinglee et l'exigence GitHub courante grandit sans que
rien ne le voie — le mode de panne est SILENCIEUX du point de vue du parc :
les slots restent enregistres et `online`, et c'est GitHub qui refuse de
leur confier un job ("required runner version"). Vu du superviseur, rien ne
rougit : ni conteneur en erreur, ni boucle, ni sentinel. Un organe qui dit
"online" ne mesure pas "eligible".

Cet organe compare la version epinglee a l'exigence GitHub courante
(`repos/actions/runner/releases/latest`) et nomme l'ecart. Il verifie aussi
que les quatre sites de la pin sont en phase (la "verification
cross-fichiers" de la review) :

- `scripts/ci/docker/linux-runner/Dockerfile`      : `ARG RUNNER_VERSION=`
- `scripts/ci/docker/linux-runner/Dockerfile.lean`: `FROM coursia-linux-runner:<v>`
- `scripts/ci/docker/linux-runner/supervise.sh`    : `COURSIA_RUNNER_IMAGE` /
                                                    `COURSIA_LEAN_RUNNER_IMAGE`
- `scripts/ci/docker/linux-runner/entrypoint.sh`   : prose (le geste de bump
                                                    vit ici, en UN seul endroit)

Sorties :

- rc 0 : pin a jour et en phase — l'exigence courante est <= pinnee.
- rc 1 : PIN_STALE (pin < exigence GitHub courante) ou IN_PHASE_FAILURE
  (les sites ne s'accordent pas). Le rapport nomme le mode de panne
  "online mais non eligible".
- rc 2 : UNKNOWN — l'exigence GitHub n'a pas pu etre lue (403 / timeout /
  reseau). Une lecture ratee n'est pas une absence mesuree : on ne rend
  jamais "a jour" sur un defaut de lecture.

Run (CI) :
    python scripts/ci/check_runner_version_pin.py [--repo-root DIR]
                [--required-version X.Y.Z]   # injection test, sinon GitHub API
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

# Sites machine-assertables de la pin. Chaque site expose son versionneur.
PIN_SITES = {
    "Dockerfile:ARG": lambda text: _first(
        re.search(r"^ARG RUNNER_VERSION=([0-9]+\.[0-9]+\.[0-9]+)", text, re.M)
    ),
    "Dockerfile.lean:FROM": lambda text: _first(
        re.search(
            r"^FROM coursia-linux-runner:([0-9]+\.[0-9]+\.[0-9]+)", text, re.M
        )
    ),
    "supervise.sh:IMAGE": lambda text: _first(
        re.search(
            r"COURSIA_RUNNER_IMAGE:-coursia-linux-runner:([0-9]+\.[0-9]+\.[0-9]+)",
            text,
        )
    ),
    "supervise.sh:LEAN_IMAGE": lambda text: _first(
        re.search(
            r"COURSIA_LEAN_RUNNER_IMAGE:-coursia-lean-runner:([0-9]+\.[0-9]+\.[0-9]+)",
            text,
        )
    ),
}


def _first(m: re.Match | None) -> str | None:
    return m.group(1) if m else None


def parse_pins(repo_root: Path) -> dict[str, str | None]:
    """Lit la pin de chaque site machine-assertable du runner dir.

    `--repo-root` est le point d'entree : les tests hermétiques injectent un
    faux depot, le CI laisse le defaut derive de `__file__`.
    """
    runner_dir = repo_root / "scripts" / "ci" / "docker" / "linux-runner"
    pins: dict[str, str | None] = {}
    for site, versionner in PIN_SITES.items():
        filename = site.split(":", 1)[0]
        try:
            pins[site] = versionner((runner_dir / filename).read_text(encoding="utf-8"))
        except OSError as e:
            pins[site] = f"<lecture impossible: {e.__class__.__name__}>"
    return pins


def fetch_required_version(gh: list[str] | None = None) -> str | None:
    """Exigence GitHub courante via `gh api repos/actions/runner/releases/latest`.

    Retourne None si la lecture echoue (jamais de valeur par defaut : un 403
    est une question, pas une absence mesuree, cf. #15342).
    """
    cmd = gh or ["gh", "api", "repos/actions/runner/releases/latest", "--jq", ".tag_name"]
    try:
        r = subprocess.run(
            cmd, capture_output=True, text=True, encoding="utf-8", timeout=30
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if r.returncode != 0:
        return None
    m = re.search(r"v?([0-9]+\.[0-9]+\.[0-9]+)", r.stdout.strip())
    return m.group(1) if m else None


def version_key(v: str) -> tuple[int, ...]:
    return tuple(int(x) for x in v.split("."))


def report(pins: dict[str, str | None], required: str | None) -> dict:
    """Verdict de l'organe : phase + ecart vis-a-vis de l'exigence GitHub."""
    # Une valeur non-versionnee (lecture impossible, regex sans hit) est une
    # erreur de mesure, pas une pin : on ne peut pas la comparer.
    bad = [
        s
        for s, v in pins.items()
        if not re.fullmatch(r"[0-9]+\.[0-9]+\.[0-9]+", v or "")
    ]
    if bad:
        return {
            "guard_pass": False,
            "status": "IN_PHASE_FAILURE",
            "detail": "site(s) de pin illisible ou non versionne : "
            + ", ".join(bad),
            "pins": pins,
            "required_version": required,
            "exit_code": 1,
        }
    values = list(pins.values())
    if len(set(values)) > 1:
        return {
            "guard_pass": False,
            "status": "IN_PHASE_FAILURE",
            "detail": "les sites de pin ne s'accordent pas",
            "pins": pins,
            "required_version": required,
            "exit_code": 1,
        }
    pinned = values[0]
    if required is None:
        return {
            # Rien a comparer : ni pass ni fail -- un defaut de lecture ne
            # justifie pas un vert (exit 2 le fait rougir en CI, advisory).
            "guard_pass": None,
            "status": "UNCHECKED_REQUIREMENT",
            "detail": "exigence GitHub illisible (403/timeout) — aucun verdict",
            "pins": pins,
            "pinned_version": pinned,
            "required_version": None,
            "exit_code": 2,
        }
    stale = version_key(pinned) < version_key(required)
    return {
        "guard_pass": not stale,
        "status": "PIN_STALE" if stale else "PIN_OK",
        "detail": (
            "online mais non eligible : la pin "
            f"{pinned} est derriere l'exigence GitHub {required} — bump par "
            "rebuild (ARG RUNNER_VERSION du Dockerfile), jamais a chaud"
            if stale
            else f"pin {pinned} >= exigence {required}"
        ),
        "pins": pins,
        "pinned_version": pinned,
        "required_version": required,
        "exit_code": 1 if stale else 0,
    }


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    ap.add_argument("--required-version", default=None,
                    help="exigence GitHub (injection test; defaut: API live)")
    args = ap.parse_args(argv)

    pins = parse_pins(args.repo_root)
    required = args.required_version or fetch_required_version()
    verdict = report(pins, required)

    print(json.dumps(verdict, indent=2, ensure_ascii=False))
    if verdict["exit_code"] == 1:
        print(f"[RUNNER-VERSION-PIN] {verdict['status']} : {verdict['detail']}")
    elif verdict["exit_code"] == 2:
        print("[RUNNER-VERSION-PIN] UNKNOWN : exigence GitHub illisible — "
              "enqueter avant de conclure quoi que ce soit.")
    else:
        print(f"[RUNNER-VERSION-PIN] {verdict['status']} : {verdict['detail']}")
    return verdict["exit_code"]


if __name__ == "__main__":
    sys.exit(main())
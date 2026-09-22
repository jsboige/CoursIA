#!/usr/bin/env python3
"""Forge an installation access token for a per-lane GitHub App.

Why this organ exists (#17437): the fleet's congestion is a *shared* GraphQL
bucket. Every lane signs as one GitHub login, so its 5000 req/h is divided by
the number of lanes, and the merge gate -- which is GraphQL -- is the first
thing to starve. Per-lane machine accounts do not fix it: GitHub's Terms allow
one free machine account per person, and the cohort created 2026-09-22 was
measured at the *unauthenticated* tier (REST 60/h, GraphQL 0/0) on three
distinct accounts. A GitHub App installation carries its OWN bucket.

The token this prints lives one hour. It is never written to disk, never
persisted into `gh`'s shared configuration, and never echoed back with the
private key that produced it.

Examples:
  python scripts/secrets/github_app_token.py --app-id 123456 \
      --key ~/.secrets/coursia-lane-po-2024.pem --repo jsboige/CoursIA
  export GH_TOKEN="$(python scripts/secrets/github_app_token.py ... --quiet)"
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

EXIT_OK = 0
EXIT_DEFECT = 1
EXIT_UNREACHABLE = 2

JWT_SKEW_SECONDS = 60
JWT_TTL_SECONDS = 540  # GitHub refuses a JWT whose exp is more than 10 min out.


class ForgeError(RuntimeError):
    """The organ cannot prove the token it would return is the right one."""


def _read_private_key(path: Path) -> str:
    """Read the PEM. A missing or non-PEM file is a DEFECT, never a warning."""
    try:
        pem = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise ForgeError(f"cannot read private key at {path}: {exc}") from exc
    if "PRIVATE KEY" not in pem:
        # Deliberately does NOT echo the content: a wrong file is often a
        # secret of another kind, and printing it is how one leak becomes two.
        raise ForgeError(f"{path} does not look like a PEM private key")
    return pem


def build_jwt(app_id: str, pem: str, now: int) -> str:
    """Sign the app-level JWT. `now` is injected so tests are deterministic."""
    try:
        import jwt  # PyJWT
    except ImportError as exc:  # pragma: no cover - environment failure
        raise ForgeError("PyJWT is required: pip install 'pyjwt[crypto]'") from exc
    payload = {
        "iat": now - JWT_SKEW_SECONDS,
        "exp": now + JWT_TTL_SECONDS,
        "iss": str(app_id),
    }
    return jwt.encode(payload, pem, algorithm="RS256")


def _api(endpoint: str, bearer: str, method: str = "GET") -> object:
    """One call through `gh api`, with the credential passed in the ENVIRONMENT.

    Never `gh auth login`: that writes into a configuration shared by every
    lane on the machine, so a wrong identity installed there outlives the
    mistake and hits the neighbouring sessions (#17425).
    """
    import os

    cmd = ["gh", "api", endpoint, "-X", method,
           "-H", "Accept: application/vnd.github+json"]
    env = {**os.environ, "GH_TOKEN": bearer, "GH_HOST": "github.com"}
    proc = subprocess.run(cmd, capture_output=True, text=True,
                          encoding="utf-8", errors="replace",
                          timeout=60, env=env)
    if proc.returncode != 0:
        raise ForgeError(f"`gh api {endpoint}` failed: {proc.stderr.strip()[:300]}")
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise ForgeError(f"`gh api {endpoint}` returned non-JSON") from exc


def resolve_installation(jwt_token: str, repo: str | None, owner: str | None) -> int:
    """Find the installation id, from the repo when possible."""
    if repo:
        data = _api(f"repos/{repo}/installation", jwt_token)
    elif owner:
        data = _api(f"users/{owner}/installation", jwt_token)
    else:
        raise ForgeError("need --installation-id, or --repo, or --owner")
    if not isinstance(data, dict) or "id" not in data:
        raise ForgeError("installation lookup returned no id")
    return int(data["id"])


def mint(jwt_token: str, installation_id: int) -> dict:
    data = _api(f"app/installations/{installation_id}/access_tokens",
                jwt_token, method="POST")
    if not isinstance(data, dict) or not data.get("token"):
        raise ForgeError("installation token endpoint returned no token")
    return data


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--app-id", required=True)
    p.add_argument("--key", required=True, type=Path, help="path to the PEM")
    p.add_argument("--installation-id", type=int)
    p.add_argument("--repo", help="owner/name -- resolves the installation")
    p.add_argument("--owner", help="account login -- resolves the installation")
    p.add_argument("--quiet", action="store_true",
                   help="print the token alone, for command substitution")
    args = p.parse_args(argv)

    try:
        pem = _read_private_key(args.key)
        jwt_token = build_jwt(args.app_id, pem, int(time.time()))
        installation_id = args.installation_id or resolve_installation(
            jwt_token, args.repo, args.owner)
        data = mint(jwt_token, installation_id)
    except ForgeError as exc:
        print(f"DEFECT: {exc}", file=sys.stderr)
        return EXIT_DEFECT
    except subprocess.TimeoutExpired:
        print("UNREACHABLE: GitHub did not answer in time.", file=sys.stderr)
        return EXIT_UNREACHABLE

    token = data["token"]
    if args.quiet:
        print(token)
        return EXIT_OK

    print(token)
    print(f"  installation : {installation_id}", file=sys.stderr)
    print(f"  expires_at   : {data.get('expires_at', '?')}", file=sys.stderr)
    print("  the token is NOT written to disk and NOT installed into `gh`.",
          file=sys.stderr)
    return EXIT_OK


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Enregistre les GitHub Apps de lane par le flux App Manifest (#17437, Q39).

Une App = un clic. La page locale porte un formulaire par lane, chacun avec son
manifeste pre-rempli (nom, permissions, webhook inactif). Apres « Create GitHub
App », GitHub renvoie un `code` temporaire vers le callback local, qui l'echange
contre la configuration de l'App (`POST /app-manifests/{code}/conversions`, sans
authentification, valable une heure). La cle privee est ecrite directement dans
`.secrets/github-apps/<slug>.pem` : aucun telechargement a la main, aucune cle
qui transite par un dossier de telechargements.

L'ensemble de permissions est UNE constante (`PERMISSIONS`), la meme pour toutes
les lanes. Arbitrage user du 2026-09-22 (Q39) : « donne tous les droits qui
fluidifient notre workflow ». Chaque droit y est justifie par un usage mesure
dans le depot ; deux sont ecartes avec leur motif (voir `EXCLUDED`).

Usage :
    python scripts/secrets/github_app_manifest.py                 # etat par lane (lecture seule)
    python scripts/secrets/github_app_manifest.py --print-manifest po-2023
    python scripts/secrets/github_app_manifest.py --serve         # page locale + callback

Ce qui reste un geste user : etre connecte a GitHub sous `jsboige`, cliquer
« Create GitHub App » puis « Install » (le depot CoursIA est pre-selectionne).
"""
from __future__ import annotations

import argparse
import html
import json
import os
import secrets
import subprocess
import sys
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path
from typing import Callable

REPO_ROOT = Path(__file__).resolve().parents[2]
KEY_DIR = REPO_ROOT / ".secrets" / "github-apps"
REPO = "jsboige/CoursIA"
REPO_URL = f"https://github.com/{REPO}"
# Identifiants publics, lus par `gh api repos/jsboige/CoursIA` le 2026-09-22 ;
# ils ne servent qu'a pre-selectionner le depot sur la page d'installation.
REPO_ID = 526622110
OWNER_ID = 3159389

APP_PREFIX = "coursia-lane-"
# Le pilote `coursia-lane-ai-01` existe deja (App 5036190) : il n'est pas recree,
# il s'aligne sur PERMISSIONS depuis sa page de reglages.
LANES = ("po-2023", "po-2024", "po-2025", "po-2026", "po-2027", "web1")

PERMISSIONS = {
    "metadata": "read",            # obligatoire pour toute App
    "contents": "write",           # push de branches, update-branch
    "pull_requests": "write",      # PR, reviews, levees, merge
    "issues": "write",             # claims, commentaires, labels
    "workflows": "write",          # edition de .github/workflows/** (Q39)
    "actions": "write",            # rerun (50 appels), cancel (pr_gate.py), workflow_dispatch, caches
    "checks": "read",
    "statuses": "read",
    "administration": "read",      # protection de branche lisible (#9991), actions/runners
    "security_events": "read",     # alertes CodeQL (codeql-suppressions-inertes.md)
    "vulnerability_alerts": "read",  # alertes Dependabot
    "secret_scanning_alerts": "read",
}

# Droits ecartes malgre « tous les droits » : aucun usage de lane ne les demande,
# et chacun ouvre une capacite que le workflow n'a pas aujourd'hui.
EXCLUDED = {
    "checks": "write -- seules les Apps peuvent CREER un check-run : ce serait donner a "
              "chaque lane le moyen de fabriquer un vert que le merge-gate lit",
    "administration": "write -- suppression du depot, levee de la protection de main",
    "secrets": "any -- lecture/ecriture des secrets du depot",
}

CONVERSION_URL = "https://api.github.com/app-manifests/{code}/conversions"
# Champs de la reponse de conversion qui sont des secrets : jamais ecrits hors du .pem.
SECRET_FIELDS = ("pem", "client_secret", "webhook_secret")


def app_name(lane: str) -> str:
    return f"{APP_PREFIX}{lane}"


def build_manifest(lane: str, redirect_url: str) -> dict:
    """Manifeste d'une lane. Webhook inactif, aucun evenement, App privee."""
    return {
        "name": app_name(lane),
        "url": REPO_URL,
        "description": f"Jeton d'installation de la lane {lane} sur {REPO} (bucket API propre).",
        "hook_attributes": {"url": REPO_URL, "active": False},
        "redirect_url": redirect_url,
        "public": False,
        "default_permissions": dict(PERMISSIONS),
        "default_events": [],
    }


def install_url(slug: str) -> str:
    """Page d'installation avec le compte et le depot CoursIA pre-selectionnes."""
    query = urllib.parse.urlencode(
        [("suggested_target_id", OWNER_ID), ("repository_ids[]", REPO_ID)])
    return f"https://github.com/apps/{slug}/installations/new/permissions?{query}"


def lane_status(key_dir: Path = KEY_DIR) -> dict[str, bool]:
    """Lane -> True si sa cle est deja deposee (App creee et convertie)."""
    return {lane: (key_dir / f"{app_name(lane)}.pem").exists() for lane in LANES}


def permission_mismatches(granted: dict) -> list[str]:
    """Ecarts entre les permissions accordees et PERMISSIONS (vide = conforme)."""
    out = []
    for key in sorted(set(PERMISSIONS) | set(granted or {})):
        want, got = PERMISSIONS.get(key), (granted or {}).get(key)
        if want != got:
            out.append(f"{key}: attendu {want}, obtenu {got}")
    return out


def is_git_ignored(path: Path) -> bool:
    """`git check-ignore` sur le chemin cible : la cle ne doit jamais etre commitable.

    Interroge le depot qui CONTIENT le chemin (le dossier peut ne pas exister encore).
    """
    anchor = path.parent
    while not anchor.exists():
        anchor = anchor.parent
    proc = subprocess.run(["git", "-C", str(anchor), "check-ignore", "-q", str(path)],
                          capture_output=True)
    return proc.returncode == 0


def store(app: dict, key_dir: Path = KEY_DIR,
          ignored: Callable[[Path], bool] = is_git_ignored) -> Path:
    """Ecrit la cle privee et une fiche sans secret. Refuse d'ecraser, refuse hors gitignore."""
    slug = app["slug"]
    key_dir.mkdir(parents=True, exist_ok=True)
    pem_path = key_dir / f"{slug}.pem"
    if not ignored(pem_path):
        raise RuntimeError(f"{pem_path} n'est pas ignore par git : cle non ecrite")
    fd = os.open(pem_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, "w", encoding="ascii", newline="\n") as fh:
        fh.write(app["pem"])
    meta = {k: v for k, v in app.items() if k not in SECRET_FIELDS}
    fiche = {
        "id": meta.get("id"),
        "slug": slug,
        "client_id": meta.get("client_id"),
        "owner": (meta.get("owner") or {}).get("login"),
        "permissions": meta.get("permissions"),
        "events": meta.get("events"),
        "created_at": meta.get("created_at"),
    }
    (key_dir / f"{slug}.json").write_text(
        json.dumps(fiche, indent=2) + "\n", encoding="utf-8")
    return pem_path


def convert(code: str) -> dict:
    """Echange le code temporaire contre la configuration de l'App (sans authentification)."""
    req = urllib.request.Request(
        CONVERSION_URL.format(code=urllib.parse.quote(code, safe="")),
        method="POST",
        headers={"Accept": "application/vnd.github+json",
                 "X-GitHub-Api-Version": "2022-11-28"})
    with urllib.request.urlopen(req, timeout=30) as resp:
        return json.loads(resp.read().decode("utf-8"))


def render_page(status: dict[str, bool], state: str, redirect_url: str) -> str:
    rows = []
    for lane, done in status.items():
        if done:
            rows.append(f"<li><b>{html.escape(app_name(lane))}</b> : deja creee (cle deposee)</li>")
            continue
        manifest = html.escape(json.dumps(build_manifest(lane, redirect_url)), quote=True)
        action = f"https://github.com/settings/apps/new?state={urllib.parse.quote(state)}"
        rows.append(
            f'<li><form action="{html.escape(action, quote=True)}" method="post" target="_blank">'
            f'<input type="hidden" name="manifest" value="{manifest}">'
            f'<button type="submit">Creer {html.escape(app_name(lane))}</button></form></li>')
    perms = "".join(f"<li><code>{html.escape(k)}: {html.escape(v)}</code></li>"
                    for k, v in PERMISSIONS.items())
    return ("<!doctype html><html lang=\"fr\"><meta charset=\"utf-8\">"
            "<title>Apps de lane CoursIA</title><body>"
            "<h1>Apps de lane CoursIA</h1>"
            "<p>Connecte sous <b>jsboige</b>. Un bouton = une App ; apres creation, "
            "cette page recoit la cle et affiche le lien d'installation.</p>"
            f"<ul>{''.join(rows)}</ul><h2>Permissions (identiques pour chaque lane)</h2>"
            f"<ul>{perms}</ul></body></html>")


def make_handler(state: str, redirect_url: str, key_dir: Path = KEY_DIR,
                 converter: Callable[[str], dict] = convert,
                 storer: Callable[[dict], Path] | None = None):
    storer = storer or (lambda app: store(app, key_dir))

    class Handler(BaseHTTPRequestHandler):
        def _send(self, code: int, body: str) -> None:
            data = body.encode("utf-8")
            self.send_response(code)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            self.wfile.write(data)

        def log_message(self, fmt, *args):  # le code temporaire passe dans l'URL : ne pas le journaliser
            return

        def do_GET(self):
            url = urllib.parse.urlparse(self.path)
            if url.path == "/":
                return self._send(200, render_page(lane_status(key_dir), state, redirect_url))
            if url.path != "/callback":
                return self._send(404, "introuvable")
            query = urllib.parse.parse_qs(url.query)
            if query.get("state", [""])[0] != state:
                return self._send(400, "state invalide : requete refusee")
            code = query.get("code", [""])[0]
            if not code:
                return self._send(400, "code absent")
            try:
                app = converter(code)
                storer(app)
            except (urllib.error.URLError, RuntimeError, OSError, KeyError) as exc:
                print(f"ECHEC conversion/depot : {type(exc).__name__}: {exc}", file=sys.stderr)
                return self._send(500, f"echec : {html.escape(type(exc).__name__)} -- voir la console")
            slug = app["slug"]
            gaps = permission_mismatches(app.get("permissions"))
            print(f"OK {slug} (App {app.get('id')}) -> cle deposee ; ecarts de permissions : {gaps or 'aucun'}")
            warn = ("<p><b>ECARTS de permissions :</b> " + html.escape("; ".join(gaps)) + "</p>") if gaps else ""
            link = html.escape(install_url(slug), quote=True)
            return self._send(200, f"<!doctype html><meta charset=\"utf-8\"><p>{html.escape(slug)} creee, "
                                   f"cle deposee.</p>{warn}<p><a href=\"{link}\">Installer sur CoursIA</a></p>"
                                   "<p><a href=\"/\">Retour a la liste</a></p>")

    return Handler


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--print-manifest", metavar="LANE", choices=LANES,
                   help="affiche le manifeste d'une lane (lecture seule)")
    p.add_argument("--serve", action="store_true", help="page locale + callback de conversion")
    p.add_argument("--port", type=int, default=8765)
    p.add_argument("--no-browser", action="store_true")
    p.add_argument("--secrets-dir", dest="key_dir", type=Path, default=KEY_DIR,
                   help="depot des cles (defaut : .secrets/github-apps du clone)")
    args = p.parse_args(argv)
    key_dir = args.key_dir.resolve()

    redirect_url = f"http://localhost:{args.port}/callback"
    if args.print_manifest:
        print(json.dumps(build_manifest(args.print_manifest, redirect_url), indent=2))
        return 0
    status = lane_status(key_dir)
    for lane, done in status.items():
        print(f"{app_name(lane):24} {'cle deposee' if done else 'a creer'}")
    if not args.serve:
        return 0
    if not is_git_ignored(key_dir / "probe.pem"):
        print(f"REFUS : {key_dir} n'est pas ignore par git", file=sys.stderr)
        return 1
    state = secrets.token_urlsafe(32)
    server = HTTPServer(("127.0.0.1", args.port), make_handler(state, redirect_url, key_dir))
    print(f"Page : http://localhost:{args.port}/  (Ctrl+C pour arreter)")
    if not args.no_browser:
        webbrowser.open(f"http://localhost:{args.port}/")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    return 0


if __name__ == "__main__":
    sys.exit(main())

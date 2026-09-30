"""Tests de scripts/secrets/github_app_manifest.py (#17437, Q39).

Aucun appel reseau : la conversion et le depot sont injectes. Le systeme de
fichiers reel n'est jamais touche (tmp_path).
"""
import html
import json
import re
import sys
import threading
import urllib.error
import urllib.request
from http.server import HTTPServer
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import github_app_manifest as gam  # noqa: E402

REDIRECT = "http://localhost:8765/callback"


def _app(slug="coursia-lane-po-2023", permissions=None):
    return {
        "id": 42, "slug": slug, "client_id": "Iv1.public",
        "owner": {"login": "jsboige"}, "events": [],
        "permissions": dict(gam.PERMISSIONS) if permissions is None else permissions,
        "created_at": "2026-09-22T21:30:00Z",
        "pem": "-----BEGIN RSA PRIVATE KEY-----\nFAKE\n-----END RSA PRIVATE KEY-----\n",
        "client_secret": "cs-fake", "webhook_secret": "wh-fake",
    }


# --- politique de permissions -------------------------------------------------

def test_manifest_carries_exactly_the_policy():
    m = gam.build_manifest("po-2023", REDIRECT)
    assert m["name"] == "coursia-lane-po-2023"
    assert m["default_permissions"] == gam.PERMISSIONS
    assert m["public"] is False
    assert m["hook_attributes"]["active"] is False
    assert m["default_events"] == []
    assert m["redirect_url"] == REDIRECT


def test_q39_rights_are_granted():
    for key, level in {"workflows": "write", "actions": "write", "contents": "write",
                       "pull_requests": "write", "issues": "write"}.items():
        assert gam.PERMISSIONS[key] == level, key


def test_excluded_rights_stay_excluded():
    # Un check-run ne peut etre CREE que par une App : checks=write donnerait a chaque
    # lane le moyen de fabriquer le vert que lit le merge-gate.
    assert gam.PERMISSIONS["checks"] == "read"
    assert gam.PERMISSIONS["administration"] == "read"
    assert "secrets" not in gam.PERMISSIONS
    assert set(gam.EXCLUDED) == {"checks", "administration", "secrets"}


def test_pilot_is_not_recreated():
    assert "ai-01" not in gam.LANES
    assert len(gam.LANES) == 6


def test_permission_mismatches():
    assert gam.permission_mismatches(dict(gam.PERMISSIONS)) == []
    got = dict(gam.PERMISSIONS, actions="read", pages="read")
    gaps = gam.permission_mismatches(got)
    assert any(g.startswith("actions:") for g in gaps)
    assert any(g.startswith("pages:") for g in gaps)


# --- page ---------------------------------------------------------------------

def test_page_round_trips_the_manifest():
    status = {lane: False for lane in gam.LANES}
    page = gam.render_page(status, "st4te", REDIRECT)
    values = re.findall(r'name="manifest" value="([^"]*)"', page)
    assert len(values) == len(gam.LANES)
    assert json.loads(html.unescape(values[0])) == gam.build_manifest(gam.LANES[0], REDIRECT)
    assert "state=st4te" in page


def test_page_skips_created_lanes():
    status = {lane: lane == "po-2024" for lane in gam.LANES}
    page = gam.render_page(status, "s", REDIRECT)
    assert page.count('name="manifest"') == len(gam.LANES) - 1
    assert "coursia-lane-po-2024</b> : deja creee" in page


def test_install_url_preselects_the_repo():
    url = gam.install_url("coursia-lane-po-2023")
    assert url.startswith("https://github.com/apps/coursia-lane-po-2023/installations/new/permissions?")
    assert f"suggested_target_id={gam.OWNER_ID}" in url
    assert f"repository_ids%5B%5D={gam.REPO_ID}" in url


# --- depot de la cle ----------------------------------------------------------

def test_store_writes_pem_and_a_secret_free_card(tmp_path):
    pem = gam.store(_app(), tmp_path, ignored=lambda p: True)
    assert pem.read_text(encoding="ascii").startswith("-----BEGIN RSA PRIVATE KEY-----")
    card = (tmp_path / "coursia-lane-po-2023.json").read_text(encoding="utf-8")
    for secret in ("FAKE", "cs-fake", "wh-fake"):
        assert secret not in card
    assert json.loads(card)["id"] == 42


def test_store_refuses_to_overwrite(tmp_path):
    gam.store(_app(), tmp_path, ignored=lambda p: True)
    with pytest.raises(FileExistsError):
        gam.store(_app(), tmp_path, ignored=lambda p: True)


def test_store_refuses_a_non_ignored_path(tmp_path):
    with pytest.raises(RuntimeError):
        gam.store(_app(), tmp_path, ignored=lambda p: False)
    assert not (tmp_path / "coursia-lane-po-2023.pem").exists()


def test_secrets_dir_is_ignored_by_the_versioned_rule():
    # Controle positif : la cle d'une App doit etre ignoree par .gitignore versionne,
    # pas seulement par un .git/info/exclude local (qui n'existe pas sur les autres clones).
    rule = (gam.REPO_ROOT / ".gitignore").read_text(encoding="utf-8").splitlines()
    assert ".secrets/" in rule


def test_lane_status(tmp_path):
    (tmp_path / "coursia-lane-web1.pem").write_text("x")
    status = gam.lane_status(tmp_path)
    assert status["web1"] is True
    assert status["po-2023"] is False


# --- callback -----------------------------------------------------------------

@pytest.fixture
def server(tmp_path):
    calls = {"convert": [], "store": []}

    def converter(code):
        calls["convert"].append(code)
        return _app()

    def storer(app):
        calls["store"].append(app["slug"])
        return tmp_path / f"{app['slug']}.pem"

    handler = gam.make_handler("good-state", REDIRECT, tmp_path, converter, storer)
    srv = HTTPServer(("127.0.0.1", 0), handler)
    thread = threading.Thread(target=srv.serve_forever, daemon=True)
    thread.start()
    yield f"http://127.0.0.1:{srv.server_address[1]}", calls
    srv.shutdown()


def _get(url):
    try:
        with urllib.request.urlopen(url, timeout=5) as resp:
            return resp.status, resp.read().decode("utf-8")
    except urllib.error.HTTPError as exc:
        return exc.code, exc.read().decode("utf-8")


def test_callback_rejects_a_bad_state(server):
    base, calls = server
    code, _ = _get(f"{base}/callback?code=abc&state=forged")
    assert code == 400
    assert calls["convert"] == []


def test_callback_converts_and_links_install(server):
    base, calls = server
    code, body = _get(f"{base}/callback?code=abc&state=good-state")
    assert code == 200
    assert calls["convert"] == ["abc"]
    assert calls["store"] == ["coursia-lane-po-2023"]
    assert "installations/new/permissions" in body
    assert "FAKE" not in body


def test_index_lists_the_lanes(server):
    base, _ = server
    code, body = _get(f"{base}/")
    assert code == 200
    assert "coursia-lane-web1" in body

#!/usr/bin/env python3
"""La derive de gitlink se mesure, elle ne se devine pas (Regle 2).

Ce que ce fichier garde
-----------------------
``scripts/coordination/submodule_watch.py`` mesure la Regle 2 : le gitlink
epingle dans l'arbre de CoursIA contre la tete de la branche declaree dans
``.gitmodules``. L'egalite des SHA ne dit pas *combien* le sous-module a
derive : une derive de 3 commits et une derive de 26 ne se traitent pas de la
meme facon. C'est pourquoi l'organe mesure la distance (``ahead_by`` de l'API
``compare``) et ne signale un bump en retard qu'au-dela d'un seuil.

Les trois pieges que ces tests verrouillent :

- **une mesure absente n'est jamais un zero.** Un ``compare`` muet, une erreur
  HTTP, une reponse sans ``ahead_by`` : le resultat est ``None`` (inconnu), et
  l'inconnu ne fait **jamais** passer une derive pour une egalite, ni faire
  rougir une CI de veille sur un incident de reseau ;
- **une derive courte n'est pas un retard.** Sous le seuil, rc 0 : le pin suit
  au rythme des bumps, c'est le fonctionnement normal ;
- **un depot muet n'est pas une egalite.** Un ``ls-remote`` sans reponse donne
  ``INJOIGNABLE``, jamais ``OK`` (Regle 2, R2).

Ce que ce test ne fait pas
--------------------------
Il ne lit pas le reseau : l'appel REST est injecte, et le comportement de
``gitlink_drift`` est verifie sur un faux ``git`` (ls-tree / ls-remote). La
mesure reelle est celle du rapport de l'organe, pas celle d'un test.
"""
from __future__ import annotations

import importlib.util
import json
import os
import sys
from urllib.error import HTTPError

import yaml

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
MODULE_PATH = os.path.join(ROOT, "scripts", "coordination", "submodule_watch.py")
WORKFLOW_PATH = os.path.join(ROOT, ".github", "workflows", "submodule-drift.yml")

_spec = importlib.util.spec_from_file_location("submodule_watch", MODULE_PATH)
assert _spec and _spec.loader
submodule_watch = importlib.util.module_from_spec(_spec)
sys.modules["submodule_watch"] = submodule_watch
_spec.loader.exec_module(submodule_watch)


class _FakeResponse:
    def __init__(self, payload):
        self._payload = payload

    def read(self):
        return json.dumps(self._payload).encode("utf-8")

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        return False


def _opener(payload):
    """Faux ``urlopen`` : renvoie un payload, ou leve l'exception donnee."""

    def opener(request, timeout=None):
        if isinstance(payload, Exception):
            raise payload
        return _FakeResponse(payload)

    return opener


def _fake_git(local, remote):
    """Faux runner git : ls-tree rend ``local``, ls-remote rend ``remote``."""

    class _Out:
        def __init__(self, text):
            self.returncode = 0
            self.stdout = text
            self.stderr = ""

    def run(cmd):
        if cmd[:2] == ["git", "ls-tree"]:
            return _Out(f"160000 commit {local}\tpath\n")
        if cmd[:2] == ["git", "ls-remote"]:
            return _Out(f"{remote}\trefs/heads/master\n" if remote else "")
        raise AssertionError(f"commande inattendue : {cmd}")

    return run


def _report(state, ahead):
    return {
        "repos": [
            {
                "path": "p",
                "slug": "o/r",
                "branch": "master",
                "drift": {
                    "state": state,
                    "remote_ref": "refs/heads/master",
                    "gitlink": "aaaa",
                    "remote_head": "bbbb",
                    "ahead_by": ahead,
                },
            }
        ]
    }


# --- compare_ahead : la distance, et ses absences ------------------------


def test_compare_ahead_returns_distance():
    assert submodule_watch.compare_ahead("o/r", "aaa", "bbb", _opener({"ahead_by": 26})) == 26


def test_compare_ahead_zero_is_a_measurement():
    """``ahead_by: 0`` est une mesure, pas une absence : elle vaut 0, pas None."""
    assert submodule_watch.compare_ahead("o/r", "aaa", "bbb", _opener({"ahead_by": 0})) == 0


def test_compare_ahead_http_error_is_unknown():
    err = HTTPError("https://api.github.com", 404, "Not Found", {}, None)
    assert submodule_watch.compare_ahead("o/r", "aaa", "bbb", _opener(err)) is None


def test_compare_ahead_payload_without_field_is_unknown():
    assert submodule_watch.compare_ahead("o/r", "aaa", "bbb", _opener({"status": "ahead"})) is None


def test_compare_ahead_boolean_is_not_a_distance():
    """Un booleen n'est pas une distance : ``True`` ne vaut pas 1 commit."""
    assert submodule_watch.compare_ahead("o/r", "aaa", "bbb", _opener({"ahead_by": True})) is None


def test_compare_ahead_without_identifiers_is_unknown():
    assert submodule_watch.compare_ahead(None, "aaa", "bbb", _opener({"ahead_by": 3})) is None
    assert submodule_watch.compare_ahead("o/r", None, "bbb", _opener({"ahead_by": 3})) is None
    assert submodule_watch.compare_ahead("o/r", "aaa", None, _opener({"ahead_by": 3})) is None


# --- drift_exit_code : le seuil, et ce qui ne fait pas rougir --------------


def test_drift_beyond_threshold_is_overdue():
    assert submodule_watch.drift_exit_code(_report("DERIVE", 26), 10) == 1


def test_drift_below_threshold_is_normal():
    """Une derive de 3 commits est le fonctionnement normal : rc 0."""
    assert submodule_watch.drift_exit_code(_report("DERIVE", 3), 10) == 0


def test_unmeasured_drift_does_not_fail():
    """Distance inconnue : on signale (rc 2), on ne fait pas rougir."""
    assert submodule_watch.drift_exit_code(_report("DERIVE", None), 10) == 2


def test_unreachable_repo_is_unknown():
    assert submodule_watch.drift_exit_code(_report("INJOIGNABLE", None), 10) == 2


def test_no_drift_is_quiet():
    assert submodule_watch.drift_exit_code(_report("OK", 0), 10) == 0


# --- gitlink_drift : les trois etats de la Regle 2 ------------------------


def test_gitlink_equal_is_ok():
    sub = {"path": "p", "url": "https://github.com/o/r", "branch": "master", "slug": "o/r"}
    out = submodule_watch.gitlink_drift(sub, "HEAD", _fake_git("aaaa", "aaaa"))
    assert out["state"] == "OK"
    assert out["ahead_by"] == 0


def test_gitlink_diverged_measures_distance():
    sub = {"path": "p", "url": "https://github.com/o/r", "branch": "master", "slug": "o/r"}
    out = submodule_watch.gitlink_drift(sub, "HEAD", _fake_git("aaaa", "bbbb"), _opener({"ahead_by": 26}))
    assert out["state"] == "DERIVE"
    assert out["ahead_by"] == 26


def test_gitlink_silent_remote_is_unreachable_not_ok():
    """Un ls-remote muet donne INJOIGNABLE : jamais une egalite."""
    sub = {"path": "p", "url": "https://github.com/o/r", "branch": "master", "slug": "o/r"}
    out = submodule_watch.gitlink_drift(sub, "HEAD", _fake_git("aaaa", None))
    assert out["state"] == "INJOIGNABLE"
    assert out["gitlink"] == "aaaa"
    assert out["remote_head"] is None


def test_branch_declared_is_used_not_head():
    """La branche declaree fait foi ; ``HEAD`` n'est le repli qu'en son absence."""
    seen = {}

    class _Out:
        def __init__(self, text):
            self.returncode = 0
            self.stdout = text
            self.stderr = ""

    def run(cmd):
        if cmd[:2] == ["git", "ls-remote"]:
            seen["remote_ref"] = cmd[-1]
            return _Out("")
        return _Out("160000 commit aaaa\tpath\n")

    sub = {"path": "p", "url": "https://github.com/o/r", "branch": "master", "slug": "o/r"}
    try:
        submodule_watch.gitlink_drift(sub, "HEAD", run)
    except AssertionError:
        pass
    assert seen["remote_ref"] == "refs/heads/master"


# --- le contrat du JSON, et le workflow qui le lit ------------------------


def test_unreachable_repo_has_no_distance():
    """Un depot muet n'a pas de distance : ``None``, jamais le ``0`` rassurant.

    Releve par la review du 2026-10-29 : ``INJOIGNABLE`` portait ``ahead_by: 0``,
    ce qu'un consommateur qui ne lit que ce champ traduit « pas de derive ». Le
    ``0`` est reserve a l'etat ``OK``, ou il est le resultat d'une mesure.
    """
    sub = {"path": "p", "url": "https://github.com/o/r", "branch": "master", "slug": "o/r"}
    out = submodule_watch.gitlink_drift(sub, "HEAD", _fake_git("aaaa", None))
    assert out["state"] == "INJOIGNABLE"
    assert out["ahead_by"] is None


def _drift_job():
    with open(WORKFLOW_PATH, encoding="utf-8") as fh:
        return yaml.safe_load(fh)["jobs"]["drift"]


def test_workflow_threshold_matches_the_module_default():
    """Le seuil du YAML et celui du script ne peuvent pas diverger en silence."""
    assert int(_drift_job()["env"]["MAX_AHEAD"]) == submodule_watch.DEFAULT_MAX_AHEAD


def test_workflow_never_decides_on_the_exit_code():
    """Python rend ``1`` sur une exception : le verdict ne doit pas lire ``rc``.

    C'est le defaut releve le 2026-10-29 : un plantage du script publiait
    « derive de gitlink au-dela du seuil » sur un artefact vide. La decision se
    prend sur ``drift.json``, et une mesure absente est une panne, pas une
    derive.
    """
    steps = _drift_job()["steps"]
    for step in steps:
        assert "outputs.rc" not in str(step.get("if", "")), step.get("name")
        assert "outputs.rc" not in (step.get("run") or ""), step.get("name")

    verdict = [s for s in steps if "verdict" in (s.get("name") or "").lower()]
    assert len(verdict) == 1, "un seul step de verdict : deux decisions divergeraient"
    body = verdict[0]["run"]
    assert "drift.json" in body
    assert "jq" in body
    # Le verdict distingue un artefact absent d'une derive mesuree.
    assert "! -s drift.json" in body


def test_workflow_is_advisory_on_pull_request_only():
    """Une derive anterieure a une PR n'est pas imputable a son auteur."""
    steps = _drift_job()["steps"]
    body = [s for s in steps if "verdict" in (s.get("name") or "").lower()][0]["run"]
    assert "GITHUB_EVENT_NAME" in body
    assert '"pull_request"' in body
    assert "::warning::" in body
    assert "::error::" in body

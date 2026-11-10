#!/usr/bin/env python3
"""Non-regression du job `changes` de ``lean-ci-matrix.yml`` (#22065).

Le trou : les deux lectures de l'API du job etaient repliees en silence
(``|| echo -n "" > "$out"``). Un 403 de quota rendait la liste des
fichiers modifies VIDE, donc ``any=false``, donc le build Lean etait
``skipped`` -- et ``skipped`` se replie en vert : un build qui n'a pas eu
lieu s'affichait comme fait (instance #21999, run 39814286963).

Ces tests verrouillent deux choses :

  1. une lecture d'API en echec **ne peut pas** produire une liste vide
     silencieuse -- l'appelant sort en erreur et **n'ecrit aucun fichier**
     de sortie ;
  2. le workflow lui-meme ne peut pas reintroduire le repli muet.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from lean_matrix_changed_files import (  # noqa: E402
    ApiError,
    SELF_COVER,
    main,
)

WORKFLOW = REPO / ".github" / "workflows" / "lean-ci-matrix.yml"


def _boom(*_args, **_kwargs):
    raise ApiError("gh api a echoue (rc=1) : API rate limit exceeded (HTTP 403)")


def test_1_echec_api_ne_produit_aucun_fichier(tmp_path, monkeypatch):
    """Le cas mesure (#21999) : 403 -> pas de liste vide, sortie non nulle."""
    monkeypatch.setattr("lean_matrix_changed_files._gh_api", _boom)
    monkeypatch.setattr("lean_matrix_changed_files.time.sleep", lambda _s: None)
    out = tmp_path / "changed.txt"
    rc = main([
        "--event", "pull_request", "--repo", "jsboige/CoursIA",
        "--pr", "21999", "--out", str(out), "--sleep", "0",
    ])
    assert rc == 1
    assert not out.exists(), "un echec de l'API ne doit ecrire aucun fichier"


def test_2_echec_api_apres_les_tentatives_reste_echec(tmp_path, monkeypatch):
    """Meme apres une nouvelle tentative, l'echec reste bruyant."""
    calls = {"n": 0}

    def _always_fail(*_args, **_kwargs):
        calls["n"] += 1
        raise ApiError("HTTP 403")

    monkeypatch.setattr("lean_matrix_changed_files._gh_api", _always_fail)
    monkeypatch.setattr("lean_matrix_changed_files.time.sleep", lambda _s: None)
    out = tmp_path / "changed.txt"
    rc = main([
        "--event", "pull_request", "--repo", "jsboige/CoursIA",
        "--pr", "21999", "--out", str(out), "--retries", "2", "--sleep", "0",
    ])
    assert rc == 1
    assert not out.exists()
    assert calls["n"] == 3, "2 tentatives + 1 = 3 appels"


def test_3_reussite_ecrit_la_liste(tmp_path, monkeypatch):
    monkeypatch.setattr(
        "lean_matrix_changed_files._gh_api",
        lambda *a, **k: "a.lean\nb.lean\n",
    )
    out = tmp_path / "changed.txt"
    rc = main([
        "--event", "pull_request", "--repo", "jsboige/CoursIA",
        "--pr", "21999", "--out", str(out),
    ])
    assert rc == 0
    assert out.read_text(encoding="utf-8").splitlines() == ["a.lean", "b.lean"]


def test_4_la_nouvelle_tentative_rattrape_le_403(tmp_path, monkeypatch):
    """Le 403 de quota est transitoire : le rejeu du job a reussi sur
    l'instance mesuree. Une tentative suffit a ne pas perdre le build."""
    calls = {"n": 0}

    def _fail_then_ok(*_args, **_kwargs):
        calls["n"] += 1
        if calls["n"] == 1:
            raise ApiError("HTTP 403")
        return "a.lean\n"

    monkeypatch.setattr("lean_matrix_changed_files._gh_api", _fail_then_ok)
    monkeypatch.setattr("lean_matrix_changed_files.time.sleep", lambda _s: None)
    out = tmp_path / "changed.txt"
    rc = main([
        "--event", "pull_request", "--repo", "jsboige/CoursIA",
        "--pr", "21999", "--out", str(out), "--sleep", "0",
    ])
    assert rc == 0
    assert out.read_text(encoding="utf-8").splitlines() == ["a.lean"]


def test_5_push_nouvelle_branche_donne_le_self_cover(tmp_path, monkeypatch):
    monkeypatch.setattr(
        "lean_matrix_changed_files._gh_api",
        lambda *a, **k: pytest.fail("aucun appel API sur une nouvelle branche"),
    )
    out = tmp_path / "changed.txt"
    rc = main([
        "--event", "push", "--repo", "jsboige/CoursIA",
        "--before", "0000000000000000000000000000000000000000",
        "--sha", "abc123", "--out", str(out),
    ])
    assert rc == 0
    assert out.read_text(encoding="utf-8").splitlines() == [SELF_COVER]


def test_6_workflow_dispatch_donne_le_self_cover(tmp_path, monkeypatch):
    monkeypatch.setattr(
        "lean_matrix_changed_files._gh_api",
        lambda *a, **k: pytest.fail("aucun appel API en workflow_dispatch"),
    )
    out = tmp_path / "changed.txt"
    rc = main([
        "--event", "workflow_dispatch", "--repo", "jsboige/CoursIA",
        "--out", str(out),
    ])
    assert rc == 0
    assert out.read_text(encoding="utf-8").splitlines() == [SELF_COVER]


def test_7_le_workflow_ne_peut_plus_ecraser_la_liste_en_silence():
    """Garde de non-regression sur le workflow lui-meme : le repli muet
    (``|| echo -n "" > "$out"``) ne doit plus apparaitre dans le CODE.

    Les lignes de commentaire sont ignorees : le workflow documente le
    trou ferme, et un commentaire n'est pas une commande.
    """
    lines = WORKFLOW.read_text(encoding="utf-8").splitlines()
    code = [ln for ln in lines if not ln.lstrip().startswith("#")]
    text = "\n".join(code)
    assert 'echo -n "" > "$out"' not in text, (
        "le workflow reintroduit le repli muet : un echec de l'API "
        "produirait une liste vide et un faux vert"
    )
    assert "|| echo -n" not in text, (
        "le workflow reintroduit un repli muet sur l'echec de l'API"
    )


def test_8_le_workflow_appelle_le_lecteur_echouant():
    """Le job doit appeler le lecteur en Python, pas refaire l'appel en
    shell (le shell peut reintroduire le repli muet)."""
    text = WORKFLOW.read_text(encoding="utf-8")
    assert "scripts/lean/lean_matrix_changed_files.py" in text

#!/usr/bin/env python3
"""Non-regression du job `changes` de ``lean-ci-matrix.yml`` (#22065).

Le trou : les deux lectures de l'API du job etaient repliees en silence
(``|| echo -n "" > "$out"``). Un 403 de quota rendait la liste des
fichiers modifies VIDE, donc ``any=false``, donc le build Lean etait
``skipped`` -- et ``skipped`` se replie en vert : un build qui n'a pas eu
lieu s'affichait comme fait (instance #21999, run 39814286963).

Ces tests verrouillent trois choses :

  1. une lecture d'API en echec **ne peut pas** produire une liste vide
     silencieuse -- l'appelant sort en erreur et **n'ecrit aucun fichier**
     de sortie ;
  2. le workflow lui-meme ne peut pas reintroduire le repli muet ;
  3. depuis le contrat pose par #26739, les deux echecs sont **distincts** et
     celui de mesure
     porte le verdict ``INCONCLUSIVE -- ...`` que les consommateurs d'etats
     savent lire (``scripts/pr_gate.py::parse_inconclusive_message``). Le
     test nourrit le message emis a ce parseur -- le contrat est prouve de
     bout en bout, pas suppose.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
sys.path.insert(0, str(REPO / "scripts"))

from lean_matrix_changed_files import (  # noqa: E402
    EXIT_MEASURE_FAILED,
    EXIT_USAGE,
    INCONCLUSIVE_MARKER,
    ApiError,
    SELF_COVER,
    inconclusive_annotation,
    main,
)
from pr_gate import (  # noqa: E402
    QUOTA_INCONCLUSIVE_CODE,
    parse_inconclusive_message,
)

WORKFLOW = REPO / ".github" / "workflows" / "lean-ci-matrix.yml"


def _boom(*_args, **_kwargs):
    raise ApiError("gh api a echoue (rc=1) : API rate limit exceeded (HTTP 403)")


def test_1_echec_api_ne_produit_aucun_fichier(tmp_path, monkeypatch, capsys):
    """Le cas mesure (#21999) : 403 -> pas de liste vide, sortie non nulle."""
    monkeypatch.setattr("lean_matrix_changed_files._gh_api", _boom)
    monkeypatch.setattr("lean_matrix_changed_files.time.sleep", lambda _s: None)
    out = tmp_path / "changed.txt"
    rc = main([
        "--event", "pull_request", "--repo", "jsboige/CoursIA",
        "--pr", "21999", "--out", str(out), "--sleep", "0",
    ])
    assert rc == EXIT_MEASURE_FAILED
    assert not out.exists(), "un echec de l'API ne doit ecrire aucun fichier"
    assert INCONCLUSIVE_MARKER in capsys.readouterr().out


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
    assert rc == EXIT_MEASURE_FAILED
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


def test_9_l_annotation_emise_est_lue_par_le_gate(tmp_path, monkeypatch, capsys):
    """Le contrat de bout en bout (#26739) : ce que l'organe imprime sur
    stdout quand sa MESURE echoue est exactement ce que le consommateur
    d'etats sait relire.

    Le message passe par la vraie fonction du gate, jamais par une copie
    locale du format : si l'un des deux cotes derive, ce test tombe.
    """
    monkeypatch.setattr("lean_matrix_changed_files._gh_api", _boom)
    monkeypatch.setattr("lean_matrix_changed_files.time.sleep", lambda _s: None)
    out = tmp_path / "changed.txt"
    assert main([
        "--event", "pull_request", "--repo", "jsboige/CoursIA",
        "--pr", "26004", "--out", str(out), "--sleep", "0",
    ]) == EXIT_MEASURE_FAILED

    emitted = [
        line for line in capsys.readouterr().out.splitlines()
        if line.startswith("::error::")
    ]
    assert len(emitted) == 1, "l'echec de mesure doit porter exactement une annotation"
    verdict = parse_inconclusive_message(emitted[0])
    assert verdict is not None, (
        "le gate ne relit pas l'annotation de l'organe : le rouge reste "
        "indiscernable d'un echec de contenu"
    )
    assert verdict["kind"] == "quota-installation"
    assert verdict["detail"].strip()


def test_10_invocation_invalide_sort_en_usage_sans_annotation(tmp_path, capsys):
    """Une invocation fausse reste un defaut a corriger (sortie 1), et ne
    doit PAS s'annoncer INCONCLUSIVE : l'etat du depot n'y est pas inconnu,
    c'est la commande qui est fausse."""
    out = tmp_path / "changed.txt"
    rc = main(["--event", "pull_request", "--repo", "jsboige/CoursIA",
               "--out", str(out)])
    assert rc == EXIT_USAGE
    assert not out.exists()
    captured = capsys.readouterr()
    assert INCONCLUSIVE_MARKER not in captured.out
    assert INCONCLUSIVE_MARKER not in captured.err


def test_11_annotation_sur_une_ligne_et_echappee():
    """Les commandes de workflow interdisent les sauts de ligne et exigent
    l'echappement de `%`, `\\r`, `\\n` : sans cela GitHub tronque le message
    a la premiere ligne, et le detail du 403 disparait."""
    line = inconclusive_annotation("mesure 100% impossible\r\nligne 2")
    assert "\n" not in line and "\r" not in line
    assert "%" not in line.replace("%25", "").replace("%0D", "").replace("%0A", "")
    assert parse_inconclusive_message(line) is not None


def test_12_le_code_de_sortie_est_celui_du_gate():
    """Un nombre, un sens : le verdict INCONCLUSIVE porte le meme code de
    sortie dans le gate et dans la jambe de matrice. Si l'un des deux
    derive, ce test tombe -- c'est le lien qui l'empeche de deriver en
    silence, pas une copie de la valeur."""
    assert EXIT_MEASURE_FAILED == QUOTA_INCONCLUSIVE_CODE
    assert EXIT_USAGE != EXIT_MEASURE_FAILED

"""Tests de l'organe `check_empty_verdict` (issue #21750).

Le motif cherche : un verdict de mesure affiche dans une sortie commitee alors
que la mesure qu'il resume est invalide (reponse vide, ou statut HTTP non-2xx).

Les cas sont ecrits dans les DEUX sens -- ce que l'organe doit attraper (faux
negatifs de l'organe) et ce qu'il ne doit PAS attraper (faux positifs) -- parce
qu'un motif de detection se valide par ses faux negatifs, jamais par ses hits.
"""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path

_MODULE = Path(__file__).resolve().parents[1] / "notebook_tools" / "check_empty_verdict.py"
_spec = importlib.util.spec_from_file_location("check_empty_verdict", _MODULE)
assert _spec and _spec.loader
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)

analyse_block = _mod.analyse_block
analyse_notebook = _mod.analyse_notebook


def test_empty_answer_with_verdict_is_a_finding():
    """Le cas fondateur (#21750) : HTTP 200, corps vide, verdict quand meme."""
    lines = [
        "Statut HTTP avec logit_bias: 200",
        "Réponse avec logit_bias:",
        "Statut HTTP sans logit_bias (1): 200",
        "Réponse sans logit_bias (1):",
        "=> Cohérence vérifiée : les deux appels renvoient la même réponse.",
        "=> Aucune différence détectée. Le logit_bias n'a pas eu d'effet apparent.",
    ]
    hit = analyse_block("endpoint vllm", lines)
    assert hit is not None, "un verdict sur une reponse vide doit etre signale"
    assert any("vide" in r for r in hit["reasons"]), hit["reasons"]
    assert len(hit["verdicts"]) == 2, hit["verdicts"]


def test_http_error_with_verdict_is_a_finding():
    """Un appel en erreur HTTP ne peut pas fonder un verdict de difference."""
    lines = [
        "Statut HTTP avec logit_bias: 400",
        "Réponse avec logit_bias:",
        "Statut HTTP sans logit_bias (1): 200",
        "Réponse sans logit_bias (1): Je suis un assistant IA",
        "=> Différence détectée entre AVEC et SANS logit_bias.",
    ]
    hit = analyse_block("endpoint openai", lines)
    assert hit is not None, "un verdict compare a un appel en erreur doit etre signale"
    assert any("non-2xx" in r for r in hit["reasons"]), hit["reasons"]


def test_clean_block_is_not_a_finding():
    """Controle negatif : toutes les mesures valides, verdict legitime."""
    lines = [
        "Statut HTTP avec logit_bias: 200",
        "Réponse avec logit_bias: Salut! J'ai appelé Qwen.",
        "Statut HTTP sans logit_bias (1): 200",
        "Réponse sans logit_bias (1): Bonjour! Je suis Qwen",
        "=> Cohérence vérifiée : les deux appels renvoient la même réponse.",
        "=> Différence détectée entre AVEC et SANS logit_bias.",
    ]
    assert analyse_block("endpoint local-mini-v2", lines) is None


def test_explicit_error_is_not_a_conclusion():
    """`=> ERREUR` signale un echec : c'est le comportement honnete demande, pas un verdict."""
    lines = [
        "Statut HTTP avec seed: 200",
        "Réponse avec seed:",
        "=> ERREUR : les deux appels renvoient des réponses différentes.",
    ]
    assert analyse_block("endpoint x", lines) is None


def test_measurement_without_verdict_is_not_a_finding():
    """Une mesure invalide SANS verdict n'est pas une conclusion fausse."""
    lines = [
        "Statut HTTP: 500",
        "Réponse: ",
    ]
    assert analyse_block("endpoint y", lines) is None


def test_multiline_response_body_is_counted_empty():
    """Angle mort ASSUME et PINNE (revue Hermes, 2026-10-21, point 1).

    ``Reponse :`` suivi du corps sur la ligne suivante est compte comme une
    reponse VIDE. C'est un faux POSITIF possible, jamais un faux negatif :
    l'organe ne devine pas si la ligne suivante est le corps ou la mesure
    suivante, parce que deviner laisserait une reponse reellement vide se
    cacher derriere une ligne sans rapport.

    Le test epingle ce comportement pour qu'il reste un choix documente et
    non un accident.
    """
    lines = [
        "Réponse:",
        "Bonjour je suis Qwen",
        "=> Cohérence vérifiée : les deux appels renvoient la même réponse.",
    ]
    hit = analyse_block("endpoint multiline", lines)
    assert hit is not None, "le corps sur la ligne suivante compte comme reponse vide"
    assert any("vide" in r for r in hit["reasons"]), hit["reasons"]


def test_diff_base_failure_is_fail_closed(tmp_path):
    """Un diff illisible ne doit PAS degrader en "scan de tout" (revue Hermes, point 2).

    L'ancien comportement attrapait toute exception et rendait un ensemble
    vide : l'organe scannait alors tout ce qu'on lui donnait au lieu des
    seuls carnets touches -- un sweep integral, c'est-a-dire un verdict porte
    sur des carnets que la PR n'a pas touches.
    """
    target = tmp_path / "not_a_repo"
    target.mkdir(parents=True, exist_ok=True)
    try:
        _mod._changed_notebooks("origin/main", target)
    except _mod.MeasurementError as exc:
        message = str(exc)
        assert ("illisible" in message) or ("a rendu" in message), message
    else:
        raise AssertionError(
            "un diff illisible doit lever MeasurementError, "
            "pas degrader silencieusement en ensemble vide"
        )


def test_cli_returns_two_when_the_diff_is_unreadable(tmp_path):
    """Le code de sortie 2 doit dire "non mesurable", pas "aucun finding"."""
    target = tmp_path / "not_a_repo"
    target.mkdir(parents=True, exist_ok=True)
    rc = _mod.main(["--diff-base", "origin/main", str(target)])
    assert rc == 2, rc


def test_changed_notebooks_is_bounded_to_the_pr(tmp_path):
    """La base est resolue en merge-base : un carnet ajoute sur `main` apres le
    point de depart de la branche n'est PAS un carnet de la PR.

    Avec un diff a deux points (`main` contre `HEAD`), ce carnet-la
    remonterait : le garde advisorait alors sur un carnet que la PR n'a pas
    touche -- un faux positif de perimetre, sur un defaut pre-existant.
    """
    import subprocess

    repo = tmp_path / "repo"
    repo.mkdir()

    def git(*args: str) -> str:
        proc = subprocess.run(["git", "-C", str(repo), *args],
                              capture_output=True, text=True, encoding="utf-8",
                              errors="replace", check=True)
        return proc.stdout.strip()

    git("init", "-q")
    git("config", "user.email", "test@example.invalid")
    git("config", "user.name", "test")
    (repo / "a.ipynb").write_text("{}", encoding="utf-8")
    git("add", "a.ipynb")
    git("commit", "-qm", "c1")
    main_branch = git("rev-parse", "--abbrev-ref", "HEAD")

    git("checkout", "-qb", "pr")
    (repo / "b.ipynb").write_text("{}", encoding="utf-8")
    git("add", "b.ipynb")
    git("commit", "-qm", "c2")

    # La base avance APRES le point de depart de la branche.
    git("checkout", "-q", main_branch)
    (repo / "c.ipynb").write_text("{}", encoding="utf-8")
    git("add", "c.ipynb")
    git("commit", "-qm", "c3")
    git("checkout", "-q", "pr")

    changed = _mod._changed_notebooks(main_branch, repo)
    assert changed == {"b.ipynb"}, changed


def test_notebook_level_finding_carries_cell_index(tmp_path=None):
    """Le finding porte l'index de cellule, pour etre localise dans le carnet."""
    nb = {
        "cells": [
            {"cell_type": "markdown", "source": ["titre"], "metadata": {}},
            {
                "cell_type": "code",
                "id": "abc123",
                "source": ["print('x')"],
                "execution_count": 3,
                "metadata": {},
                "outputs": [
                    {
                        "output_type": "stream",
                        "name": "stdout",
                        "text": [
                            "=== Test sur endpoint 'z' ===\n",
                            "Statut HTTP: 200\n",
                            "Réponse: \n",
                            "=> Cohérence vérifiée.\n",
                        ],
                    }
                ],
            },
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path = Path(tmp_path or ".") / "tmp_empty_verdict.ipynb"
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")
    try:
        findings = analyse_notebook(path)
        assert len(findings) == 1, findings
        assert findings[0]["cell_index"] == 1, findings[0]
        assert findings[0]["cell_id"] == "abc123", findings[0]
    finally:
        path.unlink(missing_ok=True)


def test_selftest_passes():
    """Le self-test de l'organe lui-meme doit passer."""
    assert _mod.self_test() == 0


if __name__ == "__main__":
    import tempfile

    for fn in (
        test_empty_answer_with_verdict_is_a_finding,
        test_http_error_with_verdict_is_a_finding,
        test_clean_block_is_not_a_finding,
        test_explicit_error_is_not_a_conclusion,
        test_measurement_without_verdict_is_not_a_finding,
        test_multiline_response_body_is_counted_empty,
        test_selftest_passes,
    ):
        fn()
        print(f"OK: {fn.__name__}")
    with tempfile.TemporaryDirectory() as td:
        test_notebook_level_finding_carries_cell_index(td)
        print("OK: test_notebook_level_finding_carries_cell_index")
        test_diff_base_failure_is_fail_closed(td)
        print("OK: test_diff_base_failure_is_fail_closed")
        test_cli_returns_two_when_the_diff_is_unreadable(td)
        print("OK: test_cli_returns_two_when_the_diff_is_unreadable")
        test_changed_notebooks_is_bounded_to_the_pr(td)
        print("OK: test_changed_notebooks_is_bounded_to_the_pr")
    print("All tests passed.")

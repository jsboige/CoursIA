"""Test check_equivalence: verdict NOTHING_TO_COMPARE quand aucune ligne comparable.

Issue #19562 : avant le fix, le verdict EQUIVALENT 0/0 etait rendu quand le
carnet n'avait aucune sortie text/plain/stream (toutes en MIME riche ignore
par la regle du rendu Quarto). C'etait un faux vert -- une page ayant perdu
toutes ses sorties HTML rendait le meme verdict.

Le fix : verdict dedie NOTHING_TO_COMPARE, code de sortie 5 (distinct
d'EQUIVALENT rc=0). #18911 (le lecteur du verdict dans la CI) doit le
traiter comme "non verifie", pas comme "verifie".

Temoins verifies :
1. Carnet avec sorties MIME riches uniquement -> NOTHING_TO_COMPARE rc=5
2. Carnet vide (aucune sortie) -> NOTHING_TO_COMPARE rc=5
3. Sortie identique a une ligne source -> exclue -> NOTHING_TO_COMPARE rc=5
4. Sortie text/plain -> n'est PAS NOTHING_TO_COMPARE
5. Le help documente le code 5

Strategie : on importe directement la fonction check_equivalence et on
mock fetch_page, ce qui evite la dependance reseau et la confusion sur
les paths absolus Windows.
"""
import json
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

# Permet d'importer le module sans setup pytest
sys.path.insert(0, str(Path(__file__).parent.parent))
import check_equivalence as ce


def _make_notebook(tmp: Path, name: str, outputs: list, source: list = None) -> Path:
    """Construit un carnet minimal avec la liste de outputs donnee."""
    if source is None:
        source = ["x = 1"]
    nb = {
        "cells": [
            {
                "cell_type": "code",
                "execution_count": 1,
                "metadata": {},
                "source": source,
                "outputs": outputs,
            }
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    p = tmp / name
    p.write_text(json.dumps(nb), encoding="utf-8")
    return p


def _check_with_mock_page(nb_path: Path, page_html: str = "<html></html>") -> dict:
    """Lance check_equivalence en mockant fetch_page avec une page donnee."""
    with patch.object(ce, "fetch_page", return_value=(200, page_html, None)):
        with patch.object(ce, "DEFAULT_BASE_URL", "https://example.test"):
            return ce.check_equivalence(str(nb_path))


def test_mime_riche_uniquement_rien_a_comparer(tmp_path):
    """Sorties text/html uniquement (regle du rendu Quarto) -> NOTHING_TO_COMPARE."""
    nb = _make_notebook(tmp_path, "rich.ipynb", [
        {
            "output_type": "display_data",
            "data": {"text/html": ["<div>rich output</div>"], "text/plain": ["<div>rich output</div>"]},
            "metadata": {},
        }
    ])
    v = _check_with_mock_page(nb, "<html>whatever</html>")
    assert v["verdict"] == "NOTHING_TO_COMPARE", f"verdict attendu NOTHING_TO_COMPARE, got: {v!r}"
    assert v["total_lines"] == 0
    assert v["found_lines"] == 0
    assert v["missing_lines"] == []


def test_text_plain_pas_nothing_to_compare(tmp_path):
    """Sortie text/plain (ligne comparable) ne doit PAS etre NOTHING_TO_COMPARE."""
    nb = _make_notebook(tmp_path, "plain.ipynb", [
        {
            "output_type": "display_data",
            "data": {"text/plain": "valeur 42"},
            "metadata": {},
        }
    ])
    # Page qui contient "valeur 42" -> EQUIVALENT (et non NOTHING_TO_COMPARE)
    v = _check_with_mock_page(nb, "<html>valeur 42 dans la page</html>")
    assert v["verdict"] == "EQUIVALENT", f"verdict attendu EQUIVALENT, got: {v!r}"
    assert v["total_lines"] == 1
    assert v["found_lines"] == 1


def test_text_plain_manquant_donne_lost_outputs(tmp_path):
    """Sortie text/plain absente de la page -> LOST_OUTPUTS (et non NOTHING_TO_COMPARE)."""
    nb = _make_notebook(tmp_path, "plain_missing.ipynb", [
        {
            "output_type": "display_data",
            "data": {"text/plain": "valeur unique introuvable"},
            "metadata": {},
        }
    ])
    v = _check_with_mock_page(nb, "<html>rien ici</html>")
    assert v["verdict"] == "LOST_OUTPUTS", f"verdict attendu LOST_OUTPUTS, got: {v!r}"
    assert v["total_lines"] == 1
    assert v["found_lines"] == 0


def test_carnet_vide_aucune_sortie(tmp_path):
    """Carnet sans aucune sortie -> NOTHING_TO_COMPARE."""
    nb = _make_notebook(tmp_path, "empty.ipynb", [])
    v = _check_with_mock_page(nb, "<html></html>")
    assert v["verdict"] == "NOTHING_TO_COMPARE", f"verdict attendu NOTHING_TO_COMPARE, got: {v!r}"


def test_sortie_dans_sources_est_exclue(tmp_path):
    """Une sortie identique a une ligne source n'est pas comparable."""
    nb = _make_notebook(
        tmp_path, "src_dup.ipynb",
        outputs=[{
            "output_type": "stream",
            "name": "stdout",
            "text": "x = 1",  # meme que la source par defaut
        }],
    )
    v = _check_with_mock_page(nb, "<html></html>")
    assert v["verdict"] == "NOTHING_TO_COMPARE", f"verdict attendu NOTHING_TO_COMPARE, got: {v!r}"


def test_rc_distinct_equivalent_et_nothing_to_compare():
    """Le main() retourne rc=5 pour NOTHING_TO_COMPARE, rc=0 pour EQUIVALENT."""
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        # NOTHING_TO_COMPARE -> rc=5
        nb_nothing = _make_notebook(tmp_path, "n.ipynb", [
            {"output_type": "display_data", "data": {"text/html": ["<x/>"], "text/plain": ["<x/>"]}, "metadata": {}}
        ])
        with patch.object(ce, "fetch_page", return_value=(200, "<html></html>", None)):
            with patch.object(ce, "DEFAULT_BASE_URL", "https://example.test"):
                rc = ce.main(["--notebook", str(nb_nothing)])
        assert rc == 5, f"NOTHING_TO_COMPARE doit rendre rc=5, got {rc}"

        # EQUIVALENT -> rc=0
        nb_eq = _make_notebook(tmp_path, "e.ipynb", [
            {"output_type": "display_data", "data": {"text/plain": "trouve"}, "metadata": {}}
        ])
        with patch.object(ce, "fetch_page", return_value=(200, "<html>trouve</html>", None)):
            with patch.object(ce, "DEFAULT_BASE_URL", "https://example.test"):
                rc = ce.main(["--notebook", str(nb_eq)])
        assert rc == 0, f"EQUIVALENT doit rendre rc=0, got {rc}"


def test_help_documentation():
    """Le help documente le code de sortie 5 / NOTHING_TO_COMPARE."""
    out = subprocess.run(
        ["python", str(Path(__file__).parent.parent / "check_equivalence.py"), "--help"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    text = out.stdout + out.stderr
    assert "5" in text and "NOTHING_TO_COMPARE" in text, \
        f"Codes de sortie non documentes dans le help: {text!r}"


def main():
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        test_mime_riche_uniquement_rien_a_comparer(tmp_path)
        test_text_plain_pas_nothing_to_compare(tmp_path)
        test_text_plain_manquant_donne_lost_outputs(tmp_path)
        test_carnet_vide_aucune_sortie(tmp_path)
        test_sortie_dans_sources_est_exclue(tmp_path)
    test_rc_distinct_equivalent_et_nothing_to_compare()
    test_help_documentation()
    print("OK: 7/7 tests passent")


if __name__ == "__main__":
    main()

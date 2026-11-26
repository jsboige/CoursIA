# Tests de merge_executed_outputs : fusion des sorties d'un carnet execute a
# distance (QC Cloud) dans le carnet de la branche.
# Comportements couverts : copie outputs + execution_count, markdown intact,
# refus sur code different, refus sur carnet execute incomplet, empreinte
# insensible au markdown, mise en forme JSON du fichier cible conservee.

import hashlib
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from merge_executed_outputs import fingerprint, main, normalise_output  # noqa: E402


def _nb(cells):
    return {"cells": cells, "metadata": {"kernelspec": {"name": "python3"}},
            "nbformat": 4, "nbformat_minor": 5}


def _md(text):
    return {"cell_type": "markdown", "id": "m", "metadata": {}, "source": [text]}


def _code(src, outputs=None, count=None):
    return {"cell_type": "code", "execution_count": count, "id": "c", "metadata": {},
            "outputs": outputs or [], "source": src}


def _write(path, nb, indent=1, sort_keys=True):
    path.write_text(json.dumps(nb, indent=indent, ensure_ascii=False,
                               sort_keys=sort_keys) + "\n", encoding="utf-8")
    return str(path)


def _stream(text):
    return {"name": "stdout", "output_type": "stream", "text": text}


def test_merge_copies_outputs_and_keeps_markdown(tmp_path):
    target = _write(tmp_path / "t.ipynb",
                    _nb([_md("texte a jour"), _code(["x = 1\n", "print(x)"])]))
    executed = _write(tmp_path / "e.ipynb",
                      _nb([_md("ancien texte"),
                           _code(["x = 1\n", "print(x)"], [_stream("1\n")], 1)]))
    assert main([target, executed]) == 0
    nb = json.loads(Path(target).read_text(encoding="utf-8"))
    assert nb["cells"][0]["source"] == ["texte a jour"]
    assert nb["cells"][1]["execution_count"] == 1
    assert nb["cells"][1]["outputs"] == [_stream(["1\n"])]


def test_source_mismatch_refused_and_target_untouched(tmp_path):
    target = _write(tmp_path / "t.ipynb", _nb([_code("x = 1")]))
    before = Path(target).read_bytes()
    executed = _write(tmp_path / "e.ipynb", _nb([_code("x = 2", [], 1)]))
    assert main([target, executed]) == 1
    assert Path(target).read_bytes() == before


def test_code_cell_count_mismatch_refused(tmp_path):
    target = _write(tmp_path / "t.ipynb", _nb([_code("a = 1")]))
    executed = _write(tmp_path / "e.ipynb",
                      _nb([_code("a = 1", [], 1), _code("b = 2", [], 2)]))
    assert main([target, executed]) == 1


def test_unexecuted_cell_refused_unless_allowed(tmp_path):
    # Carnet enregistre sans sorties (Run All sans enregistrement, ou depot
    # par un assistant qui ne persiste pas les sorties) : execution_count nul.
    target = _write(tmp_path / "t.ipynb", _nb([_code("a = 1"), _code("b = 2")]))
    executed = _write(tmp_path / "e.ipynb", _nb([_code("a = 1", [], 1), _code("b = 2")]))
    assert main([target, executed]) == 2
    assert main([target, executed, "--allow-incomplete"]) == 0


def test_error_output_refused(tmp_path):
    target = _write(tmp_path / "t.ipynb", _nb([_code("1/0")]))
    err = {"ename": "ZeroDivisionError", "evalue": "division by zero",
           "output_type": "error", "traceback": []}
    executed = _write(tmp_path / "e.ipynb", _nb([_code("1/0", [err], 1)]))
    assert main([target, executed]) == 2


def test_dry_run_writes_nothing(tmp_path):
    target = _write(tmp_path / "t.ipynb", _nb([_code("a = 1")]))
    before = Path(target).read_bytes()
    executed = _write(tmp_path / "e.ipynb", _nb([_code("a = 1", [_stream("ok\n")], 1)]))
    assert main([target, executed, "--dry-run"]) == 0
    assert Path(target).read_bytes() == before


def test_fingerprint_ignores_markdown_and_matches_formula():
    a = _nb([_md("un"), _code(["x = 1\n", "y = 2"]), _code("z = 3")])
    b = _nb([_md("deux"), _code("x = 1\ny = 2"), _md("trois"), _code("z = 3")])
    expected = hashlib.sha256("x = 1\ny = 2\nz = 3".encode("utf-8")).hexdigest()[:16]
    assert fingerprint(a) == fingerprint(b) == expected


def test_layout_preserved_when_outputs_identical(tmp_path):
    # Fusionner un carnet avec lui-meme ne doit changer aucun octet, quelle que
    # soit la mise en forme du fichier cible.
    nb = _nb([_md("é"), _code(["x = 1\n", "x"], [{
        "data": {"text/plain": ["1"]}, "execution_count": 1, "metadata": {},
        "output_type": "execute_result"}], 1)])
    for indent, sort_keys in ((1, True), (2, False)):
        path = tmp_path / f"t{indent}.ipynb"
        _write(path, nb, indent=indent, sort_keys=sort_keys)
        before = path.read_bytes()
        assert main([str(path), str(path)]) == 0
        assert path.read_bytes() == before


def test_normalise_output_splits_text_mimes_only():
    out = normalise_output({"output_type": "display_data", "metadata": {},
                            "data": {"text/plain": "a\nb", "image/png": "iVBOR\nw0"}})
    assert out["data"]["text/plain"] == ["a\n", "b"]
    assert out["data"]["image/png"] == "iVBOR\nw0"

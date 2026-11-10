"""Tests de scripts/notebook_tools/fix_markdown_cell_schema.py (issue #20167).

Couvre :
  - retrait de execution_count / outputs sur une cellule markdown (sortie vide
    et sortie non vide) ;
  - cellule de code jamais touchee ;
  - aller-retour octet a octet sur un carnet sain, pour plusieurs formats ;
  - reecriture qui conserve le format detecte (indentation, ensure_ascii,
    ordre des cles, fin de fichier), la seule difference etant les cles ;
  - exception : un fichier non reproductible n'est jamais reecrit ;
  - --check rend 1 puis 0 apres --apply ;
  - le carnet corrige est valide au schema nbformat ;
  - le balayage --all exclut les dossiers habituels.
"""

import json
import subprocess
import sys
from pathlib import Path

import pytest

_tools_dir = str(Path(__file__).resolve().parent.parent)
if _tools_dir not in sys.path:
    sys.path.insert(0, _tools_dir)

import fix_markdown_cell_schema as fmcs  # noqa: E402
from fix_markdown_cell_schema import (  # noqa: E402
    detect_format,
    find_defects,
    iter_notebooks,
    load_notebook,
    main,
    plan_fix,
    render,
    strip_markdown_keys,
)

SCRIPT = Path(fmcs.__file__)
HEALTHY_FORMAT = (1, False, True, "\n")


def _nb(cells, minor=5):
    return {
        "cells": cells,
        "metadata": {
            "kernelspec": {"display_name": "Python 3", "language": "python", "name": "python3"},
            "language_info": {"name": "python"},
        },
        "nbformat": 4,
        "nbformat_minor": minor,
    }


def _md(source, cell_id, **extra):
    cell = {"cell_type": "markdown", "id": cell_id, "metadata": {}, "source": source}
    cell.update(extra)  # cles ajoutees en dernier : outputs est la derniere cle
    return cell


def _code(source, cell_id, count=1, outputs=None):
    # Ordre d'insertion non trie : sans cela sort_keys ne discrimine rien.
    return {
        "cell_type": "code",
        "id": cell_id,
        "metadata": {},
        "source": source,
        "execution_count": count,
        "outputs": [] if outputs is None else outputs,
    }


def _write(path: Path, nb: dict, fmt=HEALTHY_FORMAT) -> str:
    text = render(nb, fmt)
    path.write_bytes(text.encode("utf-8"))
    return text


def _stream_output(text):
    return {"name": "stdout", "output_type": "stream", "text": [text]}


def test_markdown_cell_with_empty_outputs_and_null_count_is_cleaned(tmp_path):
    nb = _nb([
        _md(["# Titre\n"], "m1", execution_count=None, outputs=[]),
        _code(["x = 1\n"], "c1"),
    ])
    path = tmp_path / "a.ipynb"
    text = _write(path, nb)
    loaded_text, loaded = load_notebook(path)
    assert loaded_text == text

    new_text, motif = plan_fix(loaded_text, loaded)

    assert motif == "" and new_text is not None
    out = json.loads(new_text)
    markdown = out["cells"][0]
    assert "execution_count" not in markdown and "outputs" not in markdown
    assert markdown == {"cell_type": "markdown", "id": "m1", "metadata": {}, "source": ["# Titre\n"]}


def test_markdown_cell_with_non_empty_outputs_is_cleaned(tmp_path):
    nb = _nb([
        _md(["Texte\n"], "m2", outputs=[_stream_output("residu de copie\n")], execution_count=3),
    ])
    path = tmp_path / "b.ipynb"
    _write(path, nb)
    text, loaded = load_notebook(path)

    new_text, motif = plan_fix(text, loaded)

    assert motif == "" and new_text is not None
    out = json.loads(new_text)
    assert set(out["cells"][0]) == {"cell_type", "id", "metadata", "source"}
    assert out["cells"][0]["source"] == ["Texte\n"]


def test_code_cell_is_never_touched(tmp_path):
    code = _code(["print('ok')\n"], "c9", count=7,
                 outputs=[_stream_output("ok\n"), _stream_output("encore\n")])
    nb = _nb([
        _md(["# A\n"], "m3", outputs=[]),
        code,
    ])
    path = tmp_path / "c.ipynb"
    _write(path, nb)
    text, loaded = load_notebook(path)

    new_text, _ = plan_fix(text, loaded)

    out = json.loads(new_text)
    assert out["cells"][1] == code  # execution_count et sorties de code intacts
    assert find_defects(out) == []


def test_find_defects_flags_markdown_only(tmp_path):
    nb = _nb([
        _md(["a\n"], "m4", execution_count=None),
        _code(["b\n"], "c4", count=None, outputs=[]),
        _md(["c\n"], "m5", outputs=[]),
    ])
    defects = find_defects(nb)
    assert [(d.index, d.keys) for d in defects] == [
        (0, ("execution_count",)),
        (2, ("outputs",)),
    ]


def test_strip_does_not_mutate_the_input():
    nb = _nb([_md(["x\n"], "m6", outputs=[])])
    before = json.dumps(nb, sort_keys=True)
    strip_markdown_keys(nb)
    assert json.dumps(nb, sort_keys=True) == before


@pytest.mark.parametrize("fmt", [
    (1, False, True, "\n"),
    (1, False, True, ""),
    (1, False, False, "\n"),
    (4, True, False, ""),
    (2, False, True, "\n"),
    (1, True, True, "\n"),
])
def test_round_trip_is_byte_identical_on_a_healthy_notebook(tmp_path, fmt):
    nb = _nb([
        _md(["# Sain\n", "Texte accentu\u00e9 : \u00e9l\u00e8ve\n"], "h1"),
        _code(["y = 2\n"], "h2", count=2, outputs=[_stream_output("2\n")]),
    ])
    path = tmp_path / "healthy.ipynb"
    text = _write(path, nb, fmt)
    loaded_text, loaded = load_notebook(path)

    assert detect_format(loaded_text, loaded) == fmt
    assert render(loaded, fmt) == text


@pytest.mark.parametrize("fmt", [
    (1, False, True, "\n"),
    (4, True, False, ""),
    (2, False, True, "\n"),
    (1, True, True, "\n"),
])
def test_apply_preserves_the_detected_format_and_only_removes_keys(tmp_path, fmt):
    nb = _nb([
        _md(["# Titre accentu\u00e9 : \u00e9l\u00e8ve\n"], "f1", execution_count=None, outputs=[]),
        _code(["z = 3\n"], "f2", count=3, outputs=[_stream_output("3\n")]),
        _md(["Suite\n"], "f3", outputs=[_stream_output("reste\n")]),
    ])
    path = tmp_path / "fmt.ipynb"
    _write(path, nb, fmt)

    assert main(["--apply", str(path)]) == 0

    new_bytes = path.read_bytes().decode("utf-8")
    expected = render(strip_markdown_keys(nb), fmt)
    assert new_bytes == expected
    assert detect_format(new_bytes, json.loads(new_bytes)) == fmt


def test_apply_on_a_clean_notebook_does_not_rewrite_it(tmp_path):
    nb = _nb([_md(["# Propre\n"], "p1"), _code(["1\n"], "p2", count=1, outputs=[])])
    path = tmp_path / "clean.ipynb"
    text = _write(path, nb)
    mtime = path.stat().st_mtime_ns

    assert main(["--apply", str(path)]) == 0

    assert path.read_bytes().decode("utf-8") == text
    assert path.stat().st_mtime_ns == mtime


def test_check_returns_one_then_zero_after_apply(tmp_path):
    nb = _nb([_md(["# A\n"], "k1", execution_count=None, outputs=[])])
    path = tmp_path / "check.ipynb"
    _write(path, nb)

    assert main(["--check", str(path)]) == 1
    assert main(["--apply", str(path)]) == 0
    assert main(["--check", str(path)]) == 0


def test_non_reproducible_format_is_an_exception_and_is_never_rewritten(tmp_path):
    # Une ligne blanche parasite dans la liste ``cells`` : JSON valide, mais
    # aucun format candidat ne reproduit ces octets.
    nb = _nb([_md(["# A\n"], "x1", outputs=[]), _code(["1\n"], "x2", count=1, outputs=[])])
    path = tmp_path / "exception.ipynb"
    text = render(nb, HEALTHY_FORMAT).replace('"cells": [\n', '"cells": [\n\n', 1)
    path.write_bytes(text.encode("utf-8"))
    loaded_text, loaded = load_notebook(path)
    assert detect_format(loaded_text, loaded) is None

    new_text, motif = plan_fix(loaded_text, loaded)
    assert new_text is None and "non reproductible" in motif

    assert main(["--apply", str(path)]) == 1
    assert path.read_bytes().decode("utf-8") == text
    assert main(["--check", str(path)]) == 1  # le defaut reste visible


def test_non_reproducible_format_from_escaped_characters_is_an_exception(tmp_path):
    # Un caractere accentue ecrit en escape dans un carnet ensure_ascii=False.
    nb = _nb([_md(["\u00e9t\u00e9 eleve\n"], "y1", outputs=[])])
    path = tmp_path / "escape.ipynb"
    # Un seul "e accent" echappe, les autres bruts : aucun format ne reproduit.
    text = render(nb, HEALTHY_FORMAT).replace("\u00e9t\u00e9", "\\u00e9t\u00e9", 1)
    path.write_bytes(text.encode("utf-8"))
    loaded_text, loaded = load_notebook(path)

    assert detect_format(loaded_text, loaded) is None
    assert main(["--apply", str(path)]) == 1
    assert path.read_bytes().decode("utf-8") == text


def test_unreadable_file_returns_two(tmp_path):
    path = tmp_path / "broken.ipynb"
    path.write_text("{ pas du json", encoding="utf-8")
    assert main(["--check", str(path)]) == 2


def test_fixed_notebook_is_valid_nbformat(tmp_path):
    nbformat = pytest.importorskip("nbformat")
    cells = [
        _md(["# Titre\n"], "v1", execution_count=None, outputs=[]),
        _code(["print(1)\n"], "v2", count=1, outputs=[_stream_output("1\n")]),
    ]
    nb = _nb(cells)
    with pytest.raises(nbformat.ValidationError):
        nbformat.validate(nbformat.from_dict(nb))

    path = tmp_path / "valid.ipynb"
    _write(path, nb)
    assert main(["--apply", str(path)]) == 0

    nbformat.validate(nbformat.read(str(path), as_version=4))


def test_iter_notebooks_excludes_the_usual_directories(tmp_path):
    root = tmp_path / "MyIA.AI.Notebooks"
    kept = root / "Series" / "S-01.ipynb"
    excluded = [
        root / "Series" / "_archive" / "old.ipynb",
        root / "_site" / "page.ipynb",
        root / ".lake" / "build.ipynb",
        root / "Series" / "checkpoints" / "ck.ipynb",
        root / "Series" / "node_modules" / "nm.ipynb",
        root / "Series" / "quantbook_output.ipynb",
    ]
    for path in [kept, *excluded]:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("{}", encoding="utf-8")

    assert list(iter_notebooks(root, tmp_path)) == [kept]


def test_paths_only_prints_just_the_defective_paths(tmp_path, capsys):
    defective = tmp_path / "d.ipynb"
    healthy = tmp_path / "h.ipynb"
    _write(defective, _nb([_md(["x\n"], "q1", outputs=[])]))
    _write(healthy, _nb([_md(["y\n"], "q2")]))

    assert main(["--paths-only", str(defective), str(healthy)]) == 0

    out = capsys.readouterr().out.strip().splitlines()
    assert out == [str(defective)]


def test_cli_check_exit_code_through_a_subprocess(tmp_path):
    path = tmp_path / "cli.ipynb"
    _write(path, _nb([_md(["x\n"], "s1", execution_count=None, outputs=[])]))
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "--check", str(path)],
        capture_output=True, text=True, encoding="utf-8",
    )
    assert result.returncode == 1, result.stdout + result.stderr
    assert "FAUTIF" in result.stdout

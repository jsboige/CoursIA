# Tests unitaires du stripper de magics IPython et des predicats associes
# (check_cell_source_parses, garde pre-commit #13326).
# Comportements couverts : drop des lignes magiques/shell, preservation du
# `%` en position de continuation (PR #13328), et consommation de la ligne
# logique complete d'une magie chainee par backslashes (TP #21036).

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check_cell_source_parses import (  # noqa: E402
    _is_line_continuation,
    _strip_ipython_magics,
)


def test_simple_magic_dropped():
    src = "%matplotlib inline\nx = 1"
    assert _strip_ipython_magics(src) == "x = 1"


def test_shell_line_dropped():
    src = "!pip install foo\ny = 2"
    assert _strip_ipython_magics(src) == "y = 2"


def test_percent_in_continuation_position_kept():
    # PR #13328 : `%` apres une parenthese ouverte = operateur de formatage,
    # pas une magie -- la ligne doit survivre.
    src = 'print("value %"\n      % (a, b))'
    out = _strip_ipython_magics(src)
    assert "% (a, b))" in out


def test_magic_with_backslash_continuations_fully_dropped():
    # TP #21036 : la cellule d'installation %pip chainee par backslashes.
    # Les lignes physiques de continuation appartiennent a la magie.
    src = (
        "# commentaire\n"
        "%pip install -q kokoro-onnx==0.6.1 numpy==2.1.3 \\\n"
        "    faster-whisper==1.2.1 soundfile==0.14.0 \\\n"
        "    requests==2.32.4\n"
        "x = 1\n"
    )
    out = _strip_ipython_magics(src)
    assert "faster-whisper" not in out
    assert "requests" not in out
    assert out.endswith("x = 1")


def test_escaped_backslash_even_parity_not_a_continuation():
    # Un backslash echappe (parite paire) ne continue pas la ligne logique :
    # la ligne suivante reste du Python ordinaire.
    src = "%time value = 'a\\\\'\nfollow = 2"
    out = _strip_ipython_magics(src)
    assert "follow = 2" in out


def test_python_backslash_continuation_preserved():
    # Une continuation legitime d'une ligne NON magique doit rester intacte.
    src = "total = 1 + \\\n    2\nprint(total)"
    assert _strip_ipython_magics(src) == src


def test_cell_magic_first_line_dropped():
    src = "%%time\nx = compute()"
    assert _strip_ipython_magics(src) == "x = compute()"


def test_triple_quote_state_survives_magic_drop():
    src = 'text = """ligne\n%pas une magie dans la chaine\nfin"""\nx = 1'
    out = _strip_ipython_magics(src)
    assert "%pas une magie dans la chaine" in out


def test_is_line_continuation_parity():
    assert _is_line_continuation("foo \\")
    assert _is_line_continuation("foo \\  ")
    assert not _is_line_continuation("foo \\\\")
    assert not _is_line_continuation("foo")
    assert not _is_line_continuation("")


def test_indented_magic_replaced_by_pass():
    # TP #21036 : magie = corps d'un bloc if. Le drop laisserait le
    # header sans corps -> la magie indentee devient `pass`.
    src = (
        "if run_inflect_nano:\n"
        "    %pip install -q inflect-nano\n"
        "x = 1\n"
    )
    out = _strip_ipython_magics(src)
    assert "    pass" in out
    assert "inflect-nano" not in out
    compile(out, "<t>", "exec")


def test_indented_magic_last_line_flushes_pass():
    src = "if flag:\n    %time compute()"
    out = _strip_ipython_magics(src)
    assert out.endswith("    pass")
    compile(out, "<t>", "exec")


def test_two_indented_magics_single_block_still_compiles():
    src = "if flag:\n    %pip install a\n    %pip install b\ny = 2\n"
    out = _strip_ipython_magics(src)
    compile(out, "<t>", "exec")
    assert "y = 2" in out

#!/usr/bin/env python3
"""Tests du garde `rm -rf` sur variable (check_rm_rf_guards, #20208).

Un detecteur se valide par ce qu'il rend FAUX, pas par ses hits : les cas
negatifs ci-dessous sont ecrits en premier, et chacun correspond a une forme
reelle rencontree pendant la mesure qui a fonde l'organe.

Run: `python -m pytest scripts/tests/test_check_rm_rf_guards.py`.
"""

from __future__ import annotations

import sys
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
if str(CI_DIR) not in sys.path:
    sys.path.insert(0, str(CI_DIR))

import check_rm_rf_guards as g  # noqa: E402


def classes(text: str) -> list[str]:
    return [s["klass"] for s in g.scan_text(text, "f.sh")]


# --- cas POSITIFS : l'organe DOIT voir ces sites -------------------------

def test_escape_root_flagged():
    assert classes('rm -rf "$VAR/dir"') == ["ESCAPE_ROOT"]


def test_escape_root_indented():
    """Le `rm` indentee est une commande en debut de ligne.

    Regression mesuree : sans `^[ \\t]*`, l'organe ne voyait que les sites en
    colonne 0 -- 2 sites trouves sur 8 attendus pendant l'acceptance.
    """
    assert classes('  rm -rf "$VAR/dir"') == ["ESCAPE_ROOT"]


def test_escape_root_after_separator():
    """Un `rm` precede d'un separateur de commande est un debut de commande.

    La commande est assemblee par morceaux : ecrite d'un seul litteral, ce
    fixture ressemblerait, dans la SOURCE, a l'invocation qu'il teste, et
    l'organe -- qui balaie les `.py` -- le compterait comme un site
    (angle mort mesure au #20209 : la baseline avait deja perime la-dessus).
    """
    assert classes("cd /tmp; " "rm -rf " '"$VAR/dir"') == ["ESCAPE_ROOT"]


def test_escape_root_braced():
    assert classes('rm -rf "${VAR}/dir"') == ["ESCAPE_ROOT"]


def test_unquoted_var_flagged():
    assert classes("rm -rf $VAR/dir") == ["UNQUOTED_VAR"]


def test_two_arguments_on_one_line_both_counted():
    """`rm -rf "$R/a" "$R/b"` : deux fuites distinctes, pas une."""
    assert classes('rm -rf "$R/a" "$R/b"') == ["ESCAPE_ROOT", "ESCAPE_ROOT"]


def test_composite_word_var_then_glob_is_escape_root():
    """`rm -rf "$X"/*` -> `rm -rf /*` si X est vide : la classe CATASTROPHIQUE.

    Angle mort mesure (#20209) : `"$X"/*` est **un** mot shell (`"$X"` puis
    `/*`). Un decoupage en tokens separes classait le premier BARE_VAR (benin)
    et ignorait le second, prive de `$` -- la forme nommee par le docstring
    passait donc invisible, et une preuve « 0 occurrence » etait fausse.
    """
    assert classes('rm -rf "$X"/*') == ["ESCAPE_ROOT"]


def test_composite_word_var_then_suffix_is_escape_root():
    """`rm -rf "$X"/dir` : meme mot composite, meme fuite hors racine."""
    assert classes('rm -rf "$X"/dir') == ["ESCAPE_ROOT"]


def test_two_invocations_on_one_line_are_two_sites():
    """`search` ne rendait que la PREMIERE invocation `rm` d'une ligne.

    Deux commandes separees par `;` sont deux sites : n'en voir qu'un laissait
    la seconde fuite hors de toute mesure.
    """
    cmd = "rm -rf " '"$A/x"; ' "rm -rf " '"$B/y"'
    found = g.scan_text(cmd, "f.sh")
    assert [s["word"] for s in found] == ['"$A/x"', '"$B/y"']
    assert {s["line"] for s in found} == {1}


# --- cas NEGATIFS : l'organe NE DOIT PAS voir ces sites ------------------

def test_bare_quoted_var_is_benign():
    """`rm -rf "$VAR"` -> `rm -rf ""` : `rm` refuse l'operande vide."""
    assert classes('rm -rf "$VAR"') == []


def test_guarded_by_parameter_expansion():
    """`${VAR:?}` couvre unset ET vide : c'est la garde acceptee."""
    assert classes('rm -rf "${VAR:?}/dir"') == []


def test_single_quoted_expansion_is_literal_not_a_leak():
    """`'${X}/work'` : les guillemets SIMPLES empechent toute expansion.

    Faux positif mesure (#20209) : le mot etait classe ESCAPE_ROOT alors qu'il
    designe un repertoire litteralement nomme `${X}/work` -- aucune fuite hors
    racine, et rien a reparer.
    """
    assert classes("rm -rf '${X}/work'") == []


def test_set_u_is_not_accepted_as_a_guard():
    """`set -u` ne couvre que l'unset, PAS le cas vide : la variable vide passe.

    Le fichier ci-dessous pose `set -u` et laisse la fuite : l'organe doit
    continuer a la voir, sinon il blanchit exactement le cas qu'il vise.
    """
    text = 'set -u\nVAR=""\nrm -rf "$VAR/dir"\n'
    assert classes(text) == ["ESCAPE_ROOT"]


def test_not_recursive_is_out_of_scope():
    """`rm -f` seul ne supprime pas d'arborescence."""
    assert classes('rm -f "$VAR/dir"') == []


def test_git_rm_is_not_a_shell_rm():
    assert classes('git rm -rf "$VAR/dir"') == []


def test_docker_rm_is_not_a_shell_rm():
    """`docker-compose rm -f $Services` a ete un faux positif de la mesure."""
    assert classes("docker-compose rm -f $Services") == []


def test_python_string_trap_is_not_counted():
    """Chaine Python construisant une commande shell : le shell emis est quote.

    Forme reelle : `scripts/notebook_tools/nse_reproduction.py:158`.
    """
    line = '''        "trap 'rm -rf \\"$allowed\\" \\"$denied\\"' EXIT; "'''
    assert classes(line) == []


def test_arguments_stop_at_the_command_separator():
    """Le `"$D/x"` du `mkdir` qui suit ne doit pas compter comme argument du `rm`.

    Regression mesuree : `rm -rf "$D/x"; mkdir -p "$D/x"` rendait DEUX sites.
    """
    found = g.scan_text('rm -rf "$D/x"; mkdir -p "$D/x"', "f.sh")
    assert len(found) == 1
    assert found[0]["word"] == '"$D/x"'


def test_escaped_quote_in_python_does_not_create_a_site():
    assert classes('print("rm -rf $X/y")') == []


# --- baseline ------------------------------------------------------------

def test_baseline_key_survives_line_shift(tmp_path):
    """La cle est fichier + argument : inserer des lignes ne la perime pas."""
    site = {"file": "a.sh", "line": 10, "word": '"$D/x"', "klass": "ESCAPE_ROOT",
            "var": "D", "why": ""}
    moved = dict(site, line=99)
    assert g._key(site) == g._key(moved)


def test_baselined_site_is_not_new(tmp_path):
    first = g.scan_text('rm -rf "$D/x"', "a.sh")
    text = "\n".join(g._key(s) for s in first) + "\n"
    bl = tmp_path / "baseline.txt"
    bl.write_text(text, encoding="utf-8")
    loaded = g.load_baseline(bl)
    assert all(g._key(s) in loaded for s in first)


def test_baseline_ignores_comments_and_blanks(tmp_path):
    bl = tmp_path / "b.txt"
    bl.write_text("# commentaire\n\n  \na.sh:\"$D/x\"\n", encoding="utf-8")
    assert g.load_baseline(bl) == {'a.sh:"$D/x"'}


def test_missing_baseline_is_empty_not_an_error(tmp_path):
    assert g.load_baseline(tmp_path / "absent.txt") == set()
